#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

#include "sds.h"
#include "chan.h"
#include "prelude.h"
#include "runtime.h"

#define myalloc malloc
#define myfree free




// initialize
pthread_attr_t attr;

void begin_run(void) {
  const rlim_t stacksize = 0xf000000;
  struct rlimit rl;
  getrlimit(RLIMIT_STACK, &rl);
  if (rl.rlim_cur < stacksize) {
    rl.rlim_cur = stacksize;
    setrlimit(RLIMIT_STACK, &rl);
  }
  srand(time(0));
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, stacksize);
  return;
}

void end_run(void) {
  pthread_exit(NULL);
}




// core
#define sizeofclo(env_size) (2 * sizeof(int) + sizeof(void(*)(void)) + env_size * sizeof(intptr_t))

typedef struct {
    unsigned int env_smax;      // maximum size
    unsigned int env_size;      // current size
    intptr_t (*fn)(intptr_t[]); // function
    intptr_t env[];             // layout: [self,fvs,args]
} clo_block;

typedef clo_block* clo_t;

void mkclo(intptr_t *lhs, intptr_t (*fn)(intptr_t[]), unsigned int fvc, unsigned int argc) {
    // layout: [env_max,env_size,fn,[self,fvs,_]]
    unsigned int env_smax = 1 + fvc + argc;
    unsigned int env_size = 1 + fvc;
    size_t clo_size = sizeofclo(env_size);
    clo_t clo = myalloc(clo_size);
    clo->env_smax = env_smax;
    clo->env_size = env_size;
    clo->fn = fn;
    clo->env[0] = (intptr_t)clo;
    *lhs = (intptr_t)clo;
}

void setclo(intptr_t box, intptr_t arg, unsigned int i) {
    // environment index starts at 1
    ((clo_t)box)->env[i] = arg;
}

void appc(intptr_t *lhs, intptr_t clo0, intptr_t arg) {
    unsigned int env_smax = ((clo_t)clo0)->env_smax;
    unsigned int env0_size = ((clo_t)clo0)->env_size;
    unsigned int env1_size = env0_size + 1;
    size_t clo0_size = sizeofclo(env0_size);
    size_t clo1_size = sizeofclo(env1_size);
    // deep copy closure
    clo_t clo1 = myalloc(clo1_size);
    memcpy(clo1, (void*)clo0, clo0_size);
    clo1->env[env0_size] = arg;
    clo1->env_size = env1_size;
    if (env1_size < env_smax) {
        *lhs = (intptr_t)clo1;
    }
    else {
        intptr_t (*fn)(intptr_t[]) = clo1->fn;
        *lhs = (*fn)(clo1->env);
        myfree(clo1);
    }
}

void ffree(intptr_t x) {
    myfree((void*)x);
}




// inductive
#define sizeofbox(argc) (sizeof(int) + argc * sizeof(intptr_t))

typedef struct {
    unsigned int ctag;
    intptr_t data[];
} box_block;

typedef box_block* box_t;

unsigned int ctagof(intptr_t box) {
    return ((box_t)box)->ctag;
}

void mkbox(intptr_t *lhs, unsigned int ctag, unsigned int argc) {
    box_t box = (box_t)myalloc(sizeofbox(argc));
    box->ctag = ctag;
    *lhs = (intptr_t)box;
}

void rebox(intptr_t *lhs, intptr_t fip, unsigned int ctag) {
    ((box_t)fip)->ctag = ctag;
    *lhs = fip;
}

void setbox(intptr_t box, intptr_t arg, unsigned int i) {
    ((box_t)box)->data[i] = arg;
}

void getbox(intptr_t *lhs, intptr_t box, unsigned int i) {
    *lhs = ((box_t)box)->data[i];
}

void failcase(void) {
    fprintf(stderr, "%s", "fail-case reached, compiler bug!\n");
    exit(1);
}

void absurd(void) {
    fprintf(stderr, "%s", "absurd case reached, compiler bug!\n");
    exit(1);
}




// lazy
#define sizeoflaz(fvc) (sizeof(intptr_t) + fvc * sizeof(intptr_t))

typedef struct {
    intptr_t (*fn)(intptr_t[]); // function
    intptr_t env[];             // layout: [fvs]
} laz_block;

typedef laz_block* laz_t;

void lazy(intptr_t *lhs, intptr_t (*fn)(intptr_t *), unsigned int fvc) {
    // layout: [fn,[fvs]]
    unsigned int laz_size = sizeoflaz(fvc);
    laz_t laz = myalloc(laz_size);
    laz->fn = fn;
    *lhs = (intptr_t)laz;
}

void setlazy(intptr_t laz, intptr_t arg, unsigned int i) {
    ((laz_t)laz)->env[i] = arg;
}

void force(intptr_t *lhs, intptr_t laz) {
    laz_t laz1 = (laz_t)laz;
    intptr_t (*fn)(intptr_t[]) = laz1->fn;
    *lhs = (*fn)(laz1->env);
}




// primitive operators
void __neg__(intptr_t *lhs, intptr_t e) { *lhs = -e; }
void __add__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 + e2; }
void __sub__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 - e2; }
void __mul__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 * e2; }
void __div__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e2 == 0 ? 0 : e1 / e2; }

void __mod__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e2 == 0) {
        *lhs = 0;
    }
    else {
        intptr_t r = e1 % e2;
        *lhs = r < 0 ? r + labs(e2) : r;
    }
}

void __lte__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 <= e2 ? __true__ : __false__; }
void __gte__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 >= e2 ? __true__ : __false__; }
void __lt__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 < e2 ? __true__ : __false__; }
void __gt__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 > e2 ? __true__ : __false__; }
void __eq__(intptr_t *lhs, intptr_t e1, intptr_t e2) { *lhs = e1 == e2 ? __true__ : __false__; }
void __chr__(intptr_t *lhs, intptr_t e) { __mod__(lhs, e, 256); }
void __ord__(intptr_t *lhs, intptr_t e) { *lhs = e; }

void __str__(intptr_t *lhs, char *buf) {
    *lhs = (intptr_t)sdsnew(buf);
}

void __push__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    char c[] = { (char)e2, '\0' };
    sds str = sdsdup((sds)e1);
    *lhs = (intptr_t)sdscat((sds)str, c);
}

void __cat__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    sds str = sdsdup((sds)e1);
    *lhs = (intptr_t)sdscatsds(str, (sds)e2);
}

void __size__(intptr_t *lhs, intptr_t e) {
    *lhs = (intptr_t)sdslen((sds)e);
}

void __indx__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    intptr_t i;
    sds str = (sds)e1;
    if (sdslen(str) == 0) {
        *lhs = 0;
    }
    else {
        __mod__(&i, e2, (intptr_t)sdslen(str));
        *lhs = str[i];
    }
}




// primitive effects
typedef struct {
    intptr_t clo; // closure
    intptr_t ch;  // channel
} farg_block;

typedef farg_block* farg_t;

void __print__(intptr_t *lhs, intptr_t e) {
    sds str = (sds)e;
    printf("%s", str);
    *lhs = __tt__;
}

void __prerr__(intptr_t *lhs, intptr_t e) {
    sds str = (sds)e;
    fprintf(stderr, "%s", str);
    *lhs = __tt__;
}

void __readln__(intptr_t *lhs, intptr_t e) {
    char* buf = NULL; size_t size; ssize_t len; sds str;
    len = getline(&buf, &size, stdin) - 1;
    buf[len] = 0;
    str = sdsnew(buf);
    free(buf);
    *lhs = (intptr_t)str;
}

void *__fork_fn__(void *args) {
    farg_t fargs = args;
    intptr_t lhs, laz;
    intptr_t clo = fargs->clo;
    intptr_t ch = fargs->ch;
    myfree(fargs);
    appc(&laz, clo, ch);
    myfree((clo_t)clo);
    force(&lhs, laz);
    return NULL;
}

void __fork__(intptr_t *lhs, intptr_t e) {
    pthread_t tr;
    chan_t* ch = chan_init(0);
    clo_t clo = (clo_t)e;
    farg_t fargs = malloc(sizeof(farg_block));
    fargs->clo = (intptr_t)clo;
    fargs->ch = (intptr_t)ch;
    pthread_create(&tr, &attr, (void *(*)(void *))__fork_fn__, fargs);
    *lhs = (intptr_t)ch;
}

void __send__(intptr_t *lhs, intptr_t c, intptr_t e) {
    chan_send((chan_t*)c, (void*)e);
    *lhs = c;
}

void __recv0__(intptr_t *lhs, intptr_t c) {
    intptr_t msg;
    intptr_t box;
    chan_recv((chan_t*)c, (void*)&msg);
    mkbox(&box, __exU__, 2);
    setbox(box, msg, 0);
    setbox(box, c, 1);
    *lhs = box;
}

void __recv1__(intptr_t *lhs, intptr_t c) {
    intptr_t msg;
    intptr_t box;
    chan_recv((chan_t*)c, (void*)&msg);
    mkbox(&box, __exL__, 2);
    setbox(box, msg, 0);
    setbox(box, c, 1);
    *lhs = box;
}

void __close0__(intptr_t *lhs, intptr_t c) {
    chan_dispose((chan_t*)c);
    *lhs = __tt__;
}

void __close1__(intptr_t *lhs, intptr_t c) {
    *lhs = __tt__;
}




// magic
void magic(void) {
    fprintf(stderr, "%s", "magic reached, nothing to do\n");
    exit(1);
}
