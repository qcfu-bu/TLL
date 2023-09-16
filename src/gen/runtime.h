#ifndef RUNTIME_H
#define RUNTIME_H


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


#define myalloc malloc
#define myfree free
#define nothing 0


// initialize
static pthread_attr_t attr;

static inline void begin_run(void) {
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

static inline void end_run(void) {
  pthread_exit(NULL);
}


static inline void ffree(intptr_t x) {
    myfree((void*)x);
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

static inline intptr_t mkclo(intptr_t (*fn)(intptr_t[]), unsigned int fvc, unsigned int argc) {
    // layout: [env_max,env_size,fn,[self,fvs,_]]
    unsigned int env_smax = 1 + fvc + argc;
    unsigned int env_size = 1 + fvc;
    size_t clo_size = sizeofclo(env_size);
    clo_t clo = (clo_t)myalloc(clo_size);
    clo->env_smax = env_smax;
    clo->env_size = env_size;
    clo->fn = fn;
    clo->env[0] = (intptr_t)clo;
    return (intptr_t)clo;
}

static inline void setclo(intptr_t box, intptr_t arg, unsigned int i) {
    // environment index starts at 1
    ((clo_t)box)->env[i] = arg;
}

static inline intptr_t appc(intptr_t clo0, intptr_t arg) {
    unsigned int env_smax = ((clo_t)clo0)->env_smax;
    unsigned int env0_size = ((clo_t)clo0)->env_size;
    unsigned int env1_size = env0_size + 1;
    size_t clo0_size = sizeofclo(env0_size);
    size_t clo1_size = sizeofclo(env1_size);
    // deep copy closure
    clo_t clo1 = (clo_t)myalloc(clo1_size);
    memcpy(clo1, (void*)clo0, clo0_size);
    clo1->env[env0_size] = arg;
    clo1->env_size = env1_size;
    if (env1_size < env_smax) {
        return (intptr_t)clo1;
    }
    else {
        intptr_t (*fn)(intptr_t[]) = clo1->fn;
        intptr_t result = (*fn)(clo1->env);
        myfree(clo1);
        return result;
    }
}


// inductive
#define sizeofbox(argc) (sizeof(int) + argc * sizeof(intptr_t))

typedef struct {
    unsigned int ctag;
    intptr_t data[];
} box_block;

typedef box_block* box_t;

static inline unsigned int ctagof(intptr_t box) {
    return ((box_t)box)->ctag;
}

static inline intptr_t mkbox(unsigned int ctag, unsigned int argc) {
    box_t box = (box_t)myalloc(sizeofbox(argc));
    box->ctag = ctag;
    return (intptr_t)box;
}

static inline intptr_t rebox(intptr_t fip, unsigned int ctag) {
    ((box_t)fip)->ctag = ctag;
    return fip;
}

static inline void setbox(intptr_t box, intptr_t arg, unsigned int i) {
    ((box_t)box)->data[i] = arg;
}

static inline intptr_t getbox(intptr_t box, unsigned int i) {
    return ((box_t)box)->data[i];
}

static inline void failcase(void) {
    fprintf(stderr, "%s", "fail-case reached, compiler bug!\n");
    exit(1);
}

static inline void absurd(void) {
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

static inline intptr_t lazy(intptr_t (*fn)(intptr_t *), unsigned int fvc) {
    // layout: [fn,[fvs]]
    unsigned int laz_size = sizeoflaz(fvc);
    laz_t laz = (laz_t)myalloc(laz_size);
    laz->fn = fn;
    return (intptr_t)laz;
}

static inline void setlazy(intptr_t laz, intptr_t arg, unsigned int i) {
    ((laz_t)laz)->env[i] = arg;
}

static inline intptr_t force(intptr_t laz) {
    laz_t laz1 = (laz_t)laz;
    intptr_t (*fn)(intptr_t[]) = laz1->fn;
    return (*fn)(laz1->env);
}


// primitive operators
static inline intptr_t __neg__(intptr_t e) { return -e; }
static inline intptr_t __add__(intptr_t e1, intptr_t e2) { return e1 + e2; }
static inline intptr_t __sub__(intptr_t e1, intptr_t e2) { return e1 - e2; }
static inline intptr_t __mul__(intptr_t e1, intptr_t e2) { return e1 * e2; }
static inline intptr_t __div__(intptr_t e1, intptr_t e2) { return e2 == 0 ? 0 : e1 / e2; }

static inline intptr_t __mod__(intptr_t e1, intptr_t e2) {
    if (e2 == 0) {
        return 0;
    }
    else {
        intptr_t r = e1 % e2;
        return r < 0 ? r + labs(e2) : r;
    }
}

static inline intptr_t __lte__(intptr_t e1, intptr_t e2) { return e1 <= e2 ? __true__ : __false__; }
static inline intptr_t __gte__(intptr_t e1, intptr_t e2) { return e1 >= e2 ? __true__ : __false__; }
static inline intptr_t __lt__(intptr_t e1, intptr_t e2) { return e1 < e2 ? __true__ : __false__; }
static inline intptr_t __gt__(intptr_t e1, intptr_t e2) { return e1 > e2 ? __true__ : __false__; }
static inline intptr_t __eq__(intptr_t e1, intptr_t e2) { return e1 == e2 ? __true__ : __false__; }
static inline intptr_t __chr__(intptr_t e) { return __mod__(e, 256); }
static inline intptr_t __ord__(intptr_t e) { return e; }

static inline intptr_t __str__(char *buf) {
    return (intptr_t)sdsnew(buf);
}

static inline intptr_t __push__(intptr_t e1, intptr_t e2) {
    char c[] = { (char)e2, '\0' };
    sds str = sdsdup((sds)e1);
    return (intptr_t)sdscat((sds)str, c);
}

static inline intptr_t __cat__(intptr_t e1, intptr_t e2) {
    sds str = sdsdup((sds)e1);
    return (intptr_t)sdscatsds(str, (sds)e2);
}

static inline intptr_t __size__(intptr_t e) {
    return (intptr_t)sdslen((sds)e);
}

static inline intptr_t __indx__(intptr_t e1, intptr_t e2) {
    intptr_t i;
    sds str = (sds)e1;
    if (sdslen(str) == 0) {
        return 0;
    }
    else {
        i = __mod__(e2, (intptr_t)sdslen(str));
        return str[i];
    }
}


// primitive effects
typedef struct {
    intptr_t clo; // closure
    intptr_t ch;  // channel
} farg_block;

typedef farg_block* farg_t;

static inline intptr_t __print__(intptr_t e) {
    sds str = (sds)e;
    printf("%s", str);
    return __tt__;
}

static inline intptr_t __prerr__(intptr_t e) {
    sds str = (sds)e;
    fprintf(stderr, "%s", str);
    return __tt__;
}

static inline intptr_t __readln__(intptr_t e) {
    char* buf = NULL; size_t size; ssize_t len; sds str;
    len = getline(&buf, &size, stdin) - 1;
    buf[len] = 0;
    str = sdsnew(buf);
    free(buf);
    return (intptr_t)str;
}

static inline void *__fork_fn__(void *args) {
    farg_t fargs = (farg_t)args;
    intptr_t lhs, laz;
    intptr_t clo = fargs->clo;
    intptr_t ch = fargs->ch;
    myfree(fargs);
    laz = appc(clo, ch);
    myfree((clo_t)clo);
    lhs = force(laz);
    return NULL;
}

static inline intptr_t __fork__(intptr_t e) {
    pthread_t tr;
    chan_t* ch = chan_init(0);
    clo_t clo = (clo_t)e;
    farg_t fargs = (farg_t)myalloc(sizeof(farg_block));
    fargs->clo = (intptr_t)clo;
    fargs->ch = (intptr_t)ch;
    pthread_create(&tr, &attr, (void *(*)(void *))__fork_fn__, fargs);
    return (intptr_t)ch;
}

static inline intptr_t __send__(intptr_t c, intptr_t e) {
    chan_send((chan_t*)c, (void*)e);
    return c;
}

static inline intptr_t __recv0__(intptr_t c) {
    intptr_t msg;
    intptr_t box;
    chan_recv((chan_t*)c, (void**)&msg);
    box = mkbox(__exU__, 2);
    setbox(box, msg, 0);
    setbox(box, c, 1);
    return box;
}

static inline intptr_t __recv1__(intptr_t c) {
    intptr_t msg;
    intptr_t box;
    chan_recv((chan_t*)c, (void**)&msg);
    box = mkbox(__exL__, 2);
    setbox(box, msg, 0);
    setbox(box, c, 1);
    return box;
}

static inline intptr_t __close0__(intptr_t c) {
    chan_dispose((chan_t*)c);
    return __tt__;
}

static inline intptr_t __close1__(intptr_t c) {
    return __tt__;
}

// magic
static inline void magic(void) {
    fprintf(stderr, "%s", "magic reached, nothing to do\n");
    exit(1);
}


#endif // RUNTIME_H
