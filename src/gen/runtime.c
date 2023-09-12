#include "chan.h"
#include <pthread.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

#include "prelude.h"
#include "runtime.h"

#define myalloc malloc
#define myfree free




// core
#define sizeofclo(env_size) (2 * sizeof(int) + sizeof(intptr_t) + env_size * sizeof(intptr_t))

typedef struct {
    unsigned int env_smax;      // maximum size
    unsigned int env_size;      // current size
    intptr_t (*fn)(intptr_t[]); // function
    intptr_t env[];             // layout: [self,fvs,args]
} clo_block;

typedef clo_block* clo_t;

void mkclo(intptr_t *lhs, intptr_t (*fn)(intptr_t[]), int fvc, int argc) {
    // layout: [env_max,env_size,fn,[self,fvs,_]]
    unsigned int env_smax = 1 + fvc + argc;
    unsigned int env_size = 1 + fvc;
    unsigned int clo_size = sizeofclo(env_size);
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
    unsigned int env_size = ((clo_t)clo0)->env_size;
    unsigned int clo1_size = sizeofclo(env_size + 1);
    // deep copy closure
    clo_t clo1 = myalloc(clo1_size);
    memcpy(clo1, (clo_t)clo0, clo1_size);
    clo1->env[env_size] = arg;
    clo1->env_size = env_size + 1;
    if (env_size + 1 < env_smax) {
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
    intptr_t data[10];
} box_block;

typedef box_block* box_t;

unsigned int ctagof(intptr_t box) {
    return ((box_t)box)->ctag;
}

void mkbox(intptr_t *lhs, unsigned int ctag, int argc) {
    box_t box = (box_t)myalloc(sizeofbox(argc));
    box->ctag = ctag;
}

void rebox(intptr_t *lhs, intptr_t fip, unsigned int ctag) {
    ((box_t)fip)->ctag = ctag;
    *lhs = fip;
}

void setbox(intptr_t box, intptr_t arg, int i) {
    ((box_t)box)->data[i] = arg;
}

void getbox(intptr_t *lhs, intptr_t box, int i) {
    *lhs = ((box_t)box)->data[i];
}

void absurd() {
    fprintf(stderr, "%s", "absurd case reached, please report bug\n");
    exit(1);
}




// lazy
#define sizeoflaz(fvc) (sizeof(intptr_t) + fvc * sizeof(intptr_t))

typedef struct {
    intptr_t (*fn)(intptr_t[]); // function
    intptr_t env[];             // layout: [fvs]
} laz_block;

typedef laz_block* laz_t;

void lazy(intptr_t *lhs, intptr_t (*fn)(intptr_t *), int fvc) {
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
    myfree(laz1);
}




// primitive operators
typedef struct {
    
} str_block;

void __neg__(intptr_t *lhs, intptr_t e) {
    *lhs = -e;
}

void __add__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    *lhs = e1 + e2;
}

void __sub__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    *lhs = e1 - e2;
}

void __mul__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    *lhs = e1 * e2;
}

void __div__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e2 == 0) {
        *lhs = 0;
    }
    else {
        *lhs = e1 / e2;
    }
}

void __mod__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e2 == 0) {
        *lhs = 0;
    }
    else {
        intptr_t r = e1 % e2;
        *lhs = r < 0 ? r + labs(e2) : r;
    }
}

void __lte__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e1 <= e2) {
        *lhs = __true__;
    }
    else {
        *lhs = __false__;
    }
}

void __gte__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e1 >= e2) {
        *lhs = __true__;
    }
    else {
        *lhs = __false__;
    }
}

void __lt__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e1 < e2) {
        *lhs = __true__;
    }
    else {
        *lhs = __false__;
    }
}

void __gt__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e1 > e2) {
        *lhs = __true__;
    }
    else {
        *lhs = __false__;
    }
}

void __eq__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    if (e1 == e2) {
        *lhs = __true__;
    }
    else {
        *lhs = __false__;
    }
}

void __chr__(intptr_t *lhs, intptr_t e) {
    __mod__(lhs, e, 256);
}

void __ord__(intptr_t *lhs, intptr_t e) {
    *lhs = e;
}

void __push__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    unsigned int len = strlen((str_t)e1);
    str_t str = myalloc((len + 2) * sizeof(char));
    strcpy(str, (str_t)e1);
    str[len] = (char)e2;
    str[len + 1] = 0;
    *lhs = (intptr_t)str;
}

void __cat__(intptr_t *lhs, intptr_t e1, intptr_t e2) {
    unsigned int len1 = strlen((str_t)e1);
    unsigned int len2 = strlen((str_t)e2);
    str_t str = myalloc((len1 + len2 + 1) * sizeof(char));
    strcpy(str, (str_t)e1);
    strcpy(str + len1, (str_t)e1);
    str[len1 + len2] = 0;
    *lhs = (intptr_t)str;
}

void __size__(intptr_t *lhs, intptr_t e) {
    *lhs = strlen((str_t)e);
}





// magic
void magic() {
    fprintf(stderr, "%s", "magic reached, nothing to do\n");
    exit(1);
}
