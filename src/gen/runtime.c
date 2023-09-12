#include "chan.h"
#include <pthread.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

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

void setclo(intptr_t lhs, intptr_t arg, unsigned int i) {
    // environment index starts at 1
    ((clo_t)lhs)->env[i] = arg;
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





void absurd() {
    fprintf(stderr, "%s", "absurd case reached, please report bug\n");
    exit(1);
}


// magic
void magic() {
    fprintf(stderr, "%s", "magic reached, nothing to do\n");
    exit(1);
}
