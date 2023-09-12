#ifndef RUNTIME_H
#define RUNTIME_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define nothing 0


// core
void mkclo(intptr_t *lhs, intptr_t (*fn)(intptr_t[]), int fvc, int argc);
void setclo(intptr_t lhs, intptr_t arg, unsigned int i);
void appc(intptr_t *lhs, intptr_t clo, intptr_t arg);
void ffree(intptr_t x);

// inductive
void mkbox(intptr_t *lhs, unsigned int ctag, int argc);
void rebox(intptr_t *lhs, intptr_t fip, unsigned int ctag);
void setbox(intptr_t box, intptr_t arg, int i);


void absurd();
void magic();



#endif // RUNTIME_H
