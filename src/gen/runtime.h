#ifndef RUNTIME_H
#define RUNTIME_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define nothing 0

// initialize
void begin_run(void);
void end_run(void);

// core
void mkclo(intptr_t *lhs, intptr_t (*fn)(intptr_t[]), unsigned int fvc, unsigned int argc);
void setclo(intptr_t clo, intptr_t arg, unsigned int i);
void appc(intptr_t *lhs, intptr_t clo, intptr_t arg);
void ffree(intptr_t x);

// inductive
unsigned int ctagof(intptr_t box);
void mkbox(intptr_t *lhs, unsigned int ctag, unsigned int argc);
void rebox(intptr_t *lhs, intptr_t fip, unsigned int ctag);
void setbox(intptr_t box, intptr_t arg, unsigned int i);
void getbox(intptr_t *lhs, intptr_t box, unsigned int i);
void absurd();

// lazy
void lazy(intptr_t *lhs, intptr_t (*fn)(intptr_t[]), unsigned int fvc);
void setlazy(intptr_t laz, intptr_t arg, unsigned int i);
void force(intptr_t *lhs, intptr_t laz);

// primitive operators
void __neg__(intptr_t *lhs, intptr_t e);
void __add__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __sub__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __mul__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __div__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __mod__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __lte__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __gte__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __lt__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __gt__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __eq__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __chr__(intptr_t *lhs, intptr_t e);
void __ord__(intptr_t *lhs, intptr_t e);
void __str__(intptr_t *lhs, char* buf);
void __push__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __cat__(intptr_t *lhs, intptr_t e1, intptr_t e2);
void __size__(intptr_t *lhs, intptr_t e);
void __indx__(intptr_t *lhs, intptr_t e1, intptr_t e2);

// primitive effects
void __print__(intptr_t *lhs, intptr_t e);
void __prerr__(intptr_t *lhs, intptr_t e);
void __readln__(intptr_t *lhs, intptr_t e);


// magic
void magic();



#endif // RUNTIME_H
