#ifndef RUNTIME_H
#define RUNTIME_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/_types/_intptr_t.h>

#define nothing 0

// initialize
void begin_run(void);
void end_run(void);

// core
intptr_t mkclo(intptr_t (*fn)(intptr_t[]), unsigned int fvc, unsigned int argc);
void setclo(intptr_t clo, intptr_t arg, unsigned int i);
intptr_t appc(intptr_t clo, intptr_t arg);
void ffree(intptr_t x);

// inductive
unsigned int ctagof(intptr_t box);
intptr_t mkbox(unsigned int ctag, unsigned int argc);
intptr_t rebox(intptr_t fip, unsigned int ctag);
void setbox(intptr_t box, intptr_t arg, unsigned int i);
intptr_t getbox(intptr_t box, unsigned int i);
void failcase(void);
void absurd(void);

// lazy
intptr_t lazy(intptr_t (*fn)(intptr_t[]), unsigned int fvc);
void setlazy(intptr_t laz, intptr_t arg, unsigned int i);
intptr_t force(intptr_t laz);

// primitive operators
intptr_t __neg__(intptr_t e);
intptr_t __add__(intptr_t e1, intptr_t e2);
intptr_t __sub__(intptr_t e1, intptr_t e2);
intptr_t __mul__(intptr_t e1, intptr_t e2);
intptr_t __div__(intptr_t e1, intptr_t e2);
intptr_t __mod__(intptr_t e1, intptr_t e2);
intptr_t __lte__(intptr_t e1, intptr_t e2);
intptr_t __gte__(intptr_t e1, intptr_t e2);
intptr_t __lt__(intptr_t e1, intptr_t e2);
intptr_t __gt__(intptr_t e1, intptr_t e2);
intptr_t __eq__(intptr_t e1, intptr_t e2);
intptr_t __chr__(intptr_t e);
intptr_t __ord__(intptr_t e);
intptr_t __str__(char* buf);
intptr_t __push__(intptr_t e1, intptr_t e2);
intptr_t __cat__(intptr_t e1, intptr_t e2);
intptr_t __size__(intptr_t e);
intptr_t __indx__(intptr_t e1, intptr_t e2);

// primitive effects
intptr_t __print__(intptr_t e);
intptr_t __prerr__(intptr_t e);
intptr_t __readln__(intptr_t e);
intptr_t __fork__(intptr_t e);
intptr_t __send__(intptr_t c, intptr_t e);
intptr_t __recv0__(intptr_t c);
intptr_t __recv1__(intptr_t c);
intptr_t __close0__(intptr_t c);
intptr_t __close1__(intptr_t c);

// magic
void magic(void);



#endif // RUNTIME_H
