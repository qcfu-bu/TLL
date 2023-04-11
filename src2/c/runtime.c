#define GC_THREADS

#include "chan.h"
#include "gc.h"
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "prelude.h"
#include "runtime.h"

#define INIT() GC_INIT()
#define MALLOC GC_malloc
#define FREE GC_free

/*-------------------------------------------------------*/

tll_ptr to_bit(int i) {
  tll_node x = (tll_node)MALLOC(tll_node_size);
  if (i) {
    x->tag = true_c;
  } else {
    x->tag = false_c;
  }
  return x;
}

tll_ptr to_ascii(char c) {
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = Ascii_c;
  x->data = (tll_ptr *)MALLOC(tll_ptr_size * 8);
  int bit;
  for (int i = 0; i < 8; i++) {
    bit = (c & (1 << i)) >> i;
    x->data[7 - i] = to_bit(bit);
  }
  return (tll_ptr)x;
}

tll_ptr to_string(char *s) {
  tll_node tmp;
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = EmptyString_c;
  int len = strlen(s);
  for (int i = 2; i <= len; i++) {
    tmp = (tll_node)MALLOC(tll_node_size);
    tmp->tag = String_c;
    tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * 2);
    tmp->data[0] = to_ascii(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (tll_ptr)x;
}

char from_ascii(tll_ptr x) {
  char c;
  tll_ptr b;
  for (int i = 0; i < 8; i++) {
    b = ((tll_node)x)->data[7 - i];
    switch (((tll_node)b)->tag) {
    case true_c:
      c |= 1 << i;
      break;
    case false_c:
      c &= ~(1 << i);
      break;
    }
  }
  return c;
}

char *from_string(tll_ptr x) {
  char *str;
  int len = 0;
  tll_node tmp = (tll_node)x;
  while (tmp->tag != EmptyString_c) {
    tmp = (tll_node)(tmp->data[1]);
    len++;
  }
  str = (char *)MALLOC(len + 1);
  tmp = (tll_node)x;
  for (int i = 0; i < len; i++) {
    str[i] = from_ascii(tmp->data[0]);
    tmp = (tll_node)(tmp->data[1]);
  }
  return str;
}

/*-------------------------------------------------------*/

tll_ptr proc_stdout(tll_ptr ch) {
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep) {
    chan_recv((chan_t *)ch, &msg);
    if (b) {
      str = from_string(msg);
      fputs(str, stdout);
      FREE(str);
      b = !b;
    } else {
      switch (((tll_node)msg)->tag) {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stdin(tll_ptr ch) {
  int b = 0, rep = 1;
  char *buffer;
  size_t len;
  tll_ptr msg;
  while (rep) {
    if (b) {
      getline(&buffer, &len, stdin);
      msg = to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    } else {
      chan_recv((chan_t *)ch, &msg);
      switch (((tll_node)msg)->tag) {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stderr(tll_ptr ch) {
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep) {
    chan_recv((chan_t *)ch, &msg);
    if (b) {
      str = from_string(msg);
      fputs(str, stderr);
      FREE(str);
      b = !b;
    } else {
      switch (((tll_node)msg)->tag) {
      case true_c:
        b = !b;
        break;
      case false_c:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

/*-------------------------------------------------------*/

void instr_init() { INIT() }

/*-------------------------------------------------------*/

void instr_clo(tll_ptr *x, tll_ptr (*f)(tll_ptr, tll_env), int size, ...) {
  va_list ap;
  tll_clo tmp = (tll_clo)MALLOC(tll_clo_size);
  tmp->f = f;
  tmp->env = (tll_env)MALLOC(tll_ptr_size * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    tmp->env[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

/*-------------------------------------------------------*/

void instr_app(tll_ptr *x, tll_ptr clo, tll_ptr v) {
  tll_ptr (*f)(tll_ptr, tll_env) = ((tll_clo)clo)->f;
  tll_env env = ((tll_clo)clo)->env;
  *x = (*f)(v, env);
}

/*-------------------------------------------------------*/

void instr_struct(tll_ptr *x, int tag, int size, ...) {
  va_list ap;
  tll_node tmp = (tll_node)MALLOC(tll_node_size);
  tmp->tag = tag;
  tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    tmp->data[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

/*-------------------------------------------------------*/

void instr_open(tll_ptr *x, tll_ptr (*f)(tll_ptr)) {
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_fork(tll_ptr *x, tll_ptr (*f)(tll_env), int size, ...) {
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  tll_env local = (tll_env)MALLOC(tll_ptr_size * (size + 1));

  local[0] = ch;
  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    local[i + 1] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  pthread_create(&th, 0, (void *)f, local);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_send(tll_ptr *x, tll_ptr ch, tll_ptr msg) {
  chan_send((chan_t *)ch, msg);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_recv(tll_ptr *x, tll_ptr ch) {
  tll_ptr msg;
  chan_recv((chan_t *)ch, &msg);
  instr_struct(x, 0, 2, msg, ch);
}

/*-------------------------------------------------------*/

void instr_close(tll_ptr *x, tll_ptr ch) {
  chan_dispose((chan_t *)ch);
  instr_struct(x, tt_c, 0);
}

/*-------------------------------------------------------*/

void instr_free_clo(tll_ptr *x) {
  FREE(((tll_clo)x)->env);
  FREE(x);
}

/*-------------------------------------------------------*/

void instr_free_struct(tll_ptr *x) {
  FREE(((tll_node)x)->data);
  FREE(x);
}

/*-------------------------------------------------------*/

void instr_free_thread(tll_env env) { FREE(env); }
