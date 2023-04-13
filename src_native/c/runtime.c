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

void *tll_malloc(size_t size)
{
  void *x = malloc(size);
  if (x == NULL)
  {
    printf("cannot allocate");
    abort();
  }
  return x;
}

#define INIT()
#define MALLOC tll_malloc
#define FREE free

/*-------------------------------------------------------*/

tll_ptr to_char(unsigned long c)
{
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = Char_c;
  x->data = (tll_ptr *)MALLOC(tll_ptr_size);
  x->data[0] = (tll_ptr)c;
  return (tll_ptr)x;
}

tll_ptr to_string(char *s)
{
  tll_node tmp;
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = EmptyString_c;
  int len = strlen(s);
  for (int i = 2; i <= len; i++)
  {
    tmp = (tll_node)MALLOC(tll_node_size);
    tmp->tag = String_c;
    tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * 2);
    tmp->data[0] = to_char(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (tll_ptr)x;
}

unsigned long from_ascii(tll_ptr x)
{
  unsigned long c = (unsigned long)((tll_node)x)->data[0];
  return (c % 256);
}

char *from_string(tll_ptr x)
{
  char *str;
  int len = 0;
  tll_node tmp = (tll_node)x;
  while (tmp->tag != EmptyString_c)
  {
    tmp = (tll_node)(tmp->data[1]);
    len++;
  }
  str = (char *)MALLOC(len + 1);
  tmp = (tll_node)x;
  for (int i = 0; i < len; i++)
  {
    str[i] = from_ascii(tmp->data[0]);
    tmp = (tll_node)(tmp->data[1]);
  }
  return str;
}

/*-------------------------------------------------------*/

tll_ptr proc_stdout(tll_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = from_string(msg);
      fputs(str, stdout);
      FREE(str);
      b = !b;
    }
    else
    {
      if (msg)
      {
        b = !b;
      }
      else
      {
        rep = !rep;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stdin(tll_ptr ch)
{
  int b = 0, rep = 1;
  char *buffer;
  size_t len;
  tll_ptr msg;
  while (rep)
  {
    if (b)
    {
      getline(&buffer, &len, stdin);
      msg = to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    }
    else
    {
      chan_recv((chan_t *)ch, &msg);
      if (msg)
      {
        b = !b;
      }
      else
      {
        rep = !rep;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stderr(tll_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = from_string(msg);
      fputs(str, stderr);
      FREE(str);
      b = !b;
    }
    else
    {
      if (msg)
      {
        b = !b;
      }
      else
      {
        rep = !rep;
      }
    }
  }
  return NULL;
}

/*-------------------------------------------------------*/

void instr_init() { INIT() }

/*-------------------------------------------------------*/

void instr_clo(tll_ptr *x, tll_ptr (*f)(tll_ptr, tll_env), int size, ...)
{
  va_list ap;
  tll_clo tmp = (tll_clo)MALLOC(tll_clo_size);
  tmp->f = f;
  tmp->env = (tll_env)MALLOC(tll_ptr_size * (size + 1));

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->env[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

/*-------------------------------------------------------*/

void instr_app(tll_ptr *x, tll_ptr clo, tll_ptr v)
{
  tll_ptr (*f)(tll_ptr, tll_env) = ((tll_clo)clo)->f;
  tll_env env = ((tll_clo)clo)->env;
  *x = (*f)(v, env);
}

/*-------------------------------------------------------*/

void instr_struct(tll_ptr *x, int tag, int size, ...)
{
  va_list ap;
  tll_node tmp = (tll_node)MALLOC(tll_node_size);
  tmp->tag = tag;
  tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * (size + 1));

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->data[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

/*-------------------------------------------------------*/

void instr_open(tll_ptr *x, tll_ptr (*f)(tll_ptr))
{
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_fork(tll_ptr *x, tll_ptr (*f)(tll_env), int size, ...)
{
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  tll_env local = (tll_env)MALLOC(tll_ptr_size * (size + 2));

  local[0] = ch;
  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    local[i + 1] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  pthread_create(&th, 0, (void *)f, local);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_send(tll_ptr *x, tll_ptr ch, tll_ptr msg)
{
  chan_send((chan_t *)ch, msg);
  *x = ch;
}

/*-------------------------------------------------------*/

void instr_recv(tll_ptr *x, tll_ptr ch)
{
  tll_ptr msg;
  chan_recv((chan_t *)ch, &msg);
  instr_struct(x, 0, 2, msg, ch);
}

/*-------------------------------------------------------*/

void instr_close(tll_ptr *x, tll_ptr ch)
{
  /* chan_dispose((chan_t *)ch); */
  *x = 0;
}

/*-------------------------------------------------------*/

void instr_free_clo(tll_ptr *x)
{
  /* FREE(((tll_clo)x)->env); */
  /* FREE(x); */
}

/*-------------------------------------------------------*/

void instr_free_struct(tll_ptr *x)
{
  /* FREE(((tll_node)x)->data); */
  /* FREE(x); */
}

/*-------------------------------------------------------*/

void instr_free_thread(tll_env env)
{ /* FREE(env); */
}
