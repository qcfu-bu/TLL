#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include "gc.h"
#include "chan.h"

#include "prelude.h"
#include "runtime.h"

void instr_init()
{
  GC_INIT();
}

void instr_mov(tll_ptr *x, tll_ptr v)
{
  *x = v;
}

void instr_clo(
    tll_ptr *x,
    tll_ptr (*f)(tll_ptr, tll_env),
    int size, tll_env env,
    int narg, ...)
{
  va_list ap;
  tll_clo tmp = (tll_clo)GC_malloc(tll_clo_size);
  tmp->f = f;
  tmp->env = (tll_env)GC_malloc(tll_ptr_size * (size + narg + 1));

  tmp->env[0] = 0;
  memcpy(tmp->env + narg + 1, env, size * tll_ptr_size);
  va_start(ap, narg);
  for (int i = 0; i < narg; i++)
  {
    tmp->env[i + 1] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

void instr_call(tll_ptr *x, tll_ptr clo, tll_ptr v)
{
  tll_ptr (*f)(tll_ptr, tll_env) = ((tll_clo)clo)->f;
  tll_env env = ((tll_clo)clo)->env;
  env[0] = clo;
  *x = (*f)(v, env);
}

void instr_struct(tll_ptr *x, int tag, int size, ...)
{
  va_list ap;
  tll_node tmp = (tll_node)GC_malloc(tll_node_size);
  tmp->tag = tag;
  tmp->data = (tll_ptr *)GC_malloc(tll_ptr_size * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->data[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
}

void instr_open(
    tll_ptr *x,
    tll_ptr (*f)(tll_env), tll_ptr m,
    int size, tll_env env,
    int narg, ...)
{
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  tll_env local = (tll_env)GC_malloc(tll_ptr_size * (size + narg + 1));

  local[0] = ch;
  memcpy(local + narg + 1, env, size * tll_ptr_size);
  va_start(ap, narg);
  for (int i = 0; i < narg; i++)
  {
    local[i + 1] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  pthread_create(&th, m, (void *)f, local);
  instr_struct(x, 0, 2, ch, m);
}

tll_ptr proc_sender(tll_ptr x, tll_env env)
{
  int res = chan_send((chan_t *)env[1], x);
  return env[1];
}

void instr_send(tll_ptr *x, tll_ptr ch, int mode)
{
  instr_clo(x, &proc_sender, 0, 0, 1, ch);
}

void instr_recv(tll_ptr *x, tll_ptr ch, int tag)
{
  tll_ptr msg;
  int res = chan_recv((chan_t *)ch, &msg);
  instr_struct(x, tag, 2, msg, ch);
}

void instr_close(tll_ptr *x, tll_ptr ch, int mode)
{
  chan_dispose((chan_t *)ch);
  instr_struct(x, tt_c, 0);
}

tll_ptr instr_to_bit(int i)
{
  tll_node x = (tll_node)GC_malloc(tll_node_size);
  if (i)
  {
    x->tag = true_c;
  }
  else
  {
    x->tag = false_c;
  }
  return x;
}

tll_ptr instr_to_ascii(char c)
{
  tll_node x = (tll_node)GC_malloc(tll_node_size);
  x->tag = Ascii_c;
  x->data = (tll_ptr *)GC_malloc(tll_ptr_size * 8);
  int bit;
  for (int i = 0; i < 8; i++)
  {
    bit = (c & (1 << i)) >> i;
    x->data[7 - i] = instr_to_bit(bit);
  }
  return (tll_ptr)x;
}

tll_ptr instr_to_string(char *s)
{
  tll_node tmp;
  tll_node x = (tll_node)GC_malloc(tll_node_size);
  x->tag = EmptyString_c;
  int len = strlen(s);
  for (int i = 1; i <= len; i++)
  {
    tmp = (tll_node)GC_malloc(tll_node_size);
    tmp->tag = String_c;
    tmp->data = (tll_ptr *)GC_malloc(tll_ptr_size * 2);
    tmp->data[0] = instr_to_ascii(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (tll_ptr)x;
}

char instr_from_ascii(tll_ptr x)
{
  char c;
  tll_ptr b;
  for (int i = 0; i < 8; i++)
  {
    b = ((tll_node)x)->data[7 - i];
    switch (((tll_node)b)->tag)
    {
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

char *instr_from_string(tll_ptr x)
{
  char *str;
  int len = 0;
  tll_node tmp = (tll_node)x;
  while (tmp->tag != EmptyString_c)
  {
    tmp = (tll_node)(tmp->data[1]);
    len++;
  }
  str = (char *)GC_malloc(len + 1);
  tmp = (tll_node)x;
  for (int i = 0; i < len; i++)
  {
    str[i] = instr_from_ascii(tmp->data[0]);
    tmp = (tll_node)(tmp->data[1]);
  }
  return str;
}

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
      str = instr_from_string(msg);
      fputs(str, stdout);
      GC_free(str);
      b = !b;
    }
    else
    {
      switch (((tll_node)msg)->tag)
      {
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
      msg = instr_to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    }
    else
    {
      chan_recv((chan_t *)ch, &msg);
      switch (((tll_node)msg)->tag)
      {
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
      str = instr_from_string(msg);
      fputs(str, stderr);
      GC_free(str);
      b = !b;
    }
    else
    {
      switch (((tll_node)msg)->tag)
      {
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

void instr_prim(tll_ptr *x, tll_ptr (*f)(tll_ptr))
{
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}

void instr_free_clo(tll_ptr *x)
{
  GC_free(((tll_clo)x)->env);
  GC_free(x);
}

void instr_free_struct(tll_ptr *x)
{
  GC_free(((tll_node)x)->data);
  GC_free(x);
}

void instr_free_thread(tll_env env)
{
  GC_free(env);
}
