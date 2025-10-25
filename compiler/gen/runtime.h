#ifndef RUNTIME_H
#define RUNTIME_H
#define GC_THREADS

#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

// #include "gc.h"
#include "prelude.h"

#define tll_alloc(n) malloc(n)
#define tll_free(n) free(n)

/* Object Kinds */
enum {
  TLL_CLOSURE_KIND,
  TLL_CTOR_KIND,
  TLL_THUNK_KIND,
  TLL_STRING_KIND,
  TLL_CHANNEL_KIND,
};

/* Base Objects */
typedef struct {
  size_t m_kind;
} tll_object;

/* Closures */
typedef struct {
  tll_object m_header;
  unsigned int m_size;  // number of argument that have been fixed
  unsigned int m_arity; // number of arguments expected by m_fun
  tll_object *(*m_fun)(tll_object *[]);
  tll_object *m_objs[]; // [self, fvs, args]
} tll_closure_object;

#define SIZE_OF_CLOSURE(n)                                                     \
  (offsetof(tll_closure_object, m_objs) + (n) * sizeof(tll_object *))

/* Ctors */
typedef struct {
  tll_object m_header;
  unsigned int m_size;
  unsigned int m_tag;
  tll_object *m_objs[];
} tll_ctor_object;

#define SIZE_OF_CTOR(n)                                                        \
  (offsetof(tll_ctor_object, m_objs) + (n) * sizeof(tll_object *))

/* Thunks */
typedef struct {
  tll_object m_header;
  unsigned int m_size;
  tll_object *(*m_fun)(tll_object *[]);
  tll_object *m_objs[];
} tll_thunk_object;

#define SIZE_OF_THUNK(n)                                                       \
  (offsetof(tll_thunk_object, m_objs) + (n) * sizeof(tll_object *))

/* Strings */
typedef struct {
  tll_object m_header;
  unsigned int m_size; // byte length including '\0' terminator
  char m_data[];
} tll_string_object;

#define sizeof_string(n)                                                       \
  (offsetof(tll_string_object, m_data) + (n) * sizeof(char))

/* Channels */
typedef struct {
  tll_object m_header;

  // Unbuffered channel properties
  pthread_mutex_t r_mu;
  pthread_mutex_t w_mu;
  tll_object *m_data;

  // Shared properties
  pthread_mutex_t m_mu;
  pthread_cond_t r_cond;
  pthread_cond_t w_cond;
  int r_waiting;
  int w_waiting;
} tll_channel_object;

/* Initializer */
static pthread_attr_t attr;

static inline void tll_init(void) __attribute__((always_inline));

static inline void tll_init(void) {
  // initialize GC
  // GC_INIT();
  // set thread stacksize
  const rlim_t stacksize = 0x8000000;
  struct rlimit rl;
  getrlimit(RLIMIT_STACK, &rl);
  if (rl.rlim_cur < stacksize) {
    rl.rlim_cur = stacksize;
    setrlimit(RLIMIT_STACK, &rl);
  }
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, stacksize);
}

static inline void tll_exit(void) { pthread_exit(NULL); }

/* Functional Core */
static inline tll_object *tll_closure_make(tll_object *(*fun)(tll_object *[]),
                                           unsigned int fvc,
                                           unsigned int argc) {
  const unsigned int size = 1 + fvc;
  const unsigned int arity = size + argc;
  const size_t closure_size = SIZE_OF_CLOSURE(size);
  tll_closure_object *clo = (tll_closure_object *)tll_alloc(closure_size);
  clo->m_header.m_kind = TLL_CLOSURE_KIND;
  clo->m_size = size;
  clo->m_arity = arity;
  clo->m_fun = fun;
  clo->m_objs[0] = (tll_object *)clo;
  return (tll_object *)clo;
}

static inline void tll_closure_set(tll_object *clo, tll_object *arg,
                                   unsigned int i) {
  // environment index starts at 1
  ((tll_closure_object *)clo)->m_objs[i] = arg;
}

static inline tll_object *tll_closure_app(tll_object *o, tll_object *arg) {
  const tll_closure_object *clo = (tll_closure_object *)o;
  const unsigned int size = clo->m_size;
  const unsigned int arity = clo->m_arity;
  const size_t closure_size = SIZE_OF_CLOSURE(size);
  const size_t applied_size = SIZE_OF_CLOSURE(size + 1);
  // deep copy closure
  tll_closure_object *app = (tll_closure_object *)tll_alloc(applied_size);
  memcpy(app, (tll_closure_object *)clo, closure_size);
  app->m_size = size + 1;
  app->m_objs[size] = arg;
  if (size + 1 < arity) {
    return (tll_object *)app;
  } else {
    tll_object *(*fun)(tll_object *[]) = app->m_fun;
    tll_object *result = (*fun)(app->m_objs);
    tll_free(app);
    return result;
  }
}

/* Inductive Data */
static inline unsigned int tll_ctor_get_tag(tll_object *ctor) {
  return ((tll_ctor_object *)ctor)->m_tag;
}

static inline tll_object *tll_ctor_make(const unsigned int tag,
                                        const unsigned int argc) {
  tll_ctor_object *ctor = (tll_ctor_object *)tll_alloc(SIZE_OF_CTOR(argc));
  ctor->m_header.m_kind = TLL_CTOR_KIND;
  ctor->m_size = argc;
  ctor->m_tag = tag;
  return (tll_object *)ctor;
}

static inline tll_object *tll_ctor_set_tag(tll_object *ctor, unsigned int tag) {
  ((tll_ctor_object *)ctor)->m_tag = tag;
  return ctor;
}

static inline void tll_ctor_set(tll_object *ctor, tll_object *arg,
                                unsigned int i) {
  ((tll_ctor_object *)ctor)->m_objs[i] = arg;
}

static inline tll_object *tll_ctor_get(tll_object *ctor, unsigned int i) {
  return ((tll_ctor_object *)ctor)->m_objs[i];
}

static inline void failcase(void) {
  fprintf(stderr, "%s", "Fail-case reached, compiler bug!\n");
  abort();
}

static inline void absurd(void) {
  fprintf(stderr, "%s", "Absurd case reached, compiler bug!\n");
  abort();
}

/* Monadic Thunks */
static inline tll_object *tll_thunk_make(tll_object *(*fun)(tll_object **),
                                         const unsigned int fvc) {
  const unsigned int th_size = SIZE_OF_THUNK(fvc);
  tll_thunk_object *th = (tll_thunk_object *)tll_alloc(th_size);
  th->m_header.m_kind = TLL_THUNK_KIND;
  th->m_size = fvc;
  th->m_fun = fun;
  return (tll_object *)th;
}

static inline void tll_thunk_set(tll_object *th, tll_object *arg,
                                 unsigned int i) {
  ((tll_thunk_object *)th)->m_objs[i] = arg;
}

static inline tll_object *tll_thunk_force(tll_object *o) {
  tll_thunk_object *th = (tll_thunk_object *)o;
  tll_object *(*fun)(tll_object *[]) = th->m_fun;
  return (*fun)(th->m_objs);
}

/* Primitive Operators */
static inline tll_object *tll_box(size_t n) {
  return (tll_object *)(((size_t)(n) << 1) | 1);
}

static inline size_t tll_unbox(tll_object *o) { return (size_t)(o) >> 1; }

static inline tll_object *tll_int64_to_int(int64_t n) {
  return tll_box((unsigned)((int)n));
}

static inline int64_t tll_scalar_to_int64(tll_object *a) {
  return (int)((unsigned)tll_unbox(a));
}

static inline tll_object *tll_int_neg(tll_object *e) {
  const int64_t v = tll_scalar_to_int64(e);
  return tll_int64_to_int(-v);
}

static inline tll_object *tll_int_add(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return tll_int64_to_int(v1 + v2);
}

static inline tll_object *tll_int_sub(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return tll_int64_to_int(v1 - v2);
}

static inline tll_object *tll_int_mul(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return tll_int64_to_int(v1 * v2);
}

static inline tll_object *tll_int_div(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v2 == 0 ? 0 : tll_int64_to_int(v1 / v2);
}

static inline tll_object *tll_int_mod(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  if (v2 == 0) {
    return 0;
  } else {
    const ssize_t r = v1 % v2;
    return r < 0 ? tll_int64_to_int(r + labs(v2)) : tll_int64_to_int(r);
  }
}

static inline tll_object *tll_int_lte(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v1 <= v2 ? tll_int64_to_int(__true__) : tll_int64_to_int(__false__);
}

static inline tll_object *tll_int_gte(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v1 >= v2 ? tll_int64_to_int(__true__) : tll_int64_to_int(__false__);
}

static inline tll_object *tll_int_lt(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v1 < v2 ? tll_int64_to_int(__true__) : tll_int64_to_int(__false__);
}

static inline tll_object *tll_int_gt(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v1 > v2 ? tll_int64_to_int(__true__) : tll_int64_to_int(__false__);
}

static inline tll_object *tll_int_eq(tll_object *e1, tll_object *e2) {
  const int64_t v1 = tll_scalar_to_int64(e1);
  const int64_t v2 = tll_scalar_to_int64(e2);
  return v1 == v2 ? tll_int64_to_int(__true__) : tll_int64_to_int(__false__);
}

static inline tll_object *tll_int_to_char(tll_object *e) {
  return tll_int_mod(e, tll_int64_to_int(256));
}

static inline tll_object *tll_char_to_int(tll_object *e) { return e; }

/* Strings */
static inline tll_object *tll_string_make(char *buf) {
  const size_t n = strlen(buf) + 1;
  tll_string_object *s = (tll_string_object *)tll_alloc(sizeof_string(n));
  s->m_header.m_kind = TLL_STRING_KIND;
  s->m_size = n;
  memcpy(s->m_data, (char *)buf, n);
  return (tll_object *)s;
}

static inline tll_object *tll_string_pushback(tll_object *e1, tll_object *e2) {
  const tll_string_object *s1 = (tll_string_object *)e1;
  const size_t s1_size = s1->m_size;
  const size_t s2_size = s1_size + 1;
  tll_string_object *s2 =
      (tll_string_object *)tll_alloc(sizeof_string(s2_size));
  s2->m_header.m_kind = TLL_STRING_KIND;
  s2->m_size = s2_size;
  memcpy(s2->m_data, (char *)s1->m_data, s1_size);
  s2->m_data[s2_size - 2] = tll_unbox(e2);
  s2->m_data[s2_size - 1] = 0;
  return (tll_object *)s2;
}

static inline tll_object *tll_string_concat(tll_object *e1, tll_object *e2) {
  const tll_string_object *s1 = (tll_string_object *)e1;
  const tll_string_object *s2 = (tll_string_object *)e2;
  const size_t s1_size = s1->m_size;
  const size_t s2_size = s2->m_size;
  const size_t s3_size = s1_size + s2_size - 1;
  tll_string_object *s3 =
      (tll_string_object *)tll_alloc(sizeof_string(s3_size));
  s3->m_header.m_kind = TLL_STRING_KIND;
  s3->m_size = s3_size;
  memcpy(s3->m_data, (char *)s1->m_data, s1_size);
  memcpy(s3->m_data + s1_size - 1, (char *)s2->m_data, s2_size);
  s3->m_data[s3_size - 1] = 0;
  return (tll_object *)s3;
}

static inline tll_object *tll_string_size(tll_object *e) {
  const tll_string_object *s = (tll_string_object *)e;
  return (tll_object *)tll_box(s->m_size - 1);
}

static inline tll_object *tll_string_at(tll_object *e1, tll_object *e2) {
  const tll_string_object *s = (tll_string_object *)e1;
  const size_t s_size = s->m_size;
  const long i = tll_unbox(e2);
  if (s->m_size == 1) {
    return 0;
  } else {
    long r = i % (s_size - 1);
    r = r < 0 ? r + labs(i) : r;
    return tll_box(s->m_data[r]);
  }
}

/* Channels */
static inline tll_object *tll_channel_make() {
  tll_channel_object *c =
      (tll_channel_object *)tll_alloc(sizeof(tll_channel_object));
  pthread_mutex_init(&c->w_mu, NULL);
  pthread_mutex_init(&c->r_mu, NULL);
  pthread_mutex_init(&c->m_mu, NULL);
  pthread_cond_init(&c->r_cond, NULL);
  pthread_cond_init(&c->w_cond, NULL);
  c->m_header.m_kind = TLL_CHANNEL_KIND;
  c->r_waiting = 0;
  c->w_waiting = 0;
  c->m_data = NULL;
  return (tll_object *)c;
}

/* Primitive Effects */
typedef struct {
  tll_object *closure; // closure
  tll_object *channel; // channel
} fork_arguments;

static inline tll_object *tll_effect_print(tll_object *e) {
  const tll_string_object *s = (tll_string_object *)e;
  printf("%s", s->m_data);
  return tll_box(__tt__);
}

static inline tll_object *tll_effect_prerr(tll_object *e) {
  const tll_string_object *s = (tll_string_object *)e;
  fprintf(stderr, "%s", s->m_data);
  return tll_box(__tt__);
}

static inline tll_object *tll_effect_readln(tll_object *e) {
  char *buf = NULL;
  size_t size;
  const size_t len = getline(&buf, &size, stdin) - 1;
  buf[len] = 0;
  tll_object *s = tll_string_make(buf);
  free(buf);
  return s;
}

static inline void *tll_fork_fun(void *args) {
  fork_arguments *fork_args = (fork_arguments *)args;
  tll_object *closure = fork_args->closure;
  tll_object *channel = fork_args->channel;
  tll_free(fork_args);
  tll_object *th = tll_closure_app(closure, channel);
  tll_free(closure);
  tll_thunk_force(th);
  return NULL;
}

static inline tll_object *tll_effect_fork(tll_object *e) {
  pthread_t thread;
  tll_object *c = tll_channel_make();
  fork_arguments *fork_args =
      (fork_arguments *)tll_alloc(sizeof(fork_arguments));
  fork_args->closure = e;
  fork_args->channel = c;
  pthread_create(&thread, &attr, (void *(*)(void *))tll_fork_fun, fork_args);
  return (tll_object *)c;
}

static inline tll_object *tll_effect_send(tll_object *o, tll_object *arg) {
  tll_channel_object *c = (tll_channel_object *)o;
  pthread_mutex_lock(&c->w_mu);
  pthread_mutex_lock(&c->m_mu);

  c->m_data = arg;
  c->w_waiting++;

  if (c->r_waiting > 0) {
    // Signal waiting reader.
    pthread_cond_signal(&c->r_cond);
  }

  // Block until reader consumed c->data.
  pthread_cond_wait(&c->w_cond, &c->m_mu);

  pthread_mutex_unlock(&c->m_mu);
  pthread_mutex_unlock(&c->w_mu);
  return (tll_object *)c;
}

static inline tll_object *tll_effect_recv0(tll_object *o) {
  tll_channel_object *c = (tll_channel_object *)o;
  pthread_mutex_lock(&c->r_mu);
  pthread_mutex_lock(&c->m_mu);

  while (!c->w_waiting) {
    // Block until writer has set chan->data.
    c->r_waiting++;
    pthread_cond_wait(&c->r_cond, &c->m_mu);
    c->r_waiting--;
  }

  tll_object *msg = c->m_data;
  c->w_waiting--;

  // Signal waiting writer.
  pthread_cond_signal(&c->w_cond);

  pthread_mutex_unlock(&c->m_mu);
  pthread_mutex_unlock(&c->r_mu);

  tll_object *ctor = tll_ctor_make(__exU__, 2);
  tll_ctor_set(ctor, msg, 0);
  tll_ctor_set(ctor, o, 1);
  return ctor;
}

static inline tll_object *tll_effect_recv1(tll_object *o) {
  tll_channel_object *c = (tll_channel_object *)o;
  pthread_mutex_lock(&c->r_mu);
  pthread_mutex_lock(&c->m_mu);

  while (!c->w_waiting) {
    // Block until writer has set chan->data.
    c->r_waiting++;
    pthread_cond_wait(&c->r_cond, &c->m_mu);
    c->r_waiting--;
  }

  tll_object *msg = c->m_data;
  c->w_waiting--;

  // Signal waiting writer.
  pthread_cond_signal(&c->w_cond);

  pthread_mutex_unlock(&c->m_mu);
  pthread_mutex_unlock(&c->r_mu);

  tll_object *ctor = tll_ctor_make(__exL__, 2);
  tll_ctor_set(ctor, msg, 0);
  tll_ctor_set(ctor, o, 1);
  return ctor;
}

static inline tll_object *tll_effect_close0(tll_object *o) {
  tll_channel_object *c = (tll_channel_object *)o;
  pthread_mutex_destroy(&c->w_mu);
  pthread_mutex_destroy(&c->r_mu);

  pthread_mutex_destroy(&c->m_mu);
  pthread_cond_destroy(&c->r_cond);
  pthread_cond_destroy(&c->w_cond);
  tll_free(c);

  return tll_box(__tt__);
}

static inline tll_object *tll_effect_close1(tll_object *c) {
  return tll_box(__tt__);
}

// magic
static inline void tll_magic(void) {
  fprintf(stderr, "%s", "Magic reached.\n");
  abort();
}

#endif // RUNTIME_H
