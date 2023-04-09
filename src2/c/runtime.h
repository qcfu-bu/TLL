#ifndef runtime_h
#define runtime_h

typedef void *tll_ptr;

typedef tll_ptr *tll_env;

typedef struct
{
  tll_ptr (*f)(tll_ptr, tll_env);
  tll_env env;
} _tll_clo;

typedef struct
{
  int tag;
  tll_ptr *data;
} _tll_node;

typedef _tll_clo *tll_clo;
typedef _tll_node *tll_node;

#define tll_ptr_size sizeof(tll_ptr)
#define tll_clo_size sizeof(_tll_clo)
#define tll_node_size sizeof(_tll_node)

tll_ptr proc_sender(tll_ptr x, tll_env env);
tll_ptr proc_stdout(tll_ptr ch);
tll_ptr proc_stdin(tll_ptr ch);
tll_ptr proc_stderr(tll_ptr ch);

void instr_init();
void instr_mov(tll_ptr *x, tll_ptr v);
void instr_clo(tll_ptr *x, tll_ptr (*f)(tll_ptr, tll_env),
               int size, tll_env env, int narg, ...);
void instr_call(tll_ptr *x, tll_ptr clo, tll_ptr v);
void instr_struct(tll_ptr *x, int tag, int size, ...);
void instr_open(tll_ptr *x, tll_ptr (*f)(tll_env),
                int size, tll_env env, int narg, ...);
void instr_send(tll_ptr *x, tll_ptr ch, int mode);
void instr_recv(tll_ptr *x, tll_ptr ch, int mode);
void instr_close(tll_ptr *x, tll_ptr ch, int mode);
void instr_prim(tll_ptr *x, tll_ptr (*f)(tll_ptr));
void instr_free_clo(tll_ptr *x);
void instr_free_struct(tll_ptr *x);
void instr_free_thread(tll_env env);

#endif
