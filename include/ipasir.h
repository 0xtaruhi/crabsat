/* IPASIR: reentrant incremental SAT solver API (implemented by crabsat).
 *
 * Build with `cargo build --release -p crabsat-ipasir` and link with
 * target/release/libcrabsat_ipasir.a (plus -lpthread -ldl -lm) or
 * target/release/libcrabsat_ipasir.so.
 */
#ifndef ipasir_h_INCLUDED
#define ipasir_h_INCLUDED

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

const char *ipasir_signature(void);
void *ipasir_init(void);
void ipasir_release(void *solver);
void ipasir_add(void *solver, int32_t lit_or_zero);
void ipasir_assume(void *solver, int32_t lit);
int ipasir_solve(void *solver);
int32_t ipasir_val(void *solver, int32_t lit);
int ipasir_failed(void *solver, int32_t lit);
void ipasir_set_terminate(void *solver, void *data,
                          int (*terminate)(void *data));
void ipasir_set_learn(void *solver, void *data, int max_length,
                      void (*learn)(void *data, int32_t *clause));

#ifdef __cplusplus
}
#endif

#endif
