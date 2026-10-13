/* Minimal IPASIR client: x1 | x2, !x1 | x2, then assume !x2.
 *
 *   cargo build --release -p crabsat-ipasir
 *   cc -Iinclude examples/ipasir_example.c \
 *      target/release/libcrabsat_ipasir.a -lpthread -ldl -lm -o example
 *
 * (Linux; see include/ipasir.h for other platforms.)
 */
#include <stdio.h>

#include "ipasir.h"

int main(void) {
  void *s = ipasir_init();
  printf("%s\n", ipasir_signature());
  ipasir_add(s, 1), ipasir_add(s, 2), ipasir_add(s, 0);
  ipasir_add(s, -1), ipasir_add(s, 2), ipasir_add(s, 0);
  int res = ipasir_solve(s);
  printf("solve: %d, x2 = %d\n", res, ipasir_val(s, 2));
  if (res != 10 || ipasir_val(s, 2) != 2)
    return 1;
  ipasir_assume(s, -2);
  res = ipasir_solve(s);
  printf("solve with -2: %d, failed(-2) = %d\n", res, ipasir_failed(s, -2));
  if (res != 20 || !ipasir_failed(s, -2))
    return 1;
  ipasir_release(s);
  return 0;
}
