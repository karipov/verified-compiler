// the runtime for compiled programs: it sets up the heap, calls the compiled code, and prints
// the answer the same way `Value.toString` in `Parse.lean` does
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

// 16 million words (128 MiB). the model has an unlimited heap; programs that need more than
// this aren't covered
#define HEAP_WORDS (1 << 24)

extern uint64_t lisp_entry(uint64_t *heap);

// numbers end in 0b00, booleans in 0b0011111, and pairs are pointers ending in 0b010
static void print_value(uint64_t v) {
  if ((v & 0b11) == 0) {
    printf("%llu", (unsigned long long)(v >> 2));
  } else if ((v & 0b1111111) == 0b0011111) {
    printf((v >> 7) ? "true" : "false");
  } else if ((v & 0b111) == 0b010) {
    uint64_t *p = (uint64_t *)(v - 0b010);
    printf("(pair ");
    print_value(p[0]);
    printf(" ");
    print_value(p[1]);
    printf(")");
  } else {
    printf("<unknown value %#llx>", (unsigned long long)v);
  }
}

// the error handler. the compiled code calls it when a check fails, and it never returns
void lisp_error(void) {
  printf("error\n");
  exit(1);
}

int main(void) {
  uint64_t *heap = aligned_alloc(16, HEAP_WORDS * sizeof(uint64_t));
  if (heap == NULL) {
    fprintf(stderr, "couldn't allocate the heap\n");
    return 2;
  }
  print_value(lisp_entry(heap));
  printf("\n");
  return 0;
}
