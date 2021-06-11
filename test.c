#include <stdio.h>

int test() {
  int y __attribute__((nospec));
  int w __attribute__((nospec));
  int z;
  int x;
  x = z;
  // w = y;

  if (y == 0) {
     w = 3;
  }
  return 1;
}

int main() { }

