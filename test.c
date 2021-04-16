#include <stdio.h>

int test() {
  int y __attribute__((nospec));
  int z;
  int x;
  x = z;

  if (y == 0) {
    x = 3;
  }
  return 1;
}

int main() { }

