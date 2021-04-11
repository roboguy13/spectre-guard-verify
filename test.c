int test() {
  int y __attribute__((nospec));
  int x;
  y = 1;
  if (y == 0) {
    x = 3;
  }
}
