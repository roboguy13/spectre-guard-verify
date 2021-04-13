int test() {
  int y __attribute__((nospec));
  int x;
  y = 1;
  x = y;
  /*
  if (y == 0) {
    x = 3;
  }
  */
  return 1;
}
