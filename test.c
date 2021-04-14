int test() {
  int y __attribute__((nospec));
  int x;
  x = y;
  /*
  if (y == 0) {
    x = 3;
  }
  */
  return 1;
}
