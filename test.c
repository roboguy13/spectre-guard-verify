int test() {
  int y __attribute__((nospec));
  int z;
  int x;
  x = z;

  if (z == 0) {
    x = 3;
  }
  return 1;
}
