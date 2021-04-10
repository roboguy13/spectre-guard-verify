int test(int x) {
  int y __attribute__((nospec));
  y = 1;
  for (int i = 0; i < x; ++i) {
    y *= x;
  }
}
