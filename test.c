char f(int x) { return 'a'; }

int g(int y) {
  __attribute__((annotate("nospec"))) int z;
  return y*2;
}

int main() {
  return g(3);
}

