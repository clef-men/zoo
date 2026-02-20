// g++ -O2 fib_sequential.cpp -o fib_sequential.cpp.exe 

#include <iostream>

long fib(long n) {
  if (n < 2) return n;
  return fib(n - 1) + fib(n - 2);
}

int main(int argc, char *argv[]) {
  if (argc < 2) {
    std::cerr << "Missing a command-line integer argument (N)\n";
    return 2;
  }
  int n = std::stoi(argv[1]);
  long res = fib(n);
  std::cout << res << "\n";
  return 0;
}
