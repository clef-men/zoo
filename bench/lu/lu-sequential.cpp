// g++ -O1 lu-sequential.cpp -o lu-sequential.cpp.exe 

#include <vector>
#include <cstdlib>
#include <iostream>

typedef std::vector<std::vector<double>> matrix;

matrix create_rand(int sz) {
  matrix m(sz);
  for (int i = 0; i < sz; ++i) {
    std::vector<double> v(sz);
    for (int j = 0; j < sz; ++j) {
      v[j] = rand();
    }
    m[i] = v;
  }
  return m;
}

void lu(matrix m, int sz) {
  for (int k = 0; k < sz - 1; ++k) {
    for (int i = k + 1; i < sz; ++i) {
      double factor = m[i][k] / m[k][k];
      for (int j = k + 1; j < sz; ++j) {
	m[i][j] = m[i][j] - factor * m[k][j];
      }
      m[i][k] = factor;
    }
  }
}

int main(int argc, char *argv[]) {
  if (argc < 2) {
    std::cerr << "Missing a command-line integer argument (size)\n";
    return 2;
  }
  int sz = std::stoi(argv[1]);
  matrix m = create_rand(sz);
  lu(m, sz);
  return 0;
}
