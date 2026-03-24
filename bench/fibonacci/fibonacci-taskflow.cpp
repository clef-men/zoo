// This example is derived from
//   https://github.com/taskflow/taskflow/blob/master/examples/fibonacci.cpp
// with the following modifications to make it similar to our OCaml benchmark:
// - a sequential cutoff (as an environment variable)
// - choice of number of threads (as an environment variable)

// To compile:
//   git clone https://github.com/taskflow/taskflow.git /tmp/taskflow
//   clang++ -std=c++20 -pthread -O3 -I/tmp/taskflow fibonacci-taskflow.cpp -o /tmp/fibonacci-taskflow.exe

#include <taskflow/taskflow.hpp>
#include <cstdlib>
#include <iostream>
#include <chrono>

long fibo(long N) {
  if (N < 2) return N;
  return fibo(N - 1) + fibo(N - 2);
}

long spawn_async(tf::Executor& executor, long N, long cutoff) {
  
  if (N <= cutoff) {
    return fibo(N); 
  }
  
  long res1, res2;
  
  tf::TaskGroup tg = executor.task_group();
  
  tg.silent_async([&executor, N, cutoff, &res1]() { 
    res1 = spawn_async(executor, N - 1, cutoff); 
  });

  // tail recursion optimization
  res2 = spawn_async(executor, N - 2, cutoff);

  tg.corun();

  return res1 + res2;
}

void usage_fail() {
  std::cerr << "usage: CUTOFF=20 NUM_THREADS=4 ./fibonacci N\n";
  std::exit(EXIT_FAILURE);
}

int main(int argc, char* argv[]) {

  long N, cutoff, num_threads;


  if(argc != 2) usage_fail();
  N = std::atol(argv[1]);

  {
    const char* s = std::getenv("CUTOFF");
    if (!s) usage_fail();
    cutoff = std::atol(s);
  }

  {
    const char* s = std::getenv("NUM_THREADS");
    if (!s) usage_fail();
    num_threads = std::atol(s);
  }

  // Create executor explicitly
  tf::Executor executor(num_threads);

  auto tbeg = std::chrono::steady_clock::now();

  auto future = executor.async([&executor, N, cutoff]() { 
    return spawn_async(executor, N, cutoff); 
  });

  printf("fib[%zu] = %zu\n", N, future.get());

  auto tend = std::chrono::steady_clock::now();

  std::cout << "elapsed time: " 
            << std::chrono::duration_cast<std::chrono::milliseconds>(tend - tbeg).count()
            << " ms\n";

  return 0;
}
