#include <stdio.h>

int double_deref(const int **p) {
  return **p;
}

void deref_and_print(int *p) {
  printf("deref in C has value: %d\n", *p);
}

int add_one_int(int x) {
  return 2 + x;
}

void printer() {
  printf("printing from C\n");
}

// function with many arguments, to test functionality when some args are stored
// on the stack
int test_stack_spill(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j, int k, int l) {
  return a+b+c+d+e+f+g+h+i+j+k+l;
}

unsigned int get_unsigned_int() {
  return -10;
}

short add_int16(short x) {
  return x + 3;
}

long add_short_to_long(short x, long y) {
  return x + y;
}

int* pointer_test() {
  int *point = malloc(sizeof(int)); 
  *point=1;  
  return point;
}

int* array_pointer_test() {
  const int COUNT = 3;
  int *arr = malloc(COUNT*sizeof(int));
  for(int i = 0; i < COUNT; ++i) 
    arr[i] = i;
  return arr;
}

void swap_double_ptrs(short **x, short **y) {
  short temp = **x;
  **x = **y;
  **y = temp;
}

// examples of C writing values and pointers to Miri memory,
// suggested by Ralf in
// https://github.com/rust-lang/miri/issues/2365#issuecomment-1192512642

void set(short *x, short val) { *x = val; }
void set2(short **x, short val) { **x = val; }

void setptr(short **x, short *val) { *x = val; }
void setptr2(short ***x, short *val) { **x = val; }
