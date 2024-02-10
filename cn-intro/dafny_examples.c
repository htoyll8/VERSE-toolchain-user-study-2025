// Simple CN examples - derived from the Dafny tutorial:  
// https://dafny.org/dafny/OnlineTutorial/guide.html

// Mike Dodds - Galois Inc - January 2024

struct int_pair
{
  int fst;
  int snd;
};

void multiple_returns(int x, int y, struct int_pair *ret)
/*@ requires take PairPre = Owned<struct int_pair>(ret) @*/
/*@ requires (0 - power(2,31)) < x + y; x + y < power(2,31) @*/
/*@ requires (0 - power(2,31)) < x - y; x - y < power(2,31) @*/
/*@ ensures take PairPost = Owned<struct int_pair>(ret) @*/
/*@ ensures PairPost.fst == x + y @*/
/*@ ensures PairPost.snd == x - y @*/
{
  ret->fst = x + y;
  ret->snd = x - y;
  return;
}

/*@
function (integer) max_spec (integer a, integer b)
{
  if (a > b){
    a
  } else {
    b
  }
}
@*/

int max(int a, int b)
/*@ ensures (a >= b && return == a) || (a < b && return == b) @*/
/*@ ensures return == max_spec(a,b) @*/
{
  if (a > b)
  {
    return a;
  }
  else
  {
    return b;
  }
}
void max_test()
{
  int v;
  v = max(-2, 7);
  assert(v == 7);
}

// Compute the absolute value a function.

/*@
function (integer) abs_spec(integer x)
{
  if (x < 0) {
    (0 - x)
  } else {
    x
  }
}
@*/

int abs(int x)
/*@ requires (0 - power(2,31) < x) @*/ // TODO: why is this required?
/*@ ensures 0 <= return @*/
/*@ ensures (x < 0 && return == (0 - x)) || (0 <= x && return == x) @*/
/*@ ensures 0 <= return && (return == x || return == (0 - x)) @*/ // Same property
/*@ ensures return == abs_spec(x) @*/                             // Same property
{
  if (x < 0)
  {
    return (-1 * x);
  }
  else
  {
    return x;
  }
}
void abs_testing()
{
  int v = abs(3);
  assert(0 <= v);
  assert(v == 3);
}

// A specialized version of the same function

int abs_neg(int x)
/*@ requires (0 - power(2,31) < x) @*/
/*@ requires x < 0 @*/
/*@ ensures 0 <= return @*/
/*@ ensures 0 <= return && (return == x || return == (0 - x)) @*/
{
  return -x;
}

// Another specialized version of the same function

int abs_stupid(int x)
/*@ requires (0 - power(2,31) < x) @*/
/*@ requires x == (0 - 1) @*/
/*@ ensures 0 <= return @*/
/*@ ensures 0 <= return && (return == x || return == (0 - x)) @*/
{
  return x + 2;
}

// /*@
// function [rec] (integer) fib_spec(integer n)
// {
//   if (n == 0) { 0 }
//   else { if (n == 1) { 1 }
//   else { fib_spec(n - 1) + fib_spec(n - 2)}}
// }
// @*/

// int compute_fib(int n)
// /*@ requires 0 <= n @*/
// /*@ ensures return == fib_spec(n) @*/
// {
//   int i = 1;
//   int a = 0;
//   int b = 1;

//   if (n == 0)
//   {
//     /*@ unfold fib_spec(0) @*/
//     return 0;
//   };

//   while (i < n)
//   /*@ inv 0 < i; i <= n @*/
//   /*@ inv a == fib_spec(i - 1) @*/
//   /*@ inv b == fib_spec(i) @*/
//   {
//     /*@ unfold fib_spec(i) @*/
//     int tmp_a = a;
//     a = b;
//     b = tmp_a + b;
//     i = i + 1;
//   }

//   return b;
// }

int find(int *a, int length, int key)
/*@ requires 0 < length @*/
/*@ requires take IndexPre = each (integer j; 0 <= j && j < length)
                                  {Owned<int>(a + j)} @*/
/*@ ensures take IndexPost = each (integer j; 0 <= j && j < length)
                                  {Owned<int>(a + j)} @*/
/*@ ensures (return < 0) || (IndexPost[return] == key) @*/
// TODO: prove that if return == 0, the key isn't present in the index
/*@ ensures IndexPre == IndexPost @*/
{
  int idx = 0;

  while (idx < length)
  /*@ inv {a}unchanged; {length}unchanged; {key}unchanged @*/
  /*@ inv 0 <= idx; idx <= length @*/
  /*@ inv take IndexInv = each (integer j; 0 <= j && j < length)
                               {Owned<int>(a + j)} @*/
  /*@ inv IndexInv == IndexPre @*/
  {
    /*@ extract Owned<int>, idx @*/
    /*@ instantiate good<int>, idx  @*/ // TODO: what does this do?
    if (*(a + idx) == key)
    {
      return idx;
    }
    idx = idx + 1;
  };
  idx = -1;
  return idx;
}

// Binary search algorithm. We can't prove this functionally correct because CN
// doesn't support universal quantification, which is necessary to establish
// that the list is sorted. 

int binary_search(int *a, int length, int value)
/*@ requires 0 <= length @*/
/*@ requires (2 * length) < power(2,31) @*/
/*@ requires take IndexPre = each (integer j; 0 <= j && j < length)
                                  {Owned<int>(a + j)} @*/
/*@ ensures take IndexPost = each (integer j; 0 <= j && j < length)
                                  {Owned<int>(a + j)} @*/
/*@ ensures IndexPost == IndexPre @*/
{
  int low = 0;
  int high = length;

  while (low < high)
  /*@ inv {a}unchanged; {length}unchanged @*/
  /*@ inv 0 <= low; low <= high; high <= length @*/
  /*@ inv (low + high) < power(2,31) @*/
  /*@ inv take IndexInv = each (integer j; 0 <= j && j < length)
                               {Owned<int>(a + j)} @*/
  /*@ inv IndexInv == IndexPre @*/
  {
    int mid = (low + high) / 2;
    /*@ extract Owned<int>, mid @*/
    /*@ instantiate good<int>, mid  @*/
    if (a[mid] < value)
    {
      low = mid + 1;
    }
    else if (value < a[mid])
    {
      high = mid;
    }
    else if (value == a[mid])
    {
      return mid;
    }
  };
  return -1;
}
