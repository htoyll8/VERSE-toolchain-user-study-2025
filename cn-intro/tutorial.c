// Some simple CN examples for tutorial purposes
// Mike Dodds - Galois Inc - January 2024

// CN Manual (WIP): https://github.com/rems-project/cerberus/blob/master/backend/cn/manual/manual.md

/*
MDD gripes / questions:
- Is there a way to add inline assertions?  UPDATE: Yes! You can write 'assert
  <something>', or comment it using the CN syntax. But there's no particular
  magic about this - it seems to just be a wrapper around the normal C assert
  command.
- Is it possible to assert proof-state properties inline? Eg. assert what's
  currently owned? UPDATE: inline assertions are checked, and these can be
  enclosed in 'magic comments'. But this is just the same as asserting a
  concrete fact about the program state. I.e we can't use this for ghost state
  assertions.
- What's going on with the 'take' syntax? Something like the inhale / exhale in
  Dafny? UPDATE: this is 'resource-let' - see the manual
- How do we get CN to dump out the txt trace? UPDATE: this seems to be
  hard-coded
- confused by the {x}@start notation? UPDATE: seems to deprecated now.
- What does free look like? Malloc?
- Confused by the 'extract' operation? How does it know which resource to access?
- V. confusing error message without the 'unchanged' modifier on invariants

Suggestions / warts:
- It would be great to just get syntax highlighting working on the CN portions
  of the file
- The debug mode at the moment is extremely rudimentary
- Give the HTML output flag a more descriptive name
- Fix the hard-coded txt trace file
- Post-state variable assertions are a weird little gotcha? ie. can't assert
  properties of a variable in the post-state, but only the return value.
- Unclear what the meaning / types of the values bound by 'take' are? UPDATE: I
  think I understand this now.
*/

// A main() function that does nothing. This can't fault, and therefore requires
// no CN annotations.

int main()
{
  return 0;
}

// A function that adds two numbers together. This can overflow, but we can add
// a requires-clause that enforces that x and y are both zero. This makes the
// function trivially non-faulting.

signed int add_1(signed int x, signed int y)
/*@ requires x == 0; y == 0 @*/
/*@ ensures return == x + y @*/
/*@ ensures return == {x}@start + {y}@start @*/ // <-- equivalent???
{
  signed int i;
  i = x + y;
  return i;
}

// This function is also trivially non-faulting if we only require one integer
// to be zero.

signed int add_2(signed int x, signed int y)
/*@ requires x == 0 @*/
/*@ ensures return == x + y @*/
{
  signed int i;
  i = x + y;
  return i;
}

// Verifying the addition function for arbitrary inputs requires that the total
// cannot overflow.

signed int add_3(signed int x, signed int y)
// Note the lower and upper bounds here:
/*@ requires (0 - power(2,31)) <= x + y;  x + y < power(2,31) @*/
/*@ ensures return == x + y @*/
{
  signed int i;
  i = x + y;
  return i;
}

// Verifying unsigned integer addition. Note we don't need to add a lower bound
// any more.

unsigned int add_4(unsigned int x, unsigned int y)
/*@ requires x + y < power(2,31) @*/
/*@ ensures return == x + y @*/
{
  signed int i;
  i = x + y;
  return i;
}

// This is the example from the paper. Here we show that the value stored in
// memory is correctly incremented.

signed int inc_1(signed int i)
/*@ requires i < power(2,31) - 1 @*/
/*@ ensures return == i + 1 @*/
{
  i = i + 1;
  return i;
}

// Modified example from the paper, written by OliverB. This example shows how
// CN can work with struct types.

struct s
{
  int x;
  int y;
};

void zero_y_1(struct s *p)
/*@ requires take StructPre  = Owned<struct s>(p) @*/
/*@ ensures  take StructPost = Owned<struct s>(p) @*/
/*@ ensures  StructPre.x == StructPost.x @*/
/*@ ensures  StructPost.y == 0 @*/
{
  p->y = 0;
  // p->x = 7;  // <-- This would fail
}

// DOESN'T WORK: In the POPL paper, there was some kind of field override
// syntax, but this seems to be broken at the moment.

// void zero_y_2(struct s *p)
// /*@ requires take StructPre  = Owned<struct s>(p) @*/
// /*@ ensures  take StructPost = Owned<struct s>(p) @*/
// /*@ ensures  StructPost == StructPre{.y = 0} @*/ // <-- Keep everything the same except field y.
//                                                         [CURRENTLY DOESN'T WORK]
// {
//   p->y = 0;
// }

// This examples swaps the values stored in *a and *b, via a temporary variable

void swap_1(int *a, int *b)
/*@ requires take Pa = Owned(a) @*/
/*@ requires take Pb = Owned(b) @*/
/*@ ensures take Qa = Owned(a) @*/
/*@ ensures take Qb = Owned(b) @*/
/*@ ensures Qb == Pa @*/
/*@ ensures Qa == Pb @*/
{
  int temp = *a;
  *a = *b;
  // *a = 0;  // <-- This would fail
  *b = temp;
}

// Inline assertions are supported, but that they seem to use the standard C
// syntax for boolean assertions rather than CN's syntax.

int assert_1(int x)
/*@ requires x == 7 @*/
/*@ ensures return == 0 @*/
{
  x = 0;
  assert(x == 0);
  return (x);
}

// This alternative syntax for assertion also works:

int assert_2(int x)
/*@ requires x == 7 @*/
/*@ ensures return == 0 @*/
{
  x = 0;
  /*@ assert(x == 0) @*/
  return (x);
}

// We can assert properties about memory cells as well. I guess CN is checking
// these by symbolic simulation over the Cerberus semantics

void inline_assert_1(int *x, int *y)
/*@ requires take Xpre = Owned<int>(x) @*/
/*@ requires take Ypre = Owned<int>(y) @*/
/*@ requires *x == 7; *y == 7 @*/
/*@ ensures take Xpost = Owned<int>(x) @*/
/*@ ensures take Ypost = Owned<int>(y) @*/
/*@ ensures *x == 0; *y == 0 @*/
{
  *x = 0;
  /*@ assert(*x == 0 && *y == 7) @*/
  // /*@ assert take Xmid = Owned<int>(x) @*/ <-- Doesn't parse, can't use CN syntax here
  // /*@ assert *x == 0; *y == 7 @*/ // <-- Doesn't parse, can't use CN syntax here
  *y = 0;
}

// Variables x / y are bound at the start of the function, even in the ensures
// clauses. So we can't assert properties of stack variables in the post-state.

// For example, this doesn't work:

// void assign_2 (int x)
// /*@ requires x == 7 @*/
// /*@ ensures x == 0 @*/
// {
//   x = 0;
// }

// On the other hand, we can assert properties of the post-state easily if the
// values are locations in memory

void assign_ptr_1(int *x, int *y)
/*@ requires take Xpre = Owned<int>(x) @*/
/*@ requires take Ypre = Owned<int>(y) @*/
/*@ requires *x == 7; *y == 7 @*/
/*@ ensures take Xpost = Owned<int>(x) @*/
/*@ ensures take Ypost = Owned<int>(y) @*/
/*@ ensures *x == 0; *y == 0 @*/
{
  *x = 0;
  *y = 0;
}

// An example with a terminating loop. Note we don't need an invariant here
// because the loop exit condition implies the postcondition

int loop_1()
/*@ ensures return == 7 @*/
{
  int i = 0;
  while (i != 7)
  {
    // Don't do anything
  };
  return i;
}

// An example with a non-terminating loop. This is a partial-correctness logic,
// so a proof doesn't imply termination.

void loop_2()
/*@ ensures false @*/
{
  int i = 0;
  while (i < 10)
  /*@ inv i == 0 @*/ // <-- exit condition never satisfied
  {
    // Don't do anything
  };
}

// An example with a more interesting loop

int loop_3(int i)
/*@ requires 0 <= i; i < power(2,31) @*/
{
  int n = 0;
  int acc = 0;

  while (n != i)
  /*@ inv n <= i @*/
  /*@ inv 0 <= acc; acc <= n @*/
  {
    acc = n - acc;
    n++;
  };
  return acc;
}

// A finitely bounded loop. Note that CN won't prove this without the invariant,
// although actually we could definitely BMC it using Crucible.

int loop_4()
/*@ ensures return == 1 @*/
{
  int n = 0;
  int acc = 0;

  while (n < 1)
  /*@ inv (n == 0 && acc == 0)
          ||
          (n == 1 && acc == 1) @*/
  {
    n++;
    acc++;
  };
  return acc;
}

// A function that writes 7 into a given offset in an array of size n

void array_write_1(int *arr, int size, int off)
/*@ requires 0 <= off; off < size @*/
/*@ requires take arrayStart = each (integer j; 0 <= j && j < size) {Owned(arr + j)} @*/
/*@ ensures take arrayEnd = each (integer j; 0 <= j && j < size) {Owned(arr + j)} @*/
{
  int i = off;
  /*@ extract Owned<int>, i @*/ // <-- required to read / write
  // TODO: how does this know which ownership predicate to bind to?
  arr[off] = 7;
  i++;
  return;
}

// A function that writes 7 into all positions in an array of size n. This
// version of the proof doesn't establish that the resulting array contains
// all 7

void array_write_2(int *arr, int n)
/*@ requires 0 < n @*/
/*@ requires take arrayStart = each (integer j; 0 <= j && j < n) {Owned<int>(arr + j)} @*/
/*@ ensures take arrayEnd = each (integer j; 0 <= j && j < n) {Owned<int>(arr + j)} @*/
{
  int i = 0;
  while (i < n)
  /*@ inv {n}unchanged; {arr}unchanged @*/ // TODO: unclear why this is necessary?
  /*@ inv 0 <= i; i <= n @*/
  /*@ inv take arrayInv = each (integer j; 0 <= j && j < n) {Owned<int>(arr + j)} @*/
  {
    /*@ extract Owned<int>, i @*/ // <-- required to read / write
    *(arr + i) = 7;
    i++;
  };
  return;
}

// A data-structure representing nodes from a linked list of integers -- struct
// def and recursive predicate. Adapted from:
// https://github.com/rems-project/cerberus/blob/master/tests/cn/append.c

struct node_int_list
{
  int val;
  struct node_int_list *next;
};

/*@
// The specification-level type definition for a sequence. We use this to
// represent the contents of the list.

datatype seq {
  Seq_Nil {},
  Seq_Cons {integer val, datatype seq next}
}

// The predicate representing an in-memory list segment. Note that the return
// value of this predicate is the specification-level contents of the list, i.e
// a pure sequence of values.

predicate (datatype seq) IntListSeg(pointer p, pointer tail) {
  if (addr_eq(p,tail)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct node_int_list>(p);
    assert (is_null(H.next) || (integer)H.next != 0);
    take tl = IntListSeg(H.next, tail);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/

// A function on lists that does nothing. Note we don't need an inductive lemma
// here because the precondition is preserved by the frame rule.

struct node_int_list *list_1(struct node_int_list *xs)
/*@ requires take Xs = IntListSeg(xs,NULL) @*/
/*@ ensures take Ys = IntListSeg(return,NULL) @*/
/*@ ensures Ys == Xs @*/
{
  struct node_int_list *ys;
  ys = xs;
  return ys;
}

// A fancier example. This function walks the list and assigns 7 to the value
// field of every node. (Proof written by CPulte and modified by MDD.)

/*@
// A lemma saying that a list segment followed by a list node can be
// folded into a list segment. Note that this lemma is assumed in CN
// and would have to be proved separately in Coq.
// MDD note: I don't think this can currently be proved ...

lemma IntListSeqSnoc(pointer p, pointer tail)
  requires take l1 = IntListSeg(p, tail);
           take v = Owned<struct node_int_list>(tail)
  ensures take l2 = IntListSeg(p, v.next)
@*/

void list_2(struct node_int_list *head)
/*@ requires take Xs = IntListSeg(head,NULL) @*/
/*@ ensures take Ys = IntListSeg(head,NULL) @*/
{
  struct node_int_list *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSeg(head,curr) @*/
  /*@ inv take Remaining = IntListSeg(curr,NULL) @*/
  /*@ inv {head}unchanged @*/
  /*@ inv let i_curr = curr @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnoc(head, i_curr) @*/
  }
  return;
}

/*@
// This append function exists at the specification level

function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {val : h, next : zs}  => {
      Seq_Cons {val: h, next: append(zs, ys)}
    }
  }
}

// This lemma is assumed by CN and must be proved inductively in Coq.

lemma IntListSeqSnocVal(pointer p, pointer tail)
  requires take l1 = IntListSeg(p, tail);
           take v = Owned<struct node_int_list>(tail)
  ensures take l2 = IntListSeg(p, v.next);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} })
@*/

void list_3(struct node_int_list *head)
/*@ requires take Xs = IntListSeg(head,NULL) @*/
/*@ ensures take Ys = IntListSeg(head,NULL) @*/
{
  struct node_int_list *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSeg(head,curr) @*/
  /*@ inv take Remaining = IntListSeg(curr,NULL) @*/
  /*@ inv {head}unchanged @*/
  /*@ inv let i_curr = curr @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnocVal(head, i_curr) @*/
  }
  return;
}

// From the paper. Here power_uf(-,-) is an uninterpreted function. We use a
// lemma to allow CN to reason about this function.

void lemma_power2_def(int y)
/*@ trusted @*/
/*@ requires y >= 0 @*/
/*@ ensures (power_uf(2,y+1)) == (2 * power_uf(2,y)) @*/
/*@ ensures (power_uf(2,0)) == 1 @*/
{
}

int power2_1()
/*@ ensures return == power_uf(2,0) @*/
{
  int i = 0;
  int pow = 1;
  lemma_power2_def(i);
  return pow;
}

int power2_2(int y)
/*@ requires 0 < y; y <= 32 @*/
/*@ ensures return == power_uf(2,1) @*/
{
  int i = 0;
  int pow = 1;
  lemma_power2_def(i);

  /*@ assert (0 <= y && y <= 32) @*/
  /*@ assert (0 <= i && i <= y) @*/
  /*@ assert (pow == power_uf(2,i)) @*/
  /*@ assert (0 < pow && pow < power(2,32)) @*/
  pow = pow * 2;
  i = i + 1;
  // lemma_power2_def(i);

  /*@ assert (pow == power_uf(2,i)) @*/
  /*@ assert (0 < pow && pow < power(2,32)) @*/

  return pow;
}

// int power2_3(int y)
// /*@ requires 0 < y; y <= 32 @*/
// /*@ ensures return == power_uf(2,y) @*/
// {
//     int i = 0;
//     int pow = 1;
//     lemma_power2_def(i);

//     while (i < y)
//     /*@ inv 0 <= i; i <= y @*/
//     /*@ inv 0 <= y; y <= 32 @*/
//     /*@ inv pow == power_uf(2,i) @*/
//     /*@ inv 0 < pow; pow < power(2,32) @*/
//     {
//         pow = pow * 2;
//         lemma_power2_def(i);
//         i = i + 1;
//     };

//     return pow;
// }

// malloc() doesn't work. This isn't too surprising since it's strictly
// speaking a library function. But I wonder what the specification of that
// function should be?

// We can define a fake malloc() function that only works on ints

int *my_malloc_int()
/*@ trusted @*/
/*@ ensures take New = Block<int>(return) @*/
{
}

int *malloc_1()
/*@ ensures take New = Owned<int>(return) @*/
{
  int *new;
  new = my_malloc_int();
  *new = 7; // Have to initialize the memory before it's owned
  return new;
}

int *malloc_2()
/*@ ensures take New = Owned<int>(return) @*/
/*@ ensures *return == 7 @*/
{
  int *new;
  new = my_malloc_int();
  *new = 7;
  return new;
}

// free() is also not defined, but we can fake it

void my_free_int(int *target)
/*@ trusted @*/
/*@ requires take ToFree = Owned<int>(target) @*/
{
}

void free_1(int *x, int *y)
/*@ requires take Xpre = Owned<int>(x) @*/
/*@ requires take Ypre = Owned<int>(y) @*/
/*@ ensures take Ypost = Owned<int>(y) @*/
{
  my_free_int(x);
}

// We can use the 'extract' keyword to cast an owned piece of memory into
// another type. This example modified from
// https://github.com/rems-project/cerberus/blob/master/tests/cn/swap_pair.c

// This code takes an array of ints at *array_p and writes 7 to the n-th element

void extract_test_1(unsigned long int *array_p, int off, int n)
/*@ requires take arrayStart = each (integer j; 0 <= j && j < n) {Owned(array_p + j)} @*/
/*@ requires 0 <= off; off < n @*/
/*@ ensures  take arrayEnd =   each (integer j; 0 <= j && j < n) {Owned(array_p + j)} @*/
/*@ ensures  arrayEnd[off] == 7 @*/
{
  /*@ extract Owned<unsigned long int>, off @*/ // <-- required to read / write
  array_p[off] = 7;
}

void extract_test_2(unsigned long int *array_p, int off, int n)
/*@ requires take arrayStart = each (integer j; 0 <= j && j < n) {Owned(array_p + j)} @*/
/*@ requires 0 <= off; off < n @*/
/*@ ensures  take arrayEnd =   each (integer j; 0 <= j && j < n) {Owned(array_p + j)} @*/
/*@ ensures  arrayEnd[off] == 7 @*/
{
  /*@ extract Owned<unsigned long int>, off @*/ // <-- required to read / write
  unsigned long int tmp = array_p[off];

  array_p[off] = 7;
}

// void extract_test_2(unsigned long int *array_p, int i, int n)
// /*@ requires take arrayStart = each (integer j; 0 <= j && j < n)
//                                 {Owned(array_p + j)} @*/
// /*@ requires arrayStart[i] < power(2,31) - 1 @*/
// /*@ requires n > i; i >= 0 @*/
// /*@ ensures take arrayEnd = each (integer j; 0 <= j && j < n)
//                                 {Owned(array_p + j)} @*/
// /*@ ensures arrayEnd[i] == arrayStart[i] @*/
// {
//     /*@ extract Owned<unsigned long int>, i @*/ // <-- required to read / write
//     unsigned long int tmp = array_p[i];
//     array_p[i] = tmp;
// }

/*===================================================================*/
/* Old broken stuff below...                                         */
/*===================================================================*/

// void list_walk( struct node_int_list *head)
// /*@ requires take Xs = IntListSeg(head,NULL) @*/
// /*@ ensures take Ys = IntListSeg(head,NULL) @*/
// {
//     struct node_int_list *curr;
//     curr = head;

//     while (curr != 0)
//     /*@ inv take Visited = IntListSeg(head,curr) @*/
//     /*@ inv take Remaining = IntListSeg(curr,NULL) @*/
//     {
//         curr = curr->next;
//     }
//     return;
// }

// void list_set_to_7( struct node_int_list *head)
// /*@ requires take Xs = IntListSeg(head,NULL) @*/
// /*@ ensures take Ys = IntListSeg(head,NULL) @*/
// {
//     struct node_int_list *curr;
//     curr = head;

//     while (curr != 0)
//     /*@ inv take Visited = IntListSeg(head,curr) @*/
//     /*@ inv take Remaining = IntListSeg(curr,NULL) @*/
//     {
//         curr->val = 7;
//         curr = curr->next;
//     }
//     return;
// }

// // A list reverse function - TODO

// struct node_int_list* list_reverse( struct node_int_list *head )
// /*@ requires take Xs = IntList(head) @*/
// /*@ ensures take Ys = IntList(return) @*/
// {
//     struct node_int_list *curr;
//     curr = head;

//     struct node_int_list *prev;
//     prev = 0;
//     struct node_int_list *next;
//     next = 0;

//     // while (curr != 0) {
//     //     next = curr->next;
//     //     curr->next = prev;
//     //     prev = curr;
//     //     curr = next;
//     // }
//     curr = prev;
//     return curr;
// }

// predicate (datatype seq) IntList(pointer p) {
//   if (is_null(p)) {
//     return Seq_Nil{};
//   } else {
//     take H = Owned<struct node_int_list>(p);
//     assert (is_null(H.next) || (integer)H.next != 0);
//     take tl = IntList(H.next);
//     return (Seq_Cons { val: H.val, next: tl });
//   }
// }
