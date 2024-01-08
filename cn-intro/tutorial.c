// Some simple CN examples for tutorial purposes 
// Mike Dodds - Galois Inc - January 2024 

/*
MDD questions: 
- Is there a way to add inline assertions?  UPDATE: Yes! You can write 'assert
  <something>', or comment it using the CN syntax. But there's no particular
  magic about this - it seems to just be a wrapper around the normal C assert
  command. 
- Is it possible to assert proof-state properties inline? Eg. assert what's
  currently owned? 
- What's going on with the 'take' syntax? Something like the inhale / exhale in
  Dafny? 
- How do we get CN to dump out the txt trace? UPDATE: this seems to be
  hard-coded 
- confused by the {x}@start notation? 
- What does free look like? Malloc? 

Suggestions / warts:  
- It would be great to just get syntax highlighting working on the CN portions
  of the file
- The debug mode at the moment is extremely rudimentary 
- Give the HTML output flag a more descriptive name 
- Fix the hard-coded txt trace file 
- Post-state variable assertions are a weird little gotcha? 
- Unclear what the meaning / types of the values bound by 'take' are? 
*/

// A main() function that does nothing. This can't fault, and therefore requires
// no CN annotations. 

int main() {
    return 0;
}

// A function that adds two numbers together. This can overflow, but we can add
// a requires-clause that enforces that x and y are both zero. This makes the
// function trivially non-faulting. 

signed int add_1(signed int x, signed int y) 
/*@ requires x == 0; y == 0 @*/
/*@ ensures return == {x}@start + {y}@start @*/
// /*@ ensures return == x + y @*/ // <-- equivalent???

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
// 
{ 
    signed int i; 
    i = x + y; 
    return i; 
}

// This is the example from the paper. We need to constrain the value of i so
// that it cannot overflow. 

signed int inc_1(signed int i)
/*@ requires i < power(2,31) - 1 @*/
/*@ ensures return == {i}@start + 1 @*/
{
    i = i + 1;
    return i;
} 

// Verifying the addition function for arbitrary inputs requires that x and y
// are both non-negative and the total cannot overflow. 

signed int add_3(signed int x, signed int y) 
/*@ requires 0 <= x; 0 <= y @*/ // <-- Uncertain why this is necessary? 
/*@ requires x + y < power(2,31) @*/
/*@ ensures return == {x}@start + {y}@start @*/
{ 
    signed int i; 
    i = x + y; 
    return i; 
}

// Modified example from the paper written by OliverB. Note that the syntax in
// the CN paper is wrong. 

struct s {
    int x; 
    int y;
};

void zero_y_1(struct s *p)
/*@ requires take OP  = Owned(p) @*/
/*@ ensures  take OP2 = Owned(p) @*/
/*@ ensures  OP2.x == OP.x @*/
/*@ ensures  OP2.y == 0 @*/
{
    p->y = 0;
    // p->x = 7;  // <-- This would fail 
}

// A function that swaps values. 

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

// We can prove normal properties of straight-line code. Note that inline
// assertions are supported, but that they seem to use the standard C syntax for
// boolean assertions rather than CN's syntax. 

int assign_1 (int x) 
/*@ requires x == 7 @*/ 
/*@ ensures return == 0 @*/
{ 
  x = 0; 
  assert (x == 0); 
  return(x); 
} 

// Note that it seems like the variables x / y are bound at the start of the
// function, even in the ensures clauses. So this doesn't work: 

// void assign_2 (int x) 
// /*@ requires x == 7 @*/ 
// /*@ ensures x == 0 @*/
// { 
//   x = 0; 
// } 

// On the other hand, we can assert properties of the post-state easily if the
// values are locations in memory, and the function takes pointers  

void assign_ptr_1 (int *x, int *y) 
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

// We can assert properties inline about memory cells as well. We don't need
// ownership assertions here for some reason? I guess this is because these are
// only required wherever they could be ambiguous, ie. at control-flow and fn
// interfaces?? 

void inline_assert_1 (int *x, int *y) 
/*@ requires take Xpre = Owned<int>(x) @*/
/*@ requires take Ypre = Owned<int>(y) @*/
/*@ requires *x == 7; *y == 7 @*/
/*@ ensures take Xpost = Owned<int>(x) @*/
/*@ ensures take Ypost = Owned<int>(y) @*/
/*@ ensures *x == 0; *y == 0 @*/
{ 
  *x = 0; 
  assert (*x == 0 && *y == 7);  // Assertions are checked during verification 
  // /*@ assert take Xmid = Owned<int>(x) @*/ <-- Doesn't parse 
  // /*@ assert *x == 0; *y == 0 @*/ // <-- Doesn't parse
  *y = 0; 
} 


// A linked list of integers -- struct def and recursive predicate. Taken from:
// https://github.com/rems-project/cerberus/blob/master/tests/cn/append.c 

struct int_list { 
  int val;
  struct int_list* next;
};

/*@
datatype seq { 
  Seq_Nil {},
  Seq_Cons {integer val, datatype seq next}
}

predicate (datatype seq) IntListSeg(pointer p, pointer tail) {
  if (addr_eq(p,tail)) { 
    return Seq_Nil{};
  } else { 
    take H = Owned<struct int_list>(p);
    assert (is_null(H.next) || (integer)H.next != 0);
    take tl = IntListSeg(H.next, tail);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/

// A function on lists that does nothing 

struct int_list* list_do_nothing( struct int_list *xs ) 
/*@ requires take Xs = IntListSeg(xs,NULL) @*/
/*@ ensures take Ys = IntListSeg(return,NULL) @*/
/*@ ensures Ys == Xs @*/
{ 
    struct int_list *ys; 
    ys = xs; 
    return ys; 
}


// From the paper. Here power_uf(-,-) is an uninterpreted function. We use a
// lemma to allow CN to reason about this function. 

void lemma_power2_def(int y) 
/*@ trusted @*/
/*@ requires y >= 0 @*/
/*@ ensures (power_uf(2,y+1)) == (2 * power_uf(2,y)) @*/
/*@ ensures (power_uf(2,0)) == 1 @*/
{}

int power2_1() 
/*@ ensures return == power_uf(2,0) @*/
{
    int i = 0; 
    int pow = 1; 
    lemma_power2_def(i); 
    return pow; 
}

// int power2_2(int y) 
// /*@ requires 0 < y; y < 31 @*/
// // /*@ ensures return == power_uf(2,y) @*/
// {
//     int i = 0; 
//     int pow = 1; 
//     lemma_power2_def(i); 

//     while (i <= y) 
//     /*@ inv 0 < i; i <= y @*/
//     /*@ inv pow == power_uf(2,i) @*/
//     { 
//         pow = pow * 2; 
//         i = i + 1; 
//         lemma_power2_def(i); 
//     }
//     return pow; 
// }


// malloc() doesn't work. This isn't too surprising since it's strictly
// speaking a library function. But I wonder what the specification of that
// function should be? 

// void malloc_1() 
// /*@ ensures take New = Owned<int>(return) @*/
// {
//     int *new; 
//     new = malloc(sizeof(int)); 
//     return new; 
// }

// We can define a fake malloc() function that only works on ints 

int* my_malloc_int()
/*@ trusted @*/
/*@ ensures take New = Owned<int>(return)@*/
{}

int* malloc_assign_1()
/*@ ensures take New = Owned<int>(return)@*/
/*@ ensures *return == 7 @*/
{
    int *new; 
    new = my_malloc_int(); 
    *new = 7; 
    return new; 
}


// free() is also not defined, which is a bit more surprising. This example
// gives the following error: 
//    > tutorial.c:292:5: error: use of undeclared identifier 'free'

// void free_1( int* x, int *y )
// /*@ requires take Xpre = Owned<int>(x) @*/
// /*@ requires take Ypre = Owned<int>(y) @*/
// /*@ ensures take Ypost = Owned<int>(y) @*/
// {
//     free(x); 
// }



// We can use the 'extract' keyword to cast a piece of memory into another type.
// This example modified from
// https://github.com/rems-project/cerberus/blob/master/tests/cn/swap_pair.c 

void extract_test_1(unsigned long int *pair_p, int i, int n) 
/*@ requires take pairStart = each (integer j; 0 <= j && j < n) 
                                {Owned(pair_p + j)} @*/
/*@ requires n > i; i >= 0 @*/ 
/*@ ensures take pairEnd = each (integer j; 0 <= j && j < n) 
                                {Owned(pair_p + j)} @*/
{
    /*@ extract Owned<unsigned long int>, i @*/ // <-- required to read / write 
    unsigned long int tmp = pair_p[i];
    pair_p[i] = 7; 
}





/*===================================================================*/
/* Old broken stuff below...                                         */
/*===================================================================*/

// void list_walk( struct int_list *head) 
// /*@ requires take Xs = IntListSeg(head,NULL) @*/
// /*@ ensures take Ys = IntListSeg(head,NULL) @*/
// {
//     struct int_list *curr; 
//     curr = head; 

//     while (curr != 0) 
//     /*@ inv take Visited = IntListSeg(head,curr) @*/
//     /*@ inv take Remaining = IntListSeg(curr,NULL) @*/
//     { 
//         curr = curr->next; 
//     }
//     return;  
// }


// void list_set_to_7( struct int_list *head) 
// /*@ requires take Xs = IntListSeg(head,NULL) @*/
// /*@ ensures take Ys = IntListSeg(head,NULL) @*/
// {
//     struct int_list *curr; 
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

// struct int_list* list_reverse( struct int_list *head ) 
// /*@ requires take Xs = IntList(head) @*/
// /*@ ensures take Ys = IntList(return) @*/
// { 
//     struct int_list *curr; 
//     curr = head; 

//     struct int_list *prev;
//     prev = 0; 
//     struct int_list *next; 
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
//     take H = Owned<struct int_list>(p);
//     assert (is_null(H.next) || (integer)H.next != 0);
//     take tl = IntList(H.next);
//     return (Seq_Cons { val: H.val, next: tl });
//   }
// }

