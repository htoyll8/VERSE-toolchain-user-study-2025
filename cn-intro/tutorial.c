// Some simple CN examples 
// Mike Dodds - Galois Inc - January 2024 

// To get CN to watch this file for modifications: 
//   $ echo "tutorial.c" | entr -c ../cn/cn --slow-smt=1 --state-file=./tutorial.html tutorial.c
// This relies on the entr utility which monitors files for changes. 

/*
Question dump: 
- Is there a way to add inline assertions? 
- What's going on with the 'take' syntax? Something like the inhale / exhale in
  Dafny? 
- How do we get CN to dump out the txt trace? 

Suggestions: 
- Give the HTML output flag a better name 
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
{ 
    signed int i; 
    i = x + y; 
    return i; 
}

// This function is also trivially non-faulting if we only require one integer
// to be zero. 

signed int add_2(signed int x, signed int y) 
/*@ requires x == 0 @*/
/*@ ensures return == {x}@start + {y}@start @*/
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

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) { 
    return Seq_Nil{};
  } else { 
    take H = Owned<struct int_list>(p);
    assert (is_null(H.next) || (integer)H.next != 0);
    take tl = IntList(H.next);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/

/*@
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

// From the paper. Here power_uf(-,-) is an uninterpreted function but we use a
// lemma to allow CN to reason about it. 

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

int power2_2(int y) 
/*@ requires 0 < y; y < 31 @*/
/*@ ensures return == power_uf(2,y) @*/
{
    int i = 0; 
    int pow = 1; 
    lemma_power2_def(i); 

    while (i <= y) 
    /*@ inv 0 < i; i <= y @*/
    /*@ inv pow == power_uf(2,i) @*/
    { 
        pow = pow * 2; 
        i = i + 1; 
        lemma_power2_def(i); 
    }
    return pow; 
}

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