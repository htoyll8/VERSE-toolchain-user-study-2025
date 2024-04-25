MDD error log: 
- Very very often: forgot the `{x}unchanged` annotation on loops. The error
  message in this situation is unhelpful. It typically says `missing resource'
  at the `return` or something similar. What's actually happening is that the
  resource at the return site exists in nearly the right form, but CN can't
  prove that one or more variables have stayed the same. 
- Often: didn't include the `extract` or `instantiate` commands during error
  accesses. Typically error messages sa things like 
    `Missing resource for reading` (for `extract`) or 
    `integer value not representable at type signed int` (for `instantiate`). 
  I figured out eventually that this was what it meant. 
- Often: forgot that post-state variable names are referring to their
  _pre-state_ values. This is often super-confusing when a variable hasn't been
  modified, but the _current variable state_ and the _logical value_ aren't
  provably equivalent (thanks to the lack of `unchanged` annotations).

Gripes / questions:
- Is there a way to add inline assertions?  UPDATE: Yes! You can write 'assert
  THING', or comment it using the CN syntax. But there's no particular
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
- What does the specification for free look like? Malloc?
- Confused by the 'extract' and 'instantiate' operations? How does it know which
  resource to access? Why are they necessary? 
- V. confusing error message without the 'unchanged' modifier on invariants
- Why no implication in the syntax? 
- How to universally quantify in the postcondition? 
- CN verified functions in reverse order, which isn't a serious problem but is 
  oddly annoying. 

Design suggestions / warts:
- It would be great to just get syntax highlighting working on the CN portions
  of the file
- The debug mode at the moment is extremely rudimentary
- Give the HTML output flag a more descriptive name
- Fix the hard-coded txt trace file
- Post-state variable assertions are a weird little gotcha? ie. can't assert
  properties of a variable in the post-state, but only the return value.
- Unclear what the meaning / types of the values bound by 'take' are? UPDATE: I
  think I understand this now.
- Unclear how extract works?
- Unhelpful error message when unchanged is missed

# Quantification notes 

I'd like to write this `requires` clause, but it currently doesn't parse: 
``` 
/*@ 
requires 
  each (integer j; 0 <= j && j < length) 
  { 
    each (integer k; j < k && k < length) 
    {
      IndexPre[j] <= IndexPre[k]; 
    }
  }
@*/
```

# Even more gripes 2024-4-19

* The `power` function now claims to be uninterpreted, but somehow has an effect
  on the behavior. 

* I can write: 
```
/*@ requires 
      let MAXi32 = (i64) 2147483647i64; // TODO: lift to library 
      (i64) i + 1i64 <  MAXi32 @*/
```
... but I can't write
```
/*@ requires 
      let MAXi32 = (i64) 2147483647i64; // TODO: lift to library 
      (i64) i + (i64) 1 <  MAXi32 @*/
```

This also means you have to write: 
```
      x == (0i32 - 1i32) @*/
```
Rather than the slightly more natural version: 
```
      x == (i32) (-1) @*/
```


* Inconsistent semicolons in the spec language. Required some places, eg
  extract. Forbidden elsewhere, eg. a the end of requires / ensures 