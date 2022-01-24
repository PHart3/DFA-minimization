# DFA-minimization

This is a complete implementation of the DFA minimization algorithm found in

Timo Knuutila,  
**Re-describing an algorithm by Hopcroft**,  
Theoretical Computer Science,  
Volume 250, Issues 1–2,  
2001,  
https://doi.org/10.1016/S0304-3975(99)00150-4.  

This article uses random-access arrays for most of its main data structures. We, instead, use
red-black trees, which increases the worst-case runtime. Otherwise, our implementation follows
the article closely.

To run the algorithm on an automaton, call

`run_Equivalence A X final M trans`  

with SML/NJ, where

- `A` is the list of states (ints) of the automaton,  
- `X` the list of alphabet symbols (ints),  
- `final` the list of final states,  
- `M` the measure used for selecting which classes to insert in the list of candidates, and  
- `trans` the transition function encoded as a list of triples *(x,s,t)* of ints where *s* steps to
*t* on symbol x.  

This will print the states of the minimal DFA.  

Here, the measure refers to one of the three values  

`class | x_class | inv_class`  

where  

- `class` corresponds to *|B|*,  
- `x_class` to *|x<sup>-1</sup> &cap; B|*, and  
- `inv_class` to *|x<sup>&minus;1</sup>(B)|*.  

Note that in Section 4.5, the author should say that *x<sup>-1</sup> &cap; B* stands for
*x(A) &cap; B*, not *x<sup>-1</sup>(A) &cap; B*.  

We have also corrected a few small mistakes in the article's pseudocode. These corrections are
marked in the source code.  

Finally, this code has been tested on just a handful of examples. Please let me know of any bugs
you find.  
