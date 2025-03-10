# Categorical Semantics in Coq (WIP)

We formalize in Coq:
- an equational theory of the simply typed lambda calculus (STLC)
- just enough category theory
- sound models of STLC in Cartesian closed categories (WIP)

This was my course project of graduate level course CS 747, Formal Reasoning with Proof Assistants, given at University of Waterloo by Yizhou Zhang, 2025 Winter.

# Note on Implementation

Functional extensionality is used in the category theory library for simplicity.

# References

Below are some references on the topic.

**Categories and types**:
- R. L. Crole, *Categories for Types. Roy L. Crole*. Cambridge: University Press, 1993.
- C. A. Gunter, *Semantics of Programming Languages: Structures and Techniques*. Cambridge, Mass: MIT Press, 1993. 

**Coq**: 
- [*Software Foundations*](https://softwarefoundations.cis.upenn.edu/)
- [*Certified Programming with Dependent Types*](http://adam.chlipala.net/cpdt/)

# Version

Coq version: `8.20.0`.