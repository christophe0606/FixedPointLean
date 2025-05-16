# Introduction

It is a very simplified and quick introduction to theorem provers for embedded developers. You'll only need VS Code.

By embedded developers, I mean someone coming from a `C` language background and with absolutely no idea about theorem provers, what they are, how they can be used and why they are useful.

I hope you'll be both delighted and surprised by what you're about to learn. Despite the scary name - theorem prover - you'll see that it is actually quite practical and not too complex.

But first, we need to review some concepts which may be the only difficult part of this introduction.

# Set theory

Mathematics, as it is generally practiced, is built on top of set theory.

Everything is built from sets. 

A function \\(f\\) is a set of pairs \\(\\{x,y\\}\\) where \\(y=f(x)\\) but no recipe is given for how to compute those pairs.

Sets are untyped. For instance, one could have the set: \\(\\{1,"test",\\{"subset"\\}\\}\\)

Set theory uses classical logic where you can prove that some things exist but you can't construct an example. 

For instance, using the law of the excluded middle you know that \\(A ⋁ ¬A\\) but you don't know whether \\(A\\) is true or false.

# Another foundation for Mathematics 

It is possible to build mathematics on top of other foundations. And lots of theorem provers use the calculus of inductive constructions.

It is like a programming language! Yes! It is possible to use a programming language as a foundation of mathematics.

We are going to use the Lean 4 theorem prover to explain what it means and give some examples.

Install Lean 4 using [this documentation](https://lean-lang.org/documentation/setup/). It comes as a VS Code extension.


In the next paragraph we will study the calculus of inductive constructions using Lean 4 examples and finally explain where the theorems are.
