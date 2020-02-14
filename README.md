# B522 Programming Language Foundations

Indiana University, Spring 2020

In this course we study the mathematical foundations of programming
languages. That is, how to define programming languages and how to
reason about those languages and programs written in them.  The course
will use the online textbook

[Programming Language Foundations in Agda](https://plfa.github.io/beta/)
(PLFA) (the beta version)

[Agda](https://agda.readthedocs.io/en/v2.6.0.1/index.html) is a proof
assistant and a dependently typed language.  No prior knowledge of
Agda is assumed; it will be taught from scratch.  Prior knowledge of
another proof assistant or dependently typed language is helpful but
not necessary.


## Instructor

Prof. Jeremy Siek, Luddy 3016, [jsiek@indiana.edu](mailto:jsiek@indiana.edu)


## Lectures

Monday and Wednesday at 4:30-5:45pm in Luddy Hall Room 4101.


## Office Hours (in Luddy Hall 3016 or the neighboring 3014)

* Monday 3:00-4:30pm
* Tuesday 11:00-12:30pm
* Friday 1:30-3:00pm


## Assignments

1. January 20: Exercises `Bin` (in [Naturals](https://plfa.github.io/Naturals/)) and
  `Bin-laws` (in [Induction](https://plfa.github.io/Induction/)).
  
2. January 27: Exercises `Bin-predicates` (in [Relations](https://plfa.github.io/Relations/)) and
  `Bin-embedding` (in [Isomorphism](https://plfa.github.io/Isomorphism/)).

3. February 3: Exercises
   `⊎-weak-×` (in [Connectives](https://plfa.github.io/Connectives/)), 
   `⊎-dual-×` (in [Negation](https://plfa.github.io/Negation/)),
   `∃-distrib-⊎`,
   `∃¬-implies-¬∀`,
   `Bin-isomorphism` (in [Quantifiers](https://plfa.github.io/Quantifiers/)).

4. February 10: Exercises 
   `_<?_`, 
   `iff-erasure` (in [Decidable](https://plfa.github.io/Decidable/)),
   `foldr-++`,
   `foldr-∷`, and
   `Any-++-⇔` (in [List](https://plfa.github.io/List/)).

5. February 17: Exercises
   `mul`,
   `—↠≲—↠′`, and
   `⊢mul`
   (in [Lambda](https://plfa.github.io/Lambda/)).
   Exercises
   `progress′` and
   `unstuck`
   (in [Properties](https://plfa.github.io/Properties/)).

6. February 24: Exercises X in [DeBruijn](https://plfa.github.io/DeBruijn/),
   and X in [More](https://plfa.github.io/More/).


## Project, due May 1

Choose a language feature that is not spelled out in PLFA to formalize
in Agda. Your formalization should include both a static semantics
(aka. type system), a dynamic semantics, and a proof of type
safety. For the dynamic semantics you must use a different style than
the approach used in PLFA, that is, do not use a reduction
semantics. Examples of other styles you can use are contextual
dynamics (i.e., using evaluation contexts), abstract machines,
definitional interpreters (i.e., a recursive function), and
denotational semantics. The book _Types and Programming Langauges_ by
Benjamin Pierce has many examples of language features that would be
an appropriate choice for your project.


## Schedule

| Month    | Day | Topic    |
| -------- | --- | -------- |
| January  | 13  | [Naturals](https://plfa.github.io/Naturals/) & [Induction](https://plfa.github.io/Induction/) |
|          | 15  | [Relations](https://plfa.github.io/Relations/) |
|          | 16  | [Equality](https://plfa.github.io/Equality/) & [Isomorphism](https://plfa.github.io/Isomorphism/) (unusual day, regular time) |
| 		   | 27  | [Connectives](https://plfa.github.io/Connectives/) & [Negation](https://plfa.github.io/Negation/) |
|		   | 28  | [Quantifiers](https://plfa.github.io/Quantifiers/) & [Decidable](https://plfa.github.io/Decidable/) (unusual day, regular time) |
|		   | 29  | [Lists](https://plfa.github.io/Lists/) and higher-order functions |
| February | 3   | [Lambda](https://plfa.github.io/Lambda/) the Simply Typed Lambda Calculus |
|          | 5   | [Properties](https://plfa.github.io/Properties/) such as type safety |
|          | 10  | [DeBruijn](https://plfa.github.io/DeBruijn/) representation of variables |
|          | 12  | [More](https://plfa.github.io/More/) constructs: numbers, let, products (pairs), sums, unit, empty, lists |
|          | 17  | [STLC Termination via Logical Relations](./STLC-Termination.lagda.md) |
|          | 19  | [Inference](https://plfa.github.io/Inference/) bidirectional type inference |
|          | 24  | [Untyped](https://plfa.github.io/Untyped/) Lambda Calculus |
|          | 26  | [Confluence](https://plfa.github.io/Confluence/) of the Lambda Calculus |
| March    | 2  | [BigStep](https://plfa.github.io/BigStep/) Call-by-name Evaluation of the Lambda Calculus |
|          | 4   | [Denotational](https://plfa.github.io/Denotational/) semantics of the Lambda Calculus |
|          | 9   | [Compositional](https://plfa.github.io/Compositional/) |
|          | 11   | [Soundness](https://plfa.github.io/Soundness/) |
|          | 16  | [Adequacy](https://plfa.github.io/Adequacy/) |
|          | 18  | [ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/) |
|          | 23  | References and the Heap |
|          | 25  | Subtyping and Records |
|          | 30  | Classes and Objects (Featherweight Java) |
| April    | 1   | Gradual Typing |
|          | 6   | Universal and Existential Types (Parametric Polymorphism) |
|          | 8   | Hindley-Milner Inference |
|          | 13  | Recursive Types |
|          | 15  | Intersection and Union Types |
|          | 20  | Higher-Order Polymorphism |
|          | 22  | Dependent Types |
|          | 27  | TBD |
|          | 29  | TBD |

## Resources

* Join the course mailing list on [Piazza](https://piazza.com/iu/spring2020/b522/home).

* Join the PLFA mailing list [plfa-interest](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest)
  and ask questions!

* [Crash Course on Notation in Programming Language Theory](http://siek.blogspot.com/2012/07/crash-course-on-notation-in-programming.html)
