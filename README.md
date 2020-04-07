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
   `Any-++-⇔` (in [Lists](https://plfa.github.io/Lists/)).

5. February 17: Exercises
   `mul`,
   `—↠≲—↠′`, and
   `⊢mul`
   (in [Lambda](https://plfa.github.io/Lambda/)).
   Exercises
   `progress′` and
   `unstuck`
   (in [Properties](https://plfa.github.io/Properties/)).

6. February 28: Formalize the STLC using the extrinsic
   style, as in [Lambda](https://plfa.github.io/Lambda/),
   but using de Bruijn indices to represent variables,
   as in [DeBruijn](https://plfa.github.io/DeBruijn/).
   You should use the `ext`, `rename`, `exts`, and `subst`
   functions from the DeBruijn chapter, simplifying the
   type declarations of those functions. For example,

        exts : ∀ {Γ Δ}
          → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
            ---------------------------------
          → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)

   becomes

        exts : 
          → (Var → Term)
            ------------
          → (Var → Term)
        
   where  `Var` is define to just be `ℕ`.
   You will need to prove a type preservation lemma for
   each of `ext`, `rename`, `exts`, and `subst`,
   whose declaration will be analogous to the type 
   declaration of those functions in the DeBruijn chapter.
   For example,
   
        exts-pres : ∀ {Γ Δ σ}
          → (∀ {A x}  →      Γ ∋ x ⦂ A →            Δ ⊢ σ x ⦂ A)
            ----------------------------------------------------
          → (∀ {A B x} → Γ , B ∋ x ⦂ A → Δ , B ⊢ (exts σ) x ⦂ A)

   Prove the analogous theorem to `preserve`
   in [Properties](https://plfa.github.io/Properties/).
   You may omit natural numbers (0, suc, and case) and μ
   from your formalization of the STLC, instead
   including a unit type.

7. March 6:

    * Extend the termination proof for STLC
      to include products and sums, as they appear
      in Chapter [More](https://plfa.github.io/More/)
      (you may use either approach to products).
      Also, try to add μ and report on where the proof breaks.

    * Extend the bidirectional type rules, `synthesize`, and `inherit`
      to handle products and sums.

8. March 13: do the `variants` exercise in
   [Subtyping and Records](./lecture-notes-Subtyping.lagda.md).

9. March 30: do the `products` exercise in
   [Bisimulation](https://plfa.github.io/Bisimulation/)
   and the `big-alt-implies-multi` exercise
   in [BigStep](https://plfa.github.io/BigStep/).

10. April 3: Project Description Due.
    Write 1 page describing your project.  The description should
	include a list of the formal artifacts (definitions, theorems)
	that you plan to turn in.

11. April 10: do the `denot-plusᶜ` and `denot-church`
    in [Denotational](https://plfa.github.io/Denotational/).

## Project, due May 1

Choose a language feature that is not spelled out in PLFA to formalize
and prove type safe in Agda. (If you have a different kind of
project in mind, I'm happy to consider alternatives, so long as it
includes proving some non-trivial property of a programming language.)
Your formalization should include both a static semantics (aka. type
system), a dynamic semantics, and a proof of type safety. For the
dynamic semantics you must use a different style than the approach
used in PLFA, that is, do not use a reduction semantics. Examples of
other styles you can use are

* small-step reduction with evaluation contexts
* big-step semantics
* definitional interpreter (recursive function with gas)
* abstract machine (e.g. CEK)
* virtual machine (CAM)
* denotational semantics
* axiomatic semantics (e.g. Hoare Logic)

Resources:

* The book _Types and Programming Languages_ (TAPL) by Benjamin Pierce
  has many examples of language features that would be an appropriate
  choice for your project.
  
* The book _Semantics Engineering with PLT Redex_ by Felleisen,
  Findler, and Flatt is a good resource for evaluation contexts,
  abstract machines, and
  continuations. The earlier book draft
  [_Programming Languages and Lambda Calculi_](http://www.cs.utah.edu/plt/publications/pllc.pdf) (PLLC) by Felleisen and Flatt covers similar material.

* _The Formal Semantics of Programming Languages_ (FSPL) by Winskel
  includes lots of semantics styles (small-step, big-step, axiomatic,
  denotational), eager and lazy evaluation, nondeterminism and
  parallelism.

* _Practical Foundations for Programming Languages_ (PFPL) by Robert
  Harper includes material on logical relations.

* [Type Safety in Three Easy Lemmas](http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html) is a blog post of mine
  that shows how to prove type safety using a definitional
  interpreter with gas.

* [Type Safety in Five Easy Lemmas](http://siek.blogspot.com/2012/08/type-safety-in-five-easy-lemmas.html) is a blog post of mine
  that shows how to prove type safety using an abstract machine.


Ideas for project language features:

* Lazy evaluation (aka. call-by-need)
  (e.g., see my paper _Improving the lazy Krivine machine_)
* Let polymorphism (extend [TypeInference](./TypeInference.lagda.md))
* Continuations (PLLC)
* Featherweight Java (TAPL Chapter 19)
* Exceptions (TAPL Chapter 14)
* While loops and variable assignment (the IMP language in FSPL)
* Recursive Types (TAPL Chapter 20)
* Nondeterminism
* Parallelism
* Reasoning about program equality using logical relations (PFPL)
* Bounded Quantification (TAPL Chapter 26)
* Higher-Order Polymorphism (TAPL Chapter 30)


## Schedule

| Month    | Day | Topic    |
| -------- | --- | -------- |
| January  | 13  | [Naturals](https://plfa.github.io/Naturals/) & [Induction](https://plfa.github.io/Induction/) |
|          | 15  | [Relations](https://plfa.github.io/Relations/) |
|          | 16  | [Equality](https://plfa.github.io/Equality/) & [Isomorphism](https://plfa.github.io/Isomorphism/) (unusual day, regular time) |
| 		   | 27  | [Connectives](https://plfa.github.io/Connectives/) & [Negation](https://plfa.github.io/Negation/) |
|		   | 28  | [Quantifiers](https://plfa.github.io/Quantifiers/) & [Decidable](https://plfa.github.io/Decidable/) (unusual day, regular time) |
|		   | 29  | [Lists](https://plfa.github.io/Lists/) and higher-order functions |
| February |  3  | [Lambda](https://plfa.github.io/Lambda/) the Simply Typed Lambda Calculus |
|          |  5  | [Properties](https://plfa.github.io/Properties/) such as type safety |
|          | 10  | [DeBruijn](https://plfa.github.io/DeBruijn/) representation of variables |
|          | 12  | [More](https://plfa.github.io/More/) constructs: numbers, let, products (pairs), sums, unit, empty, lists |
|          | 17  | [STLC Termination via Logical Relations](./STLC-Termination.lagda.md) |
|          | 19  | [Inference](https://plfa.github.io/Inference/) bidirectional type inference |
|          | 24  | [Subtyping and Records](./lecture-notes-Subtyping.lagda.md) |
|          | 26  | [Bisimulation](https://plfa.github.io/Bisimulation/) |
| March    |  2  | [Untyped](https://plfa.github.io/Untyped/) Lambda Calculus |
|          |  4  | [Confluence](https://plfa.github.io/Confluence/) of the Lambda Calculus |
|          |  9  | [BigStep](https://plfa.github.io/BigStep/) Call-by-name Evaluation of the Lambda Calculus |
|          | 11  | [Denotational](https://plfa.github.io/Denotational/) semantics of the Lambda Calculus |
|          | 16  | Spring Break, no class |
|          | 18  | Spring Break, no class |
|          | 23  | More Spring Break, no class |
|          | 25  | More Spring Break, no class |
|          | 30  | [Denotational](https://plfa.github.io/Denotational/) continued, [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+March+30%2C+Denotational+Semantics/1_da4xq013) |
| April    |  1  | [Compositional](https://plfa.github.io/Compositional/) (forgot to push record!) |
|          |  6  | [Soundness](https://plfa.github.io/Soundness/), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+6%2C+Soundness+of+reduction+with+respect+to+denotational+semantics/1_o5gwttt7) |
|          |  8  | [Adequacy](https://plfa.github.io/Adequacy/) |
|          | 13  | [ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/) |
|          | 15  | [Unification](./Unification.lagda.md) |
|          | 20  | [TypeInference](./TypeInference.lagda.md) |
|          | 22  | Gradual Typing |
|          | 27  | Universal and Existential Types (Parametric Polymorphism) |
|          | 29  | References and the Heap |


## Resources

* Join the course mailing list on [Piazza](https://piazza.com/iu/spring2020/b522/home).

* Join the PLFA mailing list [plfa-interest](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest)
  and ask questions!

* [Crash Course on Notation in Programming Language Theory](http://siek.blogspot.com/2012/07/crash-course-on-notation-in-programming.html)

