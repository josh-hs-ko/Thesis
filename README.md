# Analysis and synthesis of inductive families

This implements, in Agda, a framework of composable datatype refinements and relational algebraic ornamentation based on [McBride's work on ornaments](http://personal.cis.strath.ac.uk/~conor/pub/OAAO/LitOrn.pdf), and forms the basis of [the author's DPhil dissertation](https://github.com/josh-hs-ko/dissertation/blob/master/dissertation.pdf).

All files typecheck with the development version of Agda and the Standard Library (12 Dec 2014). Note that some files can take a very long time to typecheck.

See [the author's (old) homepage](http://www.cs.ox.ac.uk/people/hsiang-shang.ko/) for more information, including published papers.

## Module descriptions

#### Prelude.Category
Basic definitions of categories, functors, and natural transformations.
The collection of objects in a category is an Agda set, i.e., equality on objects is definitional equality,
whereas the collection of arrows is a setoid, i.e., a set equipped with an equivalence relation.
All operations on morphisms must respect the equivalence relation, including the morphism maps of functors.

#### Prelude.Category.Isomorphism
Categorical definition of isomorphisms, parametrised by an underlying category.
Isomorphic objects form a setoid and are amenable to equational reasoning.
It is proved here that terminal objects are isomorphic.
A predicate saying that a morphism is part of an isomorphism is also provided.

#### Prelude.Category.Isomorphism.Functor
Isomorphisms are preserved by functors.

#### Prelude.Category.NaturalTransformation
If each of the components of a natural transformation from `F` to `G` is part of an isomorphism, then `F` and `G` are naturally isomorphic.

#### Prelude.Category.Pullback
A pullback is defined to be a terminal object in the category of spans over a slice category.
Any two pullback objects are isomorphic.
Pullback preservation and reflection of functors are also defined.
A functor preserves pullback if it preserves a particular pullback.

#### Prelude.Category.Pullback.Midpoint
*The Midpoint Lemma:*
Let X, Y, Z be objects of a category C, and X × Y, X × Z, Y × Z, and (X × Y) × Z be products.
Then (X × Y) × Z is a pullback of the projections X × Z → Z and Y × Z → Z.

#### Prelude.Category.Slice
Definition of slice categories.

#### Prelude.Category.Slice.Functor
The forgetful functor from a slice category to its underlying category is pullback-preserving.

#### Prelude.Category.Span
Definition of span categories. Products and product preservation are also defined here.

#### Prelude.Category.WCat
A "weak" category of categories, in which morphisms (i.e., functors) are considered equal if they are naturally isomorphic.
An equivalence of categories is an isomorphism in this weak category of categories.

#### Prelude.Equality
This module defines the J rule for propositional equality, a generalised K rule for heterogeneous equality,
and a predicate specifying when an element of a setoid is the unique inhabitant of the setoid.

#### Prelude.Function
This module defines pointwise equality of functions, which forms a setoid, and pointwise heterogeneous equality of functions.
The category `Fun` of sets and functions is also defined here.
The unit type is proved to be terminal in `Fun`.

#### Prelude.Function.Fam
The category `Fam` of families of sets.
An isomorphism between two families of sets in `Fam` can be broken into isomorphisms between corresponding sets in the two families.
There is a canonical way of forming pullbacks in `Fam`,
namely taking the set-theoretical pullbacks of the index set and corresponding sets in the families.
The forgetful functor from `Fam` to `Fun` preserves this pullback, and is hence pullback-preserving.

#### Prelude.Function.Isomorphism
Various ways to construct isomorphisms in `Fun`.

#### Prelude.InverseImage
Definition of inverse images of a function, and definitions of set-theoretic pullbacks in terms of inverse images and quotients.

#### Prelude.Preorder
Converse of preorders, setoids derived from preorders, implication as a preorder, and indirect reasoning combinators.

#### Prelude.Product
Auxiliary operations for dependent pairs.

#### Refinement
Definition of refinements, swaps, and upgrades.

#### Refinement.Category
Families of refinements form a category `FRef`.

#### Description
Definition of datatype descriptions, i.e., a universe for functors on families of sets.
Datatype-generic fold and induction are defined on top of descriptions.

#### Description.Horizontal
Horizontal data, which can be separated into "shape" and "core" (cf. containers), and shape equivalence.

#### Ornament
Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

#### Ornament.Algebraic
Definition of (relational) algebraic ornaments and classifying algebras.
The optimised predicate of an algebraic ornament can be swapped for a relational fold with the algebra of the ornament.

#### Ornament.Algebraic.EquivalenceTheorem
Let `D : Desc I` be a description.
The category of relational `D`-algebras and the slice category of ornaments over `D` are equivalent.

#### Ornament.Category
The category of descriptions and ornaments.
The functor `Ind` (for "induction") takes the least fixed points of descriptions and
extends ornaments to forgetful maps on those least fixed points.

#### Ornament.Equivalence
An extensional equivalence relation on ornaments, which extends to extensional equivalence on ornamental forgetful maps.

#### Ornament.Horizontal
Horizontal transformations, i.e., shape-altering morphisms between horizontal data (cf. container morphisms).
Ornaments can be derived from horizontal transformations.

#### Ornament.Horizontal.Category
The category of descriptions and families of horizontal transformations, and
the equivalence between this category and the category `Ōrn` of descriptions and ornaments.

#### Ornament.Horizontal.Equivalence
Ornamental equivalences about horizontal ornaments.

#### Ornament.Horizontal.Pullback
`Shape : Functor ḞḢTrans Fam` and `Erase : Functor Ōrn ḞḢTrans` reflect pullbacks.
This file can take a long time to typecheck.

#### Ornament.ParallelComposition
Parallel composition of ornaments.

#### Ornament.ParallelComposition.Pullback
Parallel composition of ornaments gives rise to a pullback square in `Ōrn`, which is also a pullback when mapped to `Fam` by the functor `Ind`.
This file can take a long time to typecheck.

#### Ornament.ParallelComposition.Swap
The optimised predicate for the parallel composition of two ornaments can be swapped
for the pointwise conjunction of the optimised predicates for the two component ornaments.
This file can take a long time to typecheck and may require a larger stack size.

#### Ornament.RefinementSemantics
Definition of an optimised predicate for an ornament as the parallel composition of the ornament and the singleton ornament.
This construction gives a functor from `Orn` to `FRef` which produces more representation-efficient promotion predicates.

#### Ornament.SequentialComposition
Sequential composition of ornaments.

#### Relation
Basic definitions of subsets and relations, combinators for specifying nondeterministic computation,
relational inclusion wrapped up as preorder and setoid, combinators for reasoning with relations,
componentwise relations between families of sets, and definition and properties of relators.

#### Relation.AlgCategory
Let `D : Desc I` be a description.
The category `RAlg D` is the wide subcategory of the category of relational `D`-algebras where the morphisms are restricted to be functions and are proof-relevant.
This module also defines the banana-split algebras and proves that they are products in `RAlg D`.

#### Relation.CompChain
Combinators that help avoiding explicit applications of monotonicity and associativity of relational composition
and preservation of composition by relators and converse.

#### Relation.Division
Definition of right-division of componentwise relations.

#### Relation.Fold
Definition and properties of relational fold.

#### Relation.GreedyTheorem
A variant of the Greedy Theorem and its embedding into inductive families.

#### Relation.Hylomorphism
Definition of hylomorphisms and the Hylomorphism Theorem.

#### Relation.Join
Definition and properties of binary join and its componentwise version, and definition of summing join (kept for future work).

#### Relation.Meet
Definition of meet and its componentwise version.

#### Relation.Minimum
Definition of the relation that takes a minimum from a set generated by a relation, and its componentwise version.

#### Examples.BinomialHeap
Okasaki's idea of numerical representations are nicely captured by the coherence property of upgrades;
insertion into binomial heaps is used as an example.

#### Examples.Bool

#### Examples.Fin
Finite numbers, i.e., natural numbers bounded above by a given natural number.

#### Examples.FoldFusion
Fold fusion theorems for algebraic ornamentation.

#### Examples.Insertion
The `insert` function used in insertion sort upgraded to work with vectors, ordered lists, and ordered vectors.

#### Examples.LeftistHeap
The ordering property and balancing properties of leftist heaps are treated separately when needed.

#### Examples.List
Cons-lists as an ornamentation of natural numbers.

#### Examples.List.Ordered
Ordered lists indexed with a lower bound as an ornamentation of lists.

#### Examples.List.Vec
Vectors, i.e., length-indexed lists, defined as the optimised predicate for the ornament from natural numbers to lists.

#### Examples.Metamorphism
Implementing the streaming theorem for list metamorphisms by algebraic ornamentation.

#### Examples.MinCoinChange
Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.

#### Examples.Nat
Peano-style natural numbers.

#### Examples.Nat.TotalOrdering
Decidable total ordering on natural numbers and minimum.

#### Examples.STLC
Simply typed λ-calculus à la Curry and à la Church, related by ornamentation.
