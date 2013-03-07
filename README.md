# Composable structures for dependently typed programming (TBD)

This implements, in Agda, a framework of composable datatype refinements based on [McBride's datatype ornamentation](http://personal.cis.strath.ac.uk/~conor/pub/OAAO/LitOrn.pdf).

All files typecheck with Agda 2.3.3, but note that some files can take a very long time to typecheck. (The module Thesis.Ornament.SequentialComposition would bump into [an error of Agda 2.3.2](http://code.google.com/p/agda/issues/detail?id=754).)

See [the author's homepage](http://www.cs.ox.ac.uk/people/hsiang-shang.ko/) for more information, including published papers.

## Module descriptions

#### Thesis.Prelude.Category
Basic definitions of categories, functors, and natural transformations.
The collection of objects in a category is an Agda set, i.e., equality on objects is definitional equality,
whereas the collection of arrows is a setoid, i.e., a set equipped with an equivalence relation.
All operations on morphisms must respect the equivalence relation, including the morphism maps of functors.

#### Thesis.Prelude.Category.Isomorphism
Categorical definition of isomorphisms, parametrised by an underlying category.
Isomorphic objects form a setoid and are amenable to equational reasoning.
It is proved here that terminal objects are isomorphic.
A predicate saying that a morphism is part of an isomorphism is also provided.

#### Thesis.Prelude.Category.Isomorphism.Functor
Isomorphisms are preserved by functors.

#### Thesis.Prelude.Category.NaturalTransformation
If each of the components of a natural transformation from `F` to `G` is part of an isomorphism, then `F` and `G` are naturally isomorphic.

#### Thesis.Prelude.Category.Pullback
A pullback is defined to be a terminal object in the category of spans over a slice category.
Any two pullback objects are isomorphic.
Pullback preservation of functors is also defined.

#### Thesis.Prelude.Category.Pullback.Midpoint
*The Midpoint Lemma:*
Let X, Y, Z be objects of a category C, and X × Y, X × Z, Y × Z, and (X × Y) × Z be products.
Then (X × Y) × Z is a pullback of the projections X × Z → Z and Y × Z → Z.

#### Thesis.Prelude.Category.Slice
Definition of slice categories.

#### Thesis.Prelude.Category.Slice.Functor
The forgetful functor from a slice category to its underlying category is pullback-preserving.

#### Thesis.Prelude.Category.Span
Definition of span categories. Products and product preservation are also defined here.

#### Thesis.Prelude.Category.WCat
"Weak" category of categories, in which morphisms (i.e., functors) are considered equal if they are naturally isomorphic.
An equivalence of categories is an isomorphism in this weak category of categories.

#### Thesis.Prelude.Equality
This module defines the J rule for propositional equality, a generalised K rule for heterogeneous equality,
and a predicate specifying when an element of a setoid is the unique inhabitant of the setoid.

#### Thesis.Prelude.Function
This module defines pointwise equality of functions, which forms a setoid, and pointwise heterogeneous equality of functions.
The category `Fun` of sets and functions is also defined here.
The unit type is proved to be terminal in `Fun`.

#### Thesis.Prelude.Function.Fam
The category `Fam` of families of sets.
An isomorphism between two families of sets in `Fam` can be broken into isomorphisms between corresponding sets in the two families.
There is a canonical way of forming pullbacks in `Fam`,
namely taking the set-theoretical pullbacks of the index set and corresponding sets in the families.
The forgetful functor from `Fam` to `Fun` preserves this pullback, and is hence pullback-preserving.

#### Thesis.Prelude.Function.Isomorphism
Various ways to construct isomorphisms in `Fun`.

#### Thesis.Prelude.InverseImage
Definition of inverse images of a function, and definition of set-theoretic pullbacks in terms of inverse images.

#### Thesis.Prelude.Preorder
Converse of preorders, setoids derived from preorders, implication as a preorder, and indirect reasoning combinators.

#### Thesis.Prelude.Product
Auxiliary operations for dependent pairs.

#### Thesis.Refinement
Definition of refinements, swaps, and upgrades.

#### Thesis.Refinement.Category
Families of refinements form a category `FRef`.

#### Thesis.Refinement.Isomorphism
A sufficient condition for establishing an isomorphism between the two types related by a refinement.

#### Thesis.Description
Definition of datatype descriptions, i.e., a universe for functors on families of sets.
Datatype-generic fold and induction are defined on top of descriptions.

#### Thesis.Description.HorizontalEquivalence
An inductively defined equivalence between description-based data that poses little restriction on their actual types.

#### Thesis.Ornament
Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

#### Thesis.Ornament.Algebraic
Definition of (relational) algebraic ornaments and classifying algebras.
The optimised predicate of an algebraic ornament can be swapped for a relational fold with the algebra of the ornament.

#### Thesis.Ornament.Algebraic.FundamentalTheorems
Two fundamental theorems about algebraic ornaments and classifying algebras.
*The AOCA Theorem:* Algebraic ornamentation by a classifying algebra produces an isomorphic datatype.
*The CAAO Theorem:* A classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament.

#### Thesis.Ornament.Algebraic.Fusion
Fold fusion theorems for algebraic ornamentation.

#### Thesis.Ornament.Category
The category of descriptions and ornaments.
The functor `Ind` (for "induction") takes the least fixed points of descriptions and
extends ornaments to forgetful maps on those least fixed points.

#### Thesis.Ornament.Equivalence
An extensional equivalence relation on ornaments, which extends to extensional equivalence on ornamental forgetful maps.

#### Thesis.Ornament.Isomorphism
A sufficient condition for establishing an isomorphism between the two types related by a ornament.

#### Thesis.Ornament.ParallelComposition
Parallel composition of ornaments.

#### Thesis.Ornament.ParallelComposition.Pullback
Parallel composition of ornaments, when mapped to `Fam` by the functor `Ind`, forms a pullback.
This file can take a long time to typecheck.

#### Thesis.Ornament.ParallelComposition.Swap
The optimised predicate for the parallel composition of two ornaments can be swapped
for the pointwise conjunction of the optimised predicates for the two component ornaments.
This file can take a long time to typecheck and may require a larger stack size.

#### Thesis.Ornament.RefinementSemantics
Definition of an optimised predicate for an ornament as the parallel composition of the ornament and the singleton ornament.
This construction gives a functor from `Orn` to `FRef` which produces more representation-efficient promotion predicates.

#### Thesis.Ornament.SequentialComposition
Sequential composition of ornaments.

#### Thesis.Ornament.SequentialComposition.Swap
The optimised predicate for an ornament refined by sequential composition can be swapped for the original optimised predicate.
This file can take a long time to typecheck.

#### Thesis.Relation
Basic definitions of subsets and relations, combinators for specifying nondeterministic computation,
relational inclusion wrapped up as preorder and setoid, combinators for reasoning with relations,
componentwise relations between families of sets, and definition and properties of relators.

#### Thesis.Relation.CompChain
Combinators that help avoiding explicit applications of monotonicity and associativity of relational composition
and preservation of composition by relators and converse.

#### Thesis.Relation.Division
Definition of right-division of componentwise relations.

#### Thesis.Relation.Fold
Definition and properties of relational fold.

#### Thesis.Relation.GreedyTheorem
A variant of the Greedy Theorem and its embedding into inductive families.

#### Thesis.Relation.Hylomorphism
Definition of hylomorphisms and the Hylomorphism Theorem.

#### Thesis.Relation.Join
Definition and properties of binary join and its componentwise version, and definition of summing join (kept for future work).

#### Thesis.Relation.Meet
Definition of meet and its componentwise version.

#### Thesis.Relation.Minimum
Definition of the relation that takes a minimum from a set generated by a relation, and its componentwise version.

#### Thesis.Examples.Insertion
The `insert` function used in insertion sort upgraded to work with vectors, sorted lists, and sorted vectors.

#### Thesis.Examples.LeftistHeap
The ordering property and balancing properties of leftist heaps are treated separately when needed.

#### Thesis.Examples.List
Cons-lists as an ornamentation of natural numbers.

#### Thesis.Examples.List.Sorted
Sorted lists indexed by a lower bound as an ornamentation of lists.

#### Thesis.Examples.List.Vec
Vectors, i.e., length-indexed lists, defined as the optimised predicate for the ornament from natural numbers to lists.

#### Thesis.Examples.MinCoinChange
Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.

#### Thesis.Examples.Nat
Peano-style natural numbers.

#### Thesis.Examples.Nat.TotalOrdering
Decidable total ordering on natural numbers and minimum.
