# Composable structures for dependently typed programming (TBD)

This implements, in Agda, a framework of composable datatype refinements based on [McBride's datatype ornamentation](http://personal.cis.strath.ac.uk/~conor/pub/OAAO/LitOrn.pdf).

All files typecheck with Agda 2.3.3, but note that some files can take a very long time to typecheck. (The module Ornament.SequentialComposition would bump into [an error of Agda 2.3.2](http://code.google.com/p/agda/issues/detail?id=754).)

See [the author's homepage](http://www.cs.ox.ac.uk/people/hsiang-shang.ko/) for more information, including published papers.

## Module descriptions

#### Prelude.Category
Basic definitions of categories and functors, including definitions of terminal object and functor composition.
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

#### Prelude.Category.Pullback
A pullback is defined to be a terminal object in the category of spans over a slice category.
Any two pullback objects are isomorphic.
Pullback preservation of functors is also defined.

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
Definition of inverse images of a function, and definition of set-theoretic pullbacks in terms of inverse images.

#### Prelude.Preorder
Converse of preorders, setoids derived from preorders, implication as a preorder, and indirect reasoning combinators.

#### Prelude.Product
Auxiliary operations for dependent pairs.

#### Refinement
Definition of refinements, swaps, and upgrades.

#### Refinement.Category
Families of refinements form a category `FRef`.

#### Refinement.Isomorphism
A sufficient condition for establishing an isomorphism between the two types related by a refinement.

#### Description
Definition of datatype descriptions, i.e., a universe for functors on families of sets.
Datatype-generic fold and induction are defined on top of descriptions.

#### Description.HorizontalEquivalence
An inductively defined equivalence between description-based data that poses little restriction on their actual types.

#### Ornament
Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

#### Ornament.Algebraic
Definition of (relational) algebraic ornaments and classifying algebras.
The optimised predicate of an algebraic ornament can be swapped for a relational fold with the algebra of the ornament.

#### Ornament.Algebraic.FundamentalTheorems
Two fundamental theorems about algebraic ornaments and classifying algebras.
*The AOCA Theorem:* Algebraic ornamentation by a classifying algebra produces an isomorphic datatype.
*The CAAO Theorem:* A classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament.

#### Ornament.Algebraic.Fusion
Fold fusion theorems for algebraic ornamentation.

#### Ornament.Category
The category of descriptions and ornaments.
The functor `Ind` (for "induction") takes the least fixed points of descriptions and
extends ornaments to forgetful maps on those least fixed points.

#### Ornament.Equivalence
An extensional equivalence relation on ornaments, which extends to extensional equivalence on ornamental forgetful maps.

#### Ornament.Isomorphism
A sufficient condition for establishing an isomorphism between the two types related by a ornament.

#### Ornament.ParallelComposition
Parallel composition of ornaments.

#### Ornament.ParallelComposition.Pullback
Parallel composition of ornaments, when mapped to `Fam` by the functor `Ind`, forms a pullback.
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

#### Examples.List
Cons-lists as an ornamentation of natural numbers.

#### Examples.List.Ordered
Ordered lists indexed by a lower bound as an ornamentation of lists.

#### Examples.MinCoinChange
Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.

#### Examples.Nat
Peano-style natural numbers.

#### Examples.Nat.TotalOrdering
Decidable total ordering on natural numbers and minimum.
