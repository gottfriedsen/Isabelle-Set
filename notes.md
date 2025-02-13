### Existing Examples

* naturals -> integers
* lists (broken)
* matrices (no transfer needed)

### New Examples

* integers -> polynomials over integers (actually formal power series)
* integers -> rationals -> polynomials over rationals (actually formal power series)
* option a -> list a
* option a -> sum unit a
* quotient ring over integers
  * If Z/n is implemented as a quotient of the set of integers, the unique homomorphism Z -> Z/n can not be used as an embedding for a set extension since it is not injective.
  * If Z/n is implemented as the subset {0, ..., n-1} of the set of integers, there is no need for a set extension but it is not straight forward to reuse theorems about one type for the other, since the definitions of the ring operators for both types do not coincide.

### Interesting Cases for Transfer

* Use of bounded universal quantification over entire abstract type:

  * in `Transfer_Test.thy`:

  $$
  \forall i, j, k \in \mathbb{Z}\ldotp i \cdot (j - k) = (k \cdot i) - (j \cdot i)
  $$

  * in `Polynomial.thy`:
    $$
    \forall p \in \mathbb{Z}[x]. 0 + x = x
    $$

* Use of type constraint as premise of implication inside object-logic unbounded universal quantification:

  * in `Rational.thy`:

  $$
  \forall x\ldotp x : \mathbb{Q} \longrightarrow 1 \cdot x = x
  $$

* Use of type constraint as premise of implication inside meta-logic universal quantification and side-by-side comparison with bounded object-logic quantifier:

  * in`Rational.thy`:

  $$
  \bigwedge x\; y\ldotp x : \mathbb{Q} \longrightarrow y : \mathbb{Q} \longrightarrow y \neq 0 \longrightarrow (x \cdot y) / y = y \\
  \forall x \in \mathbb{Q}\ldotp \forall y \in \mathbb{Q}\ldotp y \neq 0 \longrightarrow (x \cdot y) / y = y
  $$

* Transfer of implication with equality/inequality constraint:

  * in `Rational.thy `: see example above
  * in `Poly_Rat.thy`:

  $$
  \forall p, q \in \mathbb{Q}[x]\ldotp p = q \longrightarrow p + (-q) = 0
  $$

* Recursive polymorphic data type:

  * in `List_Set.thy`:

$$
\forall x, xs\ldotp \mathsf{Nil}\; \alpha \neq \mathsf{Cons}\; \alpha\; x\; xs
$$

* Dependent transfer rules:

  * in `Tranfer_Test.thy`:

    * The naive transfer relation below is not provable since `int_div i j` is only defined if `i` is a multiple of `j`:
      $$
      (\mathsf{Int\_Rel} \Longrightarrow \mathsf{Int\_Rel} \Longrightarrow \mathsf{Int\_Rel})\; \mathsf{int\_rep\_div}\; \mathsf{int\_div}
      $$

### Set Specific Problems for Transfer

* translation between set-membership and types
  * Problem: The premises of a theorem to be transfered often contain type constraints of the form `x : A`. In most other settings, type constraints are handled implicitly and are transfered to new type constraints. Here however, we want to transfer statements about type inhabitation to statements about set membership.
  * Solution: We define a further transfer relation which relates types and sets (if the type is not parameterized, only a single type is related to a single set). With this relation at hand, we can prove two transfer rule: One rule to transfer a type to a set and one to transfer the has-type operator `:`  to the set membership operator `∈`. (see `Rational.thy`)
* translation of polymorphic constants
  * Problem: When the sets involved in a set-extension are parameterized by some set, all definitions made by the set-extension are parameterized as well (see example from `List_Set.thy` in the section above). Since constants in the representation-level are not parametrized, this leads to differences in the term structures between terms related by the transfer relation.
  * Solution: This problem can be solved by using the `fixing` option of transfer. (e.g. `apply (transfer fixing: A)`)

### Problems for Lifting

* Automatically coming up and proving dependent type theorems from first-order transfer rules is not straight forward, because the structure of both theorems doesn't match.

  * Example of first-order transfer rule:
    $$
    \mathsf{Int\_Rel}\ i\ i' \Longrightarrow \mathsf{Int\_Rel}\ j\ j' \Longrightarrow \mathsf{divides}\ i'\ j' \Longrightarrow \mathsf{Int\_Rel}\ (\mathsf{int\_rep\_div\ i\ j})\ (\mathsf{int\_div\ i'\ j'})
    $$

  * Example of dependent type theorem
    $$
    \mathsf{int\_div} : (i : \mathsf{Int}) \Rightarrow (\mathsf{divides}\ i \boldsymbol{\cdot} \mathsf{Int}) \Rightarrow \mathsf{Int}
    $$

  * In the transfer rule, the divisibility constraint is given as a separate premise while in the type theorem, it is part of second parameter type

  * Hence, it seems worth investigating, whether an alternative approach to first-order transfer rules should be used. Reusing the notation for types results in
    $$
    \mathsf{Int\_Rel}\ i\ i' \rightarrow (\mathsf{const} \circ \mathsf{divides}\ i \boldsymbol{\cdot} \mathsf{Int\_Rel}) \rightarrow \mathsf{Int\_Rel}
    $$

  * A structurally similar syntax which is closer to the notation of first-order rules is
    $$
    \mathsf{Int\_Rel}\ i\ i' \rightarrow (\mathsf{Int\_Rel}\ j\ j' \mid \mathsf{divides}\ i\ j)\rightarrow \mathsf{Int\_Rel}
    $$

