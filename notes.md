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

### Set Specific Problems for Transfer

* translation between set-membership and types (solved, for example: see section above)
* translation of polymorphic constants (solved, for example: see section above)

