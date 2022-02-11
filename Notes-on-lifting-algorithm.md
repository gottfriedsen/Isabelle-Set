## Cases

1. Normal lifting
   * Given
     * concrete term
     * type theorem of concrete term
     * type of abstract term
   * Synthesized
     * transfer relation (non-dependent)
     * abstract term
   * Proven
     * transfer rule
     * type theorem of abstract term
2. Lifting with custom transfer rule
   * Given:
     * all from above
     * transfer relation
   * Synthesized
     * abstract term
   * Proven
     * transfer rule
     * type theorem of abstract term
3. Proving of further transfer rule
   * Given
     * all from above
     * abstract term
   * Synthesized
     * nothing
   * Proven
     * transfer rule

## Two Approaches

### 1. Approach

First Synthesize transfer relation and abstract term. Then prove transfer rule.

Pros

* More modular
* Different cases only effect first step. Second step works uniformly.

### 2. Approach

Synthesize transfer relation and abstract term as by product of proof of transfer rule.

Pros:

* No complicated synthesize algorithm and notion of polarity required
* Some further advantages according to Ondrej
* Algorithmically similar to transfer tool (?)
* Should be easy to parameterize to work with different cases


$$
\lang R, Abs, Rep, T \rang \longrightarrow R = T \circ T^{-1}
$$

$$
T_1 \circ T_2 \circ (T_1  \circ T_2)^{-1} \\
= T_1 \circ T_2  \circ T_2^{-1} \circ T_1^{-1} \\
= T_1 \circ R_1 \circ T_1^{-1}
$$

$$
T_1 \circ T_2 \circ (T_1 \circ T_2)^{-1} \\
= T_1 \circ T_2 \circ T_2^{-1} \circ T_1^{-1} \\
= T_1 \circ T_1^{-1} \circ T_1 \circ T_2 \circ T_2^{-1} \circ T_1^{-1} \\
\neq T_1 \circ T_1^{-1} \circ T_2 \circ T_2^{-1} \circ T_1 \circ T_1^{-1} \\
= T_1 \circ T_1^{-1} \circ T_2 \circ T_2^{-1} \circ (T_1 \circ T_1^{-1})^{-1} \\
= R_1 \circ R_2 \circ R_1^{-1}
$$

$$
Relat(\tau_1, \tau_2) \\
= Trans(\tau_1, \overline{\sigma}\ \kappa_1) \circ relat(\overline{\sigma}\ \kappa_1, \tau_2) \circ Trans(\tau_1, \overline{\sigma}\ \kappa_1)^{-1} \\
= (rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n)) \circ R_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2} \circ (rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n))^{-1}
$$

$$
Relat(\tau_1, \tau_2) \\
= Trans(\tau_1, \overline{\sigma}\ \kappa_1) \circ relat(\overline{\sigma}\ \kappa_1, \tau_2) \circ Trans(\tau_1, \overline{\sigma}\ \kappa_1)^{-1} \\
= (rel^{\kappa_1}\ Relat(\sigma_1, \rho_1) \ldots Relat(\sigma_n, \rho_n)) \circ R_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2} \circ (rel^{\kappa_1}\ Relat(\sigma_1, \rho_1) \ldots Relat(\sigma_n, \rho_n))^{-1}
$$

$$
rel^{\kappa_1}\ Relat(\sigma_1, \rho_1) \ldots Relat(\sigma_n, \rho_n) \\
= rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n) \circ (rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n))^{-1}
$$

$$
R_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2} \\
= T_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2}  \circ (T_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2})^{-1}
$$

$$
R_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2} \circ rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n) \\
\neq rel^{\kappa_1}\ Trans(\sigma_1, \rho_1) \ldots Trans(\sigma_n, \rho_n) \circ R_{\overline{\sigma}\ \kappa_1 \rightarrow \tau_2 \rightarrow bool}^{\kappa_1, \kappa_2}
$$



## Steps

### Lifting

### Proof of Transfer Rule

**Goal: **
$$
(T_1 \Rrightarrow T_2 \Rrightarrow \ldots  \Rrightarrow T_n)\ t\ f
$$
**Proof**:

1. rewrite function relator

   * fix

   $$
   x_i\ \textsf{for}\ i = 1 \ldots n-1
   $$

   * assume
     $$
     T_i\ x_i\ y_i
     $$

   * goal

   $$
   T_n\ (t\ x_1 \ldots x_{n-1})\ (f\ y_1 \ldots y_{n-1})
   $$

2. substitute definition of abstract value
   $$
   T_n\ (t\ x_1 \ldots x_{n-1})\ (Abs\ (t\ (Rep_1\ y_1) \ldots (Rep_{n-1}\ y_{n-1})))
   $$

3. translate relatedness by transfer relation to equivalence 
   $$
   t\ x_1 \ldots x_{n-1} \equiv_n t\ (Rep_1\ y_1) \ldots (Rep_{n-1}\ y_{n-1})
   $$

4. apply respectfulness

   1. prove
      $$
      \forall x_1, x_1' \ldots x_{n-1}, x_{n-1}'\ldotp x_1 \equiv_1 x_1' \land \ldots \land x_{n-1} \equiv_{n-1} x_{n-1}' \longrightarrow t\ x_1 \ldots x_{n-1} \equiv_n t\ x_1' \ldots x_{n-1}'
      $$

   2. goal
      $$
      x_1 \equiv_1 (Rep_1\ y_1) \land \ldots \land x_{n-1} \equiv_{n-1} (Rep_{n-1}\ y_{n-1})
      $$

5. translate equivalence to relatedness by transfer relation
   $$
   T_1\ x_1\ y_1 \land \ldots \land T_{n-1}\ x_{n-1}\ y_{n-1}
   $$

6. apply assumptions

### Proof of type

