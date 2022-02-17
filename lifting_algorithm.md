**input:**

* `lift_thms`: table of lifting theorems (`{type: Lifting Eq_rep Eq_abs T rep abs} `)
* `rel_lift_thms`: table of relator lifting theorems (`{type: [Lifting Eq_rep_1 Eq_abs_1 T_1 rep_1 abs_1; ...;  Eq_rep_n Eq_abs_n T_n rep_n abs_n] ==> Lifting (...) (...) (...) (...) (...)} `)

* `rep_term`: term on representation level
* `rep_type_thm`: type theorem about `rep_term` (`rep_term : rep_type`)
* `rsp_thm`: respectfulness theorem about `rep_term` (`Eq_rep rep_term rep_term`)
* `abs_type`: type of term on abstract level

**algorithm:**

```
lifting_step rep_type abs_type =
	(rep_tvars, abs_type_vars) = case (rep_type, abs_type) of
		| (σs κ, σs' κ) => (σs, σs)
		| (α, β) => ([α], [β])
	args = map prove_lifting_thm (zip rep_tvars abs_type_vars)
	if forall is_id_lift args
		then get_lift_thm abs_type
		else
            let lift_thm = get_lift_thm abs_type
            let rel_lift_thm = (get_rel_lift_thm rep_type)[OF args]
            comp_Lifting_thm[OF rel_lift_thm lift_thm]

prove_lifting_thm rep_type abs_type =
    case (rep_type, abs_type) of
        | (σs κ, σs' κ) =>
            let args = map prove_lifting_thm (zip σs σs')
            if forall is_id_lift args
            	then id_Lifting_thm
            	else (get_rel_lift_thm κ)[OF args]
        | (σs κ, σs' κ') where κ ≠ κ' =>
        	lifting_step rep_type abs_type
        | (α, σs' κ') => 
        	let lift_thm = get_lift_thm κ'
        	let rep_type = get_rep_ty_of_lift_thm lift_thm
        	lifting_step rep_type abs_type
        | (α, β) => id_Lifting_thm
```



