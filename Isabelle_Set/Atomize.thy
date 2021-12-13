theory Atomize
  imports HOL.HOL "HOL-Eisbach.Eisbach"
begin

method atomize' =
  (unfold atomize_imp atomize_all atomize_eq)

method atomize_rev' =
  (unfold atomize_all[symmetric] atomize_imp[symmetric])

end