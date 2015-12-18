theory Tmp
imports Main
begin

locale l1 =
  fixes le1 :: "'a => 'a => bool"

locale l2 = 
  fixes le2 :: "'b => 'b => bool"

locale l3 = l1 + l2

print_locale l3  (* types are different, which is good! *)

locale l4 = 
  la: l1 la + lb: l2 lb for la and lb +
  assumes  "la = lb"

print_locale l4  (* types identified *)

end
