theory Prelude_proof imports Prelude begin

(* FIXME move to lib_proof *)
lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

end