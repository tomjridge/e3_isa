theory E3_sound
imports E3 E3_spec 
begin

(* TODO: show by induction on m that all derivable items are included in Earley at some stage *) 

definition loop2_inv :: "'string => 'string ct_params => ty_impl_loop2 => bool" where
  "loop2_inv s ps s0 ==
    let nt0 = ps|>ct_nt0 in
    let nt_items_for_nt = ps|>ct_nt_items_for_nt in
    let f = % nt. % n. nt_items_for_nt nt (s,n,n) in
    let tm_items_for_tm = ps|>ct_p_of_tm in
    let g = % tm. %n. List.map (% x. (tm,n,x)) (tm_items_for_tm tm (s,n,n)) in
    let ps' = (| 
      sp_nt0=ps|>ct_nt0,
      sp_nt_items_for_nt=f,
      sp_tm_items_for_tm=g |)
    in
    (! x. x : (s0|>todo_done5) --> x : derivable_items ps') &

    (! x. x : (set (s0|>todo5)) --> x : derivable_items ps') &

    (! (sym::sym) j x. x : ((s0|>blocked5) (j,sym)) --> 
      (case x of (nt,aas,bs,i,j') => (bs ~= []) & (List.hd bs = sym) & (j'=j)) &
      (NTITM x) : derivable_items ps') &

    (! sym i x. x : ((s0|>complete5) (i,sym)) --> 
      (? j. x=(sym,i,j)) &
      (? x'. x' : derivable_items ps' & (sym_item_of_complete_item x' = Some x))) &

   (* we dont care about tmoracle and oracle at this point - the correctness of these should follow straightforwardly *)

    True" (* should be some relation from ty_impl loop2 to E3_spec derivable *)

lemma sound_init: "loop2_inv s ps (init_state s ps)"
  oops

lemma sound: "loop2_inv s ps s0 ==> loop2 (ctxt::'string ty_impl_ctxt) s0 = s1 ==> loop2_inv s ps s1"
  oops

lemma complete: "True (* FIXME *)"

end
