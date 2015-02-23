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

lemma t1: "blocked5 (init_state s ps) i = {}"
  apply(unfold init_state_def)
  apply(simp add: impl_mbk_def)
  apply(simp add: rev_apply_def)
  apply(case_tac " ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0)")
  apply(simp)
  apply(simp)
  done
  
lemma t2: "complete5 (init_state s ps) i = {}"
  apply(unfold init_state_def)
  apply(simp add: impl_mck_def)
  apply(simp add: rev_apply_def)
  apply(case_tac " ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0)")
  apply(simp)
  apply(simp)
  done  
  
lemma t3: "todo_done5 (init_state s ps) = NTITM ` set (ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0))  "  
  apply(unfold init_state_def)
  apply(simp add: impl_mck_def)
  apply(simp add: rev_apply_def)
  apply(case_tac " ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0)")
  apply(simp)
  apply(simp)
  done  

  
definition wf_ct_nt_items_for_nt :: "(nt => 'string substring => nt_item list) \<Rightarrow> bool"
where "wf_ct_nt_items_for_nt f \<equiv> \<forall>n ntitem sub. \<exists>s i j a i' j'. ntitem \<in> set (f n sub) \<longrightarrow> sub = (s, i, j) \<and> 
(ntitem = (n, [], a, i', j')) \<and> i' \<le> i \<and> j' \<le> j \<and> i' \<le> j'"  

lemma sound_init: "wf_ct_nt_items_for_nt (ct_nt_items_for_nt ps) \<Longrightarrow> loop2_inv s ps (init_state s ps)"
  apply(unfold loop2_inv_def)
  apply(simp add: rev_apply_def t1 t2 t3)
  apply(induct "ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0)")
  apply(clarsimp)
  apply(unfold derivable_items_def)
  apply(clarsimp)
  apply(unfold derivable_def)
  apply(simp)
  apply(unfold init_state_def)
  apply(simp add: rev_apply_def)
  apply(fold init_state_def)
  apply(clarsimp)
  apply(unfold wf_ct_nt_items_for_nt_def)
  apply(auto)
  apply(unfold init_state_def)
  apply(simp add: rev_apply_def Let_def)

lemma sound: "loop2_inv s ps s0 ==> loop2 (ctxt::'string ty_impl_ctxt) s0 = s1 ==> loop2_inv s ps s1"
  oops

lemma complete: "True (* FIXME *)"

end
