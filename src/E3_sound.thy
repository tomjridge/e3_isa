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
where "wf_ct_nt_items_for_nt f \<equiv> \<forall>n ntitem s i j as. ntitem \<in> set (f n (s, i, j)) \<longrightarrow>
(ntitem = (n, [], (NT n) # as, i, i))"  

definition wf_item_ops :: "'string ty_ops \<Rightarrow> bool"
where "wf_item_ops tyops \<equiv> \<forall>sym i j. sym_dot_i9 tyops (sym, i, j) = i \<and> sym_dot_j9 tyops (sym, i, j) = j \<and> sym6 tyops (sym, i, j) = sym"

lemma sound_init: "wf_ct_nt_items_for_nt (ct_nt_items_for_nt ps) \<Longrightarrow> loop2_inv s ps (init_state s ps)"
  apply(unfold loop2_inv_def)
  apply(induct "ct_nt_items_for_nt ps (ct_nt0 ps) (s, 0, 0)")
  apply(simp add: rev_apply_def t1 t2 t3)
  apply(unfold init_state_def derivable_items_def)
  apply(simp add: rev_apply_def t1 t2 t3 derivable_items_def)
  apply(simp add: rev_apply_def t1 t2 t3 wf_ct_nt_items_for_nt_def init_state_def Let_def image_def derivable_items_def impl_mbk_def impl_mck_def )
  apply(clarify)
by (metis (erased, hide_lams) not_Cons_self2)
  

lemma sound: "wf_ct_nt_items_for_nt (ct_nt_items_for_nt ps) \<Longrightarrow> wf_item_ops (item_ops5 ctxt) \<Longrightarrow> impl_maps (maps ctxt) \<Longrightarrow> loop2_inv s ps s0 ==> loop2 (ctxt::'string ty_impl_ctxt) s0 = s1 ==> loop2_inv s ps s1"
  apply(unfold loop2_def loop2_inv_def)
  apply(simp add: rev_apply_def Let_def)
  apply(unfold pop_todo_def)
  apply(case_tac "todo5 s0")
  apply(simp_all)
  apply(case_tac "dest_item (item_ops5 ctxt) a")
  apply(simp)
  apply(case_tac  "b2_nil (item_ops5 ctxt) prod")
  apply(simp)
  apply(case_tac "mk_sym_coord (item_ops5 ctxt) (nt2 (item_ops5 ctxt) prod, nt_dot_i9 (item_ops5 ctxt) prod, nt_dot_j9 (item_ops5 ctxt) prod)")
  apply(simp)
  apply(unfold wf_item_ops_def)
  apply(simp add: rev_apply_def Let_def)
  

  
  
  lemma complete: "True (* FIXME *)"

end
