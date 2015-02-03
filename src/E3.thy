theory E3
imports (* E3_abstract_types *) E3_core_types 
begin

definition update_oracle :: 
"('string,'todo_done,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ty_ctxt
=> 'map_sym_sym_int_int
=> nt_item*nat
=> 'map_sym_sym_int_int" where
"update_oracle ctxt m itml == let (itm,l) = itml in 
  let ops = (item_ops5 ctxt) in
  let (syms1,sym2) = ((a2 ops) itm,(hd_b2 ops) itm) in
  let (i,k,j) = ((nt_dot_i9 ops) itm,(nt_dot_j9 ops) itm,l) in
  let key = (syms1,sym2,i,j) in
  let m = (mssii_add_cod (map_sym_sym_int_int (maps ctxt))) key k m in
  m"

definition update_tmoracle :: 
"('string,'todo_done,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ty_ctxt
=> 'map_tm_int
=> tm*nat*nat
=> 'map_tm_int" where
"update_tmoracle ctxt m tmij == let (tm,i,j) = tmij in (
  let key = (tm,i) in
  let m = (mti_add_cod (map_tm_int (maps ctxt))) key j m in
  m)"

definition todo_is_empty :: "
('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2
=> bool" where
"todo_is_empty s0 == ((todo5 s0)=[])"

definition add_todo :: "
('string,item,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ty_ctxt
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2
=> item
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2" where
"add_todo ctxt s0 itm = s0 
  (| todo5 := (itm#(todo5 s0)) |)
  (| todo_done5 := (  (std_add (set_todo_done (sets ctxt))) itm (todo_done5 s0)) |)"

definition pop_todo :: "
('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2
=> (('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2 * item)" where
"pop_todo s0 = (
  case (todo5 s0) of
    [] => (failwith ''pop_todo'')
  | x#xs => (s0 (| todo5 :=xs |),x))"


definition cut :: "
('string,item,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ty_ctxt
=> nt_item
=> sym_item
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2" where
"cut ctxt bitm citm s0 == (
  let ops = (item_ops5 ctxt) in
  let nitm = ((mk_item ops) (NTITM (((shift_a2_b2_c2 ops) bitm) |> (% x. (with_j9 ops) x ((sym_dot_j9 ops) citm))))) in
  let s0 = (
    (* if this could be made O(1) our implementation would be O(n^3) overall *)
    if (std_mem (set_todo_done (sets ctxt))) nitm (todo_done5 s0) then
      s0
    else
      add_todo ctxt s0 nitm)
  in
  s0)"

definition loop2 :: "
('string,item,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,
  ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2,
  ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2) ty_ctxt
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2
=> ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2" where
"loop2 ctxt s0 == (
  let ops = (item_ops5 ctxt) in
  let (s0,itm0) = pop_todo s0 in
  (* FIXME add a case construct rather than dests *)
  case (dest_item ops) itm0 of
    NTITM nitm => (
      let complete = (b2_nil ops) nitm in
      case complete of
        True => (
          let citm = (mk_sym_coord ops) ((nt2 ops) nitm, (nt_dot_i9 ops) nitm, (nt_dot_j9 ops) nitm) in
          let k = ((sym_dot_i9 ops) citm (* FIXME could be from dot_i9 nitm *),(ops |> sym6) citm) in
          (* FIXME check whether citm has already been done? *)
          (*let citms = ctxt.maps.map_complete_key.find2 k s0.complete5 in *)
          case False (* ctxt.sets.set_sym_item.std_mem citm citms *) of (* FIXME this optimization didn't buy much *)
            True => s0
          | False => (
              (* let bitms = ctxt.maps.map_blocked_key.find2 k s0.blocked5 in *)
              let f1 = % bitm s1. cut ctxt bitm citm s1 in
              (* O(n. ln n) *)
              (* let s0 = ctxt.sets.set_nt_item.fold f1 bitms s0 in *)
              let s0 = (ctxt |> maps |> map_blocked_key |> mbk_fold_cod) k f1 (s0 |> blocked5) s0 in
              let s0 = s0 (|
                        complete5:=((ctxt |> maps |> map_complete_key |> mck_add_cod) k citm (s0 |> complete5)) |)
              in
              (* we also update the oracle at this ponat  FIXME this appears very costly *)
              let f2 = % bitm s1. s1 (| oracle5:=(update_oracle ctxt (s1 |> oracle5) (bitm,(ops |> sym_dot_j9) citm)) |) in
              (* O(n. ln n) *)
              let s0 = (ctxt |> maps |> map_blocked_key |> mbk_fold_cod) k f2 (s0 |> blocked5) s0 in
              s0))
      | False => (
          let bitm = nitm in
          let sym = (ops |> hd_b2) bitm in
          let k = ((ops |> nt_dot_j9) bitm,sym) in
          (* let bitms = ctxt.maps.map_blocked_key.find2 k s0.blocked5 in *)
          let new_key = (ctxt |> maps |> map_blocked_key |> mbk_cod_empty) k (s0 |> blocked5) in
          let s0 = s0 (|
                    blocked5:=((ctxt |> maps |> map_blocked_key |> mbk_add_cod) k bitm (s0 |> blocked5)) |)                                        
          in    

          (* we should also process the blocked item against the relevant complete items *)
          (* let citms = ctxt.maps.map_complete_key.find2 k s0.complete5 in *)
          let f3 = % citm s1. cut ctxt bitm citm s1 in
          (* O(n. ln n) *)
          let s0 = (ctxt |> maps |> map_complete_key |> mck_fold_cod) k f3 (s0 |> complete5) s0 in
          (* we also update the oracle at this ponat; FIXME this appears very costly *)
          let f4 = % citm s1. s1 (| oracle5:=(update_oracle ctxt (s1 |> oracle5) (bitm,(ops |> sym_dot_j9) citm)) |) in
          (* O(n. ln n) *)
          let s0 = (ctxt |> maps |> map_complete_key |> mck_fold_cod) k f4 (s0 |> complete5) s0 in                                                 

          (* the invariant should be: if (j,nt) is nonempty then all                                                                               
             nt items for j are already in set_todo_done; if (j,tm) is                                                                             
             nonempty then all tmitems for j are already in                                                                                        
             set_todo_done *)
          if new_key then (
            case (ops |> sym_case) sym of
              NT nt => (
                let rs = (ops |> nt_items_for_nt) nt ((ctxt |> string5), (ops |> nt_dot_i9) nitm, (ops |> nt_dot_j9) nitm) in
                let f1 = (% s1 pnitm.
                  let nitm = (ops |> mk_item) (NTITM pnitm) in
                  if ((ctxt |> sets|>set_todo_done|>std_mem) nitm (s1|>todo_done5)) then s1 else
                    add_todo ctxt s1 nitm)
                in
                let s0 = List.foldl f1 s0 rs in
                s0)
            | TM tm => (                                                                                                                           
                let titm = (ops|>mk_item) (TMITM((ops|>mk_tm_coord) (tm,(ops|>nt_dot_j9) nitm))) in
                if ((ctxt|>sets|>set_todo_done|>std_mem) titm (s0|>todo_done5)) then s0 else
                  add_todo ctxt s0 titm))
          else
            s0 
       ))
  | TMITM titm => (
      let tm = (ops|>tm5) titm in
      let p = (ops|>p_of_tm) tm in
      let i = (ops|>tm_dot_i9) titm in
      let rs = p (ctxt|>string5,i,ctxt|>length5) in                                                                                                
      let sym = (ops|>sym_of_tm) tm in
      let k = (i,sym) in                                                                                                                           
      (* lots of new complete items, so complete5 must be updated, but we must also process blocked *)
      (* let bitms = ctxt.maps.map_blocked_key.find2 k s0.blocked5 in *)
      (* update complete set *)
      let f5 = % s1 j. (                                                                                                                           
        let citm = (ops|>mk_sym_coord) (sym,i,j) in
        s1 (| complete5:=((ctxt|>maps|>map_complete_key|>mck_add_cod) k citm (s1|>complete5)) |))
      in
      let s0 = List.foldl f5 s0 rs in
      let f8 = % s1 j. (
        let i = ((ops|>tm_dot_i9) titm) in
        let citm = (ops|>mk_sym_coord) (sym,i,j) in
        let f6 = % bitm s1. cut ctxt bitm citm s1 in
        (* O(n. ln n) *)
        (* let s1 = ctxt.sets.set_nt_item.fold f1 bitms s1 in *)
        let s1 = (ctxt|>maps|>map_blocked_key|>mbk_fold_cod) k f6 (s1|>blocked5) s1 in     
        (* we also update the oracle at this point *)
        let f7 = % bitm s1. s1 (| oracle5:=(update_oracle ctxt (s1|>oracle5) (bitm,(ops|>sym_dot_j9) citm)) |) in
        (* O(n. ln n) *)
        let s1 = (ctxt|>maps|>map_blocked_key|>mbk_fold_cod) k f7 (s1|>blocked5) s1 in
        (* and the tmoracle *)
        let s1 = s1 (| tmoracle5:=(update_tmoracle ctxt (s1|>tmoracle5) (tm,i,j)) |) in                                                            
       s1)
      in
      let s0 = List.foldl f8 s0 rs in 
      s0) (* FIXME todo *)
)
"

end