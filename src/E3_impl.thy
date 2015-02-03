theory E3_impl
imports Main E3
begin

(* here we instantiate the abstract algorithm *)
record params = 
  ps_nt_items_for_nt :: "nt => ty_string substring => nt_item list"
  ps_p_of_tm :: "tm => ty_string substring => nat list"

definition impl_ops :: "params => ty_ops" where
"impl_ops p0 == (|
  sym_case = id,
  sym_of_tm = (% tm. TM tm),
  mk_tm_coord = (% (tm,i). (tm,i,i)),
  tm5 = (% (tm,i,j). tm),
  mk_sym_coord = id,
  sym6 = (% (sym,i,j). sym),
  nt2 = (% (nt,as,bs,i,j). NT nt),
  shift_a2_b2_c2 = (% (nt,as,bs,i,j). (nt,(List.hd bs)#as,List.tl bs,i,j)),
  b2_nil = (% (nt,as,bs,i,j). bs=[]),
  a2 = (% (nt,as,bs,i,j). as),
  hd_b2 = (% (nt,as,bs,i,j). List.hd bs),
  nt_items_for_nt = (p0|>ps_nt_items_for_nt),
  mk_item = id,
  dest_item = id,
  tm_dot_i9 = (% (tm,i,j). i),
  sym_dot_i9 = ( % (sym,i,j). i),
  sym_dot_j9 = ( % (sym,i,j). j),
  nt_dot_i9 = (% (nt,as,bs,i,j). i),
  nt_dot_j9 = (% (nt,as,bs,i,j). j),
  with_j9 = (% (nt,as,bs,i,j) j'. (nt,as,bs,i,j')),
  p_of_tm = (p0|>ps_p_of_tm) |)"

(* these are the implementation types - must agree with what follows *)
type_synonym mbk_key = "nat*sym"

type_synonym mck_key = "nat*sym"

type_synonym mti_key = "tm*nat"

type_synonym mssii_key = "sym list * sym * nat * nat"

type_synonym ty_impl_loop2 = "(
  item set,
  (mbk_key => nt_item set),
  (mck_key => sym_item set),
  (mssii_key=>nat set),
  (mti_key=>nat set)
  ) ty_loop2"

definition impl_std :: "(item, item set) std" where
  "impl_std = (|
    std_empty = (% _ . {}),
    std_add = (% x t. {x} Un t),
    std_mem = (% x t. x : t) |)"

definition impl_ctxt_set :: "(item,item set) ctxt_set" where
  "impl_ctxt_set = (|
    set_todo_done = impl_std |)"

type_synonym ty_impl_mbk = "(mbk_key,nt_item,(mbk_key => nt_item set),ty_impl_loop2)mbk"

definition impl_mbk :: "ty_impl_mbk" where
  "impl_mbk == (|
    mbk_empty = (% _. % k. {}),
    mbk_add_cod = (% k v t. t(k:=({v} Un (t k)))),
    mbk_fold_cod = (% k f t init. Finite_Set.fold f init (t k)),
    mbk_cod_empty = (% k t. t k =  {}) |)"



type_synonym ty_impl_mck = "(mck_key,sym_item,(mck_key => sym_item set),ty_impl_loop2)mck"

definition impl_mck :: ty_impl_mck where
  "impl_mck == (|
    mck_empty = (% _. % k. {}),
    mck_add_cod = (% k v t. t(k:=({v} Un (t k)))),
    mck_fold_cod = (% k f t init. Finite_Set.fold f init (t k)) |)"



type_synonym ty_impl_mti = "(mti_key,nat,(mti_key=>nat set))mti"

definition impl_mti :: ty_impl_mti where
  "impl_mti == (|  
    mti_empty = (% _. % k. {}),
    mti_add_cod = (% k v t. t(k:=({v} Un (t k)))),
    mti_find_cod = (% k v t. v : (t k)) |)"



type_synonym ty_impl_mssii = "(mssii_key,nat,(mssii_key=>nat set))mssii"

definition list_of_set :: "'a set => 'a list" where
  "list_of_set s = Finite_Set.fold (% a b. a#b) [] s"

definition impl_mssii :: ty_impl_mssii where
  "impl_mssii == (| 
    mssii_empty = (% _. % k. {}),
    mssii_add_cod = (% k v t. t(k:=({v} Un (t k)))),
    mssii_elts_cod = (% k t. list_of_set (t k)) |)"

definition impl_ctxt_map :: "(
  (mbk_key => nt_item set),
  (mck_key => sym_item set),
  (mssii_key=>nat set),
  (mti_key=>nat set),
  ty_impl_loop2,
  ty_impl_loop2
  ) ctxt_map" where
  "impl_ctxt_map == (|
    map_blocked_key = impl_mbk,
    map_complete_key = impl_mck,
    map_sym_sym_int_int = impl_mssii,
    map_tm_int = impl_mti |) "

definition impl_ctxt :: "(
  ty_string,  
  item,
  item set,
   (mbk_key => nt_item set),
  (mck_key => sym_item set),
  (mssii_key=>nat set),
  (mti_key=>nat set),
  ty_impl_loop2,
  ty_impl_loop2) ty_ctxt" where
  "impl_ctxt == (|
    string5=arbitrary, (* FIXME *)
    length5=0,
    item_ops5=impl_ops arbitrary, (* FIXME *)
    sets=impl_ctxt_set,
    maps=impl_ctxt_map |)"
 
definition init_state :: "ty_impl_loop2" where
  "init_state == (|
    todo_done5 = ((impl_std|>std_empty) ()),
    todo5 = [],
    oracle5 = ((impl_mssii|>mssii_empty) ()),
    tmoracle5 = ((impl_mti|>mti_empty) ()),
    blocked5 = ((impl_mbk|>mbk_empty) ()),
    complete5 = ((impl_mck|>mck_empty) ()) |) "

