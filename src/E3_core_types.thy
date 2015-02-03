theory E3_core_types
imports E3_prelude
begin

type_synonym 'a substring = "'a * nat * nat"

typedecl nt
typedecl tm

datatype nt_tm = NT nt | TM  tm

type_synonym sym = nt_tm

type_synonym tm_item = "tm * nat * nat"
type_synonym sym_item = "sym * nat * nat"
type_synonym sym_list = "sym list"
type_synonym nt_item = "nt*sym list * sym list * nat * nat"

datatype ntitm_tmitm = NTITM nt_item | TMITM tm_item

type_synonym item = ntitm_tmitm

record 'string ty_ops = 
  sym_case       :: "sym => nt_tm"
  sym_of_tm      :: "tm => sym"
  mk_tm_coord    :: "(tm * nat) => tm_item"
  tm5            :: "tm_item => tm"
  mk_sym_coord   :: "(sym * nat * nat) => sym_item"
  sym6           :: "sym_item => sym"
  nt2            :: "nt_item => sym"
  shift_a2_b2_c2 :: "nt_item => nt_item"
  b2_nil         :: "nt_item => bool"
  a2             :: "nt_item => sym_list"
  hd_b2          :: "nt_item => sym"
  nt_items_for_nt:: "nt => 'string substring => nt_item list"
  mk_item        :: "ntitm_tmitm => item"
  dest_item      :: "item => ntitm_tmitm"
  tm_dot_i9      :: "tm_item => nat"
  sym_dot_i9     :: "sym_item => nat"
  sym_dot_j9     :: "sym_item => nat"
  nt_dot_i9      :: "nt_item => nat"
  nt_dot_j9      :: "nt_item => nat"
  with_j9        :: "nt_item => nat => nt_item"
  p_of_tm        :: "tm => 'string substring => nat list"


record ('elt,'t) std = 
  std_empty :: "unit => 't"
  std_add :: "'elt => 't => 't"
  std_mem :: "'elt => 't => bool"

record ('todo_done,'set_todo_done) ctxt_set = 
  set_todo_done :: "('todo_done,'set_todo_done) std"

record ('key,'value,'t,'mbk_fold_type) mbk = 
  mbk_empty :: "unit => 't"
  mbk_add_cod :: "'key => 'value => 't => 't"
  mbk_fold_cod :: "'key => ('value => 'mbk_fold_type => 'mbk_fold_type) => 't => 'mbk_fold_type => 'mbk_fold_type"
  mbk_cod_empty :: "'key => 't => bool"

record ('key,'value,'t,'mck_fold_type) mck = 
  mck_empty :: "unit => 't"
  mck_add_cod :: "'key => 'value => 't => 't"
  mck_fold_cod :: "'key => ('value => 'mck_fold_type => 'mck_fold_type) => 't => 'mck_fold_type => 'mck_fold_type"

record ('key,'value,'t) mti = 
  mti_empty :: "unit => 't"
  mti_add_cod :: "'key => 'value => 't => 't"
  mti_find_cod :: "'key => 'value => 't => bool"
 
record ('key,'value,'t) mssii = 
  mssii_empty :: "unit => 't"
  mssii_add_cod :: "'key => 'value => 't => 't"
  mssii_elts_cod :: "'key => 't => 'value list"

record ('map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ctxt_map = 
  map_blocked_key :: "(nat*sym,nt_item,'map_blocked_key,'mbk_fold_type)mbk"
  map_complete_key :: "(nat*sym,sym_item,'map_complete_key,'mck_fold_type)mck"
  map_sym_sym_int_int :: "(sym_list * sym * nat * nat,nat,'map_sym_sym_int_int)mssii"
  map_tm_int :: "(tm*nat,nat,'map_tm_int)mti"

record ('string,'todo_done,'set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ty_ctxt = 
  string5 :: "'string"
  length5 :: "nat"
  item_ops5 :: "'string ty_ops"
  sets ::  "('todo_done,'set_todo_done) ctxt_set"
  maps :: "('map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int,'mbk_fold_type,'mck_fold_type) ctxt_map"

record ('set_todo_done,'map_blocked_key,'map_complete_key,'map_sym_sym_int_int,'map_tm_int) ty_loop2 = 
  todo_done5 :: "'set_todo_done"
  todo5 :: "item list"
  oracle5 :: "'map_sym_sym_int_int"
  tmoracle5 :: "'map_tm_int"
  blocked5 :: "'map_blocked_key"
  complete5 :: "'map_complete_key"


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

(* here we instantiate the abstract algorithm *)
record 'string ct_params = 
  ct_nt0 :: "nt"
  ct_nt_items_for_nt :: "nt => 'string substring => nt_item list"
  ct_p_of_tm :: "tm => 'string substring => nat list"

definition impl_ops :: "'string ct_params => 'string ty_ops" where
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
  nt_items_for_nt = (p0|>ct_nt_items_for_nt),
  mk_item = id,
  dest_item = id,
  tm_dot_i9 = (% (tm,i,j). i),
  sym_dot_i9 = ( % (sym,i,j). i),
  sym_dot_j9 = ( % (sym,i,j). j),
  nt_dot_i9 = (% (nt,as,bs,i,j). i),
  nt_dot_j9 = (% (nt,as,bs,i,j). j),
  with_j9 = (% (nt,as,bs,i,j) j'. (nt,as,bs,i,j')),
  p_of_tm = (p0|>ct_p_of_tm) |)"

type_synonym 'string ty_impl_ctxt = "(
  'string,  
  item,
  item set,
   (mbk_key => nt_item set),
  (mck_key => sym_item set),
  (mssii_key=>nat set),
  (mti_key=>nat set),
  ty_impl_loop2,
  ty_impl_loop2) ty_ctxt"

definition impl_ctxt :: "(
  'string,  
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
 
definition init_state :: "'string => 'string ct_params => ty_impl_loop2" where
  "init_state s ps == 
    let nt0 = (ps|>ct_nt0) in
    let init_items = ct_nt_items_for_nt ps nt0 (s,0,0) in
    let init_items = List.map (\<lambda> x. NTITM x) init_items in
    let todo_done = set(init_items) in
    (|
    todo_done5 = todo_done (* ((impl_std|>std_empty) ()) *),
    todo5 = init_items,
    oracle5 = ((impl_mssii|>mssii_empty) ()),
    tmoracle5 = ((impl_mti|>mti_empty) ()),
    blocked5 = ((impl_mbk|>mbk_empty) ()),
    complete5 = ((impl_mck|>mck_empty) ()) |) "


end
