theory E3_spec
imports E3_core_types
begin

(* this is the specification for Earley; we want soundness (easy) and completeness (harder)

we want to express soundness and completeness in terms of parse trees; the following deals with partial parse trees, and makes the measure easy to deal with

*)

typedecl ty_m (* measure type; an implementation is nat, but we keep it abstract *)

consts m_lt :: "ty_m => ty_m => bool"


(* define the relation *)

record params =
  sp_nt0 :: nt
  sp_nt_items_for_nt :: "(nt => nat => nt_item list)"
  sp_tm_items_for_tm :: "tm => nat => tm_item list"

definition sym_item_of_complete_item :: "item => (sym * nat * nat) option" where
  "sym_item_of_complete_item itm = (case itm of 
  TMITM(tm,i,j) => (Some(TM tm,i,j))
  | NTITM(nt,as,bs,i,j) => (case bs of [] => (Some(NT nt,i,j)) | _ => None))"

inductive_set derivable :: "params => (item * ty_m) set" 
for p0 :: params
where
(* start symbol corresponds to derivable item FIXME parameterize by grammar *)
d_init: "
List.member ((p0|>sp_nt_items_for_nt) (p0|>sp_nt0) 0) ((p0|>sp_nt0),[],bs',0,0)  
==> (NTITM(p0|>sp_nt0,[],bs',0,0),m) : (derivable p0)"

(* cut blocked and complete *)
| d_cut: "
(NTITM(nt,as,S#bs,i,k),m1) : (derivable p0) 
& (citm,m2) : (derivable p0)
& (sym_item_of_complete_item citm = Some(S,k,j))
& m_lt m1 m3
& m_lt m2 m3
==> (NTITM(nt,as@[S],bs,i,j),m3) : (derivable p0)"

(* generate new ntitms *)
| d_ntitm: "
(NTITM(nt,as,(NT X)#bs,i,k),m1) : (derivable p0) 
& List.member ((p0|>sp_nt_items_for_nt) X k) (X,[],bs',k,k)  (* NB this enforces expected invariants about nt_items_for_nt *)
& m_lt m1 m2
==> (NTITM(X,[],bs',k,k),m2) : (derivable p0)"

(* generate new tmitms *)
| d_tmitm: "
(NTITM(nt,as,(TM x)#bs,i,k),m1) : (derivable p0) 
& List.member ((p0|>sp_tm_items_for_tm) x k) (x,k,j)  (* FIXME string argument? length of string? *)
& m_lt m1 m2
==> (TMITM(x,k,j),m2) : (derivable p0)
"


definition derivable_items :: "params => item set" where
  "derivable_items ps = { itm. ? m. (itm,m) : derivable ps}"

end
