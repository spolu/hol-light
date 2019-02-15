(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lib.ml";;

module type Hol_kernel =
  sig
      type hol_type = private
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term = private
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term

      type thm

      type proof

      val proof_REFL : term -> proof
      val proof_TRANS : proof * proof -> proof
      val proof_MK_COMB : proof * proof -> proof
      val proof_ASSUME : term -> proof
      val proof_EQ_MP : proof -> proof -> proof
      val proof_IMPAS : proof -> proof -> proof
      val proof_DISCH : proof -> term -> proof
      val proof_DEDUCT_ANTISYM_RULE : proof * term -> proof * term -> proof
      val proof_BETA : term -> proof
      val proof_ABS : term -> proof -> proof
      val proof_INST_TYPE : (hol_type * hol_type) list -> proof -> proof
      val proof_INST : (term * term) list -> proof -> proof
      val proof_new_definition : string -> hol_type -> term -> proof
      val proof_CONJ : proof -> proof -> proof
      val proof_CONJUNCT1 : proof -> proof
      val proof_CONJUNCT2 : proof -> proof
      val proof_new_basic_type_definition :
          string -> string * string -> term * term -> proof -> proof
      val proof_SPEC : term -> proof -> proof
      val proof_SYM : proof -> proof
      val proof_GEN : proof -> term -> proof
      val proof_DISJ1 : proof -> term -> proof
      val proof_DISJ2 : proof -> term -> proof
      val proof_NOTI : proof -> proof
      val proof_NOTE : proof -> proof
      val proof_CONTR : proof -> term -> proof
      val proof_DISJCASES : proof -> proof -> proof -> proof
      val proof_CHOOSE : term -> proof -> proof -> proof
      val proof_EXISTS : term -> term -> proof -> proof

      val new_axiom_name : string -> string
      val proof_new_axiom : string -> term -> proof

      val save_proof : string -> proof -> (term option) -> unit
      val proof_database : unit -> ((string * proof * (term option)) list)

      val export_proofs : string option -> (string * proof * (term option)) list -> unit
      val export_saved_proofs : string option -> unit

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      val new_type : (string * int) -> unit
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val get_const_type : string -> hol_type
      val new_constant : string * hol_type -> unit
      val type_of : term -> hol_type
      val alphaorder : term -> term -> int
      val is_var : term -> bool
      val is_const : term -> bool
      val is_abs : term -> bool
      val is_comb : term -> bool
      val mk_var : string * hol_type -> term
      val mk_const : string * (hol_type * hol_type) list -> term
      val mk_abs : term * term -> term
      val mk_comb : term * term -> term
      val dest_var : term -> string * hol_type
      val dest_const : term -> string * hol_type
      val dest_comb : term -> term * term
      val dest_abs : term -> term * term
      val frees : term -> term list
      val freesl : term list -> term list
      val freesin : term list -> term -> bool
      val vfree_in : term -> term -> bool
      val type_vars_in_term : term -> hol_type list
      val variant : term list -> term -> term
      val vsubst : (term * term) list -> term -> term
      val inst : (hol_type * hol_type) list -> term -> term
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      val REFL : term -> thm
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
      val axioms : unit -> thm list
      val new_axiom : term -> thm
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm

      val proof_of : thm -> proof
      val substitute_proof : thm -> proof -> thm
      val save_thm : string -> thm -> thm
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term

  type thm = Sequent of (term list * term * proof)
  type proof = unit -> unit

(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type and the function space            *)
(* constructor. Later on we add as primitive the type of individuals.        *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)



  let writeln s p = p;;
(*    let q = s^"\n" in
    (output stdout q 0 (String.length q); p);;*)

  type tag = string

  type proof_info_rec =
      {disk_info: (string * string) option ref;
       status: int ref;
       references: int ref;
       queued: bool ref}

  type proof_info = Info of proof_info_rec

  type ('a, 'b) libsubst_rec = {redex:'a; residue:'b}
  type ('a, 'b) libsubst = (('a,'b) libsubst_rec) list

  let pair2libsubstrec =
    fun (a,b) -> {redex=b;residue=a}

(* note: not all of the proof_content constructors are actually used, some are just legacy from the HOL4 proof objects *)
  type proof =
      Proof of (proof_info * proof_content * (unit -> unit))
  and proof_content =
      Prefl of term
    | Pinstt of proof * ((hol_type,hol_type) libsubst)
    | Psubst of proof list * term * proof
    | Pabs of proof * term
    | Pdisch of proof * term
    | Pmp of proof * proof
    | Phyp of term
    | Paxm of string * term
    | Pdef of string * string * term
    | Ptmspec of string * string list * proof
    | Ptydef of string * string * proof
    | Ptyintro of string * string * string * string * term * term * proof
    | Poracle of tag * term list * term
    | Pdisk
    | Pspec of proof * term
    | Pinst of proof * (term,term) libsubst
    | Pgen of proof * term
    | Pgenabs of proof * term option * term list
    | Psym of proof
    | Ptrans of proof * proof
    | Pcomb of proof * proof
    | Peqmp of proof * proof
    | Peqimp of proof
    | Pexists of proof * term * term
    | Pchoose of term * proof * proof
    | Pconj of proof * proof
    | Pconjunct1 of proof
    | Pconjunct2 of proof
    | Pdisj1 of proof * term
    | Pdisj2 of proof * term
    | Pdisjcases of proof * proof * proof
    | Pnoti of proof
    | Pnote of proof
    | Pcontr of proof * term
    | Pimpas of proof * proof

  let THEORY_NAME = "hollight"

  let content_of (Proof (_,p,_)) = p

  let inc_references (Proof(Info{references=r},_,_) as p) = (
    let
        old = !r
    in
    r := old + 1;
    p)

  let concat = String.concat ""

  let dummy_fun () = ()

  let mk_proof p = Proof(Info {disk_info = ref None; status = ref 0; references = ref 0; queued = ref false},p, dummy_fun)

  let global_ax_counter = let counter = ref 1 in let f = fun () -> (let x = !counter in counter := !counter+1; x) in f

  let new_axiom_name n = concat["ax_"; n; "_"; string_of_int(global_ax_counter())]

  let proof_REFL t = writeln "REFL" (mk_proof (Prefl t))

  let proof_TRANS (p,q) = writeln "TRANS" (
    match (content_of p, content_of q) with
      (Prefl _,_) -> q
    | (_, Prefl _) -> p
    | _ -> mk_proof (Ptrans (inc_references p, inc_references q)))

  let proof_MK_COMB (p1,p2) = writeln "MK_COMB" (
    (match (content_of p1, content_of p2) with
      (Prefl tm1, Prefl tm2) -> proof_REFL (mk_comb (tm1, tm2))
    | _ ->  mk_proof (Pcomb (inc_references p1, inc_references p2))))

  let proof_ASSUME t = writeln "ASSUME "(mk_proof (Phyp t))

  let proof_EQ_MP p q = writeln "EQ_MP" (
    (match content_of p with
      Prefl _ -> q
    | _ -> mk_proof (Peqmp(inc_references p, inc_references q))))

  let proof_IMPAS p1 p2 = writeln "IMPAS" (
    mk_proof (Pimpas (inc_references p1, inc_references p2)))

  let proof_DISCH p t = writeln "DISCH" (mk_proof (Pdisch(inc_references p,t)))

  let proof_DEDUCT_ANTISYM_RULE (p1,t1) (p2,t2) = writeln "DEDUCT_ANTISYM_RULE" (
    proof_IMPAS (proof_DISCH p1 t2) (proof_DISCH p2 t1))

  let proof_BETA t = writeln "BETA" (mk_proof (Prefl t))

  let proof_ABS x p = writeln "ABS" (
    (match (content_of p) with
      Prefl tm -> proof_REFL (mk_abs(x,tm))
    | _ -> mk_proof (Pabs(inc_references p,x))))

  let proof_INST_TYPE s p = writeln "INST_TYPE" (mk_proof (Pinstt(inc_references p, map pair2libsubstrec s)))

  let proof_INST s p = writeln "INST" (mk_proof (Pinst(inc_references p, map pair2libsubstrec s)))

  let proof_new_definition cname _ t = writeln "new_definition" (mk_proof (Pdef (THEORY_NAME, cname, t)))

  let proof_new_axiom axname t = writeln "new_axiom" (mk_proof (Paxm (axname, t)))

  let proof_CONJ p1 p2 = writeln "CONJ" (mk_proof (Pconj (inc_references p1, inc_references p2)))

  let proof_CONJUNCT1 p = writeln "CONJUNCT1" (mk_proof (Pconjunct1 (inc_references p)))

  let proof_CONJUNCT2 p = writeln "CONJUNCT2" (mk_proof (Pconjunct2 (inc_references p)))

  let proof_new_basic_type_definition tyname (absname, repname) (pt,tt) p = writeln "new_basic_type_definition" (
    mk_proof(Ptyintro (THEORY_NAME, tyname, absname, repname, pt, tt,inc_references p)))

(* ---- used only in substitute_proof calls ---- *)

  let proof_SPEC s p = writeln "SPEC" (mk_proof (Pspec(inc_references p, s)))

  let proof_SYM p = writeln "SYM" (mk_proof (Psym(inc_references p)))

  let proof_GEN p a = writeln "GEN" (mk_proof (Pgen(inc_references p, a)))

  let proof_DISJ1 p a = writeln "DISJ1" (mk_proof (Pdisj1 (inc_references p, a)))

  let proof_DISJ2 p a = writeln "DISJ2" (mk_proof (Pdisj2 (inc_references p, a)))

  let proof_NOTI p = writeln "NOTI" (mk_proof (Pnoti (inc_references p)))

  let proof_NOTE p = writeln "NOTE" (mk_proof (Pnote (inc_references p)))

  let proof_CONTR p a = writeln "CONTR" (mk_proof (Pcontr (inc_references p, a)))

  let proof_DISJCASES p q r = writeln "DISJCASES" (mk_proof (Pdisjcases (inc_references p, inc_references q, inc_references r)))

  let proof_CHOOSE a p q = writeln "CHOOSE" (mk_proof (Pchoose (a, inc_references p, inc_references q)))

  let proof_EXISTS x y p  = writeln "EXISTS" (mk_proof (Pexists (inc_references p, x, y)))

(* ---- formerly known as proofio.ml ---- *)

let ensure_export_directory thyname =
  let dir = Sys.getenv "HOLPROOFEXPORTDIR" in
  let dirsub = Filename.concat dir "hollight" in
  let dirsubsub = Filename.concat dirsub thyname in
  let mk d = if Sys.file_exists d then () else Unix.mkdir d 509
  in
    (mk dir;
     mk dirsub;
     mk dirsubsub;
     dirsubsub);;

(* ---- Useful functions on terms ---- *)
let rec types_of tm =
    if is_var tm
    then [type_of tm]
    else if is_const tm
    then [type_of tm]
    else if is_comb tm
    then
        let
            (f,a) = dest_comb tm
        in
            union (types_of f) (types_of a)
    else
        let
            (x,a) = dest_abs tm
        in
            insert (type_of x) (types_of a);;

let beta_conv tm =
  try let (f,arg) = dest_comb tm in
      let (v,bod) = dest_abs f in
      vsubst [(arg,v)] bod
  with Failure _ -> failwith "beta_conv: Not a beta-redex";;

let eta_conv tm =
  try
    (let (v, bod) = dest_abs tm in
    let (f, arg) = dest_comb bod in
      if (arg = v && (not(vfree_in v f))) then
        f
      else failwith "")
  with
    Failure _ -> failwith "eta_conv: Not an eta-redex";;

let rec be_contract tm =
    let rec bec tm = try try Some (beta_conv tm)
            with Failure _ ->
                   Some (eta_conv tm)
            with Failure _ ->
                   if is_comb tm
                   then
                       (let
                           (f,x) = dest_comb tm
                       in
                           match bec f with
                               Some f' -> Some (mk_comb(f',x))
                             | None -> (match bec x with
                                            Some x' -> Some (mk_comb(f,x'))
                                          | None -> None))
                   else if is_abs tm
                   then
                       (let
                         (x,body) = dest_abs tm
                       in
                           (match bec body with
                               Some body' -> Some (mk_abs(x,body'))
                             | None -> None))
                   else None
    in
        (match bec tm with
            Some tm' -> be_contract tm'
          | None -> tm);;

let rec polymorphic x =
  if is_vartype x then true else exists polymorphic (snd (dest_type x))

(* ---- From Lib etc. ---- *)


let rec append = fun xlist l ->
  (match xlist with
    [] -> l
  | (x::xs) -> x::(append xs l));;

let assoc1 item =
  let rec assc =
    (function (((key,_) as e)::rst) -> if item=key then Some e else assc rst
      | [] -> None)
  in
    assc;;


let rec listconcat =
  function [] -> []
    | (l::ls) -> append l (listconcat ls);;

let listnull =
  function [] -> true | _ -> false;;

(* ---- exported ---- *)
let encodeXMLEntities m = m;;let encodeXMLEntities s =
  let len = String.length s in
  let encodeChar  = function '<' -> "&lt;" | '>' -> "&gt;" | '&' -> "&amp;" | '\'' -> "&apos;" | '"' -> "&quot;" | c -> String.make 1 c in
  let rec encodeStr i =  if (i<len) then (encodeChar (String.get s i))::(encodeStr (i+1)) else [] in
  String.concat "" (encodeStr 0);;

let encodeXMLEntitiesOut out = function x -> out (encodeXMLEntities x);;


let content_of (Proof (_,x,_)) = x;;

let rec explode_subst =
  function [] -> []
    | ({redex=x;residue=y}::rest) -> x::y::(explode_subst rest);;

let rec app f =
  function [] -> ()
    | (x::l) -> (f x; app f l);;

let disk_info_of (Proof(Info {disk_info=di},_,_)) = !di;;

let set_disk_info_of (Proof(Info {disk_info=di},_,_)) thyname thmname =
    di := Some (thyname,thmname);;

let references (Proof (Info info,_,_)) = !(info.references);;

let wrap b e s = b^s^e;;

let xml_empty_tag = wrap "<" "/>";;
let xml_start_tag = wrap "<" ">";;
let xml_end_tag = wrap "</" ">";;
let xml_attr attr =
    itlist (function (tag,v) ->
            function s ->
               concat[" ";tag;"=\"";v;"\"";s]
           )
           attr "";;
let xml_element tag attr children =
    let
        header = tag ^ (xml_attr attr)
    in
        (if listnull children
         then xml_empty_tag header
         else wrap (xml_start_tag header) (xml_end_tag tag) (concat children));;

let id_to_atts curthy id = [("n", encodeXMLEntities id)];; (* There is only one theory in Hol-Light, therefore id_to_atts is superfluous *)

let glob_counter = ref 1;;

let get_counter () =
  let
      res = !glob_counter
  in
    glob_counter := res + 1;
    res;;

let get_iname =  string_of_int o get_counter;;

let next_counter () = !glob_counter;;

let trivial p =
      match (content_of p) with
        Prefl _ -> true
      | Paxm _ -> true
      | Pdisk -> true
      | Phyp _ -> true
      | Poracle _ -> true
      | _ -> false;;

let do_share p = references p > 1 && not (trivial p);;

exception Err of string*string;;

(* ---- The General List Formerly Known As Net ---- *)

type 'a exprnet = (('a list) ref) * ('a -> ('a list))

let empty_net f () = (ref [], f);;

let rec lookup'_net net x =
  match net with
    [] -> raise Not_found
  | (a::l) -> if (a = x) then 0 else 1+(lookup'_net l x);;

let lookup_net (net,f) x = lookup'_net (!net) x;;

let insert'_net (net,f) x =
  try lookup'_net !net x; () with Not_found -> ((net := (!net)@[x]);());;

let rec insert_net ((net,f) as n) x =
  (app (insert_net n) (f x); insert'_net n x);;

let to_list_net (net,f) = !net;;

(* ---- The Type Net (it's not a net any more!) ---- *)

type yy_net = hol_type exprnet;;

let yy_empty = empty_net (function x -> if is_type x then snd (dest_type x) else []);;

let yy_lookup = lookup_net;;

let yy_output_types out thyname net =
    let
        all_types = to_list_net net in let rec
        xml_index ty = xml_element "tyi" [("i",string_of_int (yy_lookup net ty))] []
        and xml_const id = xml_element "tyc" (id_to_atts thyname id) []
        and out_type ty =
          if is_vartype ty then out (xml_element "tyv" [("n",encodeXMLEntities (dest_vartype ty))] [])
          else (
            match dest_type ty with
              (id, []) -> out (xml_const id)
            | (id, tl) -> out (xml_element "tya" [] ((xml_const id)::(map xml_index tl)))
          )
    in
        out "<tylist i=\"";
        out (string_of_int (length all_types));
        out "\">";
        app out_type all_types;
        out "</tylist>";;

let yy_insert = insert_net;;

(* ---- The Term Net (it's not a net anymore!) ---- *)

type mm_net = term exprnet;;

let mm_empty = empty_net (
  function tm ->
    if is_abs tm then
      (let (x,b) = dest_abs tm in [x; b])
    else if is_comb tm then
      (let (s,t) = dest_comb tm in [s; t])
    else
      [])

let mm_lookup net x = lookup_net net (be_contract x);;

let mm_insert net x = insert_net net (be_contract x);;

let mm_output_terms out thyname types net =
    let all_terms = to_list_net net in
    let xml_type ty = xml_element "tyi" [("i",string_of_int (yy_lookup types ty))] [] in
    let xml_index tm = xml_element "tmi" [("i",string_of_int (mm_lookup net tm))] [] in
    let out_term tm =
            if is_var tm
            then
                let
                    (name,ty) = dest_var tm
                in
                    out (xml_element "tmv" [("n",encodeXMLEntities name);("t", string_of_int (yy_lookup types ty))] [])
            else if is_const tm
            then
                let (name, ty) = (dest_const tm) in
                let general_ty = get_const_type name in
                let atts = [("n",encodeXMLEntities name)]
                in
                    if polymorphic general_ty then
                      out (xml_element "tmc" (atts@[("t",string_of_int (yy_lookup types ty))]) [])
                    else out (xml_element "tmc" atts [])
            else if is_comb tm
            then
                let
                    (f,a) = dest_comb tm
                in
                    out (xml_element "tma" [("f", string_of_int (mm_lookup net f));("a",string_of_int (mm_lookup net a))] [])
            else
                let
                    (x,a) = dest_abs tm
                in
                    out (xml_element "tml" [("x", string_of_int (mm_lookup net x));("a",string_of_int (mm_lookup net a))] [])
    in
        out "<tmlist i=\"";
        out (string_of_int(length all_terms));
        out "\">";
        app out_term all_terms;
        out "</tmlist>";;


(* ---- collect_types_terms ---- *)

let collect_types_terms thyname out prf c_opt =
    let
        will_be_shared prf = (
            match disk_info_of prf with
                Some _ -> true
              | None -> do_share prf) in let

        types = yy_empty () in let
        terms = mm_empty () in let

        insert_type ty = yy_insert types ty in let

        insert_term tm = (mm_insert terms tm;
                          app (yy_insert types) (types_of tm)) in let rec

        ct' prf =
            (match content_of prf with
                Pinstt(prf,tsubst) -> (app (function {redex=x;residue=u}->(insert_type x; insert_type u))
                                           tsubst;
                                       ct prf)
              | Psubst(prfs,tm,prf) -> (insert_term tm;
                                        ct prf;
                                        app ct prfs)
              | Pabs(prf,tm) -> (insert_term tm;
                                 ct prf)
              | Pdisch(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pmp(prf1,prf2) -> (ct prf1; ct prf2)
              | Poracle(_,tms,tm) -> (insert_term tm;
                                      app insert_term tms)
              | Pdef(_,_,tm) -> insert_term tm
              | Ptmspec(_,_,prf) -> ct prf
              | Ptydef(_,_,prf) -> ct prf
              | Ptyintro(_,_,_,_,pt,tt,prf) -> (insert_term pt; insert_term tt;ct prf)
              | Pspec(prf,tm) -> (insert_term tm; ct prf)
              | Pinst(prf,subst) -> (app (fun{redex=x;residue=u}->(insert_term x;
                                                              insert_term u))
                                         subst;
                                     ct prf)
              | Pgen(prf,tm) -> (insert_term tm; ct prf)
              | Pgenabs(prf,tm_opt,tms) -> (match tm_opt with
                                                Some tm -> insert_term tm
                                              | None -> ();
                                            app insert_term tms;
                                            ct prf)
              | Psym prf -> ct prf
              | Ptrans(prf1,prf2) -> (ct prf1; ct prf2)
              | Pcomb(prf1,prf2) -> (ct prf1; ct prf2)
              | Peqmp(prf1,prf2) -> (ct prf1; ct prf2)
              | Peqimp prf -> ct prf
              | Pexists(prf,ex,w) -> (insert_term ex;
                                      insert_term w;
                                      ct prf)
              | Pchoose(v,prf1,prf2) -> (insert_term v; ct prf1; ct prf2)
              | Pconj(prf1,prf2) -> (ct prf1; ct prf2)
              | Pconjunct1 prf -> ct prf
              | Pconjunct2 prf -> ct prf
              | Pdisj1(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pdisj2(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Pdisjcases(prf1,prf2,prf3) -> (ct prf1; ct prf2; ct prf3)
              | Pnoti prf -> ct prf
              | Pnote prf -> ct prf
              | Pcontr(prf,tm) -> (insert_term tm;
                                   ct prf)
              | Prefl tm -> insert_term tm
              | Phyp tm -> insert_term tm
              | Pdisk -> ()
              | Paxm (_,tm) -> insert_term tm
              | Pimpas (prf1,prf2) -> (ct prf1; ct prf2))
        and ct prf =
            if will_be_shared prf
            then ()
            else ct' prf in let

        _ = ct' prf in let
        _ = (match c_opt with
                    Some c -> insert_term c
                  | None -> ()) in let
        _ = yy_output_types out thyname types in let
        _ = mm_output_terms out thyname types terms
    in
        (types,terms);;

let rec export_proof path thyname thmname p c_opt il  =
  let outchannel = open_out (Filename.concat path (thmname^".prf")) in
  let out = output_string outchannel in
  let nout = encodeXMLEntitiesOut out in
  let
      _ = out "<proof>" in let

      (types,terms) = collect_types_terms thyname out p c_opt in let

      wti att tm =
        (out " ";
         out att;
         out "=\"";
         out (string_of_int (mm_lookup terms tm));
         out "\"") in let

      wt tm = try (out "<tmi"; wti "i" tm; out "/>") with Not_found -> raise (Err("export_proof","Term not found!")) in let

      wty ty =
        try (out "<tyi i=\"";
             out (string_of_int (yy_lookup types ty));
             out "\"/>") with Not_found -> raise (Err("export_proof","Type not found!")) in let

      wdi thy thm =
        (out "<pfact ";
         if not (thy = thyname)
         then (out "s=\"";
               out thy;
               out "\" ")
         else ();
         out "n=\"";
         nout thm;
         out "\"/>") in let

      write_proof p il =
       (let rec
          share_info_of p il =
            (match (disk_info_of p) with
              Some (thyname,thmname) -> Some(thyname,thmname,il)
            | None ->
                if do_share p then
                  let name = get_iname() in set_disk_info_of p thyname name; Some(thyname,name,(name,p,None)::il)
                else
                  None
            )
          and
          dump str il prfs =
                    (let
                        _ = out (xml_start_tag str) in let
                        res = rev_itlist (function p -> function il -> wp il p) prfs il in let
                        _ = out (xml_end_tag str)
                    in
                        res)
          and
          wp' il =
            (function
              (Prefl tm) -> (out "<prefl"; wti "i" tm; out "/>"; il)
            |  (Pinstt(p,lambda)) ->
                   (let
                        _ = out "<pinstt>" in let
                        res = wp il p in let
                        _ = app wty (explode_subst lambda) in let
                        _ = out "</pinstt>"
                    in
                        res)
            |  (Psubst(ps,t,p)) ->
                   (let
                        _ = (out "<psubst"; wti "i" t; out ">") in let
                        il' = wp il p in let
                        res = rev_itlist (function p -> function il -> wp il p) ps il' in let
                        _ = out "</psubst>"
                    in
                        res)
            |  (Pabs(p,t)) ->
                   (let
                        _ = (out "<pabs"; wti "i" t; out ">") in let
                        res = wp il p in let
                        _ = out "</pabs>"
                    in
                        res)
            |  (Pdisch(p,tm)) ->
                    (let
                        _ = (out "<pdisch"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisch>"
                    in
                        res)
            |  (Pmp(p1,p2)) -> dump "pmp" il [p1;p2]
            |  (Phyp tm) -> (out "<phyp"; wti "i" tm; out "/>"; il)
            |  (Paxm(name,tm)) ->
                    (out "<paxiom n=\"";
                     nout name;
                     out "\"";
                     wti "i" tm;
                     out "/>";
                     il)
            |  (Pdef(seg,name,tm)) ->
                    (out "<pdef s=\"";
                     out seg;
                     out "\" n=\"";
                     nout name;
                     out "\"";
                     wti "i" tm;
                     out "/>";
                     il)
            |  (Ptmspec(seg,names,p)) ->
                    (let
                        _ = (out "<ptmspec s=\""; out seg; out "\">") in let
                        res = wp il p in let
                        _ = app (function s -> (out "<name n=\""; nout s; out "\"/>")) names in let
                        _ = out "</ptmspec>"
                    in
                        res)
            |  (Ptydef(seg,name,p)) ->
                    (let
                        _ = (out "<ptydef s=\""; out seg; out "\" n=\""; nout name; out "\">") in let
                        res = wp il p in let
                        _ = out "</ptydef>"
                    in
                        res)
            |  (Ptyintro(seg,name,abs,rep,pt,tt,p)) ->
                    (let
                        _ = (out "<ptyintro s=\""; out seg; out "\" n=\""; nout name;
                             out "\" a=\""; out abs; out "\" r=\""; out rep; out "\">") in let

                        _ = wt pt in let
                        _ = wt tt in let
                        res = wp il p in let
                        _ = out "</ptyintro>"
                    in
                        res)
            |  (Poracle(tg,asl,c)) -> raise (Err("export_proof", "sorry, oracle export is not implemented!"))
(*                  (out "<poracle>";
                     app (function s -> (out "<oracle n=\""; nout s; out "\"/>")) (Tag.oracles_of tg);
                     wt c;
                     app wt asl;
                     out "</poracle>";
                     il)*)
            |  (Pspec(p,t)) ->
                    (let
                        _ = (out "<pspec"; wti "i" t; out ">") in let
                        res = wp il p in let
                        _ = out "</pspec>"
                    in
                        res)
            |  (Pinst(p,theta)) ->
                    (let
                        _ = out "<pinst>" in let
                        res = wp il p in let
                        _ = app wt (explode_subst theta) in let
                        _ = out "</pinst>"
                    in
                        res)
            |  (Pgen(p,x)) ->
                    (let
                        _ = (out "<pgen"; wti "i" x; out ">") in let
                        res = wp il p in let
                        _ = out "</pgen>"
                    in
                        res)
            |  (Pgenabs(p,opt,vl)) ->
                    (let
                        _ = out "<pgenabs" in let
                        _ = (match opt with
                                    Some c -> wti "i" c
                                  | None -> ()) in let
                        _ = out ">" in let
                        res = wp il p in let
                        _ = app wt vl in let
                        _ = out "</pgenabs>"
                    in
                        res)
                  |  (Psym p) -> dump "psym" il [p]
                  |  (Ptrans(p1,p2)) -> dump "ptrans" il [p1;p2]
                  |  (Pcomb(p1,p2)) -> dump "pcomb" il [p1;p2]
                  |  (Peqmp(p1,p2)) -> dump "peqmp" il [p1;p2]
                  |  (Peqimp p) -> dump "peqimp" il [p]
                  |  (Pexists(p,ex,w)) ->
                    (let
                        _ = (out "<pexists"; wti "e" ex; wti "w" w; out ">") in let
                        res = wp il p in let
                        _ = out "</pexists>"
                    in
                        res)
                  |  (Pchoose(v,p1,p2)) ->
                    (let
                        _ = (out "<pchoose"; wti "i" v; out ">") in let
                        il' = wp il p1 in let
                        res = wp il' p2 in let
                        _ = out "</pchoose>"
                    in
                        res)
                  |  (Pconj(p1,p2)) -> dump "pconj" il [p1;p2]
                  |  (Pimpas(p1,p2)) -> dump "pimpas" il [p1;p2]
                  |  (Pconjunct1 p) -> dump "pconjunct1" il [p]
                  |  (Pconjunct2 p) -> dump "pconjunct2" il [p]
                  |  (Pdisj1(p,tm)) ->
                    (let
                        _ = (out "<pdisj1"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisj1>"
                    in
                        res)
                  |  (Pdisj2(p,tm)) ->
                    (let
                        _ = (out "<pdisj2"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pdisj2>"
                    in
                        res)
                  |  (Pdisjcases(p1,p2,p3)) -> dump "pdisjcases" il [p1;p2;p3]
                  |  (Pnoti p) -> dump "pnoti" il [p]
                  |  (Pnote p) -> dump "pnote" il [p]
                  |  (Pcontr(p,tm)) ->
                    (let
                        _ = (out "<pcontr"; wti "i" tm; out ">") in let
                        res = wp il p in let
                        _ = out "</pcontr>"
                    in
                        res)
                  |  Pdisk -> raise (Err("wp'","shouldn't try to write pdisk"))
            )
          and wp il p =
               (let
                    res = match (share_info_of p il) with
                            Some(thyname',thmname,il') -> (wdi thyname' thmname; il')
                          | None -> wp' il (content_of p)
                in res) in let

          res = (match disk_info_of p with
                              Some(thyname',thmname') ->
                              if thyname' = thyname &
                                 thmname' = thmname
                              then
                                  wp' il (content_of p)
                              else
                                  (wdi thyname' thmname';
                                   il)
                            | None -> wp' il (content_of p))
         in res) in let

        il = write_proof p il in let
        _ = (match c_opt with
                    Some c -> wt c
                  | None -> ()) in let
        _ = (out "</proof>\n";(close_out outchannel))  in let
        _ = set_disk_info_of p thyname thmname
        in
           match il with
             [] -> () (* everything has been written *)
           | ((thmname',prf,c_opt)::rest) -> export_proof path thyname thmname' prf c_opt rest;;

let export_proofs theory_name l' =
  let theory_name = match theory_name with None -> THEORY_NAME | Some n -> n in
  let path = ensure_export_directory theory_name in
  let ostrm = open_out (Filename.concat path "facts.lst") in
  let out = output_string ostrm in
  let _ = app (function (s,_,_) -> out (s^"\n")) l' in
  let _ = flush ostrm in
  let _ =
    (match l' with
      [] -> ()
    | ((thmname,p,c_opt)::rest) -> export_proof path theory_name thmname p c_opt rest) in
  let num_int_thms = next_counter() - 1 in
  let _ = out ((string_of_int num_int_thms)^"\n");(close_out ostrm) in
  ();;

let the_proof_database = ref ([]:(string*proof*(term option)) list);;

exception Duplicate_proof_name;;

let rec search_proof_name n db =
  match db with [] -> () | ((m, a, b)::db') -> if n=m then (raise Duplicate_proof_name) else search_proof_name n db'

let save_proof name p c_opt =
  let _ = search_proof_name name (!the_proof_database)
  in
  (the_proof_database :=
    (name, p, c_opt)::(!the_proof_database));;

let proof_database () = !the_proof_database;;

(* this is a little bit dangerous, because the function is not injective,
   but I guess one can live with that *)
let make_filesystem_compatible s =
  let modify = function
    | "/" -> "_slash_"
    | "\\" -> "_backslash_"
    | "=" -> "_equal_"
    | ">" -> "_greaterthan_"
    | "<" -> "_lessthan_"
    | "?" -> "_questionmark_"
    | "!" -> "_exclamationmark_"
    | "*" -> "_star_"
    | s -> s
  in
  implode (map modify (explode s));;

let export_saved_proofs thy =
  let context = rev (proof_database ()) in
  export_proofs thy (map (function (s,p,c) -> (make_filesystem_compatible s,p,c)) context);;

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty

  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)

  let the_term_constants =
     ref ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])])]

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty)
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false

(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of a) = 0
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)

  let freesl tml = itlist (union o frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | _ -> Pervasives.compare tm v = 0

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)

  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Pervasives.compare (type_of t) y = 0
                        | _ -> false) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)

  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0
                       then if Pervasives.compare x2 t2 = 0
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c,_)) = (asl,c)

  let hyp (Sequent(asl,c,_)) = asl

  let concl (Sequent(asl,c,_)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],safe_mk_eq tm tm, proof_REFL tm)

  let TRANS (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,
                                             Comb(eql,r),
                                             proof_TRANS(p1,p2))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1,p1),Sequent(asl2,c2,p2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)),
                        proof_MK_COMB (p1,p2))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c,p)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)),proof_ABS vp)
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod,proof_BETA tm)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],
                                                                tm,
                                                                proof_ASSUME tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq,p1)) (Sequent(asl2,c,p2)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r,proof_EQ p1 p2)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1,p1)) (Sequent(asl2,c2,p2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2', safe_mk_eq c1 c2, proof_DEDUCT_ANTISYM_RULE (p1,c1) (p2,c2))

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c,p)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c,proof_INST_TYPE theta p)

  let INST theta (Sequent(asl,c,p)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c,proof_INST theta p)

(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let axname = new_axiom_name "" in
      let p = proof_new_axiom (axname) tm in
      let th = Sequent([],tm,p) in
       (the_axioms := th::(!the_axioms);
        save_proof axname p (Some tm);
        th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)

  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
        let p = proof_new_definition cname ty r in
        let concl = safe_mk_eq c r in
        save_proof ("DEF_"^cname) p (Some concl);
             let dth = Sequent([],concl,p) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"

(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    let ax1 = safe_mk_eq (Comb(abs,mk_comb(rep,a))) a in
    let ax2 = safe_mk_eq (Comb(P,r))
                          (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r)
    let tp = proof_new_basic_type_definition tyname
                                             (absname, repname)
                                             (P,x)
                                             p in
    let tname = "TYDEF_"^tyname in
    save_proof tname tp None;
    Sequent([],ax1,proof_CONJUNCT1 tp),
    Sequent([],ax2,proof_CONJUNCT2 tp)

(* ------------------------------------------------------------------------- *)
(* Dealing with proof objects.                                               *)
(* ------------------------------------------------------------------------- *)

  let substitute_proof =
    fun (Sequent (asl, c, p)) pnew -> Sequent (asl, c, pnew)

  let equals_thm (Sequent (p1,c1,_)) (Sequent (p2,c2,_)) =
    (p1 = p2) && (c1 = c2)

  let le_thm (Sequent (p1,c1,_)) (Sequent (p2,c2,_)) = (p1, c1) <= (p2, c2)

  let less_thm (Sequent (p1, c1,_)) (Sequent (p2, c2,_)) = (p1, c1) < (p2, c2)

  let proof_of (Sequent(_,_,p)) = p

  let save_thm name th =
    (save_proof name (proof_of th) (Some (concl th)); th)

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;
