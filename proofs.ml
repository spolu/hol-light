let rec term_string tm =
  match tm with
    Var(v,_) -> Printf.sprintf "v%s" v
  | Const(c,_) -> Printf.sprintf "c%s" c
  | Comb(t1,t2) -> Printf.sprintf "C(%s,%s)" (term_string t1) (term_string t2)
  | Abs(t1,t2) -> Printf.sprintf "A(%s,%s)" (term_string t1) (term_string t2)

let thm_string th =
  let asl,tm = dest_thm th in
  let rec asl_string asl =
    match asl with
      [] -> ""
    | tm::[] -> Printf.sprintf("%s") (term_string tm)
    | tm::tail -> Printf.sprintf("%s,%s") (term_string tm) (asl_string tail)
  in Printf.sprintf "T([%s],%s)" (asl_string asl) (term_string tm)

let rec inst_string insts =
  match insts with
    [] -> ""
  | (t1,t2)::[] -> Printf.sprintf "I(%s,%s)"
                                  (term_string t1)
                                  (term_string t2)
  | (t1,t2)::tail -> Printf.sprintf "I(%s,%s),%s"
                                    (term_string t1)
                                    (term_string t2)
                                    (inst_string tail)

let proof_index proof =
  let Proof(idx,_,_) = proof in idx

let proof_content_string content =
  match content with
    Prefl(tm) -> Printf.sprintf "REFL(%s)"
                                (term_string tm)
  | Ptrans(p1,p2) -> Printf.sprintf "TRANS(%d,%d)"
                                    (proof_index p1)
                                    (proof_index p2)
  | Pmkcomb(p1,p2) -> Printf.sprintf "MK_COMB(%d,%d)"
                                     (proof_index p1)
                                     (proof_index p2)
  | Pabs(p1,tm) -> Printf.sprintf "ABS(%d,%s)"
                                  (proof_index p1)
                                  (term_string tm)
  | Pbeta(tm) -> Printf.sprintf "BETA(%s)"
                                (term_string tm)
  | Passume(tm) -> Printf.sprintf "ASSUME(%s)"
                                  (term_string tm)
  | Peqmp(p1,p2) -> Printf.sprintf "EQ_MP(%d,%d)"
                                   (proof_index p1)
                                   (proof_index p2)
  | Pdeduct(p1,p2) -> Printf.sprintf "DEDUCT_ANTISYM_RULE(%d,%d)"
                                     (proof_index p1)
                                     (proof_index p2)
  | Pinst(p1,insts) -> Printf.sprintf "INST(%d,[%s])"
                                      (proof_index p1)
                                      (inst_string insts)
  | Pinstt(p1,insts) -> Printf.sprintf "INST_TYPE(%d)"
                                       (proof_index p1)
  | Paxiom(tm) -> Printf.sprintf "AXIOM(%s)"
                                 (term_string tm)
  | Pdef(tm,name,ty) -> Printf.sprintf "DEFINITION(%s,%s)"
                                       (term_string tm)
                                       name
  | Pdeft(p1,tm,name,ty) -> Printf.sprintf "TYPE_DEFINITION(%d,%s,%s)"
                                          (proof_index p1)
                                          (term_string tm)
                                          name
  | _ -> failwith "proof_content_string: unknown proof content"


let proof_string proof =
  let Proof(idx,thm,content) = proof in
  Printf.sprintf "PROOF(%d,%s)"
                 idx
                 (proof_content_string content);;

let theorem_string proof =
  let Proof(idx,thm,content) = proof in
  Printf.sprintf "THEOREM(%d,%s)"
                 idx
                 (thm_string thm);;


let dump_proofs filename =
  let foutc = open_out filename in
  (do_list (fun p -> Printf.fprintf foutc
                                    "%s\n"
                                    (proof_string p)) (proofs());
   flush foutc;
   close_out foutc);;

let dump_theorems filename =
  let foutc = open_out filename in
  (do_list (fun p -> Printf.fprintf foutc
                     "%s\n"
                     (theorem_string p)) (proofs());
   flush foutc;
   close_out foutc);;
