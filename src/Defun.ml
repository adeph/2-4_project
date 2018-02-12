(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

let cons x l = x :: l

let rec init (n : int) (mk_elt : unit -> 'a) : 'a list =
  if n > 0 then
    let h = mk_elt () in
    let t = init (n-1) mk_elt in
    h :: t
  else []

(* The defunctionalized program consists in a series of
 * 'apply' functions declarations, each of which is just a
 * switch on its first argument. A call 'apply (f, x1, .., xn)'
 * corresponds to a call 'f x1 .. xn' where f is a first-class
 * function. *)

(* All apply functions are built incrementally during the parsing
 * of the whole program. A special type 'preapply' is used to
 * represent an apply function under construction; an environment
 * is a mapping from integers to pre-apply functions (the binding at
 * n is the function that takes n+1 arguments); finally, a state
 * contains an environment and a tag counter which is incremented
 * each time a new branch is built somewhere. *)

module Env =
  Map.Make(struct type t = int let compare = compare end)

type preapply = T.variable * (T.variable list) * (T.branch list)

type state =
  { tag_count : int ;
    env : preapply Env.t
  }


let mk_preapply (nargs : int) () : preapply =
  let f = Atom.fresh "apply" in
  let y = Atom.fresh "f" in
  let xs = init nargs (fun () -> Atom.fresh "x") in
  (f, y :: xs, [])

(* Side-effect: If the apply function is not found, a new one with
 * no branches is created and added in the environment. *)
let find_apply (nargs : int) (s : state) : state * preapply =
  let env = s.env in
  try
    s, Env.find nargs env
  with Not_found ->
    let app = mk_preapply nargs () in
    { s with env = Env.add nargs app env }, app

let build_apply (pa : preapply) : T.function_declaration =
  let (f, xs, bs) = pa in
  T.Fun (f, xs, T.Swi (T.VVar (List.hd xs), bs))

let init_state () =
  { tag_count = 0 ;
    env = Env.empty
  }


let rec def_term (t : S.term) (s : state) : state * T.term =
  match t with
  | S.Exit ->
      s, T.Exit
  | S.TailCall (v, vs) ->
      let n = List.length vs in
      let s', (f, _, _) = find_apply n s in
      s', T.TailCall (f, v :: vs)
  | S.Print (v, t) ->
      let v' = def_value v in
      let s', t' = def_term t s in
      s', T.Print (v', t')
  | S.LetVal (x, v, t) ->
      let v' = def_value v in
      let s', t' = def_term t s in
      s', T.LetVal (x, v', t')
  | S.LetBlo (f, b, t) ->
      let s', b' = def_block b s in
      let s'', t' = def_term t s' in
      s'', T.LetBlo (f, b', t')

and def_value (t : S.value) : T.value =
  match t with
  | S.VVar x ->
      T.VVar x
  | S.VLit i ->
      T.VLit i
  | S.VBinOp (t, op, u) ->
      let t' = def_value t in
      let u' = def_value u in
      T.VBinOp (t', op, u')

and def_block (b : S.block) (s : state) : state * T.block =
  match b with
  | S.Lam (S.NoSelf, xs, t) ->
      let fv = S.fv_lambda xs t in
      let ys = Atom.Set.fold cons fv [] in
      let s', i = new_branch xs ys t s in
      s', T.Con (i, T.vvars ys)
  | S.Lam (S.Self _, _, _) ->
      assert false

(* Updates current state with a new branch. This branch is added
 * in the apply function for |xs| arguments. A fresh tag i is generated,
 * the new branch is _i ys -> t'_, where t' is t translated.
 * i is returned along with the new state. *)
and new_branch
    (xs : S.variable list) (ys : S.variable list)
    (t : S.term) (s : state) : state * T.tag =
  let i = s.tag_count in
  let n = List.length xs in

  (* The body-term must be translated first.
   * Indeed, if we fetched the apply function now, then all updates
   * in that apply done by _def_term t_ would be overwritten and lost
   * by the end of the current call. *)
  let s', t' = def_term t { s with tag_count = i+1 } in
  let s'', (f, zs, bl) = find_apply n s' in

  let t'' = T.sequential_let xs (T.vvars (List.tl zs)) t' in
  let bl' = (T.Branch (i, ys, t'')) :: bl in
  let app = (f, zs, bl') in
  { s'' with env = Env.add n app s''.env }, i


let defun_term (t : S.term) : T.program =
  let si = init_state () in
  let sf, t' = def_term t si in
  let env = Env.map build_apply sf.env in
  let fun_decls = Env.fold (fun _ -> cons) env [] in
  T.Prog (fun_decls, t')
