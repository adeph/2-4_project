(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

let rec def_term (t : S.term) : T.term =
  match t with
  | S.Exit ->
      T.Exit
  | S.Print (v, t) ->
      let v' = def_value v in
      let t' = def_term t in
      T.Print (v', t')
  | S.LetVal (x, v, t) ->
      let v' = def_value v in
      let t' = def_term t in
      T.LetVal (x, v', t')
  | _ ->
      assert false

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


let defun_term (t : S.term) : T.program =
  let t' = def_term t in
  T.Prog ([], t')
