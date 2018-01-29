(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

(* Rename x as y in t. Needed in the CPS translation of let-expressions. *)
let rec ren (t : S.term) (x : Atom.atom) (y : Atom.atom) : S.term =
  match t with
  | S.Var z when z == x ->
      S.Var y
  | S.Lam (S.Self f, z, t) when f <> x && z <> x ->
      let t_r = ren t x y in
      S.Lam (S.Self f, z, t_r)
  | S.Lam (S.NoSelf, z, t) when z <> x ->
      let t_r = ren t x y in
      S.Lam (S.NoSelf, z, t_r)
  | S.App (t, u) ->
      let t_r = ren t x y in
      let u_r = ren u x y in
      S.App (t_r, u_r)
  | S.BinOp (t, op, u) ->
      let t_r = ren t x y in
      let u_r = ren u x y in
      S.BinOp (t_r, op, u_r)
  | S.Print t ->
      let t_r = ren t x y in
      S.Print t_r
  | S.Let (z, t, u) when z <> x ->
      let t_r = ren t x y in
      let u_r = ren u x y in
      S.Let (z, t_r, u_r)
  | _ ->
      t

(* This is the one-pass CPS translation described by Danvy and Filinski in their 1991 paper. *)
let rec cps_transform (t : S.term) : (S.term -> S.term) -> S.term =
  match t with
  | S.Var x ->
      fun k -> k (S.Var x)
  | S.Lam (self, x, t) ->
      let k2 = Atom.fresh "k" in
      let t_tr = cps_transform t in
      fun k1 -> k1 (S.Lam (self, x, S.Lam (S.NoSelf, k2, t_tr (fun m -> S.App (S.Var k2, m)))))
  | S.App (t, u) ->
      let k2 = Atom.fresh "a" in
      let t_tr = cps_transform t in
      let u_tr = cps_transform u in
      fun k1 -> t_tr (fun m -> u_tr (fun n -> S.App ((S.App (m, n)), (S.Lam (S.NoSelf, k2, k1 (S.Var k2))))))
  | S.Lit i ->
      fun k -> k (S.Lit i)
  | S.BinOp (t, op, u) ->
      let t_tr = cps_transform t in
      let u_tr = cps_transform u in
      fun k -> t_tr (fun m -> u_tr (fun n -> k (S.BinOp (m, op, n))))
  | S.Print t ->
      let t_tr = cps_transform t in
      fun k -> t_tr (fun m -> k (S.Print m))
  | S.Let (x, t, u) ->
      (* x is renamed in u because it could be captured in the term k. *)
      let y = Atom.fresh "x" in
      let t_tr = cps_transform t in
      let u_tr = cps_transform (ren u x y) in
      fun k -> t_tr (fun n -> S.Let (y, n, u_tr k))


(* Actual translation; to be called after the CPS function, so that every rhs in an
 * application is a value. *)
let rec tc_term (t : S.term) : T.term =
  match t with
  | S.Print t ->
      let vt = tc_val t in
      let t' = tc_term t in
      T.Print (vt, t')
  | S.Var _ | S.Lit _ | S.BinOp _ ->
      T.Exit
  | _ ->
      tc_call t []

and tc_val (t : S.term) : T.value =
  match t with
  | S.Var x ->
      T.VVar x
  | S.Lit i ->
      T.VLit i
  | S.BinOp (t, op, u) ->
      let vt = tc_val t in
      let ut = tc_val u in
      T.VBinOp (vt, op, ut)
  | S.Print t ->
      tc_val t
  | _ ->
      assert false

(* tc_call evaluates expressions of the form f a1 .. an recursively. Arguments ai are treated as values
 * and eventually declared in let-expressions. The head f is read last (terminal case). *)
and tc_call (t : S.term) (vs : T.value list) : T.term =
  match t with
  | S.Var x ->
      T.TailCall (T.VVar x, vs)
  | S.App (t, u) ->
      let decl, x = tc_arg u in
      let t' = tc_call t (T.VVar x :: vs) in
      decl t'
  | _ ->
      assert false

and tc_arg (t : S.term) : (T.term -> T.term ) * Atom.atom =
  match t with
  | S.Lam _ ->
      assert false
  | S.App _ ->
      assert false
  | _ ->
      let x = Atom.fresh "x" in
      let v = tc_val t in
      (fun t' -> T.LetVal (x, v, t')), x


let cps_term (t : S.term) : T.term =
  let cps_t = cps_transform t (fun k -> k) in
  let tc_t = tc_term cps_t in
  tc_t
