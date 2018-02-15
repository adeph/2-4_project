(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

(* Rename x as y in t. Needed in the CPS translation to avoid capture of variables. *)
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
  | S.Cond (v, t, u) ->
      let v_r = ren v x y in
      let t_r = ren t x y in
      let u_r = ren u x y in
      S.Cond (v_r, t_r, u_r)
  | _ ->
      t

(* This is the one-pass CPS translation described by Danvy and Filinski in their 1991 paper. *)
let rec cps_transform (t : S.term) (k : S.term -> S.term) : S.term =
  match t with
  | S.Var x ->
      k (S.Var x)
  | S.Lam (self, x, t) ->
      let k' = Atom.fresh "k" in
      let t_tr = cps_transform t in
      k (S.Lam (self, x, S.Lam (S.NoSelf, k', t_tr (fun m ->
        S.App (S.Var k', m)))))
  | S.App (t, u) ->
      let k' = Atom.fresh "a" in
      let t_tr = cps_transform t in
      let u_tr = cps_transform u in
      t_tr (fun m ->
        u_tr (fun n ->
          S.App ((S.App (m, n)), (S.Lam (S.NoSelf, k', k (S.Var k'))))))
  | S.Lit i ->
      k (S.Lit i)
  | S.BinOp (t, op, u) ->
      let t_tr = cps_transform t in
      let u_tr = cps_transform u in
      t_tr (fun m ->
        u_tr (fun n -> k (S.BinOp (m, op, n))))
  | S.Print t ->
      let t_tr = cps_transform t in
      t_tr (fun m ->
        k (S.Print m))
  | S.Let (x, t, u) ->
      (* x is renamed in u because it could be captured in the context k. *)
      let y = Atom.fresh "x" in
      let t_tr = cps_transform t in
      let u_tr = cps_transform (ren u x y) in
      t_tr (fun n ->
        S.Let (y, n, u_tr k))
  | S.Cond (v, t, u) ->
      (* Introducing a let-in to avoid duplicating k. *)
      let k' = Atom.fresh "k" in
      let a = Atom.fresh "a" in
      let v_tr = cps_transform v in
      let t_tr = cps_transform t in
      let u_tr = cps_transform u in
      S.Let (k', S.Lam (S.NoSelf, a, k (S.Var a)),
      v_tr (fun p ->
        S.Cond (p,
        t_tr (fun m -> S.App (S.Var k', m)),
        u_tr (fun n -> S.App (S.Var k', n)))))


(* Actual translation; to be called after the CPS function, so that every rhs in an
 * application is a value. *)
let rec tail_term (t : S.term) (k : T.term -> T.term) : T.term =
  match t with
  | S.Lam _ | S.Lit _ | S.BinOp _ ->
      (* Output value of a term; discarded *)
      k T.Exit
  | S.Var _ | S.App _ ->
      tail_call t [] k
  | S.Print t ->
      k (tail_value t (fun v ->
        T.Print (v, T.Exit)))
  | S.Let (x, t, u) ->
      tail_arg t (fun a ->
        tail_term (ren u x a) k)
  | S.Cond (v, t, u) ->
      tail_value v (fun p ->
        tail_term t (fun m ->
          tail_term u (fun n ->
            k (T.Cond (p, m, n)))))

and tail_value (t : S.term) (k : T.value -> T.term) : T.term =
  match t with
  | S.Lam _ | S.App _ | S.Let _ | S.Cond _ ->
      assert false
  | S.Var x ->
      k (T.VVar x)
  | S.Lit i ->
      k (T.VLit i)
  | S.BinOp (t, op, u) ->
      tail_value t (fun v ->
        tail_value u (fun v' ->
          k (T.VBinOp (v, op, v'))))
  | S.Print t ->
      tail_value t (fun v ->
        T.Print (v, k v))

and tail_block (t : S.term) (s : S.self) (args : T.variable list) (k : T.block -> T.term) : T.term =
  match t with
  | S.Lam (S.NoSelf, x, t) ->
      tail_block t s (x :: args) k
  | _ ->
      let t' = tail_term t (fun k -> k) in
      k (T.Lam (s, args, t'))

and tail_call (t : S.term) (pi : T.value list) (k : T.term -> T.term) : T.term =
  match t with
  | S.Var x ->
      k (T.TailCall (T.VVar x, List.rev pi))
  | S.App (t, u) ->
      tail_arg u (fun a ->
        tail_call t ((T.VVar a) :: pi) k)
  | S.Lam _ ->
      tail_arg t (fun f ->
        k (T.TailCall (T.VVar f, List.rev pi)))
  | _ ->
      assert false

and tail_arg (t : S.term) (k : T.variable -> T.term) : T.term =
  match t with
  | S.Lam (self, x, t) ->
      let f = Atom.fresh "f" in
      tail_block t self [x] (fun b ->
        T.LetBlo (f, b, k f))
  | _ ->
      let a = Atom.fresh "a" in
      tail_value t (fun v ->
        T.LetVal (a, v, k a))


let cps_term (t : S.term) : T.term =
  let t' = cps_transform t (fun k -> k) in
  let t'' = tail_term t' (fun k -> k) in
  t''
