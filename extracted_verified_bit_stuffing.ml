type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 -> (match l with
             | Nil -> Nil
             | Cons (_, l0) -> skipn n0 l0)

(** val starts_with : bool list -> bool list -> bool **)

let rec starts_with a k =
  match a with
  | Nil -> (match k with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (ha, ta) ->
    (match k with
     | Nil -> True
     | Cons (hk, tk) ->
       (match eqb ha hk with
        | True -> starts_with ta tk
        | False -> False))

(** val stuff : bool list -> bool list **)

let rec stuff = function
| Nil -> Nil
| Cons (ha, ta) ->
  (match starts_with (Cons (ha, ta)) (Cons (True, (Cons (True, Nil)))) with
   | True ->
     app (Cons (True, (Cons (True, Nil)))) (Cons (False,
       (stuff (skipn (S (S O)) (Cons (ha, ta))))))
   | False -> Cons (ha, (stuff ta)))

(** val unstuff : bool list -> bool list **)

let rec unstuff = function
| Nil -> Nil
| Cons (ha, ta) ->
  (match starts_with (Cons (ha, ta)) (Cons (True, (Cons (True, Nil)))) with
   | True ->
     app (Cons (True, (Cons (True, Nil))))
       (unstuff (skipn (S (S (S O))) (Cons (ha, ta))))
   | False -> Cons (ha, (unstuff ta)))

(** val add_flags : bool list -> bool list **)

let add_flags a =
  app (Cons (False, (Cons (True, (Cons (True, (Cons (True, (Cons (False,
    Nil))))))))))
    (app a (Cons (False, (Cons (True, (Cons (True, (Cons (True, (Cons (False,
      Nil)))))))))))

(** val remove_end_flag : bool list -> bool list **)

let rec remove_end_flag a = match a with
| Nil -> Nil
| Cons (ha, ta) ->
  (match starts_with a (Cons (False, (Cons (True, (Cons (True, (Cons (True,
           (Cons (False, Nil)))))))))) with
   | True -> Nil
   | False -> Cons (ha, (remove_end_flag ta)))

(** val remove_flags : bool list -> bool list **)

let remove_flags a =
  match starts_with a (Cons (False, (Cons (True, (Cons (True, (Cons (True,
          (Cons (False, Nil)))))))))) with
  | True -> remove_end_flag (skipn (S (S (S (S (S O))))) a)
  | False -> Nil
