
(* Environment.ml *)
(* 2016 - Mickaël Laurent *)

open AST

module type T = sig

  type t

  val init : unit -> t

  val bottom : t
  val is_bottom : t -> bool

  val join : t -> t -> t
  val meet : t -> t -> t
  val widen : t -> t -> t

  val vars_list : t -> identifier list
  val unset : t -> variable -> t
  val equal : t -> t -> bool

  val assign : t -> variable -> expression -> t
  val echo : t -> expression -> t

  val assume : t -> expression -> t

  val print : t -> string

end

module Make(V : Value.T) : T = struct

  module Map = Mapext.Make
                 (struct type t = identifier
                   let compare = compare
                 end)

  (* --- Operations on maps/lists --- *)

  let keys map = List.map fst (Map.bindings map)

  let rec remove_all map keys = match keys with
    | [] -> map
    | e::lst -> Map.remove e (remove_all map lst)

  let rec keep_only_unbound_keys map keys = match keys with
    | [] -> []
    | key::lst when Map.mem key map -> keep_only_unbound_keys map lst
    | key::lst -> key::(keep_only_unbound_keys map lst)

  let rec keep_only_bound_keys map keys = match keys with
    | [] -> []
    | key::lst when Map.mem key map -> key::(keep_only_bound_keys map lst)
    | key::lst -> keep_only_bound_keys map lst

  (* ----------- BASICS ------------ *)

  type env = V.t Map.t

  type t = 
      | Env of env 
      | Bottom

  let bottom = Bottom

  let is_bottom = function
    | Bottom -> true
    | Env env -> false (* assumes no variable in env is bottom *)

  (* A clever constructor that assures the 
     above invariant is preserved *)
  let mk_env env = 
    if Map.exists (Utils.const V.is_bottom) env
    then Bottom
    else Env env

  let vars_list = function
    | Bottom -> []
    | Env e -> keys e

  let equal e1 e2 = match e1, e2 with
    | Bottom, Bottom -> true
    | Bottom, _ | _, Bottom -> false
    | Env e1, Env e2 -> Map.equal (fun x y -> x = y) e1 e2

  (* -- Operations on identifiers -- *)

  let rec is_child_of id parent = match id with
    | Group (name, pt) when pt=parent -> true
    | Group (name, pt) -> is_child_of pt parent
    | Name name -> false

  let rec is_direct_child_of id parent = match id with
    | Group (name, pt) when pt=parent -> true
    | _ -> false

  let remove_children_of env parent =
    remove_all env (List.filter (fun id -> is_child_of id parent) (keys env))

  (* --------- READ VALUE --------- *)

  let rec default_value_of env id = match id with
    | Group (_, parent) -> V.default_child (value_of_id env parent)
    | Name str -> V.top

  and value_of_id env id = if Map.mem id env then Map.find id env
    else default_value_of env id

  and value_of_var env var = match var with
    | Case parent -> V.default_child (general_value env parent)
    | Var id -> value_of_id env id

  and generalize_value env id ids = 
    let value = value_of_id env id
    in match value with
      | value when V.is_array value ->
          let direct_children = List.filter (fun key -> is_direct_child_of key id) ids
          in let general = List.fold_left (fun acc key -> V.join acc (generalize_value env key ids))
                             (V.default_child value) direct_children
          in V.value_array general
      | value -> value

  and general_value env var = match var with
    | Var id -> generalize_value env id (keys env)
    | Case _ -> value_of_var env var

  (* ----------- J.M.W ------------ *)

  let common_structure env1 env2 =
    let to_remove = keep_only_unbound_keys env2 (keys env1)
    and to_prepare = keep_only_bound_keys env2 (keys env1)
    in let env = List.fold_left (fun acc id -> Map.add id (generalize_value env1 id to_remove) acc) env1 to_prepare
    in remove_all env to_remove

  let rec _can_exists env id = match id with
    | Group (_, parent) -> if can_exists env parent
        then V.is_array (value_of_var env (Var parent))
        else false
    | Name str -> true

  and can_exists env id =
    if Map.mem id env then true
    else _can_exists env id

  let add_default_value env id = if can_exists env id
    then Map.add id (value_of_var env (Var id)) env
    else env

  let complete_structure env1 env2 =
    let to_add = keep_only_unbound_keys env1 (keys env2) in
      List.fold_left add_default_value env1 to_add

  let adapt_structure env1 env2 = common_structure (complete_structure env1 env2) (complete_structure env2 env1)

  (* map2z assume : f k d d = d *)
  let pointwise f bot a b = match a, b with
    | Bottom, x | x, Bottom -> bot x
    | Env m, Env n
      -> mk_env (Map.map2z (fun _ x y -> f x y) (adapt_structure m n) (adapt_structure n m))

  let join  = pointwise V.join  (Utils.id)
  let meet  = pointwise V.meet  (Utils.const Bottom)
  let widen = pointwise V.widen (Utils.id)

  (* ----------- EVAL ----------- *)

  let rec _isset env var = match var with
    | Var id -> if Map.mem id env then
          (if V.is_top (value_of_var env (Var id)) then V.value_unknow_bool () else V.value_bool true)
        else V.value_unknow_bool ()
    | Case _ -> V.value_unknow_bool ()

  let rec isset env vars = match vars with
    | [] -> V.value_bool true
    | var::lst -> V.logical_and (_isset env var) (isset env lst)

  let rec eval env expr = match expr with
    | Bool b -> V.value_bool b
    | Int i -> V.value_int i i
    | Float f -> V.value_float f f
    | String s -> V.value_string V.Sane
    | Array _ -> V.value_array V.top
    | Value -> V.top

    | Variable v -> general_value env v

    | Identical (e1, e2) -> V.identical (eval env e1) (eval env e2)
    | NotIdentical (e1, e2) -> V.not_identical (eval env e1) (eval env e2)
    | Equal (e1, e2) -> V.equal (eval env e1) (eval env e2)
    | Different (e1, e2) -> V.different (eval env e1) (eval env e2)
    | Leq (e1, e2) -> V.leq (eval env e1) (eval env e2)
    | Geq (e1, e2) -> V.geq (eval env e1) (eval env e2)
    | Lower (e1, e2) -> V.lower (eval env e1) (eval env e2)
    | Greater (e1, e2) -> V.greater (eval env e1) (eval env e2)

    | Not e -> V.logical_not (eval env e)
    | And (e1, e2) -> V.logical_and (eval env e1) (eval env e2)
    | Or (e1, e2) -> V.logical_or (eval env e1) (eval env e2)

    | Multiplied (e1, e2) -> V.mul (eval env e1) (eval env e2)
    | Divided (e1, e2) -> V.div (eval env e1) (eval env e2)
    | Plus (e1, e2) -> V.add (eval env e1) (eval env e2)
    | Minus (e1, e2) -> V.sub (eval env e1) (eval env e2)
    | Modulo (e1, e2) -> V.modulo (eval env e1) (eval env e2)
    | Concat (e1, e2) -> V.concat (eval env e1) (eval env e2)

    | ToBool e -> V.to_bool (eval env e)
    | ToInt e -> V.to_int (eval env e)
    | ToFloat e -> V.to_float (eval env e)
    | ToString e -> V.to_string (eval env e)
    | ToArray e -> V.to_array (eval env e)

    | Isset vars -> isset env vars
    | Sanitize e -> if V.is_sanitizable (eval env e)
        then V.value_string V.Sane
        else Utils.error "[DISAPPROVED] Trying to sanitize a non-sanitizable value"
    | StringInput -> V.value_string V.Unsane
    | IntInput (e1, e2) -> V.parse_value_int (eval env e1) (eval env e2)
    | FloatInput (e1, e2) -> V.parse_value_float (eval env e1) (eval env e2)
    | ExprFunction (name, args) -> V.top

  (* --------- ASSIGN VALUE ---------- *)

  let set_value env id value = 
    let env = remove_children_of env id
    in Map.add id value env

  let rec assign_id_value env id value = match id with
    | Name _ -> set_value env id value
    | Group (_, parent) -> let value_parent = value_of_var env (Var parent)
        in if V.is_array value_parent
          then (
            let env = if not(Map.mem parent env) then assign_id_value env parent value_parent else env
            in set_value env id value
          ) else if not(V.is_top value_parent) then (
            Utils.error "[ERROR] Trying to assign child to a non-array value"
          ) else env

  let rec assign_value env var value = match env, var with
    | Bottom, _ -> Bottom
    | Env env, Var id -> mk_env (assign_id_value env id value)
    | Env env, Case parent -> let value_parent = value_of_var env parent
        in if V.is_array value_parent
          then (
            assign_value (Env env) parent (V.join (V.value_array value) (general_value env parent))
          ) else if not(V.is_top value_parent) then (
            Utils.error "[ERROR] Trying to assign case of a non-array value"
          ) else Env env


  let assign env var expr = match env with
    | Bottom -> Bottom
    | Env env -> assign_value (Env env) var (eval env expr)

  (* ----------- ASSUME ------------ *)

  (* TODO: Some simplifications (expr=true, expr=false->Not, (double) var isolation...) *)
  let rec simplify expr = match expr with
    (* Not + Logical operations *)
    | Not (And (e1, e2)) -> simplify (Or (Not e1, Not e2))
    | Not (Or (e1, e2)) -> simplify (And (Not e1, Not e2))
    (* Logical operations *)
    | And (e1, e2) -> And (simplify e1, simplify e2)
    | Or (e1, e2) -> Or (simplify e1, simplify e2)
    (* Not + (In)equalities *)
    | Not (Identical (e1, e2)) -> simplify (NotIdentical (e1, e2))
    | Not (NotIdentical (e1, e2)) -> simplify (Identical (e1, e2))
    | Not (Equal (e1, e2)) -> simplify (Different (e1, e2))
    | Not (Different (e1, e2)) -> simplify (Equal (e1, e2))
    | Not (Leq (e1, e2)) -> simplify (Greater (e1, e2))
    | Not (Geq (e1, e2)) -> simplify (Lower (e1, e2))
    | Not (Lower (e1, e2)) -> simplify (Geq (e1, e2))
    | Not (Greater (e1, e2)) -> simplify (Leq (e1, e2))
    (* (In)equalities *)
    | Identical (e1, e2) -> Identical (simplify e1, simplify e2)
    | NotIdentical (e1, e2) -> NotIdentical (simplify e1, simplify e2)
    | Equal (e1, e2) -> Equal (simplify e1, simplify e2)
    | Different (e1, e2) -> Different (simplify e1, simplify e2)
    | Leq (e1, e2) -> Leq (simplify e1, simplify e2)
    | Geq (e1, e2) -> Geq (simplify e1, simplify e2)
    | Lower (e1, e2) -> Lower (simplify e1, simplify e2)
    | Greater (e1, e2) -> Greater (simplify e1, simplify e2)
    (* Not *)
    | Not (Not e) -> simplify e
    | Not e -> Not (simplify e)
    | expr -> expr

  let assume_comparison env lf rf f e1 e2 = match e1, e2 with
    | Variable var1, Variable var2
      -> meet (assign_value (Env env) var1 (lf (eval env e1) (eval env e2)))
           (assign_value (Env env) var2 (rf (eval env e2) (eval env e1)))
    | Variable var, e2
      -> assign_value (Env env) var (lf (eval env e1) (eval env e2))
    | e1, Variable var
      -> assign_value (Env env) var (rf (eval env e2) (eval env e1))
    | e1, e2 -> if V.is_false (f (eval env e1) (eval env e2)) then Bottom else Env env

  let rec assume env expr = match env with
    | Bottom -> Bottom
    | Env env -> (
        match (simplify expr) with
          | And (e1, e2) -> meet (assume (Env env) e1) (assume (Env env) e2)
          | Or (e1, e2) -> join (assume (Env env) e1) (assume (Env env) e2)
          | Identical (e1, e2) ->
              assume_comparison env V.assume_identical V.assume_identical V.identical e1 e2
          | NotIdentical (e1, e2) ->
              assume_comparison env V.assume_not_identical V.assume_not_identical V.not_identical e1 e2
          | Equal (e1, e2) ->
              assume_comparison env V.assume_equal V.assume_equal V.equal e1 e2
          | Different (e1, e2) ->
              assume_comparison env V.assume_different V.assume_different V.different e1 e2
          | Leq (e1, e2) ->
              assume_comparison env V.assume_leq V.assume_geq V.leq e1 e2
          | Geq (e1, e2) ->
              assume_comparison env V.assume_geq V.assume_leq V.geq e1 e2
          | Lower (e1, e2) ->
              assume_comparison env V.assume_lower V.assume_greater V.lower e1 e2
          | Greater (e1, e2) ->
              assume_comparison env V.assume_greater V.assume_lower V.greater e1 e2
          | Not (expr) -> 
              assume_comparison env V.assume_equal V.assume_equal V.equal expr (Bool false)
          | expr -> 
              assume_comparison env V.assume_equal V.assume_equal V.equal expr (Bool true)
      )

  (* ----------- MISC ------------ *)

  let unset env var = match env, var with
    | Bottom, _ -> Bottom
    | Env env, Var (Name name) -> mk_env (Map.remove (Name name) (remove_children_of env (Name name)))
    | Env env, _ -> assign_value (Env env) var V.top

  let init _ = let env = Env Map.empty
    in let env = assign_value env (Var (Name "_POST")) (V.value_array (V.value_string V.Unsane))
    in let env = assign_value env (Var (Name "_GET")) (V.value_array (V.value_string V.Unsane))
    in let env = assign_value env (Var (Name "_SERVER")) (V.value_array (V.value_string V.Unsane))
    in let env = assign_value env (Var (Name "_SESSION")) (V.value_array (V.value_string V.Sane))
    in env

  let echo env expr = match env with
    | Bottom -> Bottom
    | Env env -> if V.is_sane (eval env expr) then Env env
        else Utils.error "[DISAPPROVED] Trying to print a non-sane value"

  (* ----------- PRINT ------------ *)

  let rec print_id id = match id with
    | Name n -> n
    | Group (n, id) -> (print_id id)^"."^n

  let print_comp acc (id, value) = acc^(print_id id)^" : "^(V.print value)^"\n"

  let print t = match t with
    | Bottom -> "Bottom\n"
    | Env e -> let bindings = Map.bindings e in
          List.fold_left print_comp "Env :\n" bindings

end
