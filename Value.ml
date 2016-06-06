
(* Value.ml *)
(* 2016 - Mickaël Laurent *)

module type T = sig

  type t
  (* Sane = Not dangerous (can be sanitized or not) *)
  (* Unsane = Can be dangerous (not sanitized)  *)
  (* Unknow_sanity = Can be dangerous (can be sanitized or not)  *)
  type sanity_state = | Sane | Unsane | Unknow_sanity

  val top : t
  val bottom : t

  val value_bool : bool -> t
  val value_unknow_bool : unit -> t
  val value_int : int -> int -> t
  val parse_value_int : t -> t -> t
  val value_float : float -> float -> t
  val parse_value_float : t -> t -> t
  val value_string : sanity_state -> t
  val value_array : t -> t

  val is_bottom : t -> bool
  val is_top : t -> bool
  val is_sanitizable : t -> bool
  val is_sane : t -> bool
  val default_child : t -> t
  val is_array : t -> bool
  val is_true : t -> bool
  val is_false : t -> bool

  val join : t -> t -> t
  val meet : t -> t -> t
  val widen : t -> t -> t

  val to_bool : t -> t
  val to_int : t -> t
  val to_float : t -> t
  val to_string : t -> t
  val to_array : t -> t

  val neg : t -> t
  val add : t -> t -> t (* For numbers and arrays *)
  val sub : t -> t -> t
  val inv : t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val modulo : t -> t -> t

  val concat : t -> t -> t (* Operator '.' : Concat strings *)

  val logical_not : t -> t
  val logical_and : t -> t -> t
  val logical_or : t -> t -> t

  val equal : t -> t -> t
  val different : t -> t -> t
  val identical : t -> t -> t
  val not_identical : t -> t -> t
  val leq : t -> t -> t
  val geq : t -> t -> t
  val lower : t -> t -> t
  val greater : t -> t -> t

  val assume_equal : t -> t -> t
  val assume_different : t -> t -> t
  val assume_identical : t -> t -> t
  val assume_not_identical : t -> t -> t
  val assume_leq : t -> t -> t
  val assume_geq : t -> t -> t
  val assume_lower : t -> t -> t
  val assume_greater : t -> t -> t

  val print : t -> string

end;;

module Mixed : T = struct

  type sanity_state = | Sane | Unsane | Unknow_sanity

  type 'a bound = | Val of 'a
                  | Pinf
                  | Minf

  let bound_min b1 b2 = match b1, b2 with
    | Minf, _ | _, Minf -> Minf
    | Pinf, b | b, Pinf -> b
    | Val v1, Val v2 when v1<v2 -> Val v1
    | Val v1, Val v2 -> Val v2
  let bound_max b1 b2 = match b1, b2 with
    | Pinf, _ | _, Pinf -> Pinf
    | Minf, b | b, Minf -> b
    | Val v1, Val v2 when v1>v2 -> Val v1
    | Val v1, Val v2 -> Val v2

  let bound_leq b1 b2 = match b1, b2 with
    | Minf, _ -> true
    | _, Minf -> false
    | _, Pinf -> true
    | Pinf, _ -> false
    | Val v1, Val v2 -> (v1<=v2)
  let bound_greater b1 b2 = not (bound_leq b1 b2)
  let bound_geq b1 b2 = (bound_greater b1 b2) || (b1 = b2)
  let bound_lower b1 b2 = not (bound_geq b1 b2)

  let rec bound_min_lst lst = match lst with
    | [e] -> e
    | e::lst -> bound_min e (bound_min_lst lst)
    | [] -> Pinf

  let rec bound_max_lst lst = match lst with
    | [e] -> e
    | e::lst -> bound_max e (bound_max_lst lst)
    | [] -> Minf

  let int_bound_abs b = match b with
    | Minf | Pinf -> Pinf
    | Val v when v < 0 -> Val (-v)
    | Val v -> Val v

  let int_bound_sign b neg pos = match b with
    | Minf -> neg
    | Pinf -> pos
    | Val v when v = 0 -> Val (0)
    | Val v when v < 0 -> neg
    | _ -> pos
  let float_bound_sign b neg pos = match b with
    | Minf -> neg
    | Pinf -> pos
    | Val v when v = 0. -> Val (0.)
    | Val v when v < 0. -> neg
    | _ -> pos

  let int_bound_neg b = match b with
    | Minf -> Pinf
    | Pinf -> Minf
    | Val v -> Val (-v)
  let float_bound_neg b = match b with
    | Minf -> Pinf
    | Pinf -> Minf
    | Val v -> Val (0. -. v)

  let int_bound_add b1 b2 = match b1, b2 with
    | Minf, _ | _, Minf -> Minf
    | Pinf, _ | _, Pinf -> Pinf
    | Val v1, Val v2 -> Val (v1+v2)
  let float_bound_add b1 b2 = match b1, b2 with
    | Minf, _ | _, Minf -> Minf
    | Pinf, _ | _, Pinf -> Pinf
    | Val v1, Val v2 -> Val (v1+.v2)

  let int_bound_mul b1 b2 = match b1, b2 with
    | Minf, v | v, Minf -> (match int_bound_sign v Minf Pinf with
                             | Pinf -> Minf
                             | Minf -> Pinf
                             | Val x -> Val 0)
    | Pinf, v | v, Pinf -> (match int_bound_sign v Minf Pinf with
                             | Pinf -> Pinf
                             | Minf -> Minf
                             | Val x -> Val 0)
    | Val v1, Val v2 -> Val (v1*v2)
  let float_bound_mul b1 b2 = match b1, b2 with
    | Minf, v | v, Minf -> (match float_bound_sign v Minf Pinf with
                             | Pinf -> Minf
                             | Minf -> Pinf
                             | Val x -> Val 0.)
    | Pinf, v | v, Pinf -> (match float_bound_sign v Minf Pinf with
                             | Pinf -> Pinf
                             | Minf -> Minf
                             | Val x -> Val 0.)
    | Val v1, Val v2 -> Val (v1*.v2)

  let int_bound_inv b neg = match b with
    | Val 0 -> if neg then Minf else Pinf
    | Val v -> Val (1./.(float_of_int v))
    | Minf | Pinf -> Val 0.

  let float_bound_inv b neg = match b with
    | Val 0. -> if neg then Minf else Pinf
    | Val v -> Val (1./.v)
    | Minf | Pinf -> Val 0.

  let bound_cast_to_float b = match b with
    | Val v -> Val (float_of_int v)
    | Minf -> Minf
    | Pinf -> Pinf

  let bound_cast_to_int b sup = match b, sup with
    | Val v, true -> if float_of_int (int_of_float v) < v
        then Val ((int_of_float v) + 1) else Val (int_of_float v)
    | Val v, false -> if float_of_int (int_of_float v) > v
        then Val ((int_of_float v) - 1) else Val (int_of_float v)
    | Minf, _ -> Minf
    | Pinf, _ -> Pinf

  type t = | Top (* one of the following types, or even null or another type *)
           | Bool of bool option
           | Int of (int bound) * (int bound)
           | Float of (float bound) * (float bound)
           | String of sanity_state
           | Array of t (* t represent the default data type for contained elements *)
           | Bottom

  let normalize t = match t with
    | Int (_, Minf) -> Bottom
    | Int (Pinf, _) -> Bottom
    | Int (b1, b2) when bound_leq b1 b2 -> Int(b1,b2)
    | Int _ -> Bottom
    | Float (_, Minf) -> Bottom
    | Float (Pinf, _) -> Bottom
    | Float (b1, b2) when bound_leq b1 b2 -> Float(b1,b2)
    | Float _ -> Bottom
    | t -> t

  let top = Top
  let bottom = Bottom

  let value_bool b = Bool (Some b)
  let value_unknow_bool _ = Bool None
  let value_int b1 b2 = normalize (Int (Val b1, Val b2))
  let parse_value_int b1 b2 = match b1, b2 with
    | Int (i1, _), Int (_, i2) -> normalize (Int (i1, i2))
    | Int (i1, _), _ -> normalize (Int (i1, Pinf))
    | _, Int (_, i2) -> normalize (Int (Minf, i2))
    | _, _ -> normalize (Int (Minf, Pinf))
  let value_float b1 b2 = normalize (Float (Val b1, Val b2))
  let parse_value_float b1 b2 = match b1, b2 with
    | Float (f1, _), Float (_, f2) -> normalize (Float (f1, f2))
    | Float (f1, _), _ -> normalize (Float (f1, Pinf))
    | _, Float (_, f2) -> normalize (Float (Minf, f2))
    | _, _ -> normalize (Float (Minf, Pinf))
  let value_string s = String s
  let value_array t = Array t


  (* ----- PROPERTIES ----- *)

  let is_bottom t = (t = Bottom)
  let is_top t = (t = Top)

  let is_sanitizable t1 = match t1 with
    | String Unsane -> true
    (*| String Unknow_sanity -> true*)
    | _ -> false

  let is_sane t1 = match t1 with
    | String Sane -> true
    | Bool _ -> true
    | Int _ -> true
    | Float _ -> true
    | _ -> false

  let default_child t = match t with
    | Bottom -> Bottom
    | Top -> Top
    | Array t -> t
    | _ -> Utils.error "[ERROR] Trying to access child of non-array variable !"

  let is_array t = match t with
    | Array _ -> true
    | _ -> false

  let is_true t = match t with
    | Bool (Some true) -> true
    | _ -> false

  let is_false t = match t with
    | Bool (Some false) -> true
    | _ -> false

  (* ----- J.M.W ----- *)

  let rec join t1 t2 = match t1, t2 with
    | Bottom, t | t, Bottom -> t
    | Top, _ | _, Top -> Top
    | t1, t2 when t1 = t2 -> t1
    | Int (l1, r1), Int (l2, r2) ->
        normalize (Int (bound_min l1 l2, bound_max r1 r2))
    | Float (l1, r1), Float (l2, r2) ->
        normalize (Float (bound_min l1 l2, bound_max r1 r2))
    | Bool _, Bool _ -> Bool None
    | String _, String _ -> String Unknow_sanity
    | Array t1, Array t2 -> Array (join t1 t2)
    | _, _ -> Top

  let rec meet t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Top, t | t, Top -> t
    | t1, t2 when t1 = t2 -> t1
    | Int (l1, r1), Int (l2, r2) ->
        normalize (Int (bound_max l1 l2, bound_min r1 r2))
    | Float (l1, r1), Float (l2, r2) ->
        normalize (Float (bound_max l1 l2, bound_min r1 r2))
    | Bool (None), Bool t | Bool t, Bool (None) -> Bool t
    | Bool _, Bool _ -> Bottom
    (* A string can sometimes be Unsane and assumed as Sane... *)
    | String Sane, String t | String t, String Sane -> String Sane
    | String _, String _ -> String Unsane
    | Array t1, Array t2 -> Array (meet t1 t2)
    | _, _ -> Top

  let rec widen t1 t2 = match t1, (join t1 t2) with
    | Top, _ | _, Top -> Top
    | Bottom, t | t, Bottom -> t
    | t1, t2 when t1 = t2 -> t2
    | Int (l1, r1), Int (l2, r2) when bound_lower l2 l1 && bound_greater r2 r1
      -> Int(int_bound_sign l2 Minf (Val(1)), int_bound_sign r2 (Val(-1)) Pinf)
    | Int (l1, r1), Int (l2, r2) when bound_lower l2 l1
      -> Int(int_bound_sign l2 Minf (Val(1)), r2)
    | Int (l1, r1), Int (l2, r2) when bound_greater r2 r1
      -> Int(l2, int_bound_sign r2 (Val(-1)) Pinf)
    | Int (l1, r1), Int (l2, r2) -> Int (l2, r2)
    | Float (l1, r1), Float (l2, r2) when bound_lower l2 l1 && bound_greater r2 r1
      -> Float(Minf, Pinf)
    | Float (l1, r1), Float (l2, r2) when bound_lower l2 l1 -> Float(Minf, r2)
    | Float (l1, r1), Float (l2, r2) when bound_greater r2 r1 -> Float(l2, Pinf)
    | Float (l1, r1), Float (l2, r2) -> Float (l2, r2)
    | Bool _, Bool _ -> Bool None
    | String _, String _ -> String Unknow_sanity
    | Array t1, Array t2 -> Array (widen t1 t2)
    | _, _ -> Top

  (* ----- CONVERTIONS ----- *)

  let to_bool t = match t with
    | Bottom -> Bottom
    | Bool _ -> t
    | Int (Val 0, Val 0) -> Bool (Some false)
    | Int _ when meet t (Int (Val 0, Val 0)) = Bottom -> Bool (Some true)
    | Float (Val 0., Val 0.) -> Bool (Some false)
    | Float _ when meet t (Float (Val 0., Val 0.)) = Bottom -> Bool (Some true)
    | _ -> Bool None

  let to_int t = match t with
    | Bottom -> Bottom
    | Int _ -> t
    | Bool (Some true) -> Int (Val 1, Val 1)
    | Bool (Some false) -> Int (Val 0, Val 0)
    | Bool None -> Int (Val 0, Val 1)
    | Float (a, b) -> Int (bound_cast_to_int a false, bound_cast_to_int b true)
    | _ -> Int (Minf, Pinf)

  let to_float t = match t with
    | Bottom -> Bottom
    | Float _ -> t
    | Int (a, b) -> Float (bound_cast_to_float a, bound_cast_to_float b)
    | _ -> Float (Minf, Pinf)

  let to_string t = match t with
    | Bottom -> Bottom
    | String _ -> t
    | Bool _ -> String Sane
    | Int _ -> String Sane
    | Float _ -> String Sane
    | _ -> String Unknow_sanity

  let to_array t = match t with
    | Bottom -> Bottom
    | Array _ -> t
    | _ -> Array Top

  (* ----- OPERATIONS ----- *)

  let neg t1 = match t1 with
    | Bottom -> Bottom
    | Int (b1,b2) -> Int(int_bound_neg b2, int_bound_neg b1)
    | Float (b1, b2) -> Float(float_bound_neg b2, float_bound_neg b1)
    | _ -> Top

  let rec add t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Array t1, Array t2 -> Array (join t1 t2)
    | Int (l1,r1), Int (l2,r2) -> Int(int_bound_add l1 l2, int_bound_add r1 r2)
    | Float (l1,r1), Float (l2,r2) ->
        Float(float_bound_add l1 l2, float_bound_add r1 r2)
    | (Int _ as i), (Float _ as f) | (Float _ as f), (Int _ as i) ->
        add f (to_float i)
    | _, _ -> Top

  let sub t1 t2 = add t1 (neg t2)

  let rec inv t1 =
    let neg_inv t1 =
      match t1 with
        | Bottom -> Bottom
        | Int (b1, b2) -> Float (int_bound_inv b2 true, int_bound_inv b1 true)
        | Float (b1, b2) -> Float (float_bound_inv b2 true, float_bound_inv b1 true)
        | _ -> Top
    and pos_inv t1 =
      match t1 with
        | Bottom -> Bottom
        | Int (b1, b2) -> Float (int_bound_inv b2 false, int_bound_inv b1 false)
        | Float (b1, b2) -> Float (float_bound_inv b2 false, float_bound_inv b1 false)
        | _ -> Top
    in match t1 with
      | Bottom -> Bottom
      | Int (b1, b2) ->
          let lp = meet t1 (Int (Minf, Val (-1)))
          and rp = meet t1 (Int (Val 1, Pinf))
          in join (neg_inv lp) (pos_inv rp)
      | Float (b1, b2) ->
          let lp = meet t1 (Float (Minf, Val 0.))
          and rp = meet t1 (Float (Val 0., Pinf))
          in join (neg_inv lp) (pos_inv rp)
      | _ -> Top

  let rec mul t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Int (l1,r1), Int (l2,r2) ->
        let lst = [int_bound_mul l1 l2; int_bound_mul l1 r2;
                   int_bound_mul r1 l2; int_bound_mul r1 r2] in
          Int (bound_min_lst lst, bound_max_lst lst)
    | Float (l1,r1), Float (l2,r2) ->
        let lst = [float_bound_mul l1 l2; float_bound_mul l1 r2;
                   float_bound_mul r1 l2; float_bound_mul r1 r2] in
          Float (bound_min_lst lst, bound_max_lst lst)
    | (Int _ as i), (Float _ as f) | (Float _ as f), (Int _ as i) ->
        mul f (to_float i)
    | _, _ -> Top

  let div t1 t2 = mul t1 (inv t2)

  let modulo t1 t2 =
    let pos_mod t1 b = match t1 with
      | Bottom -> Bottom
      | Int (b1, b2) -> Int (Val 0, bound_min b2 b)
      | _ -> Top
    and neg_mod t1 b = match t1 with
      | Bottom -> Bottom
      | Int (b1, b2) -> Int (int_bound_neg (bound_min (int_bound_abs b1) b), Val 0)
      | _ -> Top
    in match t1, t2 with
      | Bottom, _ | _, Bottom -> Bottom
      | Int _, Int (b3, b4) ->
          let b = bound_max (int_bound_abs b3) (int_bound_abs b4)
          and lp = meet t1 (Int (Minf, Val 0))
          and rp = meet t1 (Int (Val 0, Pinf))
          in join (neg_mod lp b) (pos_mod rp b)
      | _, _ -> Top

  (* Assume that concatenate an integer (or float) to a string does not change with  his sanity state (sanitizing does not affect it) *)
  let concat t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | String a, String b when a = b -> String a
    | String _, String _ -> String Unknow_sanity
    | String a, Int _ | Int _, String a -> String a
    | String a, Float _ | Float _, String a -> String a
    | Float _, Float _ | Int _, Int _ | Float _, Int _ | Int _ , Float _ -> String Sane
    | _, _ -> Top

  let logical_not t1 = match t1 with
    | Bottom -> Bottom
    | Bool (None) -> Bool (None)
    | Bool (Some b) -> Bool (Some (not b))
    | _ -> Bool (None)

  let logical_and t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Bool (Some false), _ | _, Bool (Some false) -> Bool (Some false)
    | Bool (Some true), Bool (Some true) -> Bool (Some true)
    | Bool _, Bool _ -> Bool (None)
    | _, _ -> Bool (None)

  let logical_or t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Bool (Some true), _ | _, Bool (Some true) -> Bool (Some true)
    | Bool (Some false), Bool (Some false) -> Bool (Some false)
    | Bool _, Bool _ -> Bool (None)
    | _, _ -> Bool (None)

  let equal t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Bool (Some a), Bool (Some b) when a=b -> Bool (Some true)
    | Bool (Some a), Bool (Some b) -> Bool (Some false)
    | Int (Val a, Val b), Int (Val c, Val d) when a=b && b=c && c=d -> Bool (Some true)
    | Int (a, b), Int (c, d) when is_bottom (meet (Int(a,b)) (Int(c,d))) -> Bool (Some false)
    | Float (Val a, Val b), Float (Val c, Val d) when a=b && b=c && c=d -> Bool (Some true)
    | Float (a, b), Float (c, d) when is_bottom (meet (Float(a,b)) (Float(c,d)))
      -> Bool (Some false)
    | _, _ -> Bool (None)

  let different t1 t2 = logical_not (equal t1 t2)

  let identical t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Top, _ | _, Top -> equal t1 t2
    | Bool _, Bool _ -> equal t1 t2
    | Int _, Int _ -> equal t1 t2
    | Float _, Float _ -> equal t1 t2
    | String _, String _ -> equal t1 t2
    | Array _, Array _ -> equal t1 t2
    | _, _ -> Bool (Some false)

  let not_identical t1 t2 = logical_not (identical t1 t2)

  let leq t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Int (a, b), Int (c, d) when bound_leq b c -> Bool (Some true)
    | Int (a, b), Int (c, d) when bound_greater a d -> Bool (Some false)
    | Float (a, b), Float (c, d) when bound_leq b c -> Bool (Some true)
    | Float (a, b), Float (c, d) when bound_greater a d -> Bool (Some false)
    | _, _ -> Bool (None)

  let greater t1 t2 = logical_not (leq t1 t2)

  let geq t1 t2 = logical_or (greater t1 t2) (equal t1 t2)

  let lower t1 t2 = logical_not (geq t1 t2)

  (* ----- ASSUME ----- *)

  let remove_singleton t n = match t with
    | Int (Val v, b2) when v = n -> normalize (Int (Val (v+1), b2))
    | Int (b1, Val v) when v = n -> normalize (Int (b1, Val (v-1)))
    | t -> t

  let assume_equal t1 t2 = meet (meet t1 t2) t1

  let assume_different t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Bool (Some b1), Bool (Some b2) when b1 = b2 -> Bottom
    | Bool None, Bool (Some b) -> Bool (Some (not b))
    | Int (b1, b2), Int (Val n1, Val n2) when n1 = n2
      -> remove_singleton (Int (b1,b2)) n1
    | t1, t2 -> t1

  let assume_identical t1 t2 = match t1, t2 with
    | Top, t2 -> t2
    | t1, Top -> t1
    | Bool _, Bool _ -> assume_equal t1 t2
    | Int _, Int _ -> assume_equal t1 t2
    | Float _, Float _ -> assume_equal t1 t2
    | String _, String _ -> assume_equal t1 t2
    | Array _, Array _ -> assume_equal t1 t2
    | _, _ -> Bottom

  let assume_not_identical t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Bool _, Bool _ -> assume_different t1 t2
    | Int _, Int _ -> assume_different t1 t2
    | Float _, Float _ -> assume_different t1 t2
    | String _, String _ -> assume_different t1 t2
    | Array _, Array _ -> assume_different t1 t2
    | t1, t2 -> t1

  let assume_leq t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Int (b1, b2), Int (b3, b4) ->
        normalize (Int (b1, bound_min b2 b4))
    | Float (b1, b2), Float (b3, b4) ->
        normalize (Float (b1, bound_min b2 b4))
    | t1, t2 -> t1

  let assume_geq t1 t2 = match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Int (b1, b2), Int (b3, b4) ->
        normalize (Int (bound_max b1 b3, b2))
    | Float (b1, b2), Float (b3, b4) ->
        normalize (Float (bound_max b1 b3, b2))
    | t1, t2 -> t1

  let assume_lower t1 t2 = match t1, t2 with
    | Int _, Int _ -> assume_leq t1 (add t2 (value_int (-1) (-1)))
    | t1, t2 -> assume_different (assume_leq t1 t2) t2

  let assume_greater t1 t2 = match t1, t2 with
    | Int _, Int _ -> assume_geq t1 (add t2 (value_int 1 1))
    | t1, t2 -> assume_different (assume_geq t1 t2) t2

  (* ----- PRINT ----- *)

  let print_int_bound b = match b with
    | Pinf -> "+oo"
    | Minf -> "-oo"
    | Val v -> string_of_int v

  let print_float_bound b = match b with
    | Pinf -> "+oo"
    | Minf -> "-oo"
    | Val v -> string_of_float v

  let rec print t = match t with
    | Top -> "Top"
    | Bottom -> "Bottom"
    | Bool (Some true) -> "Bool T"
    | Bool (Some false) -> "Bool F"
    | Bool None -> "Bool"
    | Int (b1, b2) -> "Int ["^(print_int_bound b1)^";"^(print_int_bound b2)^"]"
    | Float (b1, b2) -> "Float ["^(print_float_bound b1)^";"^(print_float_bound b2)^"]"
    | String Unknow_sanity -> "String"
    | String Sane -> "String S"
    | String Unsane -> "String U"
    | Array t -> "Array "^(print t)

end;;
