(* 補助的な諸々 (pair とか冗長ですが either との双対性を強調するために導入しました) *)
type ('a,'b) either = Left of 'a | Right of 'b
type ('a,'b) pair = Pair of 'a * 'b
let id x = x
let ($) f g x = f (g x)
let (<&>) f g x = Pair(f x, g x)
let (<|>) f g = function Left x -> f x | Right x -> g x
let left x = Left x and right x = Right x
let fst (Pair(x,_)) = x and snd (Pair(_,y)) = y

(* F の型 *)
module type F = sig
  type 'a t 
  val fmap : ('a -> 'b) -> 'a t -> 'b t
end
              
(* F の例 *)
module F_int_list : F = struct
  type 'a t = Nil | Cons of int * 'a
  let fmap f = function
    | Nil -> Nil
    | Cons(i,x) -> Cons(i,f x)
end
                      
(* F の不動点の型 *)
module type FixpointType = sig
  type 'a t
  type mu = In of mu t
  type 'a his = His of ('a, 'a his t) pair
  type 'a fut = Fut of ('a, 'a fut t) either
  val in_ : mu t -> mu
  val out : mu -> mu t
  val cata : ('a t -> 'a) -> mu -> 'a
  val ana : ('a -> 'a t) -> 'a -> mu
  val hylo : ('b t -> 'b) -> ('a -> 'a t) -> 'a -> 'b
  val meta : ('a t -> 'a) -> ('a -> 'a t) -> mu -> mu
  val para : ((mu, 'a) pair t -> 'a) -> mu -> 'a
  val apo : ('a -> (mu, 'a) either t) -> 'a -> mu
  val histo : ('a his t -> 'a) -> mu -> 'a
  val futu : ('a -> 'a fut t) -> 'a -> mu
  val chrono : ('b his t -> 'b) -> ('a -> 'a fut t) -> 'a -> 'b
  val zygo : ('b t -> 'b) -> (('b, 'a) pair t -> 'a) -> mu -> 'a
  val cozygo : ('b -> 'b t) -> ('a -> ('b, 'a) either t) -> 'a -> mu
  val dyna : ('b his t -> 'b) -> ('a -> 'a t) -> 'a -> 'b
  val codyna : ('b t -> 'b) -> ('a -> 'a fut t) -> 'a -> 'b
  val mutu : ('a -> 'b) -> ('a t -> 'a) -> mu -> 'b
end
                         
(* F の不動点を生成するファンクタ *)
module MakeFixpoint (F:F) : FixpointType = struct
  type 'a t = 'a F.t
  type mu = In of mu t
  type 'a his = His of ('a, 'a his t) pair
  let head (His(Pair(x,_))) = x
  let (<*>) f g x = His((f<&>g) x)
  type 'a fut = Fut of ('a, 'a fut t) either
  let last x = Fut(Left x)
  let (<+>) f g (Fut x) = (f<|>g) x
  let in_ x = In x
  let out (In x) = x
  (* catamorphism *)
  let rec cata phi x = phi (F.fmap (cata phi) (out x))
  (* anamorphism *)
  let rec ana psi x = in_ (F.fmap (ana psi) (psi x))
  (* hylomorphism : cata phi . ana psi *)
  let rec hylo phi psi x = phi (F.fmap (hylo phi psi) (psi x))
  (* metamorphism *)
  let meta phi psi = ana psi $ cata phi
  (* paramorphism *)
  let rec para phi x = phi (F.fmap (id <&> para phi) (out x))
  (* apomorphism *)
  let rec apo psi x = in_ (F.fmap (id <|> apo psi) (psi x))
  (* histomorphism *)
  let histo phi = head $ cata (phi<*>id)
  (* futumorphism *)
  let futu psi = ana (psi<+>id) $ last
  (* chronomorphism *)
  let chrono phi psi = histo phi $ futu psi
  (* zygomorphism : para = zygo in_ *)
  let zygo f phi = snd $ cata ((f $ F.fmap fst) <&> phi)
  (* cozygomorphism : apo = cozygo out *)
  let cozygo f psi = ana ((F.fmap left $ f) <|> psi) $ right
  (* dynamorphism *)
  let dyna f g = chrono f (F.fmap last $ g)
  (* codynamorphism *)
  let codyna f g = chrono (f $ F.fmap head) g
  (* mutumorphism *)
  let mutu proj phi x = proj (cata phi x)
end
