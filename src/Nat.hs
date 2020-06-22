{-# LANGUAGE
    DataKinds, PolyKinds, TypeFamilies, GADTs, TypeOperators
  , UndecidableInstances
  #-}
module Nat where
import Data.Kind (Type)

data (==) :: k -> k -> Type where
  Refl :: x == x

sym :: a == b -> b == a
sym Refl = Refl

data Nat where
  Z :: Nat
  S :: Nat -> Nat

two :: Nat
two = S (S Z)



data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type family (a :: Nat) :+: (b :: Nat) where
  Z :+: b = b
  S a :+: b = S (a :+: b)

type family (a :: Nat) :*: (b :: Nat) where
  Z :*: b = Z
  (S a) :*: b = b :+: (a :*: b)

type family (a :: Nat) :^: (b :: Nat) where
  a :^: Z = S Z
  a :^: (S b) = a :*: (a :^: b)

type Two = 'S ('S Z)
type Four = 'S ('S ('S ('S Z)))

example :: Two :^: Two == Four
example = Refl

assocAdd :: SNat a -> SNat b -> SNat c -> (a :+: b) :+: c == (a :+: (b :+: c))
assocAdd SZ b c = Refl
assocAdd (SS a) b c =
  case assocAdd a b c of
    Refl -> Refl

addIdR  :: SNat a -> a :+: 'Z == a
addIdR SZ = Refl
addIdR (SS a) =
  case addIdR a of
    Refl -> Refl

addSuccR :: SNat a -> SNat b -> a :+: ('S b) == 'S (a :+: b)
addSuccR SZ b = Refl
addSuccR (SS a) b =
  case addSuccR a b of
    Refl -> Refl

addComm :: SNat a -> SNat b -> a :+: b == (b :+: a)
addComm SZ b =
  case addIdR b of
    Refl -> Refl
addComm (SS a) b =
  case addSuccR b a of
    Refl ->
      case addComm a b of
        Refl -> Refl
      




  
