{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-} 
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Tagged.TagSet where
import Data.Proxy
import GHC.Exts (Constraint)
import GHC.TypeLits
import Data.List (intersperse)


type family Before (s :: Symbol) (ss :: [Symbol] ) :: Constraint where
 Before s '[]        = ()
 Before s (h ': t)   = CmpSymbol s h ~ 'LT

data Tag :: (Symbol -> Constraint) -> Symbol -> * where
 Tag :: (KnownSymbol s, con s) => Tag con s

testTag :: KnownSymbol s => Tag KnownSymbol s
testTag = Tag

test0_4 = insert (testTag @"0") $ insert (testTag @"1") $ insert (testTag @"2") $ insert (testTag @"3") $ insert (testTag @"4") $ SNil

showTag :: Tag con s -> String
showTag t = case t of Tag -> "Tag ( " ++ symbolVal t ++ " )"

data TagSet :: (Symbol -> Constraint ) -> [Symbol] -> * where
 SNil :: TagSet con '[] 
 SCon :: Before s ss => Tag con s -> TagSet con ss -> TagSet con (s ': ss)

tagSetSize :: TagSet con l -> Int
tagSetSize SNil = 0
tagSetSize (SCon Tag tl) = 1 + tagSetSize tl

showTagSet :: TagSet con l -> String
showTagSet l = "TagSet [ " ++ ( concat $ intersperse ", " $ showTagSet' l ) ++ " ]"

showTagSet' :: TagSet con l -> [String]
showTagSet'  SNil       = []
showTagSet' (SCon t ts) = showTag t : showTagSet' ts

type family Insert (s :: Symbol) (ss :: [Symbol]) :: [Symbol] where
 Insert s '[]       = '[s]
 Insert s (h ': t)  = Insert' (CmpSymbol s h) s h t

type family Insert' (o :: Ordering) (s :: Symbol) (h :: Symbol) (t :: [Symbol] ) :: [Symbol] where
 Insert' 'LT s h t = s ': h ': t
 Insert' 'EQ s h t = h ': t
 Insert' 'GT s h t = h ': (Insert s t)

class Insertable s ss where
 insert :: Tag con s -> TagSet con ss -> TagSet con (Insert s ss)

class (CmpSymbol s h ~ o) => Insertable' (o :: Ordering) (s :: Symbol) (h :: Symbol) (t :: [Symbol] ) where
 insert' :: Tag con s -> TagSet con (h ': t) -> TagSet con (Insert' o s h t) 

instance Insertable s '[] where
 insert t SNil = SCon t $ SNil

instance Insertable' (CmpSymbol s h) s h t => Insertable s (h ': t) where
 insert t l = insert' t l

instance CmpSymbol s h ~ 'LT => Insertable' 'LT s h t where
 insert' t l = SCon t l

instance CmpSymbol s h ~ 'EQ => Insertable' 'EQ s h t where
 insert' t l = l 

instance (Before h (Insert s t), Insertable s t, CmpSymbol s h ~ 'GT) => Insertable' 'GT s h t where
 insert' t1 (SCon t2 l) = SCon t2 $ insert t1 l

------------ 

type family Merge (l1 :: [Symbol]) (l2 :: [Symbol]) :: [Symbol] where
 Merge '[] l2 = l2
 Merge (h1 ': t1) l2 = Merge t1 (Insert h1 l2)

class Mergeable (l1 :: [Symbol]) (l2 :: [Symbol]) where
 merge :: TagSet con l1 -> TagSet con l2 -> TagSet con (Merge l1 l2)

instance Mergeable '[] l where
 merge SNil l = l

instance (Mergeable l1 (Insert s1 l2), Insertable s1 l2) => Mergeable (s1 ': l1) l2 where
 merge (SCon t1 l1) l2 = merge l1 $ insert t1 l2

----

class TagNum (s :: Symbol) (ss :: [Symbol]) where
 tagNum :: Tag con s -> TagSet con ss -> Int

instance {-# OVERLAPPING #-}  (Before s l) => TagNum s (s ': l) where
 tagNum Tag (SCon Tag l) = tagSetSize l

instance {-# OVERLAPPABLE #-} (TagNum s l) => TagNum s (h ': l) where
 tagNum t (SCon _ l) = tagNum t l
