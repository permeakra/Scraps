{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-} 
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Tagged.TagSet where
import Data.Proxy
import GHC.Exts (Constraint)
import GHC.TypeLits
import Data.List (intersperse)
import GHC.Exts (Any)
import Unsafe.Coerce

type family Before (s :: Symbol) (ss :: [Symbol] ) :: Constraint where
 Before s '[]        = ()
 Before s (h ': t)   = CmpSymbol s h ~ 'LT

data Tag :: (Symbol -> Constraint) -> Symbol -> * where
 Tag :: (KnownSymbol s, con s) => Tag con s

class DynTag (s :: Symbol) where
 type DynType s :: *
 dynToAny     :: Proxy s -> DynType s -> Any
 dynToAny _    = unsafeCoerce
 dynFromAny   :: Proxy s -> Any -> DynType s
 dynFromAny _  = unsafeCoerce


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

class TagNum s ss where
 tagNum :: Tag con s -> TagSet con ss -> Int

class CmpSymbol s h ~ ord =>  TagNum' (ord :: Ordering) (s :: Symbol) (h :: Symbol) (t :: [Symbol]) where
 tagNum' :: Tag con s -> TagSet con (h ': t) -> Int

instance TagNum' (CmpSymbol s h) s h t => TagNum s (h ': t) where
 tagNum = tagNum'

instance CmpSymbol s s ~ 'EQ =>  TagNum' 'EQ s s t where
 tagNum' _ ts = tagSetSize ts

instance (TagNum s t, CmpSymbol s h ~ 'LT) =>  TagNum' 'LT s h t where
 tagNum' t (SCon _ tts) = 1 + tagNum t tts

instance (TagNum s t, CmpSymbol s h ~ 'GT) =>  TagNum' 'GT s h t where
 tagNum' t (SCon _ tts) = tagNum t tts




------------------------

class Insert s il ~ ol => Insertable (s :: Symbol) (il :: [Symbol] ) (ol :: [Symbol]) where
 type Insert s il :: [Symbol]
 insert :: Tag con s -> TagSet con il -> TagSet con ol

class (Insert' ord s h il ~ ol, CmpSymbol s h ~ ord) => Insertable' (ord:: Ordering)  (s :: Symbol) (h :: Symbol) (il :: [Symbol] ) (ol :: [Symbol] ) where
 type Insert' ord s h il :: [Symbol]
 insert' :: Tag con s -> TagSet con (h ': il) -> TagSet con ol

instance Insertable s '[] '[s] where
 type Insert s '[] = '[s]
 insert t SNil = SCon t SNil

instance Insertable' (CmpSymbol s h) s h t ol =>  Insertable s (h ': t) ol where
 type Insert s (h ': t) = Insert' (CmpSymbol s h) s h t
 insert = insert'

instance CmpSymbol s h ~ 'LT => Insertable' 'LT s h t (s ': h ': t) where
 type Insert' 'LT s h t = (s ': h ': t)
 insert' t tl = SCon t tl

instance (Insertable s t o, Before h o, CmpSymbol s h ~ 'GT)  => Insertable' 'GT s h t (h ': o ) where
 type Insert' 'GT s h t = h ': Insert s t
 insert' n (SCon h t) = SCon h $ insert n t

-------------------------

class Add s il ~ ol => Addable (s :: Symbol) (il :: [Symbol] ) (ol :: [Symbol] ) where
 type Add s il :: [Symbol]
 add :: Tag con s -> TagSet con il -> TagSet con ol

class (Add' ord s h il ~ ol, CmpSymbol s h ~ ord) => Addable' (ord :: Ordering) (s :: Symbol) (h :: Symbol) (il :: [Symbol]) (ol :: [Symbol]) where
 type Add' ord s h il :: [Symbol]
 add' :: Tag con s -> TagSet con (h ': il) -> TagSet con ol

instance Addable s il ~ ol => Addable s '[] '[s] where
 type Add s '[] = '[s]
 add t SNil = SCon t SNil

instance (Addable' ord s h il ol, CmpSymbol s h ~ ord) => Addable s (h ': il) ol where
 type Add s (h ': il) = Add' (CmpSymbol s h) s h il
 add = add'

instance (CmpSymbol s h ~ 'LT) => Addable' 'LT s h il (s ': h ': il) where
 type Add' 'LT s h il = s ': h ': il
 add' t tl = SCon t tl

instance (CmpSymbol s s ~ 'EQ) => Addable' 'EQ s s il (s ':  il) where
 type Add' 'EQ s s il = s ': il
 add' t tl = tl

instance (CmpSymbol s h ~ 'GT, Addable s il ol, Before s ol) => Addable' 'GT s h il (s ':  ol) where
 type Add' 'GT s h il = s ': Add s il
 add' t (SCon h tl) = SCon t $ add t tl

---------------------------

class Remove s il ~ ol => Removable (s :: Symbol) (il :: [Symbol]) (ol :: [Symbol]) where
 type Remove s il :: [Symbol]
 remove:: Tag con s -> TagSet con il -> TagSet con ol

class (Remove' ord s h il ~ ol, CmpSymbol s h ~ ord) => Removable' (ord :: Ordering) (s :: Symbol) (h :: Symbol) (il :: [Symbol]) (ol :: [Symbol]) where
 type Remove' ord s h il :: [Symbol]
 remove' :: Tag con s -> TagSet con (h ': il) -> TagSet con ol

instance Removable s '[s] '[] where
 type Remove s '[s] = '[]
 remove _ (SCon _ SNil) = SNil

instance Removable' 'EQ s s l l where
 type Remove' 'EQ s s l = l
 remove' _ (SCon _ l) = l

instance (ol ~ (h ': iil), iil ~ Remove s il, Before h iil, CmpSymbol s h ~ 'GT, Removable s il iil) => Removable' 'GT s h il ol where
 type Remove' 'GT s h il = h ': Remove s il
 remove' t (SCon h l) = SCon h $ remove t l




