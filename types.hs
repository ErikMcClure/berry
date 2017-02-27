-- The fundamental type here has a "join" operation that acts as a union between all possible data types and ranges.
-- Because this operation is idempotent and has an identity element (an empty type), it forms a Semilattice

import Data.Monoid
import Data.Semiring
import Data.Maybe

data RefInt = ConstantInt Int | RefInt Int | NoLimit deriving (Show, Eq)

data TypeInner = 
  IntDef Int Int |
  FloatDef Float Float |
  ArrayDef TypeDef RefInt |
  SliceDef TypeDef Int Int |
  Ref TypeDef |
  EnumDef Int |
  Polytype Int |
  Constant TypeDef |
  RefConstant Int |
  Parameters [TypeDef] |
  Complex Int [TypeDef] [TypeDef] [TypeConstraint] | -- id, members, inheritance, constraints
  FuncDef Int TypeDef [TypeDef] [TypeConstraint] | -- id, return value, parameters, constraints
  Algebriac [TypeDef]
  deriving (Show, Eq)

data TypeDef = None | Anything | TypeDef TypeInner deriving (Show, Eq)
data TypeConstraintInner = 
  ConstantConstraint TypeDef |
  ComplexConstraint [TypeDef] | -- inheritance only
  FuncConstraint TypeDef [TypeDef] | -- return value and parameters only
  AlgebriacConstraint [TypeConstraint]
  deriving (Show, Eq)
  
data TypeConstraint = Variadic | Instance TypeDef | TypeConstraint Int TypeConstraintInner deriving (Show, Eq)

--instance Ord TypeDef where
--  (TypeDef s1 _) `compare` (TypeDef s2 _) = s1 `compare` s2
--  (TypeDef s1 _) `compare` None = s1 `compare` 0
--  None `compare` (TypeDef s2 _) = 0 `compare` s2
--  None `compare` None = 0 `compare` 0
  
instance Monoid TypeDef where
  mempty = None
  mappend x y = union x y
  mconcat x = foldr mappend mempty x
  
instance Semiring TypeDef where
  one = Anything
  (<.>) x y = intersect x y

data TypeContext = TypeContext [(Int,Int)] [TypeDef]

map2 :: (a -> a -> b) -> [a] -> [a] -> [b]
map2 _ [] []    = []
map2 f (x:xs) (y:ys) = f x y : map2 f xs ys

-- Absorbs a type into an algebriac typelist by either merging it into an existing compatible type, or appending it on the end
absorb :: TypeDef -> [TypeDef] -> [TypeDef]
absorb (TypeDef (Algebriac y)) x = (foldr absorb y x)
absorb y (x:xs)
  | t /= None = (t:xs)
  | otherwise = (x:(absorb y xs))
  where t = (merge x y)
absorb y [] = [y]

-- Attempts to merge two RefInts
mergerefint :: (Int -> Int -> Int) -> RefInt -> RefInt -> Maybe RefInt
mergerefint f (ConstantInt x) (ConstantInt y) = Just (ConstantInt (f x y))
mergerefint _ NoLimit (ConstantInt y) = Just (ConstantInt y)
mergerefint _ (ConstantInt x) NoLimit = Just (ConstantInt x)
mergerefint _ NoLimit NoLimit = Just NoLimit
mergerefint _ (RefInt i1) (RefInt i2)
  | i1 == i2 = Just (RefInt i1)
  | otherwise = Nothing
mergerefint _ _ _ = Nothing

-- The merge operator attempts to union two types, but if they are disparate, simply returns None
merge :: TypeDef -> TypeDef -> TypeDef
merge (TypeDef (IntDef min1 max1)) (TypeDef (IntDef min2 max2))
  | min1 <= (max2 + 1) && min2 <= (max1 + 1) = (TypeDef (IntDef (min min1 min2) (max max1 max2)))
  | otherwise = None
  
merge (TypeDef (FloatDef min1 max1)) (TypeDef (FloatDef min2 max2))
  | min1 <= max2 && min2 <= max1 = (TypeDef (FloatDef (min min1 min2) (max max1 max2)))
  | otherwise = None
  
merge (TypeDef (ArrayDef t1 len1)) (TypeDef (ArrayDef t2 len2))
  | t /= None = (maybe None (\l -> (TypeDef (ArrayDef t l))) (mergerefint max len1 len2))
  | otherwise = None
  where t = (merge t1 t2)
  
merge (TypeDef (SliceDef t1 s1 len1)) (TypeDef (SliceDef t2 s2 len2))
  | t /= None = (TypeDef (SliceDef t (min s1 s2) (max len1 len2)))
  | otherwise = None
  where t = (merge t1 t2)
  
merge (TypeDef (Ref t1)) (TypeDef (Ref t2))
  | t /= None = (TypeDef (Ref t))
  | otherwise = None
  where t = (merge t1 t2)
  
merge (TypeDef (EnumDef i1)) (TypeDef (EnumDef i2))
  | i1 == i2 = (TypeDef (EnumDef i1))
  | otherwise = None
  
merge (TypeDef (Polytype i1)) (TypeDef (Polytype i2))
  | i1 == i2 = (TypeDef (Polytype i1))
  | otherwise = None
  
merge (TypeDef (Constant t1)) (TypeDef (Constant t2))
  | t /= None = (TypeDef (Constant t))
  | otherwise = None
  where t = (merge t1 t2)
  
merge (TypeDef (RefConstant i1)) (TypeDef (RefConstant i2))
  | i1 == i2 = (TypeDef (RefConstant i1))
  | otherwise = None

merge (TypeDef (Parameters t1)) (TypeDef (Parameters t2)) = (TypeDef (Parameters (map2 merge t1 t2)))
  
merge (TypeDef (Complex i1 t1 b1 c1)) (TypeDef (Complex i2 t2 b2 c2))
  | i1 == i2 = (TypeDef (Complex i1 (map2 merge t1 t2) (map2 merge b1 b2) (map2 unionConstraint c1 c2)))
  | otherwise = None
  
merge (TypeDef (FuncDef i1 r1 t1 c1)) (TypeDef (FuncDef i2 r2 t2 c2))
  | i1 == i2 = (TypeDef (FuncDef i1 (merge r1 r2) (map2 merge t1 t2) (map2 unionConstraint c1 c2)))
  | otherwise = None

merge (TypeDef (Algebriac t1)) (TypeDef (Algebriac t2))
  = (TypeDef (Algebriac (foldr absorb t1 t2)))
  
merge (TypeDef (Algebriac t)) y = (TypeDef (Algebriac (absorb y t)))
merge x (TypeDef (Algebriac t)) = (TypeDef (Algebriac (absorb x t)))  
merge None y = y
merge x None = x
merge Anything _ = Anything
merge _ Anything = Anything
merge x y
  | x == y = x
  | otherwise = None

-- Merges two type constraints, throwing away the ID of the second one because the specific ID is irrelevent so long as it exists
mergeConstraint :: TypeConstraint -> TypeConstraint -> Maybe TypeConstraint
mergeConstraint (TypeConstraint i (ConstantConstraint x)) (TypeConstraint _ (ConstantConstraint y))
  | t /= None = Just (TypeConstraint i (ConstantConstraint t))
  | otherwise = Nothing
  where t = (merge x y)
  
mergeConstraint (TypeConstraint i (ComplexConstraint x)) (TypeConstraint _ (ComplexConstraint y))
  = Just (TypeConstraint i (ComplexConstraint (map2 merge x y)))

  
mergeConstraint (TypeConstraint i (FuncConstraint x t1)) (TypeConstraint _ (FuncConstraint y t2))
  | t /= None = Just (TypeConstraint i (FuncConstraint t (map2 merge t1 t2)))
  | otherwise = Nothing
  where t = (merge x y)
  
mergeConstraint (TypeConstraint i (AlgebriacConstraint x)) (TypeConstraint _ (AlgebriacConstraint y)) = Just (TypeConstraint i (AlgebriacConstraint (x ++ y)))
mergeConstraint (TypeConstraint i (AlgebriacConstraint x)) y = Just (TypeConstraint i (AlgebriacConstraint (y:x)))
mergeConstraint x (TypeConstraint i (AlgebriacConstraint y)) = Just (TypeConstraint i (AlgebriacConstraint (x:y)))
mergeConstraint Variadic Variadic = Just Variadic
mergeConstraint _ _ = Nothing

-- The union operation attempts to merge two types, but if merge returns None, creates an algebriac union instead.
union :: TypeDef -> TypeDef -> TypeDef
union None None = None 
union x y
  | t /= None = t
  | otherwise = (TypeDef (Algebriac [x,y]))
  where t = (merge x y)

unionConstraint :: TypeConstraint -> TypeConstraint -> TypeConstraint
unionConstraint (TypeConstraint i x) (TypeConstraint i2 y)
  = (maybe (TypeConstraint i (AlgebriacConstraint [(TypeConstraint i x), (TypeConstraint i2 y)])) id (mergeConstraint (TypeConstraint i x) (TypeConstraint i y)))

-- If the given type is in the algebriac type, returns intersection of that type and the one in the algebriac type. 
extract :: [TypeDef] -> TypeDef -> TypeDef
extract (x:xs) y
  | t /= None = t
  | otherwise = (extract xs y)
  where t = (intersect x y)
extract [] y = None
  
extractConstraint :: [TypeConstraint] -> TypeConstraint -> Maybe TypeConstraint
extractConstraint (x:xs) y = (maybe (extractConstraint xs y) Just (intersectConstraint x y))
extractConstraint [] y = Nothing

-- The intersection returns a type that satifies the ranges of both input types, or None if they are exclusive.
-- This function does NOT evaluate constraints, and instead generates an intersection between constraints
intersect :: TypeDef -> TypeDef -> TypeDef
intersect (TypeDef (IntDef min1 max1)) (TypeDef (IntDef min2 max2))
  | min1 <= max2 && min2 <= max1 = (TypeDef (IntDef (max min1 min2) (min max1 max2)))
  | otherwise = None
  
intersect (TypeDef (FloatDef min1 max1)) (TypeDef (FloatDef min2 max2))
  | min1 <= max2 && min2 <= max1 = (TypeDef (FloatDef (max min1 min2) (min max1 max2)))
  | otherwise = None
  
intersect (TypeDef (ArrayDef t1 len1)) (TypeDef (ArrayDef t2 len2))
  | t /= None = (maybe None (\l -> (TypeDef (ArrayDef t l))) (mergerefint min len1 len2))
  | otherwise = None
  where t = (intersect t1 t2)
  
intersect (TypeDef (SliceDef t1 s1 len1)) (TypeDef (SliceDef t2 s2 len2))
  | t /= None = (TypeDef (SliceDef t (max s1 s2) (min len1 len2)))
  | otherwise = None
  where t = (intersect t1 t2)
  
intersect (TypeDef (Ref t1)) (TypeDef (Ref t2))
  | t /= None = (TypeDef (Ref t))
  | otherwise = None
  where t = (intersect t1 t2)
  
intersect (TypeDef (EnumDef i1)) (TypeDef (EnumDef i2))
  | i1 == i2 = (TypeDef (EnumDef i1))
  | otherwise = None
  
intersect (TypeDef (Polytype i1)) (TypeDef (Polytype i2))
  | i1 == i2 = (TypeDef (Polytype i1))
  | otherwise = None
  
intersect (TypeDef (Constant t1)) (TypeDef (Constant t2))
  | t /= None = (TypeDef (Constant t))
  | otherwise = None
  where t = (intersect t1 t2)
  
intersect (TypeDef (RefConstant i1)) (TypeDef (RefConstant i2))
  | i1 == i2 = (TypeDef (RefConstant i1))
  | otherwise = None

intersect (TypeDef (Parameters t1)) (TypeDef (Parameters t2)) = (TypeDef (Parameters (filter (/= None) (map2 intersect t1 t2))))

intersect (TypeDef (Complex i1 t1 b1 c1)) (TypeDef (Complex i2 t2 b2 c2))
  | i1 == i2 = (TypeDef (Complex i1 (filter (/= None) (map2 intersect t1 t2)) (filter (/= None) (map2 intersect b1 b2)) (catMaybes (map2 intersectConstraint c1 c2))))
  | otherwise = None
  
intersect (TypeDef (FuncDef i1 r1 t1 c1)) (TypeDef (FuncDef i2 r2 t2 c2))
  | i1 == i2 = (TypeDef (FuncDef i1 (intersect r1 r2) (filter (/= None) (map2 intersect t1 t2)) (catMaybes (map2 intersectConstraint c1 c2))))
  | otherwise = None

intersect (TypeDef (Algebriac x)) (TypeDef (Algebriac y))
  | t /= [] = (TypeDef (Algebriac t))
  | otherwise = None
  where t = (filter (/= None) (foldr (\l r -> (extract x l) : r) [] y))
  
intersect (TypeDef (Algebriac x)) y
  | t /= None = (TypeDef (Algebriac [t]))
  | otherwise = None
  where t = (extract x y)
  
intersect x (TypeDef (Algebriac y))
  | t /= None = (TypeDef (Algebriac [t]))
  | otherwise = None
  where t = (extract y x)
  
intersect Anything y = y
intersect x Anything = x
intersect _ _ = None

intersectConstraint :: TypeConstraint -> TypeConstraint -> Maybe TypeConstraint
intersectConstraint (TypeConstraint i (ConstantConstraint x)) (TypeConstraint _ (ConstantConstraint y))
  | t /= None = Just (TypeConstraint i (ConstantConstraint t))
  | otherwise = Nothing
  where t = (intersect x y)
  
intersectConstraint (TypeConstraint i (ComplexConstraint x)) (TypeConstraint _ (ComplexConstraint y))
  | t /= [] = Just (TypeConstraint i (ComplexConstraint t))
  | otherwise = Nothing
  where t = (filter (/= None) (map2 intersect x y))
  
intersectConstraint (TypeConstraint i (FuncConstraint x t1)) (TypeConstraint _ (FuncConstraint y t2))
  | t /= None = Just (TypeConstraint i (FuncConstraint t (filter (/= None) (map2 intersect t1 t2))))
  | otherwise = Nothing
  where t = (intersect x y)
  
intersectConstraint (TypeConstraint i (AlgebriacConstraint x)) (TypeConstraint _ (AlgebriacConstraint y))
  | t /= [] = Just (TypeConstraint i (AlgebriacConstraint t))
  | otherwise = Nothing
  where t = (catMaybes (foldr (\l r -> (extractConstraint x l) : r) [] y))
  
intersectConstraint (TypeConstraint i (AlgebriacConstraint x)) y
  = (maybe Nothing (\t -> Just (TypeConstraint i (AlgebriacConstraint [t]))) (extractConstraint x y))
  
intersectConstraint x (TypeConstraint i (AlgebriacConstraint y))
  = (maybe Nothing (\t -> Just (TypeConstraint i (AlgebriacConstraint [t]))) (extractConstraint y x))
  
intersectConstraint Variadic Variadic = Just Variadic
intersectConstraint _ _ = Nothing


--pullconstraint :: Typedef -> TypeConstraint -> TypeConstraint -> TypeConstraint

-- Attempts to infer missing template arguments from the function parameters only. The return value must be calculated by Algorithm W
--resolve :: [TypeDef] -> [TypeDef] -> [TypeConstraint] -> [TypeConstraint] -> [TypeConstraint]
--resolve x y (u:us) (v:vs)
--  | u == None = ()
--  | otherwise = u:(resolve x y us vs)

-- Within checks the first type argument against the second type, treating the second type as a constraint
-- This function takes a context used to evaluate the constraints.
within :: TypeDef -> TypeDef -> TypeContext -> Bool
within (TypeDef (IntDef min1 max1)) (TypeDef (IntDef min2 max2)) _ = min1 <= max2 && min2 <= max1
within (TypeDef (FloatDef min1 max1)) (TypeDef (FloatDef min2 max2)) _  = min1 <= max2 && min2 <= max1
within (TypeDef (ArrayDef t1 len1)) (TypeDef (ArrayDef t2 len2)) w  = (within t1 t2 w)
within (TypeDef (SliceDef t1 s1 len1)) (TypeDef (SliceDef t2 s2 len2)) w  = (within t1 t2 w) && (s1 >= s2) && (len1 <= len2)
within (TypeDef (Ref t1)) (TypeDef (Ref t2)) w = (within t1 t2 w)
within (TypeDef (EnumDef t1)) (TypeDef (EnumDef t2)) _ = t1 == t2
within (TypeDef (Polytype t1)) (TypeDef (Polytype t2)) _ = t1 == t2
within (TypeDef (Constant t1)) (TypeDef (Constant t2)) w  = (within t1 t2 w)  
within x y _ = (intersect x y) == x
















-- Given a function definition template[A, B:A, int C < 3, ...] void foobar(i16, u8, A, Bar[A, C]&, B[:], ...)
-- The definition of this function is represented as:
--testfunc = (TypeDef (FuncDef 1 None [
--  (TypeDef (IntDef −32768 32767)),
--  (TypeDef (IntDef 0 255)),
--  (TypeDef (Polytype 1)),
--  (TypeDef (Ref (TypeDef (Complex 4 [] [] [(TypeDef (Polytype 1)), (TypeDef (Polytype 3))])))),  -- '4' here references 'Bar'
--  (TypeDef (SliceDef (Polytype 2) 0 0)),
--  (TypeDef (Parameters []))]
--  [(TypeConstraint 1 Anything),
--  (TypeConstraint 2 (ComplexConstraint [(TypeDef (Polytype 1))])),
--   (TypeConstraint 3 (ConstantConstraint (TypeDef ()) )),
-- Variadic]))
   
-- An attempt to instantiate this function from foobar[Foo](-2, 1, a, b, c[1:2])