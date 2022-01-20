-- Algebriac type system with subtyping, as defined in <>

data BoolType = True | False

data Type = 
  BoolType |
  IntType Int Int |
  FloatType Float Float |
  RecordType [String Type] |
  ArrayType Int Type |
  SliceType Int Int Type |
  FuncType Type [Type] | 
  Algebriac [Type]

  