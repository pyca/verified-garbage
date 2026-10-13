module

/-!
# SM4's linear transformations

The round function `T` of encryption applies the linear transformation `L`,
and that of the key schedule `T'` applies `L'`; the implementations share
their rounds between the two, parameterized by which.
-/

@[expose] public section

namespace VG.Impl.Sm4

/-- `L` (encryption) or `L'` (the key schedule). -/
inductive Lin | enc | key
  deriving DecidableEq, Repr

end VG.Impl.Sm4
