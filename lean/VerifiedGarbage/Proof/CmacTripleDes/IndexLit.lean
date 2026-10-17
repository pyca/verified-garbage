module

public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.Index
meta import VerifiedGarbage.Impl.CmacTripleDes.Index

/-!
# The key schedule's bit maps as tables, for the kernel

Each evaluated once, here: the code built from them on every target (the
round's, `IP`'s and `IP⁻¹`'s bit permutations, `roundKeys`), its checks and
`keyBit_eq` read the tables rather than evaluate the specification's
permutations again.
-/

@[expose] public section

namespace VG

materialize_table Impl.CmacTripleDes.expSrc 48
materialize_table Impl.CmacTripleDes.pSrc 32
materialize_table Impl.CmacTripleDes.ipSrc 64
materialize_table Impl.CmacTripleDes.fpSrc 64
materialize_table Impl.CmacTripleDes.pc1Src 56
materialize_table Impl.CmacTripleDes.rkSrc 16 48

end VG
