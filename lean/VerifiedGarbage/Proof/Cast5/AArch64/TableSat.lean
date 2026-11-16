module

public import VerifiedGarbage.Proof.Cast5.AArch64.Block
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Cast5.Tables

/-!
# CAST5 on AArch64: the table of the scans, for the contracts' witnesses

The modes whose block code scans `VG_CAST5_S1234` state their contracts on
`AArch64.abi.withConsts ecbConsts`; their witnesses hold the table at
`0x100000` (`ecbSatMem`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64
open VG.Impl.Cast5 (s1234 s1234Sym ecbConsts)

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the contracts' witness: the table at `0x100000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := constMem 0x100000 s1234

theorem ecbSatMem_held : ∀ i < 512,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  unfold ecbSatMem
  intro i hi
  exact constMem_held _ _ (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi)

end VG.Proof.Cast5.AArch64
