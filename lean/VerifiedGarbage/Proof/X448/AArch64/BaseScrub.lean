module

public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X448.AArch64.Base.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X448's base-point multiplication on AArch64, without secret residue

The postcondition of `vg_x448_base` reads the memory on return only within
`out` (`ScrubAll.ScrubAllOk`, as x86-64's `baseOut` in
`Proof/X448/X86_64/Scrub.lean` proves it): its implementation, which has no
frames, returns with every register it may leave secret cleared
(`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.BaseScrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem baseOk (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) :
    ScrubAllOk (Spec.X448.x448BaseContract (abi.withConsts (c₀ :: cs)) 0) 0
      (Spec.X448.x448BaseSig.retBits abi.ptrBits) :=
  scrubAllOk_consts0 (sig := Spec.X448.x448BaseSig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.x448BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _
    have : Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
      simp only [Spec.X448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
    rw [this]; exact h

/-- `vg_x448_base`, scrubbed. -/
def baseReg : Registration Spec.X448.x448BaseApi AArch64.target :=
  ScrubAll.scrubAllOf {
    code := Impl.X448.AArch64.Base.x448Base
    verified := Proof.X448.AArch64.Base.x448Base_verified
    consts := Impl.X448.AArch64.Base.combConsts
    stack := 0 }
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
      .v26, .v27, .v28, .v29, .v30, .v31],
     [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (baseOk _ _) (by dsimp only [ScrubAll.retBitsOf]; lit_decide)

end VG.Proof.X448.AArch64.BaseScrub
