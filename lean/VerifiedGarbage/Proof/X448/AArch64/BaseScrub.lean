module

public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
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

/-- `vg_x448_base` as emitted, cleanup included
(`Impl.X448.AArch64.Base.Fn.x448Base`): it meets its contract in constant
time and returns without secret residue. What the cleanup needs of the code
(`ScrubAll.scrubSide`) is evaluated here, by the kernel. -/
theorem x448Base :
    VerifiedScrubbed AArch64.target Impl.X448.AArch64.Base.Fn.x448Base
      (Spec.X448.x448BaseContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts)) 0 :=
  ScrubAll.verifiedScrubbed (api := Spec.X448.x448BaseApi)
    { code := Impl.X448.AArch64.Base.x448Base
      verified := Proof.X448.AArch64.Base.x448Base_verified
      consts := Impl.X448.AArch64.Base.combConsts
      stack := 0 } _
    (baseOk _ _) (by dsimp only; lit_decide)

end VG.Proof.X448.AArch64.BaseScrub
