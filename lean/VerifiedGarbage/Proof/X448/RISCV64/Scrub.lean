module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Verified
public import VerifiedGarbage.Proof.X448.RISCV64.Exchange
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on RISC-V, without secret residue

`vg_x448_base` and `vg_x448_exchange`, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within `out` (`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/X448/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-! ## Postconditions -/

theorem baseOut (stack : Nat) : PostOut (Spec.X448.x448BaseContract RISCV64.abi stack) (Spec.X448.x448BaseSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
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

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X448.exchangeContract RISCV64.abi stack) (Spec.X448.exchangeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _ ∧ _
    have : Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
      simp only [Spec.X448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
    rw [this]; exact h

/-! ## The registrations -/

/-- `Spec.X448.exchangeApi`. -/
def exchangeReg : Registration Spec.X448.exchangeApi RISCV64.target :=
  withScrub {
      code := Impl.Xdh.RISCV64.exchange "vg_x448" Impl.X448.RISCV64.R64.x448 56
      verified := Proof.X448.RISCV64.Exchange.exchange_verified }
    (exchangeOut _)

/-- `Spec.X448.x448BaseApi`. -/
def baseReg : Registration Spec.X448.x448BaseApi RISCV64.target :=
  withScrub {
      code := Impl.X448.RISCV64.R64.x448Base
      verified := Proof.X448.RISCV64.R64.x448Base_verified }
    (baseOut _)

end VG.Proof.X448.RISCV64.Scrub
