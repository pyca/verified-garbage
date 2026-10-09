import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)

structure Flags (v : Nat) (L : Nat → List Zq) (s : State) : Prop where
  bound : (s.gpr .x27).toNat<512
  zero : s.gpr .x27=0#64 ↔ ∀k<v,(L k).length=256

theorem flagsSemantic_ok {v blocks : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) :
    WP isa (.block (flagsCode (v-1))) s fun t => Rows v blocks σ L t ∧ Flags v L t := by
  refine WP.mono (flagsRows_ok hp h) fun t ⟨ht,hf⟩ => ⟨ht,?_,?_⟩
  · rw [hf]
    apply foldedFlags_bound
    intro k hk
    have hkv : k<v := by have:=hp.streams; omega
    rw [h.counts k hkv]
    omega
  · rw [hf,foldedFlags_zero]
    constructor
    · intro hz k hk
      have he := congrArg BitVec.toNat (hz k (by have:=hp.streams; omega))
      rw [h.counts k hk] at he
      have := h.length k hk
      change 256-(L k).length=0 at he
      omega
    · intro hz k hk
      have hkv : k<v := by have:=hp.streams; omega
      apply BitVec.eq_of_toNat_eq
      rw [h.counts k hkv,hz k hkv]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
