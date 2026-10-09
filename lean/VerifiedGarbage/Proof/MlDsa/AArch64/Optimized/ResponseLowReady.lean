import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowGroup

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

structure LowReady (g B : Nat) (s : State) : Prop extends HighPack.HighConstants g s where
  q : ∀e<4,vword (s.v .v16) e=8380417#32
  round32 : ∀e<4,vword (s.v .v25) e=4194304#32
  halfQ : ∀e<4,vword (s.v .v26) e=4190208#32
  twiceG : ∀e<4,vword (s.v .v21) e=BitVec.ofNat 32 (2*g)
  normLo : ∀e<4,vword (s.v .v27) e=BitVec.ofNat 32 (B-1)
  normWidth : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2*B-1)

theorem LowReady.frame {g B : Nat} {s t : State} {rs : List VReg} (h : LowReady g B s)
    (hv : ∀r,r∉rs → t.v r=s.v r)
    (hc : ∀r∈[VReg.v16,.v17,.v18,.v19,.v20,.v21,.v24,.v25,.v26,.v27],r∉rs) : LowReady g B t := by
  constructor
  · constructor
    · rw [hv .v17 (hc _ (by decide))]; exact h.add
    · rw [hv .v18 (hc _ (by decide))]; exact h.mul
    · rw [hv .v19 (hc _ (by decide))]; exact h.round
    · rw [hv .v20 (hc _ (by decide))]; exact h.modulus
  · rw [hv .v16 (hc _ (by decide))]; exact h.q
  · rw [hv .v25 (hc _ (by decide))]; exact h.round32
  · rw [hv .v26 (hc _ (by decide))]; exact h.halfQ
  · rw [hv .v21 (hc _ (by decide))]; exact h.twiceG
  · rw [hv .v27 (hc _ (by decide))]; exact h.normLo
  · rw [hv .v24 (hc _ (by decide))]; exact h.normWidth

theorem LowReady.group {g B : Nat} {s t : State} (h : LowReady g B s)
    (hk : StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t) : LowReady g B t := h.frame hk.vec (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Response
