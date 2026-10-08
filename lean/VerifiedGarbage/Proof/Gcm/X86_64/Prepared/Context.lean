import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP
import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# Prepared GHASH contexts: preservation under disjoint writes

The trusted storage format is in `Spec.Gcm.Prepared`. This module supplies
its instance of the existing context-mode interface; no contract changes.
-/

namespace VG.Proof.Gcm.X86_64.Stitch
open VG VG.X86_64

/-- The key context of `vg_aes_gcm_init_prepared`. -/
def CtxMode.prepared : CtxMode where
  len := 1024
  ok := Spec.Gcm.PreparedPowersRepr
  ge := by decide
  le := Nat.le_refl _
  frame {rs m m' p} hf hd hw h := by
    have hH : Spec.Gcm.ctxH m' p = Spec.Gcm.ctxH m p :=
      VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr =>
        (hd r hr).sub_left (Offset.sub_base _ (show 240 + 16 ≤ 1024 by decide))
    have keep (o : Nat) (ho : o + 16 ≤ 1024) :
        m'.readW (p + BitVec.ofNat 64 o) 128 = m.readW (p + BitVec.ofNat 64 o) 128 :=
      hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base _ ho (by omega)) hd (by decide)
    intro k hk
    rw [keep _ (by omega), keep _ (by omega), hH]
    exact h k hk

/-- The interleaved-loop precondition, with prepared powers. -/
structure SPrePrepared (s₀ : State) : Prop where
  base : SPre s₀
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 1024
  wrap_k : (kp s₀).toNat + 1024 ≤ 2 ^ 64
  d_k : (dR s₀).Disjoint (kPR s₀)
  p_k : (pR s₀).Disjoint (kPR s₀)
  pow : Spec.Gcm.PreparedPowersRepr s₀.mem (kp s₀)

theorem SPreM.toPrepared {s₀ : State} (h : SPreM CtxMode.prepared s₀) : SPrePrepared s₀ :=
  ⟨h.base, h.k_in, h.wrap_k, h.d_k, h.p_k, h.ok⟩

end VG.Proof.Gcm.X86_64.Stitch
