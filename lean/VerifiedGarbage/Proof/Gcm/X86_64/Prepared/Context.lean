module

public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Powers
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Prepared GHASH contexts: preservation under disjoint writes

The trusted storage format is in `Spec.Gcm.Prepared`. This module supplies
its instance of the existing context-mode interface; no contract changes.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch
open VG VG.X86_64

/-- A prepared key context holding its first `n` pairs of powers (`PowersN`),
for loops that read no other. -/
def CtxMode.preparedN (n : Nat) (hn : n ≤ 24 := by decide) : CtxMode where
  len := 1024
  ok := PowersN n
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

/-- The key context of `vg_aes_gcm_prepare`: all 24 pairs, whose `ok` is
`Spec.Gcm.PreparedPowersRepr`. -/
abbrev CtxMode.prepared : CtxMode := CtxMode.preparedN 24

/-- The interleaved-loop precondition, with prepared powers. -/
structure SPrePrepared (s₀ : State) (lo : Nat := 16) (n : Nat := 24) : Prop where
  base : SPre s₀ lo
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 1024
  wrap_k : (kp s₀).toNat + 1024 ≤ 2 ^ 64
  d_k : (dR s₀).Disjoint (kPR s₀)
  p_k : (pR s₀).Disjoint (kPR s₀)
  pow : PowersN n s₀.mem (kp s₀)

theorem SPreM.toPrepared {s₀ : State} {lo n : Nat} {hn : n ≤ 24} (h : SPreM (CtxMode.preparedN n hn) s₀ lo) :
    SPrePrepared s₀ lo n :=
  ⟨h.base, h.k_in, h.wrap_k, h.d_k, h.p_k, h.ok⟩

end VG.Proof.Gcm.X86_64.Stitch
