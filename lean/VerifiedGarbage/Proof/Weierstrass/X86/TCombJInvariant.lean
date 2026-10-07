import VerifiedGarbage.Proof.Weierstrass.X86.TCombInv
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- The loop's invariant at `esi = j`: `A` is a Jacobian triple of
`[Σ_{i<j} d_i 2^(wi)]G`, and the table of bits (all `w J` bytes) and the
tables are where the digits and the selection read them. -/
structure TCombJInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : KeepRegs (powClob) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (zmul (bpart K.w k j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T

/-- `[Σ_{i≤j} d_i 2^(wi)]G` from the sum below `j` and the entry `j`. -/
theorem bpart_succ_pt {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) {w : Nat} (hw : 1 ≤ w)
    (k j : Nat) :
    zmul (bpart w k (j + 1)) (G C) = Spec.Weierstrass.add (zmul (bpart w k j) (G C)) (bentry C w k j) := by
  rw [bentry_eq hw, hC.add_zmul hG, bpart_succ]

end VG.Proof.Weierstrass.X86
