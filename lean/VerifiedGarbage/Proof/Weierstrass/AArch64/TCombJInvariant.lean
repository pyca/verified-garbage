import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.Booth
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- After `j` public windows, `A` represents the signed Booth partial sum in
Jacobian coordinates. Scalar bytes and every table row remain available. -/
structure TCombJInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (tcombClob K.M.n) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (zmul (bpart K.w k j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : s.syms K.tsym = T

/-- `[Σ_{i≤j} d_i 2^(wi)]G` from the sum below `j` and the entry `j`. -/
theorem bpart_succ_pt {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) {w : Nat} (hw : 1 ≤ w)
    (k j : Nat) :
    zmul (bpart w k (j + 1)) (G C) = Spec.Weierstrass.add (zmul (bpart w k j) (G C)) (bentry C w k j) := by
  rw [bentry_eq hw, hC.add_zmul hG, bpart_succ]

/-- The comb working ranges do not overwrite the modulus. -/
theorem tcombW_mo {K : TCombCfg} {size m : Nat} {mem : Mem} {base : Addr} (hL : TCombLay K size)
    (hM : ModOkA K.M size m mem base) : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [tcombW, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
  · have := hL.comb.lay.mo y (combWs_slots _ y hy); dsimp only [TCombCfg.toComb] at this ⊢; omega
  · have := hM.sep; dsimp only [TCombCfg.toComb] at this ⊢; omega
  · have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega

end VG.Proof.Weierstrass.AArch64
