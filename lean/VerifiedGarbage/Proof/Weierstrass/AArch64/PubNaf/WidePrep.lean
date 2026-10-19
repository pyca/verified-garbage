module
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNafWide
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Impl.Weierstrass.AArch64.PubNafWide
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 PubNaf
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
/-- `prep` writes the `64 n + 1` digits of the scalar of `n` words at `src`. -/
theorem prep7_ok (K : WinCfg) (hR : Regs K.M.n) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src + 8 * K.M.n ≤ size) (hsrc8 : src % 8 = 0)
    (hbits : K.bits < 4096) (hb : K.bits + (64 * K.M.n + 1) ≤ size) :
    WP isa (prep7 K src) s fun t =>
      PrepSt K.M.n base size K.bits (wordsVal s.mem base src K.M.n) (64 * K.M.n + 1) t ∧
      KeepRegs (clobs K.M.n) s t ∧ Outside base K.bits (64 * K.M.n + 1) s.mem t.mem := by
  let k := wordsVal s.mem base src K.M.n
  have hk : k < 2 ^ (64 * K.M.n) := wordsVal_lt ..
  have hle := hR.le
  let D := 64 * K.M.n + 1
  let I (m : Nat) (t : State) := PrepSt K.M.n base size K.bits k (D - m) t ∧
    KeepRegs (clobs K.M.n) s t ∧ Outside base K.bits D s.mem t.mem
  rw [prep7]
  refine WP.seq (WP.mono (init_ok K hR hs hsrc hsrc8 hbits) fun a ⟨ia, ka, ma⟩ => ?_)
  refine countLoop_ok (Inv := I) (n := D) (by omega_arith) ?_ ?_ (by omega_arith) ?_
  · intro m t hm hmD hI
    have hp := FastNaf7.residual_boundB (B := 64 * K.M.n) (Nat.le_of_lt hk) (j := D - m) (by omega_arith)
    have hp' : FastNaf7.residual k (D - m) ≤ 2 ^ (64 * K.M.n) :=
      Nat.le_trans hp (Nat.pow_le_pow_right (by decide) (by omega_arith))
    refine WP.mono (prepStep_ok hR hI.1 hb (by omega_arith) hp') fun u ⟨iu, ku, ou⟩ => ?_
    have he : D - (m - 1) = D - m + 1 := by omega_arith
    refine ⟨⟨?_, hI.2.1.trans ku, hI.2.2.trans ou⟩, ?_⟩
    · rw [he]; exact iu
    · rw [iu.count]; congr 1; omega_arith
  · intro t hI
    exact hI
  · refine ⟨?_, ka, ?_⟩
    · simpa only [Nat.sub_self] using ia
    · rw [ma]; intro _ _; rfl


end VG.Proof.Weierstrass.AArch64.PubNafWide
