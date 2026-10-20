module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointWindow
import VerifiedGarbage.Proof.Dsa.Joint
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild

/-! # Four joint windows consume two exponent bytes -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- After `j` windows of the bytes `v` (of `u`) and `z` (of `v`) from `t₀`,
where `Y ≡ g^E y^F R`. -/
structure JointWinInv (t₀ : State) (P : Addr) (w : Nat) (minv : BitVec 64)
    (n xc g y E F v z j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P w minv n xc
  tab : JointTab t.mem P w n g y
  ylt : wv t.mem P (slot w aY) w < n
  val : wv t.mem P (slot w aY) w % n =
    (g ^ (E * 4 ^ j + v / 4 ^ (4 - j)) * y ^ (F * 4 ^ j + z / 4 ^ (4 - j))) * 2 ^ (64 * w) % n
  bytes : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 ((256 * v + z) * 4 ^ j)
  count : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (4 - j)
  frm : Frm P (crtWinRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem jointWinStep_ok (M : Mont) {t s : State} {P : Addr} {w n xc g y E F v z j : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (hj : j < 4)
    (h : JointWinInv t P w minv n xc g y E F v z j s) :
    WP isa (seqs (Joint.window M.mm)) s fun s' =>
      JointWinInv t P w minv n xc g y E F v z (j + 1) s' ∧ ((s'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 4) := by
  have hp : 4 ^ j ≤ 64 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (jointWindow_ok M h.ctx h.tab hw hw' hR h.ylt h.val h.bytes
    (by have := Nat.mul_le_mul_left (256 * v + z) hp; omega_arith) h.count (by omega_arith))
    fun s' ⟨hc, ht, hy, hval, hb, hn, h3, hf, hk⟩ => ⟨⟨hc, ht, hy, ?_, ?_, ?_,
      h.frm.trans hf, (h.keep.trans hk).mono (by decide)⟩, ?_⟩
  · rw [hval, (VG.Proof.Dsa.joint_byte_step hv hz hj E F).1,
      (VG.Proof.Dsa.joint_byte_step hv hz hj E F).2]
  · rw [hb, Nat.pow_succ]; congr 1; ac_rfl
  · rw [hn]; congr 1
  · rw [h3, cnt_ne (by omega_arith)]; omega_arith

theorem jointWins_ok (M : Mont) {t : State} {P : Addr} {w n xc g y E F v z : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (h : JointWinInv t P w minv n xc g y E F v z 0 t) :
    WP isa (.loop (seqs (Joint.window M.mm)) (.nonzero .x .x3)) t
      (JointWinInv t P w minv n xc g y E F v z 4) :=
  count_loop (cr := .x3) (n := 4) (by decide) (JointWinInv t P w minv n xc g y E F v z)
    (fun _ hj _ hI => jointWinStep_ok M hw hw' hR hv hz hj hI) h

end VG.Proof.Dsa.AArch64
