module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow
import VerifiedGarbage.Proof.Dsa.Joint
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Four joint windows consume two exponent bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem jointWinStep_ok (M : Mont) (Sq : MontS) {t s : State} {P : Addr} {w n xc g y E F v z j : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (hj : j < 4)
    (h : JointWinInv t P w minv n xc g y E F v z j s) :
    WP isa (Joint.window Sq.mm M.mm) s fun s' => s'.zf = some (decide (j + 1 = 4)) ∧
      JointWinInv t P w minv n xc g y E F v z (j + 1) s' := by
  have hp : 4 ^ j ≤ 64 := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (jointWindow_ok M Sq h.ctx h.tab hw hw' hR h.ylt h.val h.bytes
    (by have := Nat.mul_le_mul_left (256 * v + z) hp; omega) h.count (by omega) (by omega))
    fun s' ⟨hc, ht, hy, hval, hb, hn, hz', hf, hk⟩ => ⟨?_, hc, ht, hy, ?_, ?_, ?_,
      h.frm.trans hf, (h.keep.trans hk).mono (by decide)⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [hval, (VG.Proof.Dsa.joint_byte_step hv hz hj E F).1,
      (VG.Proof.Dsa.joint_byte_step hv hz hj E F).2]
  · rw [hb, Nat.pow_succ]; congr 1; ac_rfl
  · rw [hn]; congr 1

theorem jointWins_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {w n xc g y E F v z : Nat}
    {minv : BitVec 64} (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hv : v < 256) (hz : z < 256) (h : JointWinInv t P w minv n xc g y E F v z 0 t) :
    WP isa (.loop (Joint.window Sq.mm M.mm) .ne) t (JointWinInv t P w minv n xc g y E F v z 4) :=
  wp_upto (a := 0) (N := 4) (by decide) (JointWinInv t P w minv n xc g y E F v z)
    (fun _ _ hj _ hI => jointWinStep_ok M Sq hw hw' hR hv hz hj hI) (fun _ h => h) h

end VG.Proof.Dsa.X86_64
