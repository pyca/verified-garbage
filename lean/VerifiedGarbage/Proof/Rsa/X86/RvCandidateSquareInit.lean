module

public import VerifiedGarbage.Proof.Rsa.X86.RvSquareInit
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareLoop
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps

/-! # The squaring search following a candidate's exponentiation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n sqStart sqIter)

theorem candSquareInit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m y eLen dLen : Nat}
    (h : KS g s0 (upd A mY (y * 2 ^ (64 * g.n) % m)) liveSq AW [wR] V slotsExp s)
    (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (yl : y < m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (limit : 8 * (dLen + eLen) ≤ 16384) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candSquareInit s fun t =>
      SI g s0 A AW V m 0 (8 * (dLen + eLen))
      (sqStart m y) t := by
  have cop := VG.Proof.Bignum.coprime_pow2 odd (64 * g.n)
  unfold VG.Impl.Rsa.X86.RecoverRt.candSquareInit VG.Impl.Rsa.X86.RecoverRt.eqAt
  simp only [seqs]
  refine WP.seq (WP.mono (h.eqS_w (d := sE1) (a := mY) (b := aO)
    (by simp [liveSq]) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.eqS_w (d := sE2) (a := mY) (b := aNg)
    (by simp [liveSq]) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, _⟩ => ?_)
  have eo : (if y * 2 ^ (64 * g.n) % m = A aO then 1 else 0) = b2n (decide (y = 1)) := by
    simp only [one, VG.Proof.Rsa.eq_one_mont cop hm yl rfl]
    simp [b2n]
  have en : (if y * 2 ^ (64 * g.n) % m = A aNg then 1 else 0) = b2n (decide (y = m - 1)) := by
    simp only [neg, VG.Proof.Rsa.eq_neg_mont cop hm yl rfl]
    simp [b2n]
  simp only [upd_self, upd_ne _ _ (by decide : aO ≠ mY), upd_ne _ _ (by decide : aNg ≠ mY), eo, en] at h2
  refine WP.mono (sqInit_ok h2 (e1 := decide (y = 1)) (e2 := decide (y = m - 1))
    (by simp) (by simp) (by simp [upd, sE1, sE2]) (by simp [upd]) ae ad (by omega)) fun s3 h3 => ?_
  have initial : SI g s0 A AW V m 0 (8 * (dLen + eLen)) (sqStart m y) s3 := by
    refine h3.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
    intro d hd
    simp only [slotsSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [slotsExp, VS, upd, sqStart, b2n, sInv, sCnt, sTc, sCand, sK, sDone, sOk, sE1, sE2]
  exact initial

end VG.Proof.Rsa.X86.Recover
