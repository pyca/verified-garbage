module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.Rd.DetPartsW
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW1
import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2B
import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeSqrtW
import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2A
import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdWTime
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # Appendix C.2 by words on i686: `det`'s timing

`d e - 1` and the factors are checked by the taint analysis; the pieces between them have their own
timing (`twos_relCT` … `sqrt_relCT`); `det_relCT` composes them.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys

theorem deMinusPubW : PubA deMinus := ⟨_, by taint_decide⟩
theorem factorsPubW : PubA factors := ⟨_, by taint_decide⟩

/-- `d e - 1`, then the views of `twos`' inputs. -/
theorem deMinus_step {g : Geo} {n : Nat} {s : State} (h : D0W g n s) : WP isa deMinus s (TW0 g n) := by
  obtain ⟨s0, A, AW, V, hk, hz, hn⟩ := h
  refine WP.mono (deMinus_ok hk rfl hz) fun t ⟨AW1, h1, _, z1⟩ => ?_
  have z1' : AW1 0 = 0 := z1
  have h1v := (h1.view (j := VG.Impl.Rsa.X86.Recover.wZ) (by simp)).view (j := wX) (by simp)
  have h1t := h1v.mono (live' := [aZ0, aX2, VG.Impl.Rsa.X86.Recover.aN]) (liveW' := [wX])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  exact ⟨s0, _, _, _, h1t, by simp [upd, aZ0, wX, VG.Impl.Rsa.X86.Recover.wZ, z1'],
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hn⟩

theorem deMinus_relCT {g : Geo} (n : Nat) :
    RelCT isa (RA (D0W g n) (D0W g n)) deMinus (RA (TW0 g n) (TW0 g n)) :=
  deMinusPubW.relCT (fun _ h => deMinus_step h) (fun _ h => deMinus_step h)

/-- `det` related, from the GCD's and `divA`'s timing. -/
theorem det_relCT_of {g : Geo} (pg : PubG g) (n a : Nat) (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (ha : g.args nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w) (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a))
    (gcdR : RelCT isa (RA (GW0 g n) (GW0 g n)) gcdFused (RA (GW1 g n) (GW1 g n)))
    (divAR : RelCT isa (RA (PA1 g n) (PA1 g n)) divA (RA (DA1 g n) (DA1 g n))) :
    RelCT isa (RA (D0W g n) (D0W g n)) det (RA (fun _ => True) (fun _ => True)) := by
  have t13 : VG.Proof.Bignum.ShiftStages.tz (n - 1) < 2 ^ 13 :=
    Nat.lt_of_lt_of_le (VG.Proof.Bignum.ShiftStages.tz_lt (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le n 1) hn'))
      (by simp only [VG.Proof.Rsa.X86.WordRt.wq]; omega)
  unfold det
  simp only [seqs]
  refine VG.RelCT.seq (deMinus_relCT n) ?_
  refine VG.RelCT.seq (twos_relCT pg n three small t13) ?_
  refine VG.RelCT.seq (gcdSet_relCT pg n) ?_
  refine VG.RelCT.seq gcdR ?_
  refine VG.RelCT.seq (aProduct_relCT pg n) ?_
  refine VG.RelCT.seq divAR ?_
  refine VG.RelCT.seq (divB_relCT pg n a ha ha0 ha1 haw hn') ?_
  refine VG.RelCT.seq (square_relCT pg n) ?_
  refine VG.RelCT.seq (minus4n_relCT pg) ?_
  refine VG.RelCT.seq (sqrt_relCT pg a ha (by omega) ha1 haw) ?_
  exact factorsPubW.relCT'

/-- `det`'s timing: its pieces in turn, between their stages. -/
theorem det_relCT {g : Geo} (pg : PubG g) (n a : Nat) (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (ha : g.args nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w) (hn0 : 2 ^ (32 * (VG.Proof.Rsa.X86.WordRt.wq a - 1)) ≤ n)
    (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    RelCT isa (RA (D0W g n) (D0W g n)) det (RA (fun _ => True) (fun _ => True)) :=
  det_relCT_of pg n a three small ha ha0 ha1 haw hn' (gcdFused_relCT pg n)
    (divA_relCT pg n a ha ha0 ha1 haw hn0 hn')

end VG.Proof.Rsa.X86.Recover
