module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedTest
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Exact three-byte 65537 takes the shortcut. Other encodings, including
leading-zero encodings of 65537, retain the existing general exponent loop. -/
theorem fastLoop_dispatch (M : Mont) {s : State} {B ep : Addr} {Z w L : Nat} {mi : BitVec 64}
    {eb : List Byte} {Q : State → Prop}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hL : L < 2^31)
    (he : word s.mem B (8*sE) = ep) (hlen : word s.mem B (8*sElen) = BitVec.ofNat 64 L)
    (hs : Src s B Z ep eb) (hel : eb.length = L)
    (fast : ∀ t, t.mem = s.mem → Keep [.x3,.x4,.x8] s t →
      L = 3 → Spec.Rsa.os2ip eb = 65537 → WP isa (Folded.fixedLoop M.mm) t Q)
    (slow : ∀ t, t.mem = s.mem → Keep [.x3,.x4,.x8] s t →
      ¬ (L = 3 ∧ Spec.Rsa.os2ip eb = 65537) → WP isa (Precomputed.expLoop M.mm) t Q) :
    WP isa (Folded.fastLoop M.mm) s Q := by
  unfold Folded.fastLoop
  refine WP.seq (WP.mono (lengthTest_ok hg hZ hL hlen) fun t ⟨ht, hm, kt⟩ => ?_)
  refine WP.ite (decide (L = 3)) ht (fun h3 => ?_) (fun hn => slow t hm (kt.mono (by decide)) (by
      intro hc
      have hnFalse : L ≠ 3 := by simpa using hn
      exact hnFalse hc.1))
  have heq : L = 3 := by simpa only [decide_eq_true_eq] using h3
  have hel3 : eb.length = 3 := hel.trans heq
  let a := eb[0]'(by omega)
  let b := eb[1]'(by omega)
  let c := eb[2]'(by omega)
  have heb : eb = [a,b,c] := List.eq_getElem_of_length_eq_three eb hel3
  have hg' : Good t B Z w mi :=
    ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩
  have htRead (i : Nat) (hi : i < 3) : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [kt.rd, kt.wr]
    exact hs.rd i (by omega)
  have ha : t.mem ep = a := by
    rw [hm]
    simpa only [BitVec.add_zero] using hs.val 0 (by omega)
  have hb : t.mem (ep+1#64) = b := by rw [hm]; exact hs.val 1 (by omega)
  have hc : t.mem (ep+2#64) = c := by rw [hm]; exact hs.val 2 (by omega)
  refine WP.seq (WP.mono (bytesTest_ok hg' hZ (by rw [hm]; exact he) a b c htRead ha hb hc)
    fun u ⟨hu, hum, ku⟩ => ?_)
  refine WP.ite (decide (Spec.Rsa.os2ip [a,b,c] = 65537)) hu
    (fun h65 => fast u (hum.trans hm) ((kt.trans ku).mono (by decide)) heq ?_)
    (fun hn => slow u (hum.trans hm) ((kt.trans ku).mono (by decide)) (by
      intro hc
      have hnFalse : Spec.Rsa.os2ip eb ≠ 65537 := by simpa [heb] using hn
      exact hnFalse hc.2))
  rw [heb]
  simpa only [decide_eq_true_eq] using h65

end VG.Proof.Bignum.AArch64.FoldedPublic
