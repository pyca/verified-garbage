module
public import VerifiedGarbage.Proof.P256.EcdhJac.State
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
public import VerifiedGarbage.Proof.P256.Linear.FortyOneCertificate
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic

/-! ### `P256.Linear.Linear41`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

theorem linear41_ok {s : State} {base : Addr} (hs : Scr s base 8192)
    (ha : wordsVal s.mem base 928 4<p) (hb : wordsVal s.mem base 960 4<p) :
    WP isa (.block (Impl.P256.Linear.linear41 512 928 960)) s fun t =>
      KeepRegs (clob 4) s t ∧ Outside base 512 32 s.mem t.mem ∧
      wordsVal t.mem base 512 4<p ∧
      wordsVal t.mem base 512 4=(4*wordsVal s.mem base 928 4+p-wordsVal s.mem base 960 4)%p := by
  have hb1 : ∀i∈FortyOneCertificate.original,instrBound i≤8192 := by decide +kernel
  have hb2 : ∀i∈FortyOneCertificate.optimized,instrBound i≤8192 := by decide +kernel
  have hc : ∀r∈FortyOneCertificate.optimized.flatMap instrClob,r∈clob 4 := by decide +kernel
  refine WP.mono (FortyOneCertificate.checked.refine (by decide) (by decide) hs hb1 hb2
    (FortyOne.reference_ok hs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb))
    fun t ⟨u,⟨_,ho,he⟩,hm,hk⟩ => ?_
  refine ⟨hk.mono hc,?_,?_,?_⟩
  · simpa only [hm] using ho
  · rw [hm,he]; exact Nat.mod_lt _ (by decide)
  · simpa only [hm] using he
end VG.Proof.P256.Linear

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M)

/-- A canonical linear combination, with the ordinary field-operation frame. -/
def LinearCorrect (code : List Instr) (o a b c d : Nat) : Prop :=
  ∀ {s : State} {base : Addr}, Scr s base 8192 →
    wordsVal s.mem base a 4<C.p → wordsVal s.mem base b 4<C.p →
    WP isa (.block code) s fun t =>
      KeepRegs (clob 4) s t ∧ Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4=(c*wordsVal s.mem base a 4+d*(C.p-wordsVal s.mem base b 4))%C.p

theorem linearField_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl)
    {code : List Instr} {o a b c d : Nat}
    (hc : LinearCorrect code o a b c d) (ho : Sl o)
    {base : Addr} {s : State} {V : List Nat} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl V E s) (ha : a∈V) (hb : b∈V) :
    WP isa (.block code) s fun t =>
      OpKeep M base o s t ∧ Inv M base 8192 C.p Sl (o::V)
        (Function.update E o (Fin.ofNat C.p c*E a-Fin.ofNat C.p d*E b)) t := by
  refine WP.mono (hc hi.scr (hi.lt a ha) (hi.lt b hb)) fun t ⟨kr,ko,hv⟩ => ?_
  have hk := linearKeep kr ko
  refine ⟨hk,hi.update layout ho hk ?_ ?_⟩
  · change wordsVal t.mem base o 4<C.p
    rw [hv]; exact Nat.mod_lt _ (Nat.pos_of_neZero C.p)
  · change toM C.p (2^256) (wordsVal t.mem base o 4)=_
    rw [hv,toM_linear (wordsVal s.mem base a 4) (wordsVal s.mem base b 4) c d (hi.lt b hb)]
    exact congrArg₂ (fun x y => Fin.ofNat C.p c*x-Fin.ofNat C.p d*y) (hi.val a ha) (hi.val b hb)

theorem linear41Field_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (h512 : Sl 512)
    {base : Addr} {s : State} {V : List Nat} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl V E s) (ha : 928∈V) (hb : 960∈V) :
    WP isa (.block (Impl.P256.Linear.linear41 512 928 960)) s fun t =>
      OpKeep M base 512 s t ∧ Inv M base 8192 C.p Sl (512::V)
        (Function.update E 512 (4*E 928-E 960)) t := by
  refine WP.mono (Linear.linear41_ok hi.scr (hi.lt 928 ha) (hi.lt 960 hb))
    fun t ⟨kr,ko,hlt,hv⟩ => ?_
  have hk := linearKeep kr ko
  refine ⟨hk,hi.update layout h512 hk hlt ?_⟩
  change toM C.p (2^256) (wordsVal t.mem base 512 4)=_
  change wordsVal t.mem base 512 4=(4*wordsVal s.mem base 928 4+C.p-wordsVal s.mem base 960 4)%C.p at hv
  rw [hv,toM_linear41 (wordsVal s.mem base 928 4) (wordsVal s.mem base 960 4) (hi.lt 960 hb)]
  exact congrArg₂ (fun x y => 4*x-y) (hi.val 928 ha) (hi.val 960 hb)
end VG.Proof.P256.EcdhDouble
