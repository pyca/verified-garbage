module
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Prep
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64

/-- Both recoders use all nine words, including the carry digit. -/
theorem dimensions : P521Joint.K.M.n=9 ∧ P521Joint.KG.M.n=9 ∧
 P521Joint.K.bits=4024 ∧ P521Joint.KG.bits=3304 ∧
 PubNaf.cacheAt P521Joint.K 1+128*P521Joint.K.M.n=8056 := by decide

/-- The generator digits stop before the arithmetic temporary at slot54. -/
theorem generator_apart : ∀w∈winW P521Joint.K ++ PubNaf.cacheW P521Joint.K,
 P521Joint.KG.bits+577≤w.1 ∨ w.1+w.2≤P521Joint.KG.bits := by decide

theorem generator_peer_apart : P521Joint.KG.bits+577≤P521Joint.K.bits := by decide

/-- Neither recoder overwrites a live verifier field or saved register. -/
theorem fields_apart : ∀i∈List.range 45,i≠TMP →
 p521.sl i+72≤P521Joint.KG.bits ∧ p521.sl i+72≤P521Joint.K.bits := by decide

def prepRanges : List (Nat×Nat) := [(P521Joint.KG.bits,577),(P521Joint.K.bits,577)]

/-- Exact production recoding, preserving the original peer scalar and generator digits. -/
theorem prep_ok {s : State} {base : Addr} (hs : Scr s base 8192) :
 WP isa (.seq P521Joint.prep7 (Impl.Weierstrass.AArch64.PubNaf.prep P521Joint.K (p521.sl V))) s fun t=>
 Scr t base 8192 ∧ t.gpr .x19=0 ∧
 (∀j<577,t.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 (wordsVal s.mem base (p521.sl U) 9) j) ∧
 (∀j<577,t.mem (off base (P521Joint.K.bits+j))=Naf5.byte (wordsVal s.mem base (p521.sl V) 9) j) ∧
 KeepRegs (VG.Proof.Weierstrass.AArch64.PubNaf.clobs 9) s t ∧ Unch base prepRanges s.mem t.mem := by
 refine WP.seq (WP.mono (PubNafWide.prep_ok P521Joint.KG (Or.inr rfl)
   (PubNaf.regs_ok9 9 (by decide) (by decide)) hs (by decide) (by decide) (by decide) (by decide))
   fun a ⟨ha,_,ga,ka,oa⟩=>?_) 
 have va : wordsVal a.mem base (p521.sl V) 9=wordsVal s.mem base (p521.sl V) 9 :=
   oa.wordsVal (Or.inl (by decide)) (by decide)
 refine WP.mono (PubNaf.prep_ok P521Joint.K (PubNaf.regs_ok9 9 (by decide) (by decide))
   ha (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht,kt,ot⟩=>?_
 refine ⟨ht.scr,?_,?_,?_,ka.trans kt,oa.unch.trans ot.unch⟩
 · rw [ht.count,Nat.sub_self]; rfl
 · intro j hj
   rw [ot.unch.byte (by
     intro w hw
     rw [List.mem_singleton.mp hw]
     have := generator_peer_apart
     change P521Joint.KG.bits+j+1≤P521Joint.K.bits ∨ _
     omega)
     (by have := hs.nowrap; change 3304+j<2^64; omega)]
   exact ga j hj
 · have h := ht.digits
   change ∀j<577,t.mem (off base (P521Joint.K.bits+j))=Naf5.byte (wordsVal a.mem base (p521.sl V) 9) j at h
   rw [va] at h
   exact h
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
