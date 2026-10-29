module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
/-! Modulus setup preserves the cached-generation controls in the upper header. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PrecomputeField.lean`, which only this module imported.
section

/-! Context creation reuses the verified public modulus loading and R² construction. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeField_ok (M : Mont) {s : State} {B np : Addr} {Z k : Nat} {nb : List Byte}
 (scratch : Scr s B Z) (base : s.gpr .x0=B) (room : slot ((k+7)/8) 8≤Z)
 (positive : 9≤k) (size : k<2^31)
 (length : word s.mem B (8*Public.sK)=BitVec.ofNat 64 k) (modulusPtr : word s.mem B (8*Public.sN)=np)
 (source : Src s B Z np nb) (span : InRegions (s.rd++s.wr) np k) (byteLength : nb.length=k)
 (odd : Spec.Rsa.os2ip nb%2=1) (normalized : 2^(64*((k+7)/8-1))≤Spec.Rsa.os2ip nb) :
 WP isa (seqs (pcLoadW++r2StepsPub M.mm)) s fun t =>
 ∃ mi, Good t B Z ((k+7)/8) mi ∧
 wv t.mem B (slot ((k+7)/8) 0) ((k+7)/8)=Spec.Rsa.os2ip nb ∧
 ((word t.mem B (slot ((k+7)/8) 0)).toNat*mi.toNat+1)%2^64=0 ∧
 wv t.mem B (slot ((k+7)/8) 4) ((k+7)/8)=2^(128*((k+7)/8))%Spec.Rsa.os2ip nb ∧
 Frm B (pcLoadRanges ((k+7)/8)++r2Ranges ((k+7)/8)) s.mem t.mem ∧ Keep mmRegs s t := by
 refine wp_seqs_append (by simp [pcLoadW,pcLoadWith]) (by simp [r2StepsPub]) ?_
 refine WP.mono (pcLoadW_ok scratch base room positive size length modulusPtr source span byteLength odd) ?_
 rintro u ⟨mi,good,modulus,inverse,frame,rest⟩
 refine WP.mono (r2Pub_ok M good room (by omega) (by omega) modulus inverse odd normalized) ?_
 rintro t ⟨goodT,boundT,valueT,frameT,restT⟩
 have nowrap : B.toNat+slot ((k+7)/8) 8≤2^64 := by have := scratch.nowrap;omega
 have sameMod : wv t.mem B (slot ((k+7)/8) 0) ((k+7)/8)=Spec.Rsa.os2ip nb :=
  (frameT.r2_wv nowrap (by decide) (by decide) (by decide) (by decide)).trans modulus
 have sameInverse : ((word t.mem B (slot ((k+7)/8) 0)).toNat*mi.toNat+1)%2^64=0 := by
  rw [frameT.r2_word nowrap (by decide) (by decide) (by decide) (by decide)]
  exact inverse
 have value : wv t.mem B (slot ((k+7)/8) 4) ((k+7)/8)=2^(128*((k+7)/8))%Spec.Rsa.os2ip nb := by
  rw [Nat.mod_eq_of_lt boundT] at valueT
  rw [←Nat.pow_add] at valueT
  have exponent : 64*((k+7)/8)+64*((k+7)/8)=128*((k+7)/8) := by omega
  rw [exponent] at valueT
  exact valueT
 exact ⟨mi,goodT,sameMod,sameInverse,value,
  (frame.mono (fun r hr => List.mem_append_left _ hr)).trans
   (frameT.mono (fun r hr => List.mem_append_right _ hr)),(rest.trans restT).mono (by simp)⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Impl.Bignum.Public

theorem precomputeField_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m')
 (lower : 16≤i) (upper : i<32) (counter : i≠sCnt) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega)
 intro r hr
 have belowN := hdr_lt_slot w aN upper
 have belowAcc := hdr_lt_slot w aAcc upper
 have belowTmp := hdr_lt_slot w aTmp upper
 have belowR2 := hdr_lt_slot w aR2 upper
 simp only [List.mem_append,pcLoadRanges,r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with (rfl|rfl|rfl|rfl) | (rfl|rfl|rfl|rfl)
 all_goals simp only [sW,sArr,sMinv] at *
 all_goals omega

theorem precomputeField_inscr {B : Addr} {w Z : Nat} {m m' : Mem}
 (frame : Frm B (pcLoadRanges w++r2Ranges w) m m') (room : slot w 8≤Z) : InScr B Z m m' := by
 intro x hx
 apply frame x
 intro r hr
 have inside : r.1+r.2≤slot w 8 := by
  rcases List.mem_append.mp hr with load | square
  · exact pcLoadRanges_le w r load
  · have two := slot_le (w:=w) (show Public.aAcc<8 by decide)
    have three := slot_le (w:=w) (show Public.aTmp<8 by decide)
    have four := slot_le (w:=w) (show Public.aR2<8 by decide)
    have count := hdr_lt_slot w 8 (show sCnt<32 by decide)
    simp only [r2Ranges,List.mem_cons,List.not_mem_nil,or_false] at square
    rcases square with rfl|rfl|rfl|rfl <;> omega
 exact Or.inr (by omega)

end VG.Proof.Ffdh.AArch64.Cached
