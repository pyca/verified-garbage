module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

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
