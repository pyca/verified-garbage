module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFinish
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFieldFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! All arithmetic after public metadata: modulus loading, R², prefix and table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeArithmetic_ok (M : Mont) {s : State} {p : Parameters} {domPtr : Addr} {dom nb gb : List Byte}
 (scratch : Scr s p.B p.Z) (base : s.gpr .x0=p.B) (space : ContextSpace p s)
 (modulusSource : Src s p.B p.Z domPtr nb) (modulusSpan : InRegions (s.rd++s.wr) domPtr p.k)
 (nbLength : nb.length=p.k) (nbValue : Spec.Rsa.os2ip nb=p.P)
 (odd : p.P%2=1) (normalized : 2^(64*(p.w-1))≤p.P)
 (source : GeneratorSource p (domPtr+BitVec.ofNat 64 p.k) gb s)
 (words : p.w=(p.k+7)/8) (positive : 9≤p.k) (size : p.k<2^31) (reduced : p.G<p.P)
 (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=domPtr)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))
 (header : Spec.Rsa.wordsAt s.mem p.ctx 3=
  [BitVec.ofNat 64 p.N,BitVec.ofNat 64 ((p.N+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)])
 (modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p) (generator : p.G=(Spec.Ffdh.domainOf p.k dom).g)
 (policy : p.N=Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k dom)) :
 WP isa (.seq (seqs (pcLoadW++r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) s fun t =>
 t.gpr .x0=1#64 ∧
 Spec.Rsa.wordsAt t.mem p.ctx (Spec.Ffdh.generationPrecomputedWords p.k)=VG.Proof.Ffdh.generationValues p.k dom ∧
 PublicFrame p s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 rw [WP.seq_iff]
 have room : slot ((p.k+7)/8) 8≤p.Z := by rw [←words];exact p.room
 refine WP.mono (precomputeField_ok M scratch base room positive size length domain modulusSource modulusSpan nbLength
  (by rw [nbValue];exact odd) (by rw [nbValue,←words];exact normalized)) ?_
 rintro a ⟨mi,goodA,modulusA,inverseA,r2A,frameA,restA⟩
 let q : Parameters := {p with mi:=mi}
 have fieldA : FieldInitial q a := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [q,words] using goodA
  · simpa only [q,words,nbValue] using modulusA
  · simpa only [q,words] using inverseA
  · simpa only [q,words,nbValue] using r2A
 have inscr : InScr p.B p.Z s.mem a.mem := by
  apply precomputeField_inscr (w:=p.w) _ p.room
  simpa only [words] using frameA
 have frame (i : Nat) (hi : 16≤i) (hi' : i<32) (counter : i≠Public.sCnt) :
  word a.mem p.B (8*i)=word s.mem p.B (8*i) := precomputeField_header frameA hi hi' counter
 have spaceA : ContextSpace q a := ⟨(space.after restA).writable,space.outside⟩
 have sourceAP := source.after_inscr inscr restA
 have sourceA : GeneratorSource q (domPtr+BitVec.ofNat 64 q.k) gb a :=
  ⟨sourceAP.source,source.length,source.value,source.separate⟩
 have headerA : Spec.Rsa.wordsAt a.mem p.ctx 3=Spec.Rsa.wordsAt s.mem p.ctx 3 := by
  apply prefixWords_unchanged (n:=3) space
  intro i hi
  exact inscr _ (space.outside i (by omega))
 refine WP.mono (precomputeFinish_ok M fieldA spaceA sourceA words (by change 0<p.k;omega) size reduced bits
  ((frame sCtx (by decide) (by decide) (by decide)).trans context)
  ((frame sDom (by decide) (by decide) (by decide)).trans domain)
  ((frame sLen (by decide) (by decide) (by decide)).trans length)
  ((frame sRows (by decide) (by decide) (by decide)).trans rows)
  (headerA.trans header) modulus generator policy) ?_
 rintro t ⟨status,canonical,frameT,restT⟩
 exact ⟨status,canonical,(PublicFrame.of_inscr inscr).trans frameT,
  (restA.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
