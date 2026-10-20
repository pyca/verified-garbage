module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePrefix
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMontgomeryOut
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTable
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeSerialization
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeWords
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! The complete callable native public-context initialization. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont CombBuilder
open VG.Spec.Rsa.Mont (numAt)

theorem combPrecomputeEntered_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : CombPrecomputeFnInput p s) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry)
      (VG.Impl.Ffdh.Arm.CombPrecompute.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VG.Proof.Ffdh.Arm.VettedBound.code))
      (entered s) fun t =>
      Frame (combPrecomputeWrites p (entered s)) (entered s).mem t.mem ∧ t.gpr .r0=1 ∧
      Spec.Ffdh.generationPrecompute p.k p.dom=
        some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  have valid := Proof.Ffdh.domainValid_mod h.valid
  change Spec.Rsa.modulusValid p.P p.k=true at valid
  have facts := Proof.Bignum.valid_facts valid p.minLength
  have params : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom)=true := by
    have v := h.valid
    unfold Spec.Ffdh.domainValid at v
    simp only [Bool.and_eq_true] at v
    exact v.1
  have bitsPos : 0<bits p := CachedSample.generation_positive params
  have bitsBound : bits p≤8192 := CachedSample.bits_bound p
  have rowsPos : 0<Spec.Rsa.FixedBaseComb.rows (bits p) := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  have rowsFit : Spec.Rsa.FixedBaseComb.rows (bits p)<2^32 := by
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth
    omega
  let op := VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul
  have grouped : WP isa (.seq
    (.seq (.block VG.Impl.Ffdh.Arm.CombPrecompute.entry) (prefixCode backend))
    (.seq VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut
      (.seq (VG.Impl.Ffdh.Arm.CombPrecompute.table op) (VG.Impl.Ffdh.Arm.Domain.ret 1))))
      (entered s) (fun t => Frame (combPrecomputeWrites p (entered s)) (entered s).mem t.mem ∧ t.gpr .r0=1 ∧
        Spec.Ffdh.generationPrecompute p.k p.dom=
          some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) := by
    rw [WP.seq_iff]
    refine WP.mono (enteredPrefix_ok backend s h) ?_
    rintro u ⟨memory,header,modulus,r2,frameU⟩
    rw [WP.seq_iff]
    refine WP.mono (montgomeryOut_ok u memory) ?_
    rintro v ⟨memoryV,workspaceV,montgomery,frameV,headerV,restV⟩
    rw [modulus,r2] at montgomery
    have modulusV := (workspaceV.number (j:=0) (memory.ready.width ▸ memory.ready.layout.2.2.1) (by decide)).trans modulus
    have r2V := (workspaceV.number (j:=4) (memory.ready.width ▸ memory.ready.layout.2.2.1) (by decide)).trans r2
    have headersV : Spec.Rsa.wordsAt v.mem (State.addr p.output) 3=
        [BitVec.ofNat 64 (bits p),BitVec.ofNat 64 ((bits p+7)/8),BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (bits p))] := by
      have preserved := wordsAt_eq (d:=0) (count:=3) headerV (by decide)
      simp only [off,BitVec.add_zero] at preserved
      exact preserved.trans header
    rw [WP.seq_iff]
    refine WP.mono (table_ok backend v memoryV modulusV r2V facts.1 rowsPos rowsFit) ?_
    rintro z ⟨coreZ,tableZ,headerZ,frameZ,restZ⟩
    have preservedZ := wordsAt_eq (d:=0) (count:=3) headerZ (by omega)
    simp only [off,BitVec.add_zero] at preservedZ
    have headersZ := preservedZ.trans headersV
    have montgomeryZ := (wordsAt_eq (d:=24) (count:=2*p.w) headerZ (by omega)).trans montgomery
    have serialized := canonical_precompute valid headersZ montgomeryZ tableZ
    refine WP.mono (ret_ok z 1 (by decide)) ?_
    rintro t ⟨⟨result,memT⟩,restT⟩
    have fullV : Frame (combPrecomputeWrites p (entered s)) u.mem v.mem := frameV.sub (by
      intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact ⟨⟨State.addr p.output,bytes p⟩,by simp [combPrecomputeWrites],Offset.sub_base _ (by have := bytes_eq p;omega)⟩)
    have fullZ : Frame (combPrecomputeWrites p (entered s)) v.mem z.mem := by
      simpa only [productWrites,combPrecomputeWrites] using frameZ
    rw [memT] at *
    exact ⟨frameU.trans (fullV.trans fullZ),result,serialized⟩
  obtain ⟨trace,t,exec,post⟩ := grouped
  cases exec with
  | seq hprefix htail =>
    cases hprefix with
    | seq hentry hprepared =>
      cases hprepared with
      | seq hprepare hboundmeta =>
        cases hboundmeta with
        | seq hbound hmetadata =>
          exact ⟨_,_,.seq hentry (.seq hprepare (.seq hbound (.seq hmetadata htail))),post⟩

theorem combPrecomputeFn_ok (backend : MontBackend) (s : State) {p : Inputs}
    (h : CombPrecomputeFnInput p s) :
    WP isa (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VG.Proof.Ffdh.Arm.VettedBound.code) s fun t =>
      abiPreserved s t ∧ t.gpr .r0=1 ∧ Spec.Ffdh.generationPrecompute p.k p.dom=
        some (Spec.Rsa.wordsAt t.mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k)) := by
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.code
  refine framed_of_separate _ s (by have := h.stackFits;omega) (combPrecomputeWrites p (entered s))
    (fun mem status => status=1 ∧ Spec.Ffdh.generationPrecompute p.k p.dom=
      some (Spec.Rsa.wordsAt mem (State.addr p.output) (Spec.Ffdh.generationPrecomputedWords p.k))) h.saved ?_
  exact combPrecomputeEntered_ok backend s h

end VG.Proof.Ffdh.Arm
