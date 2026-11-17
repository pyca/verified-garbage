module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! ### `Dsa.X86_64.RandomSampleAgreement`, which this module and modules that import it used -/

section

/-! Apply sampler leakage to contexts with independent secret tapes and memories. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_context_eq {C D : RandomContext}
    (hb : C.B = D.B) (hm : C.initialMem = D.initialMem)
    (hr : C.R = D.R) (hq : C.Q = D.Q) (hbytes : C.qBytes = D.qBytes) (hrand : C.rand = D.rand) : C = D := by
  cases C
  cases D
  cases hb
  cases hm
  cases hr
  cases hq
  cases hbytes
  cases hrand
  rfl

theorem random_sample_agreement {C D : RandomContext} {used da db : Nat} {s t : State}
    (hs : RandomReady C used da s) (ht : RandomReady D used db t)
    (hq : 1 < Spec.Dsa.decodeBE C.qBytes)
    (hB : C.B = D.B) (hR : C.R = D.R) (hQ : C.Q = D.Q) (hqBytes : C.qBytes = D.qBytes)
    (hlen : C.rand.length = D.rand.length)
    (htrace : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (C.rand.drop used)).trace =
      (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE D.qBytes) 128 (D.rand.drop used)).trace)
    {ts tt : List Leak} {u v : State} (es : Exec isa Random.sample s ts u) (et : Exec isa Random.sample t tt v) :
    ts = tt := by
  let p : RandomSamplePublic := {
    draw := {
      B := C.B
      R := C.R
      Q := C.Q
      qBytes := C.qBytes
      randLen := C.rand.length
      used := used
      draws := 128
      qlen := C.qlen
      positive := C.positive
      randBound := C.randBound
      usedBound := hs.usedBound
      drawsPos := by decide
      drawsBound := by decide }
    trace := (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (C.rand.drop used)).trace
    valid := hq }
  have hcs : p.draw.context C.rand rfl C.initialMem = C :=
    random_context_eq rfl rfl rfl rfl rfl rfl
  have hds : p.draw.context D.rand hlen.symm D.initialMem = D :=
    random_context_eq hB rfl hR hQ hqBytes rfl
  have hp : Two RandomSamplePre s t := by
    refine ⟨p, ⟨rfl, C.rand, rfl, C.initialMem, da, ?_, rfl⟩,
      rfl, D.rand, hlen.symm, D.initialMem, db, ?_, ?_⟩
    · rw [hcs]; exact hs
    · rw [hds]; exact ht
    · change (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE C.qBytes) 128 (D.rand.drop used)).trace = _
      rw [hqBytes]
      exact htrace.symm
  exact (random_sample_ct _ _ _ _ _ _ hp es et).1

end VG.Proof.Dsa.X86_64

end

end

/-! Transfer public argument and trace agreement to the complete nonce sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_draw_agree {s t : State} {used : Nat} (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace) :
    (randomSignDraw (randomInput s) used).used = (randomSignDraw (randomInput t) used).used ∧
      (randomSignDraw (randomInput s) used).scalar.isSome = (randomSignDraw (randomInput t) used).scalar.isSome ∧
      Random.sampleStatus (randomSignDraw (randomInput s) used) = Random.sampleStatus (randomSignDraw (randomInput t) used) := by
  have hq : (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key).params.q =
      (Spec.Dsa.privateKeyBytes (randomInput t).pLen (randomInput t).qLen (randomInput t).key).params.q := by
    rw [← random_q_decode, ← random_q_decode, hpub.qbytes]
  unfold randomSignDraw at htrace ⊢
  rw [hq] at htrace ⊢
  exact Random.sample_trace_agree htrace

theorem random_sign_sample_agreement {extra : Nat} {s t a b : State}
    {hs : RandomSignABI extra s} {ht : RandomSignABI extra t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    {used fuel : Nat} (ha : RandomSignRunning hs hqs used fuel a) (hb : RandomSignRunning ht hqt used fuel b)
    (hpub : RandomSignPublicAgree s t)
    (htrace : (randomSignDraw (randomInput s) used).trace = (randomSignDraw (randomInput t) used).trace)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa Random.sample a tsa u) (eb : Exec isa Random.sample b tsb w) :
    tsa = tsb := by
  obtain ⟨ma, da, hra⟩ := ha.ready
  obtain ⟨mb, db, hrb⟩ := hb.ready
  apply random_sample_agreement hra hrb hqs hpub.base (hpub.args 3 (by decide)) _ hpub.qbytes _ _ ea eb
  · change s.gpr .rcx + s.gpr .r9 = t.gpr .rcx + t.gpr .r9
    rw [hpub.regs .rcx (by decide), hpub.regs .r9 (by decide)]
  · simp only [randomContextOf, randomInput, bytesAt_length, hpub.args 4 (by decide)]
  · change (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes s)) 128 ((randomInput s).rand.drop used)).trace =
      (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (randomQBytes t)) 128 ((randomInput t).rand.drop used)).trace
    rw [random_q_decode, random_q_decode]
    exact htrace

end VG.Proof.Dsa.X86_64
