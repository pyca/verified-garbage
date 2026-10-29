module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry

/-! # The native seven-port result is the shared encoded key operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def encodedOperation (E : Environment) (m : Mem) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Spec.RsaKeyGen.keyOp E.primeLength
    (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
    (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len)
    (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)

def EncodedResult (E : Environment) (m : Mem) (t : State) : Prop :=
  let result := encodedOperation E m
  let outs := (List.range 7).map E.outputRegion
  (t.gpr .eax).toNat = Spec.RsaKeyGen.keyStatus result ∧
    match result with
    | .inl (.ok ys) => outs.map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) = ys
    | _ => ∀ r ∈ outs, Spec.Rsa.bytesAt t.mem r.base r.len = List.replicate r.len 0

theorem BodyOutcome.encoded {E : Environment} {m : Mem} {t : State} (v : E.Valid) (R : BodyOutcome E m t) :
    EncodedResult E m t := by
  have widths := v.widths
  have bits : 16 * E.primeLength = 32 * E.n := by omega
  unfold BodyOutcome WrittenCore at R
  rw [show E.outputs.n = E.n from rfl] at R
  unfold EncodedResult encodedOperation Spec.RsaKeyGen.keyOp
  rw [bits]
  cases code : Spec.RsaKeyGen.keyFromPrimes (32 * E.n)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) with
  | inr u =>
    cases u
    rw [code] at R
    refine ⟨R.1, ?_⟩
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have bound := List.mem_range.mp hi
    simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
  | inl result =>
    cases result with
    | error failure =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hi
      simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
    | ok key =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      have values : ∀ i < 7, Spec.Rsa.bytesAt t.mem (E.outputRegion i).base (E.outputRegion i).len =
          Spec.Rsa.i2osp (keyField key i) (E.outputLength i) := by
        intro i hi
        simpa only [v.outputRegion hi, v.outputLength hi] using R.2 i hi
      have joined : ((List.range 7).map E.outputRegion).map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) =
          (List.range 7).map (fun i => Spec.Rsa.i2osp (keyField key i) (E.outputLength i)) := by
        rw [List.map_map]
        exact List.map_congr_left fun i hi => values i (List.mem_range.mp hi)
      exact joined

end VG.Proof.RsaKeyGen.X86.Key
