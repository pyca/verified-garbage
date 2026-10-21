module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Established input traces supply the shared core's read-only argument view -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart ImportedPair inputReady_trace)

theorem input_trace (E : Environment) (e p q p' q' : Nat) :
    RelCT isa (SizedStart E e p q p' q') (loadInputs E.n) (ImportedPair E e p q p' q') := by
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  apply RelCT.assoc
  apply RelCT.assoc
  exact inputReady_trace E e p q p' q'

theorem runtime_input_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (RuntimeStart E sp e p q p' q') (loadInputs E.n) (RuntimeImported E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, imported⟩ := input_trace E e p q p' q' _ _ _ _ _ _ P.start A C
  obtain ⟨_, FS, KS⟩ := wp_result (loadInputs_ok P.start.inputs.left) A
  obtain ⟨_, FT, KT⟩ := wp_result (loadInputs_ok P.start.inputs.right) C
  exact ⟨trace, imported, P.left.afterFrame KS FS, P.right.afterFrame KT FT,
    P.leftArgs.keep KS FS, P.rightArgs.keep KT FT⟩

theorem loadInputs_front_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (RuntimeStart E sp e p q p' q') (selectIO loadInputs) (RuntimeImported E sp e p q p' q') :=
  selectIO_trace valid (fun _ _ P => P.start.inputs) (RuntimeStart.keepIO E sp e p q p' q')
    (runtime_input_trace E sp e p q p' q')

end VG.Proof.RsaKeyGen.X86.KeyRuntime
