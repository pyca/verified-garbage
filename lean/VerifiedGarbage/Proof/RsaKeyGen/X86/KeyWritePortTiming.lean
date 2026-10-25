module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHeaderTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Masked key output uses only public pointers and byte lengths in its trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def OutputPair (E : Environment) (s t : State) : Prop :=
  InputPair E s t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t ∧
    slot s.mem E.base kOk ≤ 1 ∧ slot t.mem E.base kOk ≤ 1

theorem selectInput_ok {E : Environment} {s : State} (h : Input E s) {j : Nat} (hj : j < 32)
    (bit : slot s.mem E.base kOk ≤ 1) :
    WP isa (sel E.n j aZero j kOk) s fun t => Input E t ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.mono (sel_ok h.ws hj (by decide) hj (by decide) bit) fun t ⟨ht, O, _, K⟩ => ?_
  refine ⟨h.keep ht K ?_, K⟩
  intro d hd
  apply BitVec.eq_of_toNat_eq
  exact O.slot (by unfold hdr; omega) (by simp)

theorem selectOutput_trace (E : Environment) (j : Nat) (hj : j < 32) :
    RelCT isa (OutputPair E) (sel E.n j aZero j kOk) (InputPair E) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, _⟩ := key_public_trace (sel_public E.n j aZero j kOk) _ _ _ _ _ _ P.2.1 A C
  obtain ⟨leftInput, leftKeeps⟩ := wp_result (selectInput_ok P.1.left hj P.2.2.1) A
  obtain ⟨rightInput, rightKeeps⟩ := wp_result (selectInput_ok P.1.right hj P.2.2.2) C
  refine ⟨trace, leftInput, rightInput, ?_⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.1.stack

theorem storeBE_key_trace (src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (argumentTaint true)) (VG.Impl.Bignum.X86.storeBE src)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  exact erased_relCT (VG.Impl.Bignum.X86.storeBE src) (VG.Impl.Bignum.X86.storeBE 0)
    (VG.Taint.hintOf taint (argumentTaint true) (VG.Impl.Bignum.X86.storeBE 0)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem writePort_trace (E : Environment) (i : Nat) (hi : i < 7) :
    RelCT isa (OutputPair E) (writePort E.n i) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold writePort writeArray seqs
  have header : (.block [.mov .ebx (.mem (VG.Impl.Mont.X86.sc (8 * i))),
      .mov .ecx (.mem (VG.Impl.Mont.X86.sc (8 * i + 4)))] : Prog isa) = headerPair true (2 * i) (2 * i + 1) := by
    unfold headerPair argumentReg
    rw [show 4 * (2 * i) = 8 * i by omega, show 4 * (2 * i + 1) = 8 * i + 4 by omega]
    rfl
  rw [header]
  exact RelCT.seq (selectOutput_trace E (outputIndex i) (outputIndex_bound hi))
    (RelCT.seq (headerPair_trace E (2 * i) (2 * i + 1) (by omega) (by omega) true)
      (storeBE_key_trace (VG.Impl.Rsa.X86.Keys.slot E.n (outputIndex i))))

end VG.Proof.RsaKeyGen.X86.Key
