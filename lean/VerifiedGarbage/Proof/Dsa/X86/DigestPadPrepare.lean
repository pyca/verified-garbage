module

public import VerifiedGarbage.Proof.Dsa.X86.DigestPadValue
public import VerifiedGarbage.Proof.Dsa.X86.DigestPadInstall
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.PointerTiming

/-! # Preparing a fixed-width digest while retaining caller operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86

def padRanges : List (Nat × Nat) := [(DigestPad.output, 32), (Layout.field .digest, 4)]

theorem digestPadPrepare_ok {s : State} {base : Addr} {size len : Nat}
    (hs : Scr s base size) (space : DigestPad.output + 32 ≤ size)
    (B : CallerBuffer s base size (.input .digest) len) (hl : len ≤ 32) :
    WP isa (.block (DigestPad.prepare len)) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off base DigestPad.output) 32) =
        operandValue s base (.input .digest) len ∧
      pointerValue base t (.input .digest) = s.gpr .edi + BitVec.ofNat 32 DigestPad.output ∧
      Outs base padRanges s.mem t.mem ∧ Keeps [.esi, .eax] s t := by
  have hz : Layout.saved ≤ size := by change 15712 + 32 ≤ size at space; change 8256 ≤ size; omega
  unfold DigestPad.prepare
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (pointer_ok hs hz (.input .digest)) fun u ⟨P, K, O⟩ => ?_)
  refine WP.block_append (WP.mono (digestPadPrefix_ok (hs.of_keeps K (by decide)) space P hl B.fits
    (by intro i hi; rw [K.2.1, K.2.2]; exact B.read i 1 (by omega)) B.apart 32 (Nat.le_refl _))
    fun v ⟨Bytes, Frame, Keep⟩ => ?_)
  have Ksv : Keeps [.esi, .eax] s v := (K.mono (by decide)).trans (Keep.mono (by decide))
  refine WP.mono (digestPadInstall_ok (hs.of_keeps Ksv (by decide)) space) fun t ⟨Ptr, F, KT⟩ => ?_
  refine ⟨?_, ?_, ?_, Ksv.trans (KT.mono (by decide))⟩
  · rw [outside_suffix_bytes F (by decide) (by have := hs.nowrap; omega), Bytes,
      paddedBytes_eq _ _ _ hl, decodeBE_zero_prefix, O]
    rfl
  · rw [Ptr, Ksv.1 _ (by decide)]
  · have F1 : Outs base padRanges u.mem v.mem := Outs.of_outside Frame (by simp [padRanges])
    have F2 : Outs base padRanges v.mem t.mem := Outs.of_outside F (by simp [padRanges])
    rw [O] at F1
    exact F1.trans F2

theorem digestPadPrepare_relCT (len : Nat) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input .digest) = pointerValue base t (.input .digest))
      (.block (DigestPad.prepare len)) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold DigestPad.prepare
  rw [List.append_assoc, List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (pointer_relCT (.input .digest) base size hz) ?_
  apply RelCT.block_append
  refine RelCT.seq (digestPadFill_relCT len) (checkedBlockInvariant
    (τ' := { workspaceTaint true with flags := true }) ?_ rfl)
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .esi (.reg .edi), .alu .add .esi (.imm 0), .store (sc 0) .esi] = _
  rfl

end VG.Proof.Dsa.X86
