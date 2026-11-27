module

public import VerifiedGarbage.Impl.AesGcm.X86.Contiguous
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Crypt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Rel2
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.Impl.AesGcm.X86.Contiguous

/-! The same IA-32 entry reads the caller's stack arguments directly for both layouts. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG.Impl.AesGcm.X86.Contiguous (FrameSize privateFrameBytes workBytes scrubBytes)
variable [size : FrameSize]
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Contiguous

theorem workBytes_big : 768 ≤ workBytes := by cases size with | mk b => cases b <;> decide

theorem workBytes_max : workBytes ≤ 2560 := by cases size with | mk b => cases b <;> decide

theorem callerAddress (sp : BitVec 32) (i : Nat) :
    argA (sp - (BitVec.ofNat 32 privateFrameBytes)) (callerSlot i) = argA sp i := by
  have shift : 4 + 4 * callerSlot i = privateFrameBytes + (4 + 4 * i) := by
    cases size with
    | mk b =>
      cases b
      · change 4 + 4 * (643+i) = 2572 + (4 + 4*i); omega
      · change 4 + 4 * (195+i) = 780 + (4 + 4*i); omega
  have add : BitVec.ofNat 32 (privateFrameBytes + (4 + 4*i)) =
      BitVec.ofNat 32 privateFrameBytes + BitVec.ofNat 32 (4 + 4*i) := BitVec.ofNat_add _ _
  rw [argA, shift, add, ←BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The tag pass reads the destination found in the caller's original slot. -/
theorem readCaller {s : State} {sp w : BitVec 32} {i o : Nat}
    (esp : s.gpr .esp = sp - (BitVec.ofNat 32 privateFrameBytes)) (ebp : s.gpr .ebp = w)
    (fw : w.toNat + workBytes ≤ 2^32) (hw : Covers [⟨w64 w,workBytes⟩] s.wr)
    (readable : InRegions (s.rd ++ s.wr) (argA sp i) 4) (fits : o + 4 ≤ 768) :
    ∃ z, runBlock isa (keep (callerSlot i) o) s = some z ∧
      z.mem = s.mem.writeW (w64 w + BitVec.ofNat 64 o) (s.mem.readW (argA sp i) 32) ∧
      (∀ r, r ≠ .eax → z.gpr r = s.gpr r) ∧ z.rd = s.rd ∧ z.wr = s.wr := by
  have read : InRegions (s.rd ++ s.wr) (argA (sp-(BitVec.ofNat 32 privateFrameBytes)) (callerSlot i)) 4 := callerAddress sp i ▸ readable
  simpa only [callerAddress] using keep_readable esp ebp fw hw read (Nat.le_trans fits workBytes_big)

theorem setup_rel {s t : State} (sameStack : s.gpr .esp = t.gpr .esp) :
    RelCT isa (Eq2 s t) (.block setup) TT :=
  rel_taint [.esp] (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact sameStack)
    (by cases size with | mk b => cases b <;> exact ⟨_, by taint_decide⟩)

end VG.Proof.AesGcm.X86.Contiguous
