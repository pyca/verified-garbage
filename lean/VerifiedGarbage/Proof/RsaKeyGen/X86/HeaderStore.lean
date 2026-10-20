module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Write a complete 64-bit metadata word using two native stores -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Header

theorem storePair_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (fit : offset + 8 ≤ size) :
    WP isa (.block [.store (sc offset) .eax, .store (sc (offset + 4)) .edx]) s fun t =>
      t.mem = s.mem.writeW (off base offset) (s.gpr .edx ++ s.gpr .eax) ∧
      Outside base offset 8 s.mem t.mem ∧ Keeps [] s t := by
  refine wp_storeS (scratch.ea (by omega)) (scratch.write (by omega)) fun a A => ?_
  have keep := A.keeps []
  have Sa := scratch.of_keeps keep (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun t T => WP.block_nil ?_
  have memory : t.mem = (s.mem.writeW (off base offset) (s.gpr .eax)).writeW
      (off base (offset + 4)) (s.gpr .edx) := by
    rw [T.mem, A.mem, keep.1 .edx (by decide)]
  refine ⟨?_, ?_, keep.trans (T.keeps [])⟩
  · rw [memory, VG.Proof.Rc2.Word32.write64_pair]
    congr 1
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [memory]
    exact ((writeW32_outside _ _ _ (by have := scratch.nowrap; omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by have := scratch.nowrap; omega)).mono (by omega) (by omega))

theorem literal_ok {s : State} {base : Addr} {size offset value : Nat}
    (scratch : Scr s base size) (fit : offset + 8 ≤ size) (zero : s.gpr .edx = 0#32) :
    WP isa (.block (literal offset value)) s fun t =>
      t.mem = s.mem.writeW (off base offset) (0#32 ++ BitVec.ofNat 32 value) ∧
      Outside base offset 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold literal
  refine wp_movS rfl fun a A _ => ?_
  refine WP.mono (storePair_ok (scratch.of_keeps A.keeps (by decide)) fit) fun t ⟨M, O, K⟩ => ?_
  refine ⟨?_, ?_, A.keeps.widen K⟩
  · rw [M, A.mem, A.gpr, A.other .edx (by decide), zero]
  · rw [A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Header
