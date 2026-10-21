module

public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.FixedBaseCombSubset
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Public low-tooth and remaining-subset indices for the table builder. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.FixedBaseComb (lowTooth)

private theorem indices : ∀ a < 32,
    ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a).toNat = lowTooth a ∧
    (BitVec.ofNat 32 a - ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a)).toNat = a-lowTooth a := by decide

theorem subsetIndices_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) (ha : a < 32) (count : s.gpr .esi = BitVec.ofNat 32 a) :
    WP isa VG.Impl.Mont.X86.Comb.subsetIndices s fun t =>
      Outs base [(28,4),(4,4)] s.mem t.mem ∧ w32 t.mem base 28 = lowTooth a ∧
      w32 t.mem base 4 = a-lowTooth a ∧ Keeps [.eax,.edx] s t := by
  unfold VG.Impl.Mont.X86.Comb.subsetIndices
  refine wp_movS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_logicS (.inl rfl) rfl fun u₃ U₃ => ?_
  have K3 : Keeps [.eax,.edx] s u₃ := ((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps
  have H3 := hs.of_keeps K3 (by decide)
  have low : u₃.gpr .eax = ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a) := by
    rw [U₃.gpr, U₂.gpr, U₁.gpr, U₂.other _ (by decide), U₁.other _ (by decide), count]
    rfl
  refine wp_storeS (H3.ea (d := 28) (by omega)) (H3.write (d := 28) (n := 4) hz) fun u₄ M₄ => ?_
  refine wp_movS rfl fun u₅ U₅ _ => wp_subS rfl fun u₆ U₆ _ => ?_
  have K6 : Keeps [.eax,.edx] s u₆ := ((K3.trans (M₄.keeps _)).widen U₅.keeps).widen U₆.keeps
  have H6 := hs.of_keeps K6 (by decide)
  refine wp_storeS (H6.ea (d := 4) (by omega)) (H6.write (d := 4) (n := 4) (by omega)) fun t M₇ => WP.block_nil ?_
  have mem : u₆.mem = u₃.mem.writeW (off base 28) (u₃.gpr .eax) := by rw [U₆.mem,U₅.mem,M₄.mem]
  have initial : u₃.mem = s.mem := U₃.mem.trans (U₂.mem.trans U₁.mem)
  have O28 : Outside base 28 4 s.mem u₆.mem := by rw [mem,initial]; exact writeW32_outside _ _ _ (by decide)
  have O4 : Outside base 4 4 u₆.mem t.mem := by rw [M₇.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨(Outs.of_outside O28 (by simp)).trans (Outs.of_outside O4 (by simp)), ?_, ?_, K6.trans (M₇.keeps _)⟩
  · rw [O4.w32 (by decide) (by decide), mem, w32_write_self, low]
    exact (indices a ha).1
  · rw [M₇.mem, w32_write_self, U₆.gpr, U₅.gpr, M₄.gpr, K3.1 .esi (by decide),
      U₅.other _ (by decide), M₄.gpr, low, count]
    exact (indices a ha).2

theorem subsetLow_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) :
    WP isa VG.Impl.Mont.X86.Comb.subsetLow s fun t =>
      Outside base 4 4 s.mem t.mem ∧ w32 t.mem base 4 = w32 s.mem base 28 ∧ Keeps [.eax] s t := by
  unfold VG.Impl.Mont.X86.Comb.subsetLow VG.Impl.Mont.X86.Dynamic.windowOffset
  refine wp_movS (readSrc_sc hs hz) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (d := 4) (by omega)) (hu.write (d := 4) (n := 4) (by omega)) fun t M => WP.block_nil ?_
  refine ⟨?_, ?_, U.keeps.trans (M.keeps _)⟩
  · rw [M.mem,U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [M.mem,w32_write_self,U.gpr]

end VG.Proof.Mont.X86.Comb
