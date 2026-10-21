module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.CombSelectMath

/-! One fixed-address masked table load, shared across table widths. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem maskedWord_ok {s : State} {table mask : MemOp} {value maskValue : BitVec 32}
    (ht : readSrc s (.mem table) = some value) (hm : readSrc s (.mem mask) = some maskValue)
    (base : mask.base ≠ .eax) :
    WP isa (.block (VG.Impl.Mont.X86.Comb.maskedWord table mask)) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = s.gpr .ebx ||| (value &&& maskValue) ∧
      Keeps [.eax, .ebx] s t := by
  unfold VG.Impl.Mont.X86.Comb.maskedWord
  refine wp_movS ht fun u₁ U₁ _ => ?_
  refine wp_logicS (.inl rfl) (by rw [readSrc_upd U₁ base]; exact hm) fun u₂ U₂ => ?_
  refine wp_orS rfl fun t U₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact U₃.mem.trans (U₂.mem.trans U₁.mem)
  · rw [U₃.gpr, U₂.gpr, U₁.gpr, U₂.other .ebx (by decide), U₁.other .ebx (by decide)]
    rfl
  · exact ((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps

/-- Read-only instructions preserve fixed memory operands whose base registers
are outside the accumulator pair. -/
theorem readSrc_mask_keeps {s t : State} {m : MemOp}
    (M : t.mem = s.mem) (K : Keeps [.eax, .ebx] s t)
    (h : m.base ∉ [.eax, .ebx]) : readSrc t (.mem m) = readSrc s (.mem m) := by
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  have addr : t.ea m = s.ea m := by simp only [State.ea, K.1 _ h]
  simp only [State.load32, addr, M, K.2.1, K.2.2]

/-- The emitted full scan accumulates the same fold as the masked lookup
algebra. No memory is written and no table-dependent address is formed. -/
theorem maskedWords_ok (js : List Nat) {s : State}
    (table mask : Nat → MemOp) (value masks : Nat → BitVec 32)
    (ht : ∀ j ∈ js, readSrc s (.mem (table j)) = some (value j))
    (hm : ∀ j ∈ js, readSrc s (.mem (mask j)) = some (masks j))
    (tb : ∀ j ∈ js, (table j).base ∉ [.eax, .ebx])
    (mb : ∀ j ∈ js, (mask j).base ∉ [.eax, .ebx]) :
    WP isa (.block (js.flatMap fun j => VG.Impl.Mont.X86.Comb.maskedWord (table j) (mask j))) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ebx = js.foldl (fun acc j => acc ||| (value j &&& masks j)) (s.gpr .ebx) ∧
      Keeps [.eax, .ebx] s t := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | cons j js ih =>
    simp only [List.flatMap_cons]
    refine WP.block_append (WP.mono (maskedWord_ok (ht j (by simp)) (hm j (by simp))
      (by have := mb j (by simp); simp only [List.mem_cons, List.not_mem_nil, or_false,
        not_or] at this; exact this.1)) fun u ⟨M, V, K⟩ => ?_)
    refine WP.mono (ih (s := u)
      (fun k hk => (readSrc_mask_keeps M K (tb k (by simp [hk]))).trans (ht k (by simp [hk])))
      (fun k hk => (readSrc_mask_keeps M K (mb k (by simp [hk]))).trans (hm k (by simp [hk])))
      (fun k hk => tb k (by simp [hk])) (fun k hk => mb k (by simp [hk]))) fun t ⟨M', V', K'⟩ => ?_
    exact ⟨M'.trans M, by simpa only [List.foldl_cons, V] using V', K.trans K'⟩

/-- A complete 32-entry instruction scan returns the indexed word. The index
is used only in the mask values, never in an address operand. -/
theorem maskedLookup_ok {s : State} (table mask : Nat → MemOp)
    (value : Nat → BitVec 32) {index : Nat} (hi : index < 32)
    (ht : ∀ j < 32, readSrc s (.mem (table j)) = some (value j))
    (hm : ∀ j < 32, readSrc s (.mem (mask j)) =
      some (if index = j then BitVec.allOnes 32 else 0#32))
    (tb : ∀ j < 32, (table j).base ∉ [.eax, .ebx])
    (mb : ∀ j < 32, (mask j).base ∉ [.eax, .ebx]) :
    WP isa (.block (.mov .ebx (.imm 0) :: (List.range 32).flatMap fun j =>
      VG.Impl.Mont.X86.Comb.maskedWord (table j) (mask j))) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = value index ∧ Keeps [.eax, .ebx] s t := by
  refine wp_movS rfl fun u U _ => ?_
  have K : Keeps [.eax, .ebx] s u := U.keeps.mono (by decide)
  refine WP.mono (maskedWords_ok (List.range 32) table mask value
    (fun j => if index = j then BitVec.allOnes 32 else 0#32)
    (fun j hj => (readSrc_mask_keeps U.mem K (tb j (List.mem_range.mp hj))).trans
      (ht j (List.mem_range.mp hj)))
    (fun j hj => (readSrc_mask_keeps U.mem K (mb j (List.mem_range.mp hj))).trans
      (hm j (List.mem_range.mp hj)))
    (fun j hj => tb j (List.mem_range.mp hj)) (fun j hj => mb j (List.mem_range.mp hj)))
    fun t ⟨M, V, K'⟩ => ?_
  refine ⟨M.trans U.mem, ?_, K.trans K'⟩
  rw [U.gpr] at V
  change t.gpr .ebx = (List.range 32).foldl _ 0#32 at V
  simpa only [masked_words_prefix, hi, ↓reduceIte] using V

end VG.Proof.Mont.X86.Dynamic
