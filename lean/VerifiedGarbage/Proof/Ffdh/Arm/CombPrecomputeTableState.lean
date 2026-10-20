module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
import VerifiedGarbage.Proof.Framework.Offset

/-! The public table is filled in increasing, densely packed entry order. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def entryOffset (p : Inputs) (digit : Nat) : Nat := 24 + 8*p.w*(digit+2)
def entryValue (p : Inputs) (digit : Nat) : Nat :=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent (bits p) digit) p.P * 2^(64*p.w) % p.P

def TablePrefix (p : Inputs) (count : Nat) (m : Mem) : Prop :=
  ∀ digit < count,
    (m.read (off (State.addr p.output) (entryOffset p digit)) (8*p.w)).toNat = entryValue p digit

theorem bytes_eq (p : Inputs) : bytes p = 24 + 272*p.w := by
  simp only [bytes,Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Inputs.w]
  omega

theorem entry_bound (p : Inputs) {digit : Nat} (hd : digit < 32) :
    entryOffset p digit + 8*p.w ≤ bytes p := by
  have bound := Nat.mul_le_mul_left (8*p.w) (by omega : digit+3 ≤ 34)
  simp only [Nat.mul_add] at bound
  rw [entryOffset,bytes_eq]
  simp only [Nat.mul_add]
  omega

theorem entry_sub (p : Inputs) {digit : Nat} (hd : digit < 32) :
    (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Sub
      ⟨State.addr p.output,bytes p⟩ := Offset.sub_base _ (entry_bound p hd)

theorem TablePrefix.after_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State} {count : Nat}
    (h : Memory p sp s) (table : TablePrefix p count s.mem) (countFit : count ≤ 32)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    TablePrefix p count t.mem := by
  intro digit hd
  have subset := entry_sub p (by omega : digit < 32)
  have separate : ∀ r ∈ [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48],
      (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact h.workspaceSeparate.symm.sub_left subset
    · rw [h.fixed]
      exact h.callSeparate.sub_left subset
  have fit := entry_bound p (by omega : digit < 32)
  have read := frame.read (r := ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩)
    (Region.contains_self _ _) separate (by have := h.output.fits; omega)
  rw [read]
  exact table digit hd

theorem TablePrefix.extend {p : Inputs} {sp : BitVec 32} {s t : State} {count : Nat}
    (h : Memory p sp s) (table : TablePrefix p count s.mem) (countFit : count < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p count),8*p.w⟩] s.mem t.mem)
    (value : (t.mem.read (off (State.addr p.output) (entryOffset p count)) (8*p.w)).toNat =
      entryValue p count) : TablePrefix p (count+1) t.mem := by
  intro digit hd
  by_cases old : digit < count
  · have order := Nat.mul_le_mul_left (8*p.w) (by omega : digit+3 ≤ count+2)
    simp only [Nat.mul_add] at order
    have digitFit := entry_bound p (by omega : digit < 32)
    have countBound := entry_bound p countFit
    have separate : (⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ : Region).Disjoint
        ⟨off (State.addr p.output) (entryOffset p count),8*p.w⟩ := by
      apply Offset.disjoint
      · left
        simp only [entryOffset,Nat.mul_add]
        omega
      · have := h.output.fits
        omega
      · have := h.output.fits
        omega
    have read := frame.read (r := ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩)
      (Region.contains_self _ _) (by intro r hr; have eq := List.mem_singleton.mp hr; subst r; exact separate)
      (by have := h.output.fits; omega)
    rw [read]
    exact table digit old
  · have eq : digit = count := by omega
    subst digit
    exact value

theorem headEq_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
  have sub : (⟨State.addr p.output,24+16*p.w⟩ : Region).Sub ⟨State.addr p.output,bytes p⟩ := by
    apply Region.sub_prefix
    rw [bytes_eq]
    omega
  apply WorkspaceEq.of_frame (by have := h.output.fits; rw [bytes_eq] at this; omega) frame
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact h.workspaceSeparate.symm.sub_left sub
  · rw [h.fixed]
    exact h.callSeparate.sub_left sub

theorem headEq_store {p : Inputs} {sp : BitVec 32} {s t : State} {digit : Nat}
    (h : Memory p sp s) (hd : digit < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (24+16*p.w) s.mem t.mem := by
  have bound := entry_bound p hd
  have order := Nat.mul_le_mul_left (8*p.w) (by omega : 2 ≤ digit+2)
  have sep : (⟨State.addr p.output,24+16*p.w⟩ : Region).Disjoint
      ⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩ := by
    apply Offset.base_disjoint
    · simp only [entryOffset]
      omega
    · have := h.output.fits
      omega
  apply WorkspaceEq.of_frame (by have := h.output.fits; rw [bytes_eq] at this; omega) frame
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact sep

end VG.Proof.Ffdh.Arm.CombBuilder
