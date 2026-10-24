module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift
import VerifiedGarbage.Proof.Mont.X86.Compact.Length

/-! # Republish pointer and width values fixed by the prepared metadata -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem lift_value {g : Geometry} (v : g.Valid) {code : Prog isa} {rs clob : List Reg} {r : Reg} {value : Nat}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint [])) code
      (VG.X86.Taint.Agree (timingTaint [])))
    (correct : ∀ s, Context g s → WP isa code s fun t =>
      (t.gpr r).toNat = value ∧ t.mem = s.mem ∧ Keeps clob s t)
    (clobbers : ∀ q ∈ clob, q ∈ clob7) (keepRegs : ∀ q ∈ rs, q ∉ clob) :
    RelCT isa (Pair g rs) code (Pair g (r :: rs)) := by
  refine lift v (raw.mono (fun _ _ h => timing_forget h) (fun _ _ h => h))
    (fun s t => (t.gpr r).toNat = value ∧ t.mem = s.mem ∧ Keeps clob s t) correct
    (fun _ _ H => H.2.2.mono clobbers) (fun _ _ H => ?_) ?_
  · rw [H.2.1]; exact Outs.refl _ _ _
  · intro s t u z H U Z q member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact BitVec.eq_of_toNat_eq (U.1.trans Z.1.symm)
    · rw [U.2.2.1 q (keepRegs q member), Z.2.2.1 q (keepRegs q member)]
      exact timing_regs H.2.2 member

theorem length_relCT {g : Geometry} (v : g.Valid) (r tmp : Reg) (k : Nat) {rs : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
      (.block (VG.Impl.Mont.X86.Compact.lenTimes r tmp k)) (VG.X86.Taint.Agree (timingTaint [])))
    (clobbers : ∀ q ∈ [r, tmp], q ∈ clob7) (keepRegs : ∀ q ∈ rs, q ∉ [r, tmp]) :
    RelCT isa (Pair g rs) (.block (VG.Impl.Mont.X86.Compact.lenTimes r tmp k)) (Pair g (r :: rs)) := by
  refine lift_value v raw (value := 4 * g.N * 2 ^ k % 2 ^ 32) ?_ clobbers keepRegs
  intro s C
  refine WP.mono (lenTimes_ok C.ws C.args v.base (by have := v.lay.header; have := v.lay.scr; omega) k) ?_
  rintro t ⟨R, M, K⟩
  refine ⟨?_, M, K⟩
  rw [R, Nat.pow_add, show 2 ^ 3 = 8 from rfl, ← Nat.mul_assoc, C.metadata.width]

theorem scratchPointer_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g []) (.block VG.Impl.Mont.X86.Compact.scratchPtr) (Pair g [.edi]) := by
  refine lift_value v scratchPtr_relCT (clob := [.edi]) (value := (g.W.toNat + g.S) % 2 ^ 32)
    ?_ (by decide) (by simp)
  intro s C
  refine WP.mono (arrayPtr_ok C.ws C.args v.base (r := .edi) (j := 2)
    (by have := v.lay.header; have := v.lay.scr; omega)) ?_
  rintro t ⟨R, M, K⟩
  refine ⟨?_, M, K⟩
  rw [R]; exact C.metadata.scratch

theorem operandPointer_relCT {g : Geometry} (v : g.Valid) (r tmp : Reg) (i value : Nat) {rs : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
      (.block (VG.Impl.Mont.X86.Compact.operandPtr r i tmp)) (VG.X86.Taint.Agree (timingTaint [])))
    (reg : r ≠ .esp) (distinct : r ≠ tmp) (index : i < 5)
    (headerFit : ∀ s, Context g s → 64 + 8 * (g.A i).toNat + 4 ≤ g.L)
    (pointer : ∀ s, Context g s → w32 s.mem g.W (64 + 8 * (g.A i).toNat) = value)
    (clobbers : ∀ q ∈ [r, tmp], q ∈ clob7) (keepRegs : ∀ q ∈ rs, q ∉ [r, tmp]) :
    RelCT isa (Pair g rs) (.block (VG.Impl.Mont.X86.Compact.operandPtr r i tmp)) (Pair g (r :: rs)) := by
  refine lift_value v raw (value := value) ?_ clobbers keepRegs
  intro s C
  refine WP.mono (operandPtr_ok C.ws C.args v.base reg distinct index (headerFit s C)) ?_
  rintro t ⟨R, M, K⟩
  refine ⟨?_, M, K⟩
  rw [R]; exact pointer s C

theorem arrayPointer_relCT {g : Geometry} (v : g.Valid) (r : Reg) (j value : Nat) {rs : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (timingTaint []))
      (.block (VG.Impl.Mont.X86.Compact.arrayPtr r j)) (VG.X86.Taint.Agree (timingTaint [])))
    (headerFit : 64 + 8 * j + 4 ≤ g.L)
    (pointer : ∀ s, Context g s → w32 s.mem g.W (64 + 8 * j) = value)
    (clobbers : ∀ q ∈ [r], q ∈ clob7) (keepRegs : ∀ q ∈ rs, q ∉ [r]) :
    RelCT isa (Pair g rs) (.block (VG.Impl.Mont.X86.Compact.arrayPtr r j)) (Pair g (r :: rs)) := by
  refine lift_value v raw (value := value) ?_ clobbers keepRegs
  intro s C
  refine WP.mono (arrayPtr_ok C.ws C.args v.base headerFit) ?_
  rintro t ⟨R, M, K⟩
  refine ⟨?_, M, K⟩
  rw [R]; exact pointer s C

end VG.Proof.Mont.X86.Compact
