import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# ML-KEM on x86-64: `writesOnly`, checked faster

`writesOnly rs c` asks, of every instruction of `c`, whether each of the sixteen
registers is in `rs` or not written: the kernel, evaluating it on the
thousands of instructions of the inlined backends, compares every register.
`writesIn rs i` asks only whether the registers `i` writes are in `rs`
(`writesOnly_of`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- Whether the registers `i` writes (`Taint.clobbers`) are all in `rs`. -/
def writesIn (rs : List Reg) (i : Instr) : Bool :=
  match i with
  | .mul _ => rs.contains .rax && rs.contains .rdx
  | .mulx hi lo _ => rs.contains hi && rs.contains lo
  | .push _ | .alloc _ | .free _ => rs.contains .rsp
  | .pop d _ => rs.contains .rsp && rs.contains d
  | _ => match Taint.dstOf i with
    | some r => rs.contains r
    | none => true

theorem writesIn_sound {rs : List Reg} {i : Instr} (h : writesIn rs i = true) {r : Reg}
    (hr : Taint.clobbers i r = true) : rs.contains r = true := by
  unfold writesIn at h
  unfold Taint.clobbers at hr
  split at hr <;> simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h hr
  · rcases hr with rfl | rfl
    exacts [h.1, h.2]
  · rcases hr with rfl | rfl
    exacts [h.1, h.2]
  · subst hr; exact h
  · subst hr; exact h
  · subst hr; exact h
  · rcases hr with rfl | rfl
    exacts [h.1, h.2]
  · split at h
    · rename_i hd; rw [hr] at hd; cases hd; exact h
    · rename_i hd; rw [hr] at hd; cases hd

theorem writesOnly_of {rs : List Reg} {c : Prog isa} (h : c.allInstrs (writesIn rs) = true) :
    writesOnly rs c = true := by
  unfold writesOnly
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  intro i hi
  rw [List.all_eq_true]
  intro r _
  cases hc : Taint.clobbers i r
  · simp
  · simpa using writesIn_sound (h i hi) hc

end VG.Proof.MlKem.X86_64
