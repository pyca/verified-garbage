import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# RSAES-OAEP on x86-64: the stack its pieces use

Code that never writes `rsp` (`NoSp`) uses 8 bytes below `rsp` for each
level of its calls (`xdepth_le`), and what code that writes `rsp` only in
its frames leaves of memory, added to a weakest precondition (`wp_frame`):
changes only within its writable regions and the stack it uses.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64

theorem xdepth_le : ∀ {c : Prog isa}, NoSp c → c.x86_64Depth ≤ 8 * c.depth
  | .block _, _ => by simp [Code.x86_64Depth]
  | .seq a b, h => by
    have ha := xdepth_le (c := a) (fun i hi => h i (List.mem_append_left _ hi))
    have hb := xdepth_le (c := b) (fun i hi => h i (List.mem_append_right _ hi))
    simp only [Code.x86_64Depth, Code.depth, Nat.max_le]; omega
  | .ite _ a b, h => by
    have ha := xdepth_le (c := a) (fun i hi => h i (List.mem_append_left _ hi))
    have hb := xdepth_le (c := b) (fun i hi => h i (List.mem_append_right _ hi))
    simp only [Code.x86_64Depth, Code.depth, Nat.max_le]; omega
  | .loop b _, h => by
    have := xdepth_le (c := b) h
    simp only [Code.x86_64Depth, Code.depth]; omega
  | .call _ b, h => by
    have := xdepth_le (c := b) h
    simp only [Code.x86_64Depth, Code.depth]; omega
  | .frame i b j, h => by
    have hi := h i (List.mem_cons_self ..)
    have hb := xdepth_le (c := b) (fun x hx => h x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    have h0 : i.frameBytes = 0 := by cases i <;> simp_all [Taint.clobbers, Taint.dstOf, Instr.frameBytes]
    simp only [Code.x86_64Depth, Code.depth, h0]; omega

/-- What code that writes `rsp` only in its frames leaves of memory. -/
theorem wp_frame {c : Prog isa} (hc : SpSafe c) (hd : c.x86_64Depth < 2 ^ 64) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ Frame (s.wr ++ [below (s.gpr .rsp) c.x86_64Depth]) s.mem s'.mem := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.stackFrame hc he hd⟩

/-- Code that never writes `rsp` writes it only in its (no) frames. -/
theorem SpSafe.of_noSp {c : Prog isa} (h : NoSp c) : SpSafe c := fun i hi => by
  have := h i hi
  cases i <;> simp_all [Taint.clobbers, Taint.dstOf, isa, Instr.dst]
  all_goals (constructor <;> intro e <;> subst e <;> simp_all)

/-! ## Pieces that keep `rsp`, MXCSR and the stack shallow -/

/-- The instructions of `c` neither write `rsp` nor load MXCSR. -/
def okI (i : Instr) : Bool := !Taint.clobbers i .rsp && !loadsMxcsr i

/-- Code that never writes `rsp` or loads MXCSR, with calls nested at most
two deep. -/
def Good (c : Prog isa) : Prop := c.allInstrs okI = true ∧ c.depth ≤ 2

theorem Good.noSp {c : Prog isa} (h : Good c) : NoSp c := fun i hi => by
  have := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans h.1) i hi
  simp only [okI, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.1

theorem Good.mx {c : Prog isa} (h : Good c) : ∀ i ∈ instrs c, loadsMxcsr i = false := fun i hi => by
  have := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans h.1) i hi
  simp only [okI, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.2

theorem Good.xdepth {c : Prog isa} (h : Good c) : c.x86_64Depth ≤ 16 := by
  have := xdepth_le h.noSp; have := h.2; omega

/-- A callee whose instructions never write `rsp` or load MXCSR, with calls
nested at most one deep. -/
theorem okI_all_of {c : Prog isa} (hs : NoSp c) (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    c.allInstrs okI = true := by
  rw [Code.allInstrs_eq] at hm ⊢
  refine List.all_eq_true.mpr fun i hi => ?_
  have h1 := hs i hi
  have h2 := List.all_eq_true.mp hm i hi
  simp only [okI, h1, Bool.not_false, Bool.true_and]; exact h2

/-- What a `Good` piece keeps: `rsp`, MXCSR, and memory but within the
writable regions and the 16 bytes below `rsp`. -/
theorem wp_good {c : Prog isa} (hc : Good c) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.mxcsr = s.mxcsr ∧
      Frame (s.wr ++ [below (s.gpr .rsp) 16]) s.mem s'.mem := by
  obtain ⟨t, s', he, hq⟩ := h
  have hsp := SpSafe.of_noSp hc.noSp
  refine ⟨t, s', he, hq, Exec.rsp hsp he, Exec.mxcsr hc.mx he, ?_⟩
  exact Frame.below_mono (Exec.stackFrame hsp he (by have := hc.xdepth; omega)) hc.xdepth (by omega)

end VG.Proof.RsaOaep.X86_64
