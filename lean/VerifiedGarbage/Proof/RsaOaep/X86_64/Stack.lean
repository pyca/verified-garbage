module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Funs
public import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# RSAES-OAEP on x86-64: the stack its pieces use

Code that never writes `rsp` (`NoSp`) uses 8 bytes below `rsp` for each
level of its calls (`xdepth_le`), and what code that writes `rsp` only in
its frames leaves of memory, added to a weakest precondition (`wp_frame`):
changes only within its writable regions and the stack it uses.
-/

@[expose] public section

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
  | .icall _, _ => by simp only [Code.x86_64Depth, Code.depth]; omega
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

/-! ## Pieces that keep `rsp`, MXCSR's control bits and the stack shallow -/

/-- The instructions of `c` do not write `rsp`. -/
def okI (i : Instr) : Bool := !Taint.clobbers i .rsp

/-- Code that never writes `rsp`, keeps MXCSR's control bits (`ctlOk`: it
loads MXCSR nowhere, and the functions it calls indirectly keep them), with
calls nested at most two deep. -/
def Good (c : Prog isa) : Prop := c.allInstrs okI = true ∧ ctlOk c = true ∧ c.depth ≤ 2

theorem Good.noSp {c : Prog isa} (h : Good c) : NoSp c := fun i hi => by
  have := List.all_eq_true.mp ((Code.allInstrs_eq (I := Instr) (C := Cond) _ _).symm.trans h.1) i hi
  simp only [okI, Bool.not_eq_true'] at this
  exact this

theorem Good.xdepth {c : Prog isa} (h : Good c) : c.x86_64Depth ≤ 16 := by
  have := xdepth_le h.noSp; have := h.2.2; omega

/-- What a piece changes of memory, within `ws`, keeping the functions at
every address and the statics. -/
structure StepW (ws : List Region) (s s' : State) : Prop where
  frame : Frame ws s.mem s'.mem
  funs : s'.funs = s.funs
  syms : s'.syms = s.syms

/-- What a `Good` piece keeps: `rsp`, MXCSR's control bits, the functions and
statics, and memory but within the writable regions and the 16 bytes below
`rsp`. -/
theorem wp_good {c : Prog isa} (hc : Good c) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      StepW (s.wr ++ [below (s.gpr .rsp) 16]) s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have hsp := SpSafe.of_noSp hc.noSp
  refine ⟨t, s', he, hq, Exec.rsp hsp he, Exec.ctl hc.2.1 he, ⟨?_, Exec.funs he, Exec.syms he⟩⟩
  exact Frame.below_mono (Exec.stackFrame hsp he (by have := hc.xdepth; omega)) hc.xdepth (by omega)

end VG.Proof.RsaOaep.X86_64
