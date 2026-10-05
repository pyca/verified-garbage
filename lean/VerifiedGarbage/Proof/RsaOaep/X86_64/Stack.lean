import VerifiedGarbage.Proof.Framework.X86_64.Depth

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
    simp only [Code.x86_64Depth, Code.depth]; omega
  | .ite _ a b, h => by
    have ha := xdepth_le (c := a) (fun i hi => h i (List.mem_append_left _ hi))
    have hb := xdepth_le (c := b) (fun i hi => h i (List.mem_append_right _ hi))
    simp only [Code.x86_64Depth, Code.depth]; omega
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

end VG.Proof.RsaOaep.X86_64
