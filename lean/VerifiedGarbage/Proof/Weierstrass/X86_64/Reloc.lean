import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Block

/-!
# Code with its operands read through other registers, on x86-64

An instruction whose memory operands are changed (`Instr.mapMem`) runs as
before from a state where each operand addresses the same bytes
(`exec_mapMem`). With the registers of `ps` pointing into the working space
(`PtrsAt`: `r = rdi + c` for each `(r, c)`), an operand through `r` addresses
what one through `rdi` does, `c` bytes further (`unptr`). Code that writes
neither `rdi` nor those registers then runs as its copy with every such
operand through `rdi` (`wp_unptr`): proofs of the inline code, its operands
at constant offsets of `rdi`, carry over to code reading them through
registers.
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64

/-- An operand through a register `r` of `ps` (with `c`) as one through `rdi`,
`c` bytes further. -/
def unptr (ps : List (Reg × Nat)) (m : MemOp) : MemOp :=
  match m.index, ps.lookup m.base with
  | none, some c => { m with base := .rdi, disp := (c : Int) + m.disp }
  | _, _ => m

/-- Each register of `ps` is `rdi` plus its offset. -/
def PtrsAt (ps : List (Reg × Nat)) (s : State) : Prop :=
  ∀ r c, ps.lookup r = some c → s.gpr r = s.gpr .rdi + BitVec.ofNat 64 c

theorem ea_unptr {ps : List (Reg × Nat)} {s : State} (h : PtrsAt ps s) (m : MemOp) :
    s.ea (unptr ps m) = s.ea m := by
  unfold unptr
  split
  · rename_i c hi hc
    simp only [State.ea, hi, h _ _ hc, BitVec.add_assoc]
    congr 1
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  · rfl

theorem PtrsAt.one {s : State} {r : Reg} {c : Nat} (h : s.gpr r = s.gpr .rdi + BitVec.ofNat 64 c) :
    PtrsAt [(r, c)] s := by
  intro q d hq
  simp only [List.lookup] at hq
  split at hq
  · rename_i he; cases hq; exact (beq_iff_eq.mp he) ▸ h
  · cases hq

theorem PtrsAt.two {s : State} {r r' : Reg} {c c' : Nat} (h : s.gpr r = s.gpr .rdi + BitVec.ofNat 64 c)
    (h' : s.gpr r' = s.gpr .rdi + BitVec.ofNat 64 c') : PtrsAt [(r, c), (r', c')] s := by
  intro q d hq
  simp only [List.lookup] at hq
  split at hq
  · rename_i he; cases hq; exact (beq_iff_eq.mp he) ▸ h
  · exact PtrsAt.one h' q d hq

theorem readSrc_mapMem {s : State} {f : MemOp → MemOp} (h : ∀ m, s.ea (f m) = s.ea m) :
    ∀ x : Src, readSrc s (x.mapMem f) = readSrc s x
  | .mem m => by simp only [Src.mapMem, readSrc, h]
  | .reg _ => rfl
  | .imm _ => rfl

theorem readSrc32_mapMem {s : State} {f : MemOp → MemOp} (h : ∀ m, s.ea (f m) = s.ea m) :
    ∀ x : Src, readSrc32 s (x.mapMem f) = readSrc32 s x
  | .mem m => by simp only [Src.mapMem, readSrc32, h]
  | .reg _ => rfl
  | .imm _ => rfl

theorem exec_mapMem {s : State} {f : MemOp → MemOp} (h : ∀ m, s.ea (f m) = s.ea m) (i : Instr) :
    exec (i.mapMem f) s = exec i s := by
  cases i <;> try rfl
  all_goals first
    | (simp only [Instr.mapMem, exec, execAlu, execAlu32, readSrc_mapMem h, readSrc32_mapMem h, h]; done)
    | (rename_i x; cases x <;> simp only [Instr.mapMem, Src.mapMem, exec, execMulx, execAdcx, execAdox,
        execCmov, readSrc, h])

/-- Whether `i` writes neither `rdi` nor a register of `rs`. -/
def keepsPtrs (rs : List Reg) (i : Instr) : Bool :=
  !Taint.clobbers i .rdi && rs.all fun r => !Taint.clobbers i r

theorem mem_of_lookup : ∀ {ps : List (Reg × Nat)} {r : Reg} {c : Nat}, ps.lookup r = some c → (r, c) ∈ ps
  | [], _, _, h => by simp at h
  | (r', c') :: ps, r, c, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      exact (beq_iff_eq.mp he) ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem PtrsAt.exec {ps : List (Reg × Nat)} {rs : List Reg} (hrs : ∀ p ∈ ps, p.1 ∈ rs) {i : Instr}
    (hk : keepsPtrs rs i = true) {s s' : State}
    (h : X86_64.exec i s = some s') (hp : PtrsAt ps s) : PtrsAt ps s' := by
  simp only [keepsPtrs, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
  intro r c hc
  have hr := hk.2 _ (hrs _ (mem_of_lookup hc))
  rw [exec_gpr hr h, exec_gpr hk.1 h, hp r c hc]

/-- Code that writes neither `rdi` nor the registers of `ps` runs as its copy
with its operands through them as operands through `rdi` (`unptr`). -/
theorem wp_unptr {ps : List (Reg × Nat)} {rs : List Reg} (hrs : ∀ p ∈ ps, p.1 ∈ rs) {Q : State → Prop} :
    ∀ (l : List Instr) {s : State}, l.all (keepsPtrs rs) = true → PtrsAt ps s →
      WP isa (.block (l.map (Instr.mapMem (unptr ps)))) s Q → WP isa (.block l) s Q
  | [], _, _, _, h => h
  | i :: l, s, hk, hp, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hk
    rw [List.map_cons, WP.block_cons_iff] at h
    obtain ⟨s₁, e₁, h₁⟩ := h
    have e₁' : X86_64.exec i s = some s₁ := (exec_mapMem (ea_unptr hp) i).symm.trans e₁
    exact WP.block_cons_iff.mpr ⟨s₁, e₁', wp_unptr hrs l hk.2 (hp.exec hrs hk.1 e₁') h₁⟩

/-- `reloc` then `unptr`: an operand at a marker of `ps` moved to its
register and back to `rdi`, at the offset of `qs` for that register. -/
theorem reloc_unptr (ps : List (Nat × Reg)) (qs : List (Reg × Nat)) (is : List Instr) :
    (Impl.Weierstrass.X86_64.Mont.reloc ps is).map (Instr.mapMem (unptr qs)) =
      is.map (Instr.mapMem (unptr qs ∘ Impl.Weierstrass.X86_64.Mont.relocTo ps)) := by
  simp only [Impl.Weierstrass.X86_64.Mont.reloc, List.map_map]
  congr 1
  funext i
  cases i <;> try rfl
  all_goals (try rename_i x; try cases x) <;> rfl

end VG.Proof.Weierstrass.X86_64.Mont
