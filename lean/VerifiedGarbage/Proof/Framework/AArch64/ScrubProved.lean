module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll

/-!
# Scrubbed code registered with its facts proved (AArch64)

`scrubAllOf`: what `ScrubAll.withScrubAll` registers, with nothing left for
the emitter to work out. The registers the tail clears are an argument (a
literal at the call site), and what the scrub needs of the code is one
Boolean (`scrubSide`) whose proof the call site gives, checked by the kernel
when its module is built: the registration is a record whose code is
`scrubAll` of literals and the code, and evaluating it inspects no code.
-/

@[expose] public section

namespace VG.AArch64.ScrubAll

open VG.Impl.Residue.AArch64

/-- `Clear.WF`, as a Boolean. -/
def wfB (cl : Clear) : Bool :=
  cl.gprs.all allGprs.contains && cl.vecs.all allVecs.contains && cl.his.all hiVecs.contains

theorem wf_of_wfB {cl : Clear} (h : wfB cl = true) : cl.WF := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The general-purpose registers the tail leaves as the code left them:
those the calling convention does not preserve that `cl` does not clear. -/
def keptG (cl : Clear) : List Reg := allGprs.filter fun q => !cl.gprs.contains q

/-- The vector registers the tail leaves, wholly or in their high halves, as
the code left them. -/
def keptV (cl : Clear) : List VReg :=
  (allVecs.filter fun w => !cl.vecs.contains w) ++ hiVecs.filter fun w => !cl.his.contains w

/-- Instruction `i` writes none of the vector registers `vs`. -/
def vkeeps (vs : RegSet VReg) (i : Instr) : Bool :=
  match vdstOf i with
  | none => true
  | some w => !vs.mem w

/-- What `scrubAllOf` needs of an instruction: it writes no PSTATE.DIT, and
none of the registers `g` and `v`. -/
def sideI (g : RegSet Reg) (v : RegSet VReg) (i : Instr) : Bool :=
  !i.writesDit && keeps g i && vkeeps v i

/-- What `scrubAllOf` needs of code `c` run by `scrubAll W rb cl`, with the
tables `ts`: `withScrubAll`'s conditions, and that `cl` is a `Clear` that has
every register `c` (callees included) may write, the link registers among
them if `c` calls. One pass over the instructions, with the registers as bit
masks (`RegSet`); only the kernel evaluates it (`Code.allInstrs`). -/
noncomputable def scrubSide (c : Prog isa) (W rb : Nat) (cl : Clear) (ts : List (String × List FnTable)) : Bool :=
  (if W = 0 then c.aarch64Depth == 0
    else decide (W < 4096) && W % 16 == 0 && decide (16 * c.aarch64Depth ≤ W) && tablesCall c ts) &&
  (rb == 0 || rb == 32 || rb == 64) && wfB cl &&
  c.allInstrs (sideI (RegSet.ofList (keptG cl)) (RegSet.ofList (keptV cl))) &&
  (c.noCalls || linkRegs.all fun q => !(keptG cl).contains q)

theorem keeps_of_side {c : Prog isa} {W rb : Nat} {cl : Clear} {ts : List (String × List FnTable)}
    (h : scrubSide c W rb cl ts = true) : cl.WF ∧ cl.Keeps c ∧ c.all (fun i => !i.writesDit) = true ∧
      (rb = 0 ∨ rb = 32 ∨ rb = 64) := by
  simp only [scrubSide, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hrb⟩, hwf⟩, hi⟩, hl⟩ := h
  have hall : ∀ i ∈ instrs c, (!i.writesDit) = true ∧ (∀ q ∈ keptG cl, clobbers i q = false) ∧
      ∀ w ∈ keptV cl, vdstOf i ≠ some w := by
    intro i hi'
    have h1 := List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans hi) i hi'
    simp only [sideI, Bool.and_eq_true] at h1
    refine ⟨h1.1.1, fun q hq => ?_, fun w hw he => ?_⟩
    · have h2 := (keeps_ofList (keptG cl) i).symm.trans h1.1.2
      simpa using List.all_eq_true.mp h2 q hq
    · have h3 := h1.2
      simp only [vkeeps, he, Bool.not_eq_true'] at h3
      have : w ∈ RegSet.ofList (keptV cl) := RegSet.mem_ofList.mpr hw
      exact absurd this (by show ¬((RegSet.ofList (keptV cl)).mem w = true); rw [h3]; exact Bool.false_ne_true)
  have hG : ∀ q ∈ allGprs, q ∉ cl.gprs → q ∈ keptG cl := fun q hq hn =>
    List.mem_filter.mpr ⟨hq, by simpa using hn⟩
  refine ⟨wf_of_wfB hwf, ⟨fun q hq hn s t u e => ?_, fun w hw s t u e => ?_⟩, ?_, or_assoc.mp hrb⟩
  · refine Exec.gpr (fun i hi' => (hall i hi').2.1 q (hG q hq hn)) e ?_
    rcases hl with hc | hl
    · exact .inl hc
    · refine .inr fun hql => ?_
      have := List.all_eq_true.mp hl q hql
      rw [Bool.not_eq_true'] at this
      exact absurd (List.contains_iff_mem.mpr (hG q hq hn)) (by rw [this]; exact Bool.false_ne_true)
  · refine Exec.vec (fun i hi' => (hall i hi').2.2 w ?_) e
    rcases hw with ⟨ha, hn⟩ | ⟨ha, hn⟩
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨ha, by simpa using hn⟩)
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨ha, by simpa using hn⟩)
  · refine Code.all_of_allInstrs ?_
    rw [Code.allInstrs_eq, List.all_eq_true]
    exact fun i hi' => (hall i hi').1

/-- `r`, its code run by `scrubAll` over its whole stack with the registers
`cl` cleared, returning without secret residue: `withScrubAll`, with the
registers the tail clears stated and what it needs of the code proved
(`scrubSide`, which the kernel evaluates where the registration is defined)
rather than found when the registration is evaluated. `W` and `rb` are the
stack and the result's bits as `hok` states them, so that `hs` is stated
with them and not with projections of `r`. -/
def scrubAllOf {api : Api} (r : Registration api target) (cl : Clear) {W rb : Nat}
    (hok : ScrubAllOk r.contract W rb) (hs : scrubSide r.code W rb cl r.tables = true)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have hok : ScrubAllOk r.contract r.stack (retBitsOf r) := by rw [hW, hb]; exact hok
  have h : scrubSide r.code r.stack (retBitsOf r) cl r.tables = true := by rw [hW, hb]; exact hs
  {
  suffix := r.suffix
  tables := r.tables
  code := scrubAll r.stack (retBitsOf r) cl r.code
  contract := r.contract
  verified := by
    obtain ⟨hwf, -, -, hrb⟩ := keeps_of_side h
    rcases Nat.eq_zero_or_pos r.stack with h0 | hpos
    · rw [h0]; exact Verified.scrubAll0 hwf r.verified hrb (h0 ▸ hok)
    · have hs := h
      simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hs
      exact Verified.scrubAll hwf r.verified ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hrb hok
  consts := r.consts
  stack := r.stack
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := all_spSafe _
  written := r.written
  writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := some ⟨by
    obtain ⟨hwf, hkp, hdit, hrb⟩ := keeps_of_side h
    rcases Nat.eq_zero_or_pos r.stack with h0 | hpos
    · have hs := h
      simp only [scrubSide, h0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hs
      rw [h0]; exact noResidue_scrubAll0 hwf hkp r.verified hs.1.1.1.1 hdit hrb
    · have hs := h
      simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hs
      exact noResidue_scrubAll hwf hkp r.verified ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hok.sp
        hs.1.1.1.1.1.2 hdit (tablesCall_syms hs.1.1.1.1.2) hrb⟩ }

end VG.AArch64.ScrubAll
