module

public import VerifiedGarbage.Impl.Scrub.AArch64.Union
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# What a function's cleanup needs of its code, as Booleans (AArch64)

The cleanup of a function (`Impl.Scrub.AArch64.scrubAll`) clears the
registers a `Clear` lists, and the function returns without secret residue if
its code writes no other register the calling convention does not preserve
(`Scrub.scrubSide`, `Proof/Framework/AArch64/ScrubProved.lean`). That is a
test of every instruction (`sideI`), which holds of code and of the code it
calls separately: an implementation that several functions call proves it
once, of its own code and the registers it states it writes (`calleeSide`),
and a function that calls it proves it of its own instructions; the two give
it of the function with the union of the registers (`sideAll_union_left`,
`sideAll_union_right`), whatever the implementation.

These are definitions on code only, for the modules that state an
implementation's facts without the proofs about the cleanup.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.Impl.Scrub.AArch64

/-- `Clear.WF`, as a Boolean. -/
def wfB (cl : Clear) : Bool :=
  cl.gprs.all allGprs.contains && cl.vecs.all allVecs.contains && cl.his.all hiVecs.contains

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

/-- What a function's cleanup needs of an instruction: it writes no
PSTATE.DIT, and none of the registers `g` and `v`. -/
def sideI (g : RegSet Reg) (v : RegSet VReg) (i : Instr) : Bool :=
  !i.writesDit && keeps g i && vkeeps v i

/-- `c.allInstrs p`, of code that calls nothing indirectly. Only the kernel
evaluates it (`Code.allInstrs`). -/
noncomputable def sideAll (p : Instr → Bool) : Prog isa → Bool
  | .block is => Code.allInstrs p (.block is : Prog isa)
  | .seq a b => sideAll p a && sideAll p b
  | .ite _ t e => sideAll p t && sideAll p e
  | .loop b _ => sideAll p b
  | .call _ b => sideAll p b
  | .frame i b j => p i && sideAll p b && p j
  | .icall .. => false

theorem allInstrs_of_sideAll {p : Instr → Bool} {c : Prog isa} (hc : sideAll p c = true) :
    c.allInstrs p = true := by
  induction c with
  | block is => exact hc
  | seq a b iha ihb =>
    simp only [sideAll, Code.allInstrs, Bool.and_eq_true] at hc ⊢; exact ⟨iha hc.1, ihb hc.2⟩
  | ite _ t e iht ihe =>
    simp only [sideAll, Code.allInstrs, Bool.and_eq_true] at hc ⊢; exact ⟨iht hc.1, ihe hc.2⟩
  | loop b _ ih => simp only [sideAll, Code.allInstrs] at hc ⊢; exact ih hc
  | call _ b ih => simp only [sideAll, Code.allInstrs] at hc ⊢; exact ih hc
  | frame i b j ih =>
    simp only [sideAll, Code.allInstrs, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨hc.1.1, ih hc.1.2⟩, hc.2⟩
  | icall => simp only [sideAll, Bool.false_eq_true] at hc

theorem sideAll_mono {p q : Instr → Bool} (h : ∀ i, p i = true → q i = true) {c : Prog isa}
    (hc : sideAll p c = true) : sideAll q c = true := by
  induction c with
  | block is =>
    simp only [sideAll, Code.allInstrs_eq, List.all_eq_true] at hc ⊢
    exact fun i hi => h i (hc i hi)
  | seq a b iha ihb => simp only [sideAll, Bool.and_eq_true] at hc ⊢; exact ⟨iha hc.1, ihb hc.2⟩
  | ite _ t e iht ihe => simp only [sideAll, Bool.and_eq_true] at hc ⊢; exact ⟨iht hc.1, ihe hc.2⟩
  | loop b _ ih => simp only [sideAll] at hc ⊢; exact ih hc
  | call _ b ih => simp only [sideAll] at hc ⊢; exact ih hc
  | frame i b j ih =>
    simp only [sideAll, Bool.and_eq_true] at hc ⊢
    exact ⟨⟨h i hc.1.1, ih hc.1.2⟩, h j hc.2⟩
  | icall => simp only [sideAll, Bool.false_eq_true] at hc

/-- `sideI` of fewer registers. -/
theorem sideI_mono {g g' : List Reg} {v v' : List VReg} (hg : ∀ q, q ∈ g' → q ∈ g)
    (hv : ∀ w, w ∈ v' → w ∈ v) {i : Instr}
    (h : sideI (RegSet.ofList g) (RegSet.ofList v) i = true) :
    sideI (RegSet.ofList g') (RegSet.ofList v') i = true := by
  simp only [sideI, Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · have h2 := h.1.2
    rw [keeps_ofList, List.all_eq_true] at h2 ⊢
    exact fun q hq => h2 q (hg q hq)
  · have h3 := h.2
    unfold vkeeps at h3 ⊢
    cases hd : vdstOf i with
    | none => rfl
    | some w =>
      simp only [hd, Bool.not_eq_true'] at h3 ⊢
      cases hm : (RegSet.ofList v').mem w with
      | false => rfl
      | true =>
        have hw : w ∈ v := hv w (RegSet.mem_ofList.mp hm)
        have : (RegSet.ofList v).mem w = true := RegSet.mem_ofList.mpr hw
        rw [h3] at this
        exact absurd this Bool.false_ne_true

/-- What neither of two lists has, of a list: it is not in the part of the
list that either has. -/
private theorem kept_union {α : Type} [BEq α] [LawfulBEq α] {l a b : List α} {q : α}
    (h : q ∈ l.filter fun q => !(l.filter fun q => a.contains q || b.contains q).contains q) :
    (q ∈ l.filter fun q => !a.contains q) ∧ (q ∈ l.filter fun q => !b.contains q) := by
  obtain ⟨hq, hn⟩ := List.mem_filter.mp h
  have hab : (a.contains q || b.contains q) = false := by
    cases hab : (a.contains q || b.contains q) with
    | false => rfl
    | true =>
      rw [List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨hq, hab⟩)] at hn
      exact absurd hn (by decide)
  rw [Bool.or_eq_false_iff] at hab
  exact ⟨List.mem_filter.mpr ⟨hq, by rw [hab.1]; rfl⟩, List.mem_filter.mpr ⟨hq, by rw [hab.2]; rfl⟩⟩

theorem keptG_union_left {a b : Clear} {q : Reg} (h : q ∈ keptG (a.union b)) : q ∈ keptG a :=
  (kept_union h).1

theorem keptG_union_right {a b : Clear} {q : Reg} (h : q ∈ keptG (a.union b)) : q ∈ keptG b :=
  (kept_union h).2

theorem keptV_union_left {a b : Clear} {w : VReg} (h : w ∈ keptV (a.union b)) : w ∈ keptV a := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (kept_union h).1
  · exact List.mem_append_right _ (kept_union h).1

theorem keptV_union_right {a b : Clear} {w : VReg} (h : w ∈ keptV (a.union b)) : w ∈ keptV b := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (kept_union h).2
  · exact List.mem_append_right _ (kept_union h).2

/-- What the cleanup of a function that calls `c` needs of `c`, for the
registers `cl` it states it writes: every instruction of `c` writes, of the
registers the calling convention does not preserve, only those of `cl`, and
no PSTATE.DIT, and `c` calls nothing indirectly. An implementation proves it
once, where it is defined; the kernel evaluates it there. -/
noncomputable def calleeSide (c : Prog isa) (cl : Clear) : Bool :=
  sideAll (sideI (RegSet.ofList (keptG cl)) (RegSet.ofList (keptV cl))) c

/-- A function's own instructions, with the union of its registers and
those of what it calls. -/
theorem sideAll_union_left {a b : Clear} {c : Prog isa} (h : calleeSide c a = true) :
    calleeSide c (a.union b) = true :=
  sideAll_mono (fun _ => sideI_mono (fun _ => keptG_union_left) (fun _ => keptV_union_left)) h

/-- The instructions of what a function calls, with the union. -/
theorem sideAll_union_right {a b : Clear} {c : Prog isa} (h : calleeSide c b = true) :
    calleeSide c (a.union b) = true :=
  sideAll_mono (fun _ => sideI_mono (fun _ => keptG_union_right) (fun _ => keptV_union_right)) h

end VG.AArch64.Scrub
