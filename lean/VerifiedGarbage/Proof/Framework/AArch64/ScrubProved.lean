module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAllW
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# The cleanup's theorems (AArch64)

The theorems a registration binds (`verified := …`), about a
function's code as emitted, its body and then its cleanup
(`Impl.Scrub.AArch64.scrubAll W rb cl`): `verifiedScrubbedAll`, with the
registers it clears stated, and `verifiedScrubbedOf`, with them read off the
code. What the cleanup needs of the code is one Boolean (`scrubSide`), which
the proof module gives by `lit_decide`, so the kernel checks it when that
module is built.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.Impl.Scrub.AArch64

theorem wf_of_wfB {cl : Clear} (h : wfB cl = true) : cl.WF := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- What `verifiedScrubbedAll` needs of code `c` run by `scrubAll W rb cl`,
with the tables `ts`: conditions on its stack, its instructions and its
calls, and that `cl` is a `Clear` that has
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

/-- What `verifiedScrubbedAll` proves of the code, for code verified against any
contract `k`: a caller that calls the scrubbed code by name (as
`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`) proves its call against
it. -/
theorem Verified.scrubAllOfV {c : Prog isa} {k : Contract isa} {cl : Clear} {W rb : Nat}
    {ts : List (String × List FnTable)} (hv : Verified target c k) (hok : ScrubAllOk k W rb)
    (h : scrubSide c W rb cl ts = true) : Verified target (VG.Impl.Scrub.AArch64.scrubAll W rb cl c) k := by
  obtain ⟨hwf, -, -, hrb⟩ := keeps_of_side h
  rcases Nat.eq_zero_or_pos W with h0 | hpos
  · subst h0; exact Verified.scrubAll0 hwf hv hrb hok
  · have hs := h
    simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hs
    exact Verified.scrubAll hwf hv ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hrb hok

/-- `Clear.union`: the registers of `a` and of `b`, in `Clear.all`'s order
(which is `Clear.of`'s). -/
abbrev clearUnion (a b : Clear) : Clear := a.union b

/-! ## The cleanup as part of the code

`verifiedScrubbedAll` is the theorem about the code with its cleanup (`scrubAll W rb cl c`, which `Impl/` defines as the
function): the proof a registration binds (`verified := …`).
`scrubSide_union` gives its side condition for a function that calls an
implementation chosen among several, from what the function proves of its
own instructions and the implementation of its own (`calleeSide`). -/

theorem wfB_union (a b : Clear) : wfB (a.union b) = true := by
  simp only [wfB, Clear.union, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨⟨fun q hq => (List.mem_filter.mp hq).1, fun w hw => (List.mem_filter.mp hw).1⟩,
    fun w hw => (List.mem_filter.mp hw).1⟩

theorem noIcall_of_sideAll {p : Instr → Bool} {c : Prog isa} (hc : sideAll p c = true) :
    noIcall c = true := by
  induction c with
  | block is => rfl
  | seq a b iha ihb => simp only [sideAll, noIcall, Bool.and_eq_true] at hc ⊢; exact ⟨iha hc.1, ihb hc.2⟩
  | ite _ t e iht ihe => simp only [sideAll, noIcall, Bool.and_eq_true] at hc ⊢; exact ⟨iht hc.1, ihe hc.2⟩
  | loop b _ ih => simp only [sideAll, noIcall] at hc ⊢; exact ih hc
  | call _ b ih => simp only [sideAll, noIcall] at hc ⊢; exact ih hc
  | frame i b j ih => simp only [sideAll, noIcall, Bool.and_eq_true] at hc ⊢; exact ih hc.1.2
  | icall => simp only [sideAll, Bool.false_eq_true] at hc

/-- What `l` has of neither `a'` nor `b`, it has of neither `a` nor `b`, for
`a` within `a'`. -/
private theorem kept_mono {α : Type} [BEq α] [LawfulBEq α] {l a a' b : List α} {q : α}
    (ha : ∀ q, q ∈ a → q ∈ a')
    (h : q ∈ l.filter fun q => !(l.filter fun q => a'.contains q || b.contains q).contains q) :
    q ∈ l.filter fun q => !(l.filter fun q => a.contains q || b.contains q).contains q := by
  obtain ⟨hq, hn⟩ := List.mem_filter.mp h
  refine List.mem_filter.mpr ⟨hq, ?_⟩
  rw [Bool.not_eq_true'] at hn ⊢
  cases hm : (l.filter fun q => a.contains q || b.contains q).contains q with
  | false => rfl
  | true =>
    obtain ⟨_, hab⟩ := List.mem_filter.mp (List.contains_iff_mem.mp hm)
    have hab' : (a'.contains q || b.contains q) = true := by
      rw [Bool.or_eq_true] at hab ⊢
      exact hab.imp (fun h => List.contains_iff_mem.mpr (ha q (List.contains_iff_mem.mp h))) id
    rw [List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨hq, hab'⟩)] at hn
    exact absurd hn (by decide)

/-- `calleeSide` of code a function calls, which holds with the registers `a`
of another function that calls it, holds with the function's own `a'`, which
has them all. -/
theorem calleeSide_union_mono {a a' b : Clear} {c : Prog isa}
    (hs : (a.gprs.all a'.gprs.contains && a.vecs.all a'.vecs.contains &&
      a.his.all a'.his.contains) = true)
    (h : calleeSide c (a.union b) = true) : calleeSide c (a'.union b) = true := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hs
  refine sideAll_mono (fun _ => sideI_mono (fun q hq => kept_mono hs.1.1 hq) fun w hw => ?_) h
  rcases List.mem_append.mp hw with h | h
  · exact List.mem_append_left _ (kept_mono hs.1.2 h)
  · exact List.mem_append_right _ (kept_mono hs.2 h)

/-- `scrubSide` of code with frames that takes no table, for the registers
`own` and `cl` together: from `calleeSide` of all of it with them (which
`sideAll_union_left` and `sideAll_union_right` give of its parts), and `own`
having the link registers. -/
theorem scrubSide_union {c : Prog isa} {W rb : Nat} {own cl : Clear}
    (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hc : calleeSide c (own.union cl) = true)
    (hl : (linkRegs.all fun q => !(keptG own).contains q) = true) :
    scrubSide c W rb (own.union cl) [] = true := by
  have hi := inames_of_noIcall (noIcall_of_sideAll hc)
  simp only [scrubSide, Nat.pos_iff_ne_zero.mp hW.1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨hW.2.1, hW.2.2⟩, hd⟩, ?_⟩, or_assoc.mpr hrb⟩, wfB_union _ _⟩, allInstrs_of_sideAll hc⟩,
    .inr ?_⟩
  · rw [tablesCall, hi]; rfl
  · rw [List.all_eq_true] at hl ⊢
    intro q hq
    have h1 := hl q hq
    rw [Bool.not_eq_true'] at h1 ⊢
    cases hm : (keptG (own.union cl)).contains q with
    | false => rfl
    | true =>
      rw [List.contains_iff_mem.mpr (keptG_union_left (List.contains_iff_mem.mp hm))] at h1
      exact absurd h1 (by decide)

/-- `scrubSide_union` for code that uses no stack (so calls nothing through
a table): from `calleeSide` of all of it with `own` and `cl` together, and
`own` having the link registers. -/
theorem scrubSide_union0 {c : Prog isa} {rb : Nat} {own cl : Clear}
    (hd : c.aarch64Depth = 0) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64)
    (hc : calleeSide c (own.union cl) = true)
    (hl : (linkRegs.all fun q => !(keptG own).contains q) = true) :
    scrubSide c 0 rb (own.union cl) [] = true := by
  simp only [scrubSide, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨hd, or_assoc.mpr hrb⟩, wfB_union _ _⟩, allInstrs_of_sideAll hc⟩, .inr ?_⟩
  rw [List.all_eq_true] at hl ⊢
  intro q hq
  have h1 := hl q hq
  rw [Bool.not_eq_true'] at h1 ⊢
  cases hm : (keptG (own.union cl)).contains q with
  | false => rfl
  | true =>
    rw [List.contains_iff_mem.mpr (keptG_union_left (List.contains_iff_mem.mp hm))] at h1
    exact absurd h1 (by decide)

/-- The link registers that `a` has, `a` with more has: the last premise of
`scrubSide_union` and `scrubSide_union0` for a function whose own registers
are themselves a union (it calls two implementations). -/
theorem linkRegs_union {a b : Clear} (h : (linkRegs.all fun q => !(keptG a).contains q) = true) :
    (linkRegs.all fun q => !(keptG (a.union b)).contains q) = true := by
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 := h q hq
  rw [Bool.not_eq_true'] at h1 ⊢
  cases hm : (keptG (a.union b)).contains q with
  | false => rfl
  | true =>
    rw [List.contains_iff_mem.mpr (keptG_union_left (List.contains_iff_mem.mp hm))] at h1
    exact absurd h1 (by decide)

/-- `r`'s code with its cleanup (`scrubAll`, over its whole stack, the
registers `cl` cleared) meets `r`'s contract in constant time and returns
without secret residue: the theorem about the code that a registration binds
(`verified := …`). -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) (cl : Clear) {W rb : Nat}
    (hok : ScrubAllOk r.contract W rb) (hs : scrubSide r.code W rb cl r.tables = true)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll W rb cl r.code) r.contract rb := by
  subst hW hb
  have hv := Verified.scrubAllOfV (ts := r.tables) r.verified hok hs
  refine ⟨hv, ?_⟩
  obtain ⟨hwf, hkp, hdit, hrb⟩ := keeps_of_side hs
  rcases Nat.eq_zero_or_pos r.stack with h0 | hpos
  · have hs' := hs
    simp only [scrubSide, h0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hs'
    rw [h0]; exact noResidue_scrubAll0 hwf hkp r.verified hs'.1.1.1.1 hdit hrb
  · have hs' := hs
    simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hs'
    exact noResidue_scrubAll hwf hkp r.verified ⟨hpos, hs'.1.1.1.1.1.1.1, hs'.1.1.1.1.1.1.2⟩ hok.sp
      hs'.1.1.1.1.1.2 hdit (tablesCall_syms hs'.1.1.1.1.2) hrb

/-- `c` with its cleanup over `W` bytes of stack, the registers it may write
cleared (`Clear.of`, read off the code), meets `c`'s contract in constant
time and returns without secret residue, if no instruction of it, or of what
it calls, writes PSTATE.DIT and it calls nothing indirectly (`sideAll`): of a
function generic over the implementations of the functions it calls, which
states no registers. -/
theorem verifiedScrubbedOf {c : Prog isa} {k : Contract isa} {W rb : Nat} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hs : sideAll (fun i => !i.writesDit) c = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubAll W rb (Clear.of c) c) k rb :=
  ⟨Verified.scrubAll (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd
      (Code.all_of_allInstrs (allInstrs_of_sideAll hs))
      (fun _ _ _ n hn => by rw [inames_of_noIcall (noIcall_of_sideAll hs)] at hn; cases hn) hrb⟩

/-- `sideAll` of code in a frame of its own (`withStackScratch`). -/
theorem sideAll_withStackScratch {p : Instr → Bool} {bytes : Nat} {r : Reg} {c : Prog isa}
    (ha : p (.alloc bytes) = true) (hr : p (.addSp r 0) = true) (hf : p (.free bytes) = true)
    (hc : sideAll p c = true) : sideAll p (Impl.StackScratch.AArch64.withStackScratch bytes r c) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, sideAll, Code.allInstrs_eq, instrs, List.all_cons,
    List.all_nil, ha, hr, hf, hc, Bool.and_self]

/-- How deeply the frames of code in a frame of its own nest. -/
theorem depth_withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) :
    (Impl.StackScratch.AArch64.withStackScratch bytes r c).aarch64Depth = c.aarch64Depth + bytes / 16 := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits, Nat.zero_max]

/-- A function's cleanup (`scrubAll`) writes no PSTATE.DIT and calls nothing:
`sideAll` of code with its cleanup, from the code's. For a function that
calls another as emitted, cleanup included. -/
theorem sideAll_scrubAll {W rb : Nat} {cl : Clear} {c : Prog isa}
    (hc : sideAll (fun i => !i.writesDit) c = true) :
    sideAll (fun i => !i.writesDit) (scrubAll W rb cl c) = true := by
  have hr : ∀ i ∈ retFix rb, (!i.writesDit) = true := by
    intro i hi
    unfold retFix at hi
    split at hi
    · rcases List.mem_singleton.mp hi with rfl; rfl
    · rcases List.mem_singleton.mp hi with rfl; rfl
    · exact absurd hi List.not_mem_nil
  have hcl : ∀ i ∈ clearsOf cl, (!i.writesDit) = true := by
    intro i hi
    simp only [clearsOf, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((⟨r, -, rfl⟩ | ⟨v, -, rfl⟩) | rfl) | ⟨v, -, rfl⟩ <;> rfl
  have hbody : sideAll (fun i => !i.writesDit) (withRet rb (.seq c (.block (clearsOf cl)))) = true := by
    simp only [withRet, sideAll, Code.allInstrs_eq, instrs, List.all_eq_true, Bool.and_eq_true]
    exact ⟨⟨hc, hcl⟩, hr⟩
  unfold scrubAll scrubSel
  split
  · exact hbody
  · simp only [sideAll, scrubTailG, Code.allInstrs_eq, instrs, List.all_eq_true, Bool.and_eq_true, hbody,
      true_and]
    refine ⟨⟨rfl, fun i hi => ?_⟩, rfl⟩
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    simp only [scrubStoresL, List.mem_map] at hi
    obtain ⟨k, -, rfl⟩ := hi
    rfl

end VG.AArch64.Scrub
