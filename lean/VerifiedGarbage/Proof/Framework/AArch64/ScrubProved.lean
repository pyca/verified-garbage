module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAllW
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Proof.Framework.Lit

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

theorem wf_of_wfB {cl : Clear} (h : wfB cl = true) : cl.WF := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

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
def scrubAllOf {api : Api} (r : Unscrubbed api target) (cl : Clear) {W rb : Nat}
    (hok : ScrubAllOk r.contract W rb)
    (hs : scrubSide r.code W rb cl r.tables = true := by
      (try dsimp only [VG.AArch64.ScrubAll.retBitsOf]); lit_decide)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have hok : ScrubAllOk r.contract r.stack (retBitsOf r) := by rw [hW, hb]; exact hok
  have h : scrubSide r.code r.stack (retBitsOf r) cl r.tables = true := by rw [hW, hb]; exact hs
  {
  suffix := r.suffix
  tables := r.tables
  code := scrubAll r.stack (retBitsOf r) cl r.code
  contract := r.contract
  verified := .scrubbed <| .abi (cs := r.consts) (sig' := api.sig) (ts := r.tables) ⟨(by
    obtain ⟨hwf, -, -, hrb⟩ := keeps_of_side h
    rcases Nat.eq_zero_or_pos r.stack with h0 | hpos
    · rw [h0]; exact Verified.scrubAll0 hwf r.verified hrb (h0 ▸ hok)
    · have hs := h
      simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hs
      exact Verified.scrubAll hwf r.verified ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hrb hok), by
    obtain ⟨hwf, hkp, hdit, hrb⟩ := keeps_of_side h
    rcases Nat.eq_zero_or_pos r.stack with h0 | hpos
    · have hs := h
      simp only [scrubSide, h0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hs
      rw [h0]; exact noResidue_scrubAll0 hwf hkp r.verified hs.1.1.1.1 hdit hrb
    · have hs := h
      simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hs
      exact noResidue_scrubAll hwf hkp r.verified ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hok.sp
        hs.1.1.1.1.1.2 hdit (tablesCall_syms hs.1.1.1.1.2) hrb⟩
  consts := r.consts
  stack := r.stack
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := all_spSafe _
  written := r.written
  writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith }

/-- What `scrubAllOf` proves of the code, for code verified against any
contract `k`: a caller that calls the scrubbed code by name (as
`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`) proves its call against
it. -/
theorem Verified.scrubAllOfV {c : Prog isa} {k : Contract isa} {cl : Clear} {W rb : Nat}
    {ts : List (String × List FnTable)} (hv : Verified target c k) (hok : ScrubAllOk k W rb)
    (h : scrubSide c W rb cl ts = true) : Verified target (VG.Impl.Residue.AArch64.scrubAll W rb cl c) k := by
  obtain ⟨hwf, -, -, hrb⟩ := keeps_of_side h
  rcases Nat.eq_zero_or_pos W with h0 | hpos
  · subst h0; exact Verified.scrubAll0 hwf hv hrb hok
  · have hs := h
    simp only [scrubSide, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hs
    exact Verified.scrubAll hwf hv ⟨hpos, hs.1.1.1.1.1.1.1, hs.1.1.1.1.1.1.2⟩ hrb hok

/-- `scrubAllOf` for code without frames (`scrubSide` with no stack, whose
depth is then 0) that keeps what `r` states of `written`: `withScrubAllW`,
with the registers the tail clears stated and what it needs of the code
proved (`scrubSide` with no stack). -/
def scrubAllWOf {api : Api} (r : Unscrubbed api target) (cl : Clear) {rb : Nat}
    (hok : ScrubAllOk r.contract 0 rb)
    (hs : scrubSide r.code 0 rb cl r.tables = true := by
      (try dsimp only [VG.AArch64.ScrubAll.retBitsOf]); lit_decide)
    (hb : retBitsOf r = rb := by rfl) : Registration api target :=
  have hok : ScrubAllOk r.contract 0 (retBitsOf r) := by rw [hb]; exact hok
  have h : scrubSide r.code 0 (retBitsOf r) cl r.tables = true := by rw [hb]; exact hs
  have hk := keeps_of_side h
  have hd : r.code.aarch64Depth = 0 := by
    have hs := h
    simp only [scrubSide, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hs
    exact hs.1.1.1.1
  { suffix := r.suffix
    tables := r.tables
    code := scrubAll 0 (retBitsOf r) cl r.code
    contract := r.contract
    verified := .scrubbed <| .abi ⟨Verified.scrubAll0 hk.1 r.verified hk.2.2.2 hok,
      noResidue_scrubAll0 hk.1 hk.2.1 r.verified hd hk.2.2.1 hk.2.2.2⟩
    consts := r.consts
    stack := r.stack
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := all_spSafe _
    written := r.written
    writtenOk := fun s t s' hs he => by
      obtain ⟨t', u, hc, hm⟩ := scrubAll0_mem hk.1 hk.2.2.2 he
      exact writtenWithin_of_mem hm (r.writtenOk s t' u hs hc)
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

/-- `Clear.union`: the registers of `a` and of `b`, in `Clear.all`'s order
(which is `Clear.of`'s). -/
abbrev clearUnion (a b : Clear) : Clear := a.union b

/-! ## The cleanup as part of the code

`verifiedScrubbed` is what `scrubAllOf` registers, as a theorem about the
code with its cleanup (`scrubAll W rb cl c`, which `Impl/` defines as the
function): the proof a registration binds (`verified := .scrubbed …`).
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

/-- `r`'s code with its cleanup (`scrubAll`, over its whole stack, the
registers `cl` cleared) meets `r`'s contract in constant time and returns
without secret residue: what `scrubAllOf` registers, as the theorem about
the code that a registration binds (`verified := .scrubbed …`). -/
theorem verifiedScrubbed {api : Api} (r : Unscrubbed api target) (cl : Clear) {W rb : Nat}
    (hok : ScrubAllOk r.contract W rb) (hs : scrubSide r.code W rb cl r.tables = true)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl)
    (hw : r.written = [] := by rfl) :
    VerifiedScrubbed target (scrubAll W rb cl r.code) r.contract rb := by
  have e : api.sig.retBits target.abi.ptrBits = retBitsOf r :=
    (Abi.retBits_withConsts_withTables target.abi api.sig api.sig r.consts r.tables).symm
  subst hW hb
  have h := (scrubAllOf r cl hok hs rfl rfl hw).verified
  have hn := h.noResidue
  rw [e] at hn
  exact ⟨h.verified, hn⟩

end VG.AArch64.ScrubAll
