module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Impl.Scrub.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce

/-!
# The registers PPC64LE code may write

Untrusted: everything here is checked by Lean. Which general-purpose and
vector registers, and whether CA, code may write, read off its instructions
(`gWrites`, `vWrites`, `caWrites`): a register no instruction writes keeps
its value through any run (`Exec.gpr_of`, `Exec.vpr_of`, `Exec.ca_of`), but
for the registers linkage code may change (`linkRegs`) in code that calls.
Calls, frames and their release change no vector register and not CA.

`Clear.of c cs` is what the scrub tail after `c` needs to clear, with the
levels `cs` of stack: the volatile registers `c` may write, and `r0` and
`r12`, which the wipe uses, when there are levels (`Clear.of_keep`,
`Clear.of_wf`).
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.Scrub.PPC64LE

/-- The register a vector instruction writes. -/
def VOp.dst : VOp → VReg
  | .cipher _ _ d .. | .sbox d _ | .sha256 d .. | .sha512 d .. | .pmsumd d .. | .logic _ d ..
  | .sel d .. | .add _ d .. | .perm d .. | .sldoi d .. | .rlw d .. | .addh d .. | .sub _ d ..
  | .minu _ d .. | .mulu _ _ d .. | .muluwm d .. | .mladduhm d .. | .shifth _ d .. | .splat _ d ..
  | .splatImm _ d _ => d

theorem VOp.eval_dst {op : VOp} {w : VReg → BitVec 128} {d : VReg} {x : BitVec 128}
    (h : op.eval w = some (d, x)) : d = op.dst := by
  cases op <;> simp only [VOp.eval] at h <;> (repeat' split at h) <;>
    first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm)
    | cases h

/-- The vector register an instruction writes, if any. -/
def vdstOf : Instr → Option VReg
  | .vop op => some op.dst
  | .lxvd2x d .. | .lxvd2xTbl d .. | .mtvsrd d _ => some d
  | _ => none

/-- Whether an instruction writes CA. -/
def writesCa : Instr → Bool
  | .addc .. | .adde .. | .addze .. | .subc .. | .sube .. => true
  | _ => false

section
variable {s s' : State}

theorem exec_vpr_ca {i : Instr} (h : exec i s = some s') :
    (∀ v, vdstOf i ≠ some v → s'.vpr v = s.vpr v) ∧ (writesCa i = false → s'.ca = s.ca) := by
  have hst : ∀ {a : Addr} {n : Nat} {v : BitVec (8 * n)}, s.store a n v = some s' →
      s'.vpr = s.vpr ∧ s'.ca = s.ca := by
    intro a n v h
    simp only [State.store] at h
    split at h <;> cases h; exact ⟨rfl, rfl⟩
  have hwv : ∀ (t : State) (d v : VReg) (x : BitVec 128), d ≠ v → (t.writeV d x).vpr v = t.vpr v :=
    fun t d v x hd => by simp [State.writeV, Ne.symm hd]
  cases i with
  | store sz t n off | stb t n off | stxvd2x t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h
    obtain ⟨a, -, h⟩ := h
    obtain ⟨h1, h2⟩ := hst h
    exact ⟨fun v _ => by rw [h1], fun _ => h2⟩
  | storeRev sz t a b =>
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff] at h
      obtain ⟨a, -, h⟩ := h
      obtain ⟨h1, h2⟩ := hst h
      exact ⟨fun v _ => by rw [h1], fun _ => h2⟩
  | load sz t n off | lbz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | loadRev sz t a b =>
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | lxvd2x d a b =>
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, rfl⟩ := h
    exact ⟨fun v hv => hwv _ _ _ _ fun e => hv (by simp [vdstOf, e]), fun _ => rfl⟩
  | vop op =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨⟨d, x⟩, he, rfl⟩ := h
    have hd := VOp.eval_dst he
    exact ⟨fun v hv => hwv _ _ _ _ fun e => hv (by dsimp only at e; rw [vdstOf, ← hd, e]), fun _ => rfl⟩
  | lxvd2xTbl d a b name ws =>
    simp only [reduceExec] at h
    split at h <;> [skip; cases h]
    simp only [Option.some.injEq] at h; subst h
    exact ⟨fun v hv => hwv _ _ _ _ fun e => hv (by simp [vdstOf, e]), fun _ => rfl⟩
  | mtvsrd d n =>
    simp only [reduceExec, Option.some.injEq] at h; subst h
    exact ⟨fun v hv => hwv _ _ _ _ fun e => hv (by simp [vdstOf, e]), fun _ => rfl⟩
  | mtlr r' =>
    simp only [exec, Option.some.injEq] at h; subst h; exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | adrSym d name =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [Option.some.injEq] at h; subst h
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | push _ | pop _ | alloc _ | free _ | bctrl => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h
       exact ⟨fun _ _ => rfl, fun h => by simp [writesCa] at h⟩)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)

theorem execBlock_vpr_ca {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    (∀ v, (∀ i ∈ is, vdstOf i ≠ some v) → s'.vpr v = s.vpr v) ∧
      ((∀ i ∈ is, writesCa i = false) → s'.ca = s.ca) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]; exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨iv, ic⟩ := ih h2
    obtain ⟨ev, ec⟩ := exec_vpr_ca he
    exact ⟨fun v hv => (iv v fun j hj => hv j (List.mem_cons_of_mem _ hj)).trans
        (ev v (hv i List.mem_cons_self)),
      fun hc => (ic fun j hj => hc j (List.mem_cons_of_mem _ hj)).trans (ec (hc i List.mem_cons_self))⟩

end

theorem call_vpr_ca {s s' : State} (h : isa.call s = some s') : s'.vpr = s.vpr ∧ s'.ca = s.ca := by
  simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem push_vpr_ca {i : Instr} {s s' : State} (h : isa.push i s = some s') :
    s'.vpr = s.vpr ∧ s'.ca = s.ca := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> (split at h <;> cases h) <;> exact ⟨rfl, rfl⟩

theorem pop_vpr_ca {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.vpr = s₂.vpr ∧ s'.ca = s₂.ca := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h <;> (split at h <;> cases h) <;> exact ⟨rfl, rfl⟩

/-- A vector register no instruction writes, and CA if no instruction writes
it, keep their values. -/
theorem Exec.vpr_ca {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    (∀ v, (∀ i ∈ instrs c, vdstOf i ≠ some v) → s'.vpr v = s.vpr v) ∧
      ((∀ i ∈ instrs c, writesCa i = false) → s'.ca = s.ca) := by
  induction h with
  | icall _ hc₁ _ hr ih =>
    rw [ret_eq hr]
    obtain ⟨cv, cc⟩ := call_vpr_ca hc₁
    exact ⟨fun v hv => by
        rw [ih.1 v fun i hi => hv i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)), cv],
      fun hc => by rw [ih.2 fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)), cc]⟩
  | icallNext _ _ _ ih =>
    exact ⟨fun v hv => ih.1 v fun i hi => hv i (List.mem_cons_of_mem _ (List.mem_append_right _ hi)),
      fun hc => ih.2 fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))⟩
  | block h => exact execBlock_vpr_ca h
  | seq _ _ ih₁ ih₂ =>
    exact ⟨fun v hv => by
        rw [ih₂.1 v fun i hi => hv i (List.mem_append_right _ hi),
          ih₁.1 v fun i hi => hv i (List.mem_append_left _ hi)],
      fun hc => by
        rw [ih₂.2 fun i hi => hc i (List.mem_append_right _ hi),
          ih₁.2 fun i hi => hc i (List.mem_append_left _ hi)]⟩
  | iteT _ _ ih =>
    exact ⟨fun v hv => ih.1 v fun i hi => hv i (List.mem_append_left _ hi),
      fun hc => ih.2 fun i hi => hc i (List.mem_append_left _ hi)⟩
  | iteF _ _ ih =>
    exact ⟨fun v hv => ih.1 v fun i hi => hv i (List.mem_append_right _ hi),
      fun hc => ih.2 fun i hi => hc i (List.mem_append_right _ hi)⟩
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ =>
    exact ⟨fun v hv => by rw [ih₂.1 v hv, ih₁.1 v hv], fun hc => by rw [ih₂.2 hc, ih₁.2 hc]⟩
  | call hc₁ _ hr ih =>
    rw [ret_eq hr]
    obtain ⟨cv, cc⟩ := call_vpr_ca hc₁
    exact ⟨fun v hv => by rw [ih.1 v hv, cv], fun hc => by rw [ih.2 hc, cc]⟩
  | frame hp _ hq ih =>
    obtain ⟨pv, pc⟩ := push_vpr_ca hp
    obtain ⟨qv, qc⟩ := pop_vpr_ca hq
    exact ⟨fun v hv => by
        rw [qv, ih.1 v fun i hi => hv i (by simp [instrs, hi]), pv],
      fun hc => by rw [qc, ih.2 fun i hi => hc i (by simp [instrs, hi]), pc]⟩

/-- Whether code calls no function (it may have frames). -/
def callFree : Prog isa → Bool
  | .block _ => true
  | .seq a b => callFree a && callFree b
  | .ite _ t e => callFree t && callFree e
  | .loop b _ => callFree b
  | .call _ _ => false
  | .frame _ b _ => callFree b
  | .icall .. => false

/-- A general-purpose register that no instruction writes keeps its value,
unless it is one of `linkRegs` and the code calls a function. -/
theorem Exec.gpr_of {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hn : callFree c = true ∨ r ∉ linkRegs) :
    s'.gpr r = s.gpr r := by
  induction h with
  | icall _ hc₁ _ hr ih =>
    rcases hn with hn | hn
    · simp [callFree] at hn
    · rw [ret_eq hr, ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))) (.inr hn),
        (call_eq hc₁).2.2.2.2 r hn]
  | icallNext _ _ _ ih =>
    rcases hn with hn | hn
    · simp [callFree] at hn
    · exact ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))) (.inr hn)
  | block h => exact execBlock_gpr hc h
  | seq _ _ ih₁ ih₂ =>
    simp only [callFree, Bool.and_eq_true] at hn
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)) (hn.imp And.right id),
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi)) (hn.imp And.left id)]
  | iteT _ _ ih =>
    simp only [callFree, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) (hn.imp And.left id)
  | iteF _ _ ih =>
    simp only [callFree, Bool.and_eq_true] at hn
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) (hn.imp And.right id)
  | loopExit _ _ ih => exact ih hc hn
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hn, ih₁ hc hn]
  | call hc₁ _ hr ih =>
    rcases hn with hn | hn
    · simp [callFree] at hn
    · rw [ret_eq hr, ih hc (.inr hn), (call_eq hc₁).2.2.2.2 r hn]
  | frame hp _ hq ih =>
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (hc _ (by simp [instrs])),
      ih (fun i hi => hc i (by simp [instrs, hi])) (by simpa [callFree] using hn), hg]

/-! ## What code writes -/

/-- The general-purpose registers code may write: its instructions'
destinations, and `linkRegs` if it calls. -/
def gWrites (c : Prog isa) : List Reg :=
  (instrs c).filterMap dstOf ++ (if callFree c then [] else linkRegs)

/-- The vector registers code may write. -/
def vWrites (c : Prog isa) : List VReg := (instrs c).filterMap vdstOf

/-- Whether code may write CA. -/
def caWrites (c : Prog isa) : Bool := (instrs c).any writesCa

theorem Exec.gpr_of_gWrites {c : Prog isa} {r : Reg} (hr : r ∉ gWrites c) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : s'.gpr r = s.gpr r := by
  simp only [gWrites, List.mem_append, List.mem_filterMap, not_or, not_exists, not_and] at hr
  refine Exec.gpr_of (fun i hi e => hr.1 i hi e) h ?_
  cases hcf : callFree c
  · simp only [hcf, Bool.false_eq_true, ite_false] at hr; exact .inr hr.2
  · exact .inl rfl

theorem Exec.vpr_of_vWrites {c : Prog isa} {v : VReg} (hv : v ∉ vWrites c) {s s' : State}
    {t : List Leak} (h : Exec isa c s t s') : s'.vpr v = s.vpr v := by
  simp only [vWrites, List.mem_filterMap, not_exists, not_and] at hv
  exact (Exec.vpr_ca h).1 v fun i hi e => hv i hi e

theorem Exec.ca_of_caWrites {c : Prog isa} (hc : caWrites c = false) {s s' : State}
    {t : List Leak} (h : Exec isa c s t s') : s'.ca = s.ca := by
  simp only [caWrites, List.any_eq_false] at hc
  exact (Exec.vpr_ca h).2 fun i hi => by simpa using hc i hi

end VG.PPC64LE

namespace VG.Impl.Scrub.PPC64LE

open VG.PPC64LE

/-! ## What the clearing after code clears -/

/-- The registers the tail after `c`, with the levels `cs` of stack, clears:
the volatile ones `c` may write, and `r0` and `r12` when there are levels
(the wipe's zero and base) or `r0` when CA is cleared (`addc r0, r0, r0`). -/
def Clear.of (c : Prog isa) (cs : List Nat) : Clear :=
  let g := gWrites c
  let lv := !cs.isEmpty
  let ca := caWrites c
  { r0 := lv || ca || g.contains .r0
    r3 := g.contains .r3
    gs := scratchRegs.filter fun r => g.contains r || (lv && r == .r12)
    ca := ca
    vs := vregs.filter fun v => (vWrites c).contains v }

/-- The general-purpose registers a clearing zeroes. -/
def Clear.Zeroes (cl : Clear) (r : Reg) : Prop := (r = .r0 ∧ cl.r0 = true) ∨ r ∈ cl.gs

instance (cl : Clear) (r : Reg) : Decidable (cl.Zeroes r) := by
  unfold Clear.Zeroes; infer_instance

/-- What the clearing needs of `cl` to run: `r0` zeroed when there are
levels or CA to clear, `r12` among those it zeroes when there are levels,
and only scratch registers among `gs`. -/
structure Clear.WF (cl : Clear) (cs : List Nat) : Prop where
  r0 : cs ≠ [] ∨ cl.ca = true → cl.r0 = true
  r12 : cs ≠ [] → .r12 ∈ cl.gs
  gs : ∀ r ∈ cl.gs, r ∈ scratchRegs

/-- Code keeps what `cl` does not clear: the volatile registers but `r3`, `r3`
unless `cl.r3`, the vector registers and CA. -/
def Clear.Keeps (cl : Clear) (c : Prog isa) : Prop :=
  ∀ s t u, Exec isa c s t u →
    (∀ r, r ≠ .r3 → (r = .r0 ∨ r ∈ scratchRegs) → ¬ cl.Zeroes r → u.gpr r = s.gpr r) ∧
    (cl.r3 = false → u.gpr .r3 = s.gpr .r3) ∧
    (∀ v, v ∉ cl.vs → u.vpr v = s.vpr v) ∧ (cl.ca = false → u.ca = s.ca)

theorem Clear.of_wf (c : Prog isa) (cs : List Nat) : (Clear.of c cs).WF cs where
  r0 h := by
    rcases h with h | h
    · cases cs with
      | nil => exact absurd rfl h
      | cons => simp [Clear.of]
    · simp only [Clear.of] at h ⊢; simp [h]
  r12 h := by
    cases cs with
    | nil => exact absurd rfl h
    | cons => simp [Clear.of, scratchRegs]
  gs r h := by simp only [Clear.of, List.mem_filter] at h; exact h.1

theorem Clear.of_keep (c : Prog isa) (cs : List Nat) : (Clear.of c cs).Keeps c := by
  intro s t u he
  refine ⟨fun r h3 hv hz => Exec.gpr_of_gWrites (fun hm => hz ?_) he, fun h => Exec.gpr_of_gWrites ?_ he,
    fun v hv => Exec.vpr_of_vWrites (fun hm => hv ?_) he, fun h => Exec.ca_of_caWrites h he⟩
  · rcases hv with rfl | hv
    · exact .inl ⟨rfl, by simp [Clear.of, hm]⟩
    · exact .inr (by simp [Clear.of, List.mem_filter, hv, hm])
  · intro hm; simp [Clear.of, hm] at h
  · exact List.mem_filter.mpr ⟨by cases v <;> simp [vregs], by simpa using hm⟩

end VG.Impl.Scrub.PPC64LE
