module
public import VerifiedGarbage.Proof.Framework.X86.StackScratch

import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.Syms
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, for code that reads tables of constants (x86)

`Verified.stackScratchWipedC`: `Verified.stackScratchWiped` for contracts
under `abi.withConsts K`, whose readable regions end with the tables `K`.
The frame is that of `Verified.stackScratchWiped`; the code runs from
`narrowC`, which is `narrow` of the state without the tables' regions
(`stripConsts`), with the tables' regions after its own. Without its tables, a
state satisfying the contract under `abi.withConsts K` satisfies it under
`abi` (`pre_consts`), so the lemmas of `StackScratch.lean` apply to it; the
tables lie outside the frame, which is within the stack the contract
reserves, so `narrowC` holds them as the entry state does.
-/

@[expose] public section

namespace VG.X86

open VG.Impl.StackScratch.X86

/-- The tables' addresses in `s`, as `abi.withConsts` states them. -/
abbrev symAddr (s : State) (name : String) : Addr := (s.syms name).setWidth 64

/-- The regions of the tables `K` in `s`. -/
abbrev constRegs (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  Abi.constRegions (symAddr s) K

/-- `s` without the regions of the tables `K` at the end of its readable regions. -/
def stripConsts (K : List (String × List (BitVec 64))) (s : State) : State :=
  s.withRegions (s.rd.take (s.rd.length - K.length)) s.wr

/-- What `abi.withConsts K` adds to the calling convention's well-formedness. -/
def ConstsOk (K : List (String × List (BitVec 64))) (st : Nat) (s : State) : Prop :=
  s.rd.drop (s.rd.length - K.length) = constRegs K s ∧ Abi.constsHeld s.mem (symAddr s) K ∧
    ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, t.Disjoint r

section
variable {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}

theorem withConsts_ptrBits : (abi.withConsts (c₀ :: cs)).ptrBits = abi.ptrBits := rfl
theorem withConsts_args : (abi.withConsts (c₀ :: cs)).args = abi.args := rfl
theorem withConsts_argArea : (abi.withConsts (c₀ :: cs)).argArea = abi.argArea := rfl
theorem withConsts_reserved : (abi.withConsts (c₀ :: cs)).reserved = abi.reserved := rfl
theorem withConsts_mem : (abi.withConsts (c₀ :: cs)).mem = abi.mem := rfl
theorem withConsts_wr : (abi.withConsts (c₀ :: cs)).wr = abi.wr := rfl
theorem withConsts_rd :
    (abi.withConsts (c₀ :: cs)).rd = fun s => s.rd.take (s.rd.length - (c₀ :: cs).length) := rfl
theorem withConsts_wf :
    (abi.withConsts (c₀ :: cs)).wf = fun ws n s => abi.wf ws n s ∧ ConstsOk (c₀ :: cs) n s := rfl
theorem withConsts_pub : (abi.withConsts (c₀ :: cs)).pub = fun s₁ s₂ =>
    abi.pub s₁ s₂ ∧ ∀ c ∈ c₀ :: cs, symAddr s₁ c.1 = symAddr s₂ c.1 := rfl
end

section
variable {sig : Sig} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The arguments do not depend on the readable regions. -/
theorem args_stripConsts {K : List (String × List (BitVec 64))} {ws : List Nat} {vals : State → List (BitVec 64)}
    (h : abi.args ws = some vals) (s : State) : vals (stripConsts K s) = vals s := by
  simp only [abi] at h
  split at h
  · cases h; rfl
  · cases h

/-- A precondition under `abi.withConsts`: the one under `abi` without the
tables' regions, and what the tables add. -/
theorem pre_consts {s : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).pre s ↔
      (sig.contract abi pre post wa st leak).pre (stripConsts (c₀ :: cs) s) ∧ ConstsOk (c₀ :: cs) st s := by
  dsimp only [Sig.contract, withConsts_args, withConsts_rd, withConsts_wr, withConsts_wf, withConsts_mem,
    withConsts_argArea, withConsts_reserved, withConsts_ptrBits]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => simp
  | some vals =>
    dsimp only
    rw [args_stripConsts h]
    constructor
    · rintro ⟨⟨hw, hd, hh, ht⟩, hrd, hwr, hpw, hres, hnw, hpr⟩
      exact ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht⟩
    · rintro ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht⟩
      exact ⟨⟨hw, hd, hh, ht⟩, hrd, hwr, hpw, hres, hnw, hpr⟩

/-- A postcondition under `abi.withConsts` is the one under `abi`. -/
theorem post_consts {s s' : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).post s s' ↔
      (sig.contract abi pre post wa st leak).post s s' := Iff.rfl

/-- The public data under `abi.withConsts`: that under `abi`, and the tables'
addresses. -/
theorem pub_consts {s₁ s₂ : State} :
    (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa st leak).pub s₁ s₂ ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ ∧
        ∀ c ∈ c₀ :: cs, symAddr s₁ c.1 = symAddr s₂ c.1 := by
  dsimp only [Sig.contract, withConsts_args, withConsts_pub, withConsts_mem, withConsts_ptrBits]
  generalize abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = o
  cases o with
  | none => simp
  | some vals =>
    cases leak with
    | none =>
      constructor
      · rintro ⟨⟨hp, hs⟩, ha, hd⟩; exact ⟨⟨hp, ha, hd⟩, hs⟩
      · rintro ⟨⟨hp, ha, hd⟩, hs⟩; exact ⟨⟨hp, hs⟩, ha, hd⟩
    | some f =>
      constructor
      · rintro ⟨⟨⟨hp, hs⟩, hl⟩, ha, hd⟩; exact ⟨⟨⟨hp, hl⟩, ha, hd⟩, hs⟩
      · rintro ⟨⟨⟨hp, hl⟩, ha, hd⟩, hs⟩; exact ⟨⟨⟨hp, hs⟩, hl⟩, ha, hd⟩

end

@[simp] theorem stripConsts_gpr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).gpr = s.gpr := rfl
@[simp] theorem stripConsts_mem (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).mem = s.mem := rfl
@[simp] theorem stripConsts_wr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).wr = s.wr := rfl
@[simp] theorem stripConsts_syms (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).syms = s.syms := rfl
theorem stackArgs_stripConsts (sig : Sig) (K : List (String × List (BitVec 64))) (s : State) :
    stackArgs sig (stripConsts K s) = stackArgs sig s := rfl

theorem stripConsts_rd_mem {K : List (String × List (BitVec 64))} {s : State} {r : Region}
    (h : r ∈ (stripConsts K s).rd) : r ∈ s.rd := List.mem_of_mem_take h

theorem setArgsState_syms (bytes k : Nat) (u : State) : (setArgsState bytes k u).syms = u.syms := by
  unfold setArgsState
  cases h : execBlock isa (setArgs bytes k) u with
  | none => rfl
  | some p => exact execBlock_syms h

theorem narrow_syms (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (s : State) :
    (narrow sig e n bytes wa s).syms = s.syms := by
  unfold narrow
  rw [State.withRegions_syms]
  exact setArgsState_syms _ _ _

theorem stackArgs_withRegions (sig : Sig) (s : State) (rd wr : List Region) :
    stackArgs sig (s.withRegions rd wr) = stackArgs sig s := rfl

/-- The state the code runs from: `narrow` of the state without the tables'
regions, with them after its own readable regions. -/
def narrowC (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (K : List (String × List (BitVec 64)))
    (s : State) : State :=
  (narrow sig e n bytes wa (stripConsts K s)).withRegions
    ((narrow sig e n bytes wa (stripConsts K s)).rd ++ constRegs K s) (narrow sig e n bytes wa (stripConsts K s)).wr

theorem narrowC_syms (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes wa K s).syms = s.syms := by
  unfold narrowC
  rw [State.withRegions_syms]
  exact narrow_syms sig e n bytes wa (stripConsts K s)

/-- `narrowC`'s memory, registers and arguments are `narrow`'s. -/
theorem narrowC_mem (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes wa K s).mem = (narrow sig e n bytes wa (stripConsts K s)).mem := by
  unfold narrowC; exact State.withRegions_mem _ _ _

theorem narrowC_gpr (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes wa K s).gpr = (narrow sig e n bytes wa (stripConsts K s)).gpr := by
  unfold narrowC; exact State.withRegions_gpr _ _ _

theorem stackArgs_narrowC (sig' sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool)
    (K : List (String × List (BitVec 64))) (s : State) :
    stackArgs sig' (narrowC sig e n bytes wa K s) = stackArgs sig' (narrow sig e n bytes wa (stripConsts K s)) := by
  unfold narrowC; exact stackArgs_withRegions _ _ _ _

theorem symAddr_congr {s s' : State} (h : s'.syms = s.syms) : symAddr s' = symAddr s := by
  show (fun name => (s'.syms name).setWidth 64) = fun name => (s.syms name).setWidth 64
  rw [h]

theorem constRegs_congr {K : List (String × List (BitVec 64))} {s s' : State} (h : s'.syms = s.syms) :
    constRegs K s' = constRegs K s := by
  simp only [constRegs, symAddr_congr h]

theorem stripConsts_narrowC (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (K : List (String × List (BitVec 64)))
    (s : State) : stripConsts K (narrowC sig e n bytes wa K s) = narrow sig e n bytes wa (stripConsts K s) := by
  have hl : (constRegs K s).length = K.length := List.length_map _
  simp only [stripConsts, narrowC, State.withRegions_rd, State.withRegions_wr, State.withRegions_withRegions,
    List.length_append, hl, Nat.add_sub_cancel, List.take_left', State.withRegions_self]

theorem narrowC_rd_drop (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool)
    (K : List (String × List (BitVec 64))) (s : State) :
    (narrowC sig e n bytes wa K s).rd.drop ((narrowC sig e n bytes wa K s).rd.length - K.length) =
      constRegs K s := by
  have hl : (constRegs K s).length = K.length := List.length_map _
  simp only [narrowC, State.withRegions_rd, List.length_append, hl, Nat.add_sub_cancel, List.drop_left']

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The stack the contract reserves below `esp`, which holds the frame. -/
theorem reserved_below (hS : 0 < stack + bytes) (s : State) :
    (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      abi.reserved (stack + bytes) s := by
  show _ ∈ (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
    List Region)
  rw [show stack + bytes = (stack + bytes - 1) + 1 by omega_using [hS]]; simp [stackBelow]

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrowC`. -/
theorem narrowC_pre (hb : 8 + 4 * slots sig + n * e.size ≤ bytes)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pre
      (narrowC sig e n bytes wa (c₀ :: cs) s) := by
  obtain ⟨hs', hd, hh, ht⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hb hpre hs'
  obtain ⟨hesp, -, -, hf⟩ := narrow_facts (nm := nm) (e := e) (n := n) hb hs'
  have hsy := narrowC_syms sig e n bytes wa (c₀ :: cs) s
  rw [pre_stackL] at hs'
  obtain ⟨⟨hst, -⟩, -, hwr, -, -, -, -⟩ := hs'
  simp only [stripConsts_gpr] at hst hesp
  simp only [stripConsts_gpr, stripConsts_mem] at hf
  have hS : 0 < bytes := by omega_using [hb]
  -- The frame is within the stack the contract reserves, which the tables are apart from.
  have htR : ∀ t ∈ constRegs (c₀ :: cs) s, ∀ {a k : Nat}, a ≤ stack + bytes →
      stack + bytes - a + k ≤ stack + bytes →
      t.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 a, k⟩ := fun t ht' _ _ ha hk =>
    ((ht t ht').2.2 _ (reserved_below (by omega_using [hS]) s)).sub_right (below_sub' _ ha hk)
  refine pre_consts.mpr ⟨?_, ?_, ?_, fun t ht' => ?_⟩
  · rw [stripConsts_narrowC]; exact hn
  · rw [narrowC_rd_drop, constRegs_congr hsy]
  · -- The tables are outside the frame.
    rw [symAddr_congr hsy]
    intro c hc i hi
    have hb64 := (ht ⟨symAddr s c.1, 8 * c.2.length⟩ (List.mem_map_of_mem hc)).1
    rw [← hh c hc i hi, narrowC_mem]
    refine hf.readW (r := ⟨symAddr s c.1, 8 * c.2.length⟩) ?_ (fun r hr => ?_) (by decide)
    · exact Offset.contains_base _ (by omega_using [hi]) (by simp only [abi_ptrBits] at hb64; omega_using [hi, hb64])
    · simp only [List.mem_singleton] at hr; subst hr
      exact htR _ (List.mem_map_of_mem hc) (by omega_using []) (by omega_using [hb])
  rw [constRegs_congr hsy] at ht'
  refine ⟨(ht t ht').1, ?_, ?_⟩
  · -- The writable regions: the buffers, the buffer and the arguments in the frame.
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · refine (ht t ht').2.1 _ ?_
      show a.1 ∈ (stripConsts (c₀ :: cs) s).wr
      rw [hwr]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), hf'⟩,
        rfl⟩
    · show t.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64,
        n * e.size⟩
      rw [sub_add_setWidth (by omega_using [hb]) (by omega_using [hst])]
      exact htR t ht' (by omega_using []) (by omega_using [hb])
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · show t.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64,
        4 * (slots sig + 1)⟩
      rw [sub_add_setWidth (by omega_using [hb]) (by omega_using [hst])]
      exact htR t ht' (by omega_using []) (by omega_using [hb])
  · -- The stack the contract with the buffer reserves.
    intro r hr
    have hr' : r ∈ (⟨((s.gpr .esp - BitVec.ofNat 32 bytes)).setWidth 64, 4⟩ ::
        stackBelow ((s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64) stack : List Region) := by
      rw [← hesp]; exact hr
    rw [Taint.sub_setWidth (by omega_using [hst])] at hr'
    simp only [List.mem_cons, stackBelow_sp'] at hr'
    rcases hr' with rfl | hr'
    · exact htR t ht' (by omega_using []) (by omega_using [hb])
    · by_cases h0 : stack = 0
      · simp [h0] at hr'
      · simp only [h0, ite_false, List.mem_singleton] at hr'; subst hr'
        exact htR t ht' (by omega_using []) (by omega_using [])

/-- A run of the code from `narrowC s` is a run of `withStackScratch` from
`s` (`withStackScratch_run`, under `abi.withConsts`). -/
theorem withStackScratchC_run {c : Prog isa}
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : NoSp c) (hd : stackUse c ≤ stack) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s)
    {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowC sig e n bytes wa (c₀ :: cs) s) t s₃)
    (ha : abiPreserved (narrowC sig e n bytes wa (c₀ :: cs) s) s₃) :
    Exec isa (withStackScratch bytes (slots sig) c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₃).gpr .edx = s₃.gpr .edx := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hs', hdrop, -, -⟩ := pre_consts.mp hs
  obtain ⟨hrun, hrd', hwr', -, -, -, -⟩ := argsState_run hs' hb
  obtain ⟨hesp, hg, -, hf⟩ := narrow_facts (nm := "") (e := e) (n := n) hb hs'
  rw [pre_stackL] at hs'
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, hres, -, -⟩ := hs'
  simp only [stripConsts_gpr] at hst hesp
  simp only [stripConsts_gpr, stripConsts_mem] at hf
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := reserved_below (by omega_using [hb]) s
  have hsp64 : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega_using [hst])
  -- The frame's push and `setArgs`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, show 0 < bytes by omega_using [hb], hb1, hb2, show bytes ≤ (s.gpr .esp).toNat by omega_using [hst],
      and_self, ite_true]
    rfl
  -- `setArgs` from the frame's push in `s`: its run without the tables' regions, widened.
  have hset := Exec.widen (Exec.block hrun) (rd := s.rd)
    (wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)
    (Covers.append (Covers.of_mem fun r hr => stripConsts_rd_mem hr) (Covers.refl _)) (Covers.refl _)
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 a, k⟩]
        (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hsp64]; exact Offset.contains_below _ ha hk (by omega_using [hst])⟩
  have hscr : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) :=
    sub_add_setWidth (by omega_using [hb]) (by omega_using [hst])
  have harea : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) :=
    sub_add_setWidth (by omega_using [hb]) (by omega_using [hst])
  have hbufR : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    refine stripConsts_rd_mem (K := c₀ :: cs) ?_
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hlistR : ∀ a ∈ (Sig.lists abi.ptrBits s.mem sig.params (stackArgs sig s)).map (fun r => (r, false)),
      a.1 ∈ s.rd := fun a ha => by
    refine stripConsts_rd_mem (K := c₀ :: cs) ?_
    rw [hrd]
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_right _ ha),
      rfl⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    show a.1 ∈ (stripConsts (c₀ :: cs) s).wr
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes wa (stripConsts (c₀ :: cs) s)).filter (·.2)).map (·.1))
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · simp only [stripConsts_gpr]; rw [hscr]; exact hF (by omega_using []) (by omega_using [hb])
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp only [stripConsts_gpr]; rw [harea]; exact hF (by omega_using []) (by omega_using [hb])
  have hcovR : Covers ((((oldRegions sig e n bytes wa (stripConsts (c₀ :: cs) s)).filter (!·.2)).map (·.1)) ++
      constRegs (c₀ :: cs) s) (s.rd ++ ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.left (Covers.of_mem fun r hr => ?_))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
      simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ((ha | rfl) | ha) | rfl
      · exact Covers.left (Covers.of_mem fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
      · simp at hf'
      · exact Covers.left (Covers.of_mem fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
      · exact Covers.right (by simp only [stripConsts_gpr]; rw [harea]; exact hF (by omega_using []) (by omega_using [hb]))
    · have hr' : r ∈ s.rd.drop (s.rd.length - (c₀ :: cs).length) := by rw [hdrop]; exact hr
      exact List.mem_of_mem_drop hr'
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowC sig e n bytes wa (c₀ :: cs) s).withRegions s.rd
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) =
      (setArgsState bytes (slots sig) (allocState bytes (stripConsts (c₀ :: cs) s))).withRegions s.rd
        (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) by
    rw [narrowC, narrow, State.withRegions_withRegions, State.withRegions_withRegions]] at hw
  rw [show (allocState bytes (stripConsts (c₀ :: cs) s)).withRegions s.rd
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) = allocState bytes s from rfl]
    at hset
  -- The pop.
  have hesp₃ : s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
    (ha.1 .esp (by simp [calleeSaved])).trans hesp
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, allocState_esp, allocState_wr,
      hesp₃, List.head?_cons, show 0 < bytes by omega_using [hb], hb1, hb2, and_self, ite_true, List.tail_cons,
      BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hset hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_esp] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_⟩, rfl, ?_, ?_⟩
  · simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .esp
    · subst hqs; simp only [ite_true]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .eax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq]
      exact hg q hqa hqs
  · -- The return address: the code writes only its regions and below `esp`.
    have hfs := Exec.frameSp he hsp (by
      show stackUse c ≤ ((narrow sig e n bytes wa (stripConsts (c₀ :: cs) s)).gpr .esp).toNat
      rw [hesp, sub_toNat (by omega_using [hst])]; omega_using [hd, hst])
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
        (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
          ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
      (Offset.base_disjoint_below _ (n := stack + bytes) (k := 4) (by omega_using [hst])).sub_right
        (below_sub' _ hx hk)
    show s₃.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
    rw [hfs.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide),
      narrowC_mem]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hR (by omega_using []) (by omega_using [hb])) (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ((ha | rfl) | ha) | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ (List.mem_append_left _ ha))
        · simp only [stripConsts_gpr]; rw [hscr]; exact hR (by omega_using []) (by omega_using [hb])
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ (List.mem_append_right _ ha))
        · simp only [stripConsts_gpr]; rw [harea]; exact hR (by omega_using []) (by omega_using [hb])
      · simp only [List.mem_singleton] at hr; subst hr
        show (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
          ⟨((narrow sig e n bytes wa (stripConsts (c₀ :: cs) s)).gpr .esp -
            BitVec.ofNat 32 (stackUse c)).setWidth 64,
            stackUse c⟩
        rw [hesp, BitVec.sub_sub, ← BitVec.ofNat_add, Taint.sub_setWidth (by omega_using [hd, hst])]
        exact hR (by omega_using [hd]) (by omega_using [hd])
  · simp [popState, State.setReg]
  · simp [popState, State.setReg]

/-- The public data of a contract does not depend on the readable and
writable regions. -/
theorem pubL_withRegions {s₁ s₂ : State} (r₁ w₁ r₂ w₂ : List Region) :
    (sig.contract abi pre post wa stack leak).pub (s₁.withRegions r₁ w₁) (s₂.withRegions r₂ w₂) ↔
      (sig.contract abi pre post wa stack leak).pub s₁ s₂ := by
  rw [pubL_stackL, pubL_stackL]; exact Iff.rfl

/-- Code verified for a function whose last argument, on the stack, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.stackScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak))
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ stack)
    (hw : 4 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratchWiped bytes (slots sig) words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hnsp : NoSp c := fun i hi => by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    simpa using hsp i hi
  have hnsp' : NoSp (.seq c (.block (wipe (8 + 4 * slots sig) words)) : Prog isa) := fun i hi => by
    simp only [instrs, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hnsp i hi
    · exact wipe_noSp _ _ i hi
  have hd' : stackUse (.seq c (.block (wipe (8 + 4 * slots sig) words)) : Prog isa) ≤ stack := by
    simp only [stackUse]; omega_using [hd]
  -- The buffer, in 64 bits, from the frame's base `E - bytes`.
  have hR : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) ∧
      stack + bytes ≤ (s.gpr .esp).toNat := fun s hs => by
    have hs' := (pre_consts.mp hs).1
    rw [pre_stack hl] at hs'
    obtain ⟨⟨hst, -⟩, -⟩ := hs'
    simp only [stripConsts_gpr] at hst
    exact ⟨sub_add_setWidth (by omega_using [hb]) (by omega_using [hst]), by omega_using [hst]⟩
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∀ b ∈ Sig.bufs sig.params (stackArgs sig s),
        b.1.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)),
          n * e.size⟩ := by
    intro s hs b hb'
    have h0 := (hR s hs).2
    have hs' := (pre_consts.mp hs).1
    rw [pre_stack hl] at hs'
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs'
    exact (Region.Disjoint.symm (hres _ (reserved_below (by omega_using [hb]) s) b (List.mem_append_left _ hb'))).sub_right
      (below_sub' _ (by omega_using []) (by omega_using [hb]))
  -- Every run is `setArgs`, then the code's run from `narrowC`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∃ t s₃ s₄,
      Exec isa c (narrowC sig e n bytes wa (c₀ :: cs) s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post
        (narrowC sig e n bytes wa (c₀ :: cs) s) s₃ ∧
      Frame [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)), n * e.size⟩]
        s₃.mem s₄.mem ∧
      s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes ∧
      Exec isa (withStackScratchWiped bytes (slots sig) words c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++
          (t ++ wipeTrace (s₃.gpr .esp) (8 + 4 * slots sig) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₄).gpr .edx = s₃.gpr .edx := by
    intro s hs
    obtain ⟨hR64, h0⟩ := hR s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowC_pre hb.1 hpreL hs)
    obtain ⟨hesp, -, -, -⟩ := narrow_facts (nm := "") (e := e) (n := n) hb.1 (pre_consts.mp hs).1
    have hespC : (narrowC sig e n bytes wa (c₀ :: cs) s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
      hesp
    have hesp₃ : s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
      (ha.1 .esp (by simp [calleeSaved])).trans hespC
    have hwr₃ : s₃.wr = (narrowC sig e n bytes wa (c₀ :: cs) s).wr := (Exec.rdwr he).2
    have hmem : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)),
        n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃, ← hR64]
      simp [narrowC, narrow, oldRegions]
    obtain ⟨m', hblk, hfr⟩ := wipe_run _ s₃ (8 + 4 * slots sig) words hmem (fun k hk => by
      rw [hesp₃, sub_add_setWidth (by omega_using [hb, hw, hk]) (by omega_using [h0])]
      exact Offset.contains_below _ (by omega_using []) (by omega_using [hw, hk]) (by omega_using [h0]))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowC sig e n bytes wa (c₀ :: cs) s) { s₃.setReg .ecx 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ?_⟩
      · have hq' : q ≠ .ecx := by rintro rfl; simp [calleeSaved] at hq
        simp only [State.setReg, hq', ↓reduceIte]
        exact ha.1 q hq
      · show m'.readW _ 32 = _
        rw [hespC, Taint.sub_setWidth (by omega_using [h0])]
        rw [hfr.readW (r := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes, 4⟩)
          (Region.contains_self _ _) (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact below_disjoint _ bytes (a := bytes) (b := bytes - (8 + 4 * slots sig))
              (by omega_using []) (by omega_using []) (.inl (by omega_using [hb])) (by omega_using []) (by omega_using [hb]))
          (by decide)]
        have h2 := ha.2
        rwa [hespC, Taint.sub_setWidth (by omega_using [h0])] at h2
    obtain ⟨hex, habi, hm, heax, hedx⟩ := withStackScratchC_run hb hnsp' hd' hs he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hesp₃, hex, habi, hm, ?_, ?_⟩
    · rw [heax]; simp [State.setReg]
    · rw [hedx]; simp [State.setReg]
  -- The public data in `narrowC`.
  have hpub : ∀ s₁ s₂,
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₁ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₂ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pub s₁ s₂ →
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub
        (narrowC sig e n bytes wa (c₀ :: cs) s₁) (narrowC sig e n bytes wa (c₀ :: cs) s₂) := by
    intro s₁ s₂ h₁ h₂ hp
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    refine pub_consts.mpr ⟨(pubL_withRegions _ _ _ _).mpr
      (narrow_pub hb.1 (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 ((pubL_withRegions _ _ _ _).mpr hp')
        hleak.toL), ?_⟩
    rw [symAddr_congr (narrowC_syms ..), symAddr_congr (narrowC_syms ..)]
    exact hsy
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_consts, post_stack]
    have hq' := (post_stack (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp (post_consts.mp hq)
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hb.1 (pre_consts.mp hs).1
    simp only [stackArgs_stripConsts, stripConsts_gpr] at hargs
    rw [stackArgs_narrowC, hargs] at hq'
    rw [hm, heax, hedx]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (stackArgs_length sig s)) _) s₃.mem) _) hq'
    have hag := narrow_agree (e := e) (n := n) hb.1 (pre_consts.mp hs).1
    simp only [stackArgs_stripConsts, stripConsts_mem] at hag
    rw [narrowC_mem] at hq''
    have h₃ := hpost _ _ _ _ _ (stackArgs_length sig s) hag hq''
    refine hpostOut _ _ _ _ _ (stackArgs_length sig s) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pubL_stack hl).mp (pub_consts.mp hp).1).1.1,
      hct _ _ _ _ _ _ (narrowC_pre hb.1 hpreL h₁) (narrowC_pre hb.1 hpreL h₂) (hpub s₁ s₂ h₁ h₂ hp)
        f₁ f₂]

end

end VG.X86
