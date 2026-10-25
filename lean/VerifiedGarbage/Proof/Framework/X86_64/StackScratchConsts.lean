module
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A scratch buffer on the stack, for code that reads tables of constants (x86-64)

`Verified.stackScratchWipedC`: `Verified.stackScratchWiped` for contracts
under `abi.withConsts K`, whose readable regions end with the tables `K`.
The frame and the state the code runs from (`narrow`) are those of
`Verified.stackScratchWiped`. Without its tables, a state satisfying the
contract under `abi.withConsts K` satisfies it under `abi` (`pre_consts`),
so the lemmas of `StackScratch.lean` apply to it; `narrow` keeps the
readable regions, the memory and the statics' addresses, and the tables lie
outside the frame, which is within the stack the contract reserves
(`narrowK_pre`). The run of the frame (`withStackScratchK_run`) is
`withStackScratch_run`'s, which needs of the entry state only that the
contract reserves the frame's stack and that the return address is outside
the writable regions.
-/

@[expose] public section

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- The regions of the tables `K` in `s`. -/
abbrev constRegs (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  Abi.constRegions (fun name => s.syms name) K

/-- `s` without the regions of the tables `K` at the end of its readable regions. -/
def stripConsts (K : List (String × List (BitVec 64))) (s : State) : State :=
  s.withRegions (s.rd.take (s.rd.length - K.length)) s.wr

/-- What `abi.withConsts K` adds to the calling convention's well-formedness. -/
def ConstsOk (K : List (String × List (BitVec 64))) (st : Nat) (s : State) : Prop :=
  s.rd.drop (s.rd.length - K.length) = constRegs K s ∧ Abi.constsHeld s.mem (fun name => s.syms name) K ∧
    ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, t.Disjoint r

@[simp] theorem stripConsts_gpr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).gpr = s.gpr := rfl
@[simp] theorem stripConsts_mem (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).mem = s.mem := rfl
@[simp] theorem stripConsts_wr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).wr = s.wr := rfl

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
  · cases h; rfl

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
    abi.pub s₁ s₂ ∧ ∀ c ∈ c₀ :: cs, s₁.syms c.1 = s₂.syms c.1 := rfl

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
      (sig.contract abi pre post wa st leak).pub s₁ s₂ ∧ ∀ c ∈ c₀ :: cs, s₁.syms c.1 = s₂.syms c.1 := by
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

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat}

@[simp] theorem narrow_syms (s : State) : (narrow sig e n bytes s).syms = s.syms := rfl

/-- `narrow` of `s` without the tables' regions is `narrow s` without them. -/
theorem stripConsts_narrow (K : List (String × List (BitVec 64))) (s : State) :
    stripConsts K (narrow sig e n bytes s) = narrow sig e n bytes (stripConsts K s) := rfl

/-- The stack the contract reserves below `rsp`, which holds the frame. -/
theorem reserved_below (hS : 0 < stack + bytes) (s : State) :
    below (s.gpr .rsp) (stack + bytes) ∈ abi.reserved (stack + bytes) s := by
  show _ ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region)
  rw [stackBelow_pos _ hS]; simp

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrow`. -/
theorem narrowK_pre (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).pre (narrow sig e n bytes s) := by
  obtain ⟨hs', hd, hh, ht⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hk hb hst hs' hl
  have hwf := ((pre_regs (by omega_arith) hl).mp hs').1
  simp only [stripConsts_gpr] at hwf
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_arith
  have hR := reserved_below (stack := stack) (bytes := bytes) (by omega_arith) s
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_eight _ (by omega_arith)
  refine pre_consts.mpr ⟨by rw [stripConsts_narrow]; exact hn, hd, hh, fun t ht' => ⟨(ht t ht').1, ?_, ?_⟩⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (ht t ht').2.1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hscr]
      exact ((ht t ht').2.2 _ hR).sub_right (Offset.sub_below _ (by omega_arith) (by omega_arith))
  · intro r hr
    have hr' : r ∈ (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩ ::
        stackBelow (s.gpr .rsp - BitVec.ofNat 64 bytes) stack : List Region) := by
      have := narrow_rsp (sig := sig) (e := e) (n := n) (bytes := bytes) hk s
      simp only [abi] at hr; rw [this] at hr; exact hr
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact ((ht t ht').2.2 _ hR).sub_right (Offset.sub_below _ (by omega_arith) (by omega_arith))
    · rcases Nat.eq_zero_or_pos stack with h0 | h0
      · subst h0; simp [stackBelow] at hr'
      · rw [stackBelow_pos _ h0, List.mem_singleton] at hr'; subst hr'
        exact ((ht t ht').2.2 _ hR).sub_right (below_below _ bytes stack)

/-- `withStackScratch_run`, from the facts about the entry state it needs: the
stack the contract reserves, and the return address outside the writable
regions. -/
theorem withStackScratchK_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsafe : SpSafe c) (hd : c.x86_64Depth ≤ stack) {s : State}
    (hsb : stack + bytes ≤ (s.gpr .rsp).toNat)
    (hretW : ∀ r ∈ s.wr, Region.Disjoint ⟨s.gpr .rsp, 8⟩ r) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr1, hr2, -⟩ := argRegs_scratch _ hk
  -- The frame's push, then `setScratch`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega_arith⟩
  have hblk := Exec.block (M := isa) (setScratch_run (argRegs.getD (sig.words abi.ptrBits).length .rax)
    (allocState bytes s))
  -- The code, with the permissions of the state after the push.
  have hcov : Covers (s.wr ++ [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩])
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_base _ (d := 8) (by omega_arith) (by omega_arith)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState (argRegs.getD (sig.words abi.ptrBits).length .rax) (allocState bytes s) from rfl] at hw
  -- The pop.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans (narrow_rsp hk s)
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr]
    refine ite_eq_left ⟨hb0, hb1, hb2, ?_, rfl, ?_⟩
    · rw [hrsp₃]; simp [allocState, State.setReg]
    · simp [allocState, State.setReg]
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, rfl, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      rw [ha.1 q hq, narrow_gpr hk]
      have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .rax := fun h => hr2 (h ▸ hq)
      simp only [hqr, hqs, ↓reduceIte]
  · -- The return address: the code writes only its regions and below `rsp`.
    have hf := Exec.stackFrame hsafe he (by omega_arith)
    simp only [narrow_wr, narrow_mem, narrow_rsp hk] at hf
    show s₃.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)
    rcases List.mem_append.mp hr' with hr' | hr'
    · rcases List.mem_append.mp hr' with hr' | hr'
      · exact hretW r' hr'
      · simp only [List.mem_singleton] at hr'; subst hr'
        have := Offset.disjoint (s.gpr .rsp - BitVec.ofNat 64 bytes) (d := bytes) (n := 8) (e := 8)
          (k := n * e.size) (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
        rwa [BitVec.sub_add_cancel] at this
    · simp only [List.mem_singleton] at hr'; subst hr'
      have := Offset.disjoint_below (s.gpr .rsp - BitVec.ofNat 64 bytes) (n := c.x86_64Depth)
        (d := bytes) (k := 8) (by omega_arith)
      rwa [BitVec.sub_add_cancel] at this
  · -- MXCSR.
    exact ha.2.2
  · simp [popState, State.setReg]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.stackScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hw : 8 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target
      (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe : SpSafe (.seq c (.block (wipe words)) : Prog isa) :=
    SpSafe.of_all (by simp only [Code.all, hsp, wipe_spSafe, Bool.and_self])
  have hdep : (Code.seq c (.block (wipe words)) : Prog isa).x86_64Depth ≤ stack := by
    simp only [Code.x86_64Depth]; omega_arith
  have hlen := regArgs_length sig
  -- What the precondition says of the entry state, without the tables.
  have hfacts : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s →
      stack + bytes ≤ (s.gpr .rsp).toNat ∧ (∀ r ∈ s.wr, Region.Disjoint ⟨s.gpr .rsp, 8⟩ r) ∧
      ∀ b ∈ Sig.bufs sig.params (regArgs sig s),
        b.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ := by
    intro s hs
    have hs' := (pre_regs (by omega_arith) hl).mp (pre_consts.mp hs).1
    obtain ⟨hwf, -, hwr, -, hres, -, -⟩ := hs'
    simp only [stripConsts_gpr, stripConsts_wr] at hwf hwr hres
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega_arith
    have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
        (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
      rw [stackBelow_pos _ (by omega_arith)]; simp
    have hscrSub : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩
        (below (s.gpr .rsp) (stack + bytes)) := by
      rw [sub_add_eight _ (by omega_arith)]; exact Offset.sub_below _ (by omega_arith) (by omega_arith)
    refine ⟨hsb, fun r hr => ?_, fun b hb' => (Region.Disjoint.symm (hres _ hbelow b hb')).sub_right hscrSub⟩
    rw [hwr] at hr
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hr
    exact hres _ (List.mem_cons_self ..) a (List.mem_filter.mp ha').1
  -- Every run is the code's run from `narrow`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s → ∃ t s₃ m',
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).post
        (narrow sig e n bytes s) s₃ ∧
      Frame [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩] s₃.mem m' ∧
      Exec isa (withStackScratchWiped bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) words c) s
        (t ++ wipeTrace (s.gpr .rsp - BitVec.ofNat 64 bytes) words)
        (popState bytes s { s₃.setReg32 .r11 0 with mem := m' }) ∧
      abiPreserved s (popState bytes s { s₃.setReg32 .r11 0 with mem := m' }) ∧
      (popState bytes s { s₃.setReg32 .r11 0 with mem := m' }).mem = m' ∧
      (popState bytes s { s₃.setReg32 .r11 0 with mem := m' }).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨hsb, hretW, -⟩ := hfacts s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowK_pre hk hb hst hs hl)
    have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
      (ha.1 .rsp (by simp [calleeSaved])).trans (narrow_rsp hk s)
    have hwr₃ : s₃.wr = (narrow sig e n bytes s).wr := (Exec.rdwr he).2
    have hb0 := hb.1
    have hb3 := hb.2.2.2
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ s₃ words
      (by rw [hwr₃, narrow_wr]; simp)
      (fun k hk' => by
        have h8 := Offset.contains_base (s.gpr .rsp - BitVec.ofNat 64 bytes + 8) (d := 8 * k) (n := 8)
          (k := n * e.size) (by omega_arith) (by omega_arith)
        rwa [hrsp₃, show s.gpr .rsp - BitVec.ofNat 64 bytes + BitVec.ofNat 64 (8 + 8 * k) =
            s.gpr .rsp - BitVec.ofNat 64 bytes + 8 + BitVec.ofNat 64 (8 * k) by
          rw [BitVec.add_assoc]; congr 1; exact (BitVec.ofNat_add_ofNat ..).symm])
    have he' := Exec.seq he (Exec.block hblk)
    rw [hrsp₃] at he'
    have ha' : abiPreserved (narrow sig e n bytes s) { s₃.setReg32 .r11 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ?_, ha.2.2⟩
      · have hq' : q ≠ .r11 := by rintro rfl; simp [calleeSaved] at hq
        simp only [State.setReg32, State.setReg, hq', ↓reduceIte]
        exact ha.1 q hq
      · rw [narrow_rsp hk]
        show m'.readW _ 64 = _
        rw [hfr.readW (r := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega_arith))
          (by decide)]
        have h2 := ha.2.1
        rwa [narrow_rsp hk] at h2
    obtain ⟨hex, habi, hm, hrax⟩ := withStackScratchK_run hk hb hst hsafe hdep hsb hretW he' ha'
    exact ⟨t, s₃, m', he, hq, hfr, hex, habi, hm, by rw [hrax]; simp [State.setReg32, State.setReg]⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, m', -, hq, hfr, hex, ha, hm, hrax⟩ := hrun s hs
    obtain ⟨-, -, hdisj⟩ := hfacts s hs
    refine ⟨_, _, hex, ha, ?_⟩
    refine post_consts.mpr ((post_regs (by omega_arith)).mpr ?_)
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)).mp (post_consts.mp hq)
    rw [narrow_regArgs hk] at hq'
    rw [hm, hrax]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_arith))) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s (by omega_arith)) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    have hsp₁₂ : s₁.gpr .rsp = s₂.gpr .rsp := ((pub_regs (by omega_arith) hl).mp hp').1
    rw [hct _ _ _ _ _ _ (narrowK_pre hk hb hst h₁ hl) (narrowK_pre hk hb hst h₂ hl)
      (pub_consts.mpr ⟨narrow_pub hk hp' hl, fun c hc => hsy c hc⟩) f₁ f₂, hsp₁₂]

end

end VG.X86_64
