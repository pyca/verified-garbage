module
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch

import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A scratch buffer on the stack, for code that reads tables of constants (ARMv7)

As on IA-32 (`Proof/Framework/X86/StackScratchConsts.lean`), whose `sym` also
widens a 32-bit address. `Verified.stackScratchWipedC`:
`Verified.stackScratchWiped` for contracts under `abi.withConsts K`, whose
readable regions end with the tables `K`. The frame is that of
`Verified.stackScratchWiped`; the code runs from `narrowC`, which is `narrow`
of the state without the tables' regions (`stripConsts`), with the tables'
regions after its own. Without its tables, a state satisfying the contract
under `abi.withConsts K` satisfies it under `abi` (`pre_consts`), so the
lemmas of `StackScratch.lean` apply to it; the tables lie outside the frame,
which is within the stack the contract reserves, so `narrowC` holds them as
the entry state does.

What the contract says of a table, for code that addresses it from
`s.syms name` with 32-bit arithmetic (`adrSym`, then `ldr`/`ldrb`), is in
`ConstsOk.inRegions` (the code may read it), `ConstsOk.fit` (it does not
wrap around the 32-bit address space) and `ConstsOk.readW` (its words).
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

theorem State.withRegions_syms (s : State) (rd wr : List Region) :
    (s.withRegions rd wr).syms = s.syms := rfl

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
    (∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, t.Disjoint r) ∧
    ∀ t ∈ constRegs K s, t.base.toNat % 64 = 0

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

/-! ## Reading a table

What `ConstsOk` says of the table `(name, ws)`, in the form the code's 32-bit
addresses take: `State.addr (s.syms name + x)`. -/

section
variable {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {name : String}
  {ws : List (BitVec 64)}

/-- The tables' addresses agree, as the public data under `abi.withConsts`
says (`pub_consts`), exactly when their 32-bit addresses do, as
`Taint.AgreeS` states it. -/
theorem symAddr_eq_iff {s₁ s₂ : State} : symAddr s₁ name = symAddr s₂ name ↔ s₁.syms name = s₂.syms name :=
  ⟨fun h => by simpa using congrArg (BitVec.setWidth 32) h, fun h => by rw [symAddr, symAddr, h]⟩

/-- The table does not wrap around the 32-bit address space. -/
theorem ConstsOk.fit (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    (s.syms name).toNat + 8 * ws.length ≤ 2 ^ 32 := by
  have h1 := (h.2.2.1 ⟨symAddr s name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc)).1
  have e : (symAddr s name).toNat = (s.syms name).toNat := by
    simp only [symAddr, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (s.syms name).isLt (by decide))
  dsimp only at h1
  rwa [abi_ptrBits, e] at h1

/-- The table's address is a multiple of 64. -/
theorem ConstsOk.aligned (h : ConstsOk K st s) (hc : (name, ws) ∈ K) : (symAddr s name).toNat % 64 = 0 :=
  h.2.2.2 ⟨symAddr s name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc)

/-- An address in the table, from the static's address in 32 bits. -/
theorem symAddr_add {x : BitVec 32} (h : (s.syms name).toNat + x.toNat < 2 ^ 32) :
    State.addr (s.syms name + x) = symAddr s name + BitVec.ofNat 64 x.toNat := by
  have e := addr_add (a := s.syms name) h
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e

/-- The code may read the table: `w` bytes at offset `x` within it. -/
theorem ConstsOk.inRegions (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {x : BitVec 32} {w : Nat}
    (hx : x.toNat + w ≤ 8 * ws.length) (hw : 0 < w) (wr : List Region) :
    InRegions (s.rd ++ wr) (State.addr (s.syms name + x)) w := by
  have hf := h.fit hc
  have hm : (⟨symAddr s name, 8 * ws.length⟩ : Region) ∈ s.rd := by
    have hm' : (⟨symAddr s name, 8 * ws.length⟩ : Region) ∈ s.rd.drop (s.rd.length - K.length) := by
      rw [h.1]; exact List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc
    exact List.mem_of_mem_drop hm'
  refine ⟨_, List.mem_append_left _ hm, ?_⟩
  rw [symAddr_add (by omega_using [hx, hw, hf])]
  exact Offset.contains_base _ hx (by omega_using [])

/-- Word `i` of the table. -/
theorem ConstsOk.readW (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {i : Nat} (hi : i < ws.length) :
    s.mem.readW (State.addr (s.syms name + BitVec.ofNat 32 (8 * i))) 64 = ws.getD i 0 := by
  have hf := h.fit hc
  rw [addr_add (by omega_using [hi, hf])]
  exact h.2.1 _ hc i hi

end

@[simp] theorem stripConsts_gpr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).gpr = s.gpr := rfl
@[simp] theorem stripConsts_sp (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).sp = s.sp := rfl
@[simp] theorem stripConsts_mem (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).mem = s.mem := rfl
@[simp] theorem stripConsts_wr (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).wr = s.wr := rfl
@[simp] theorem stripConsts_syms (K : List (String × List (BitVec 64))) (s : State) :
    (stripConsts K s).syms = s.syms := rfl
theorem armArgs_stripConsts (sig : Sig) (K : List (String × List (BitVec 64))) (s : State) :
    armArgs sig (stripConsts K s) = armArgs sig s := rfl

theorem stripConsts_rd_mem {K : List (String × List (BitVec 64))} {s : State} {r : Region}
    (h : r ∈ (stripConsts K s).rd) : r ∈ s.rd := List.mem_of_mem_take h

theorem setArgsState_syms (bytes k : Nat) (u : State) : (setArgsState bytes k u).syms = u.syms := by
  unfold setArgsState
  cases h : execBlock isa (setArgs bytes k) u with
  | none => rfl
  | some p => exact execBlock_syms h

theorem narrow_syms (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) :
    (narrow sig e n bytes m s).syms = s.syms := by
  unfold narrow
  rw [State.withRegions_syms]
  exact setArgsState_syms _ _ _

theorem armArgs_withRegions (sig : Sig) (s : State) (rd wr : List Region) :
    armArgs sig (s.withRegions rd wr) = armArgs sig s := rfl

/-- The state the code runs from: `narrow` of the state without the tables'
regions, with them after its own readable regions. -/
def narrowC (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : State :=
  (narrow sig e n bytes m (stripConsts K s)).withRegions
    ((narrow sig e n bytes m (stripConsts K s)).rd ++ constRegs K s) (narrow sig e n bytes m (stripConsts K s)).wr

theorem narrowC_syms (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes m K s).syms = s.syms := by
  unfold narrowC
  rw [State.withRegions_syms]
  exact narrow_syms sig e n bytes m (stripConsts K s)

/-- `narrowC`'s memory, registers, stack pointer and arguments are `narrow`'s. -/
theorem narrowC_mem (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes m K s).mem = (narrow sig e n bytes m (stripConsts K s)).mem := by
  unfold narrowC; exact State.withRegions_mem _ _ _

theorem narrowC_gpr (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes m K s).gpr = (narrow sig e n bytes m (stripConsts K s)).gpr := by
  unfold narrowC; exact State.withRegions_gpr _ _ _

theorem narrowC_sp (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes m K s).sp = (narrow sig e n bytes m (stripConsts K s)).sp := by
  unfold narrowC; exact State.withRegions_sp _ _ _

theorem narrowC_wr (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : (narrowC sig e n bytes m K s).wr = (narrow sig e n bytes m (stripConsts K s)).wr := by
  unfold narrowC; exact State.withRegions_wr _ _ _

theorem armArgs_narrowC (sig' sig : Sig) (e : Elem) (n bytes m : Nat)
    (K : List (String × List (BitVec 64))) (s : State) :
    armArgs sig' (narrowC sig e n bytes m K s) = armArgs sig' (narrow sig e n bytes m (stripConsts K s)) := by
  unfold narrowC; exact armArgs_withRegions _ _ _ _

theorem symAddr_congr {s s' : State} (h : s'.syms = s.syms) : symAddr s' = symAddr s := by
  show (fun name => (s'.syms name).setWidth 64) = fun name => (s.syms name).setWidth 64
  rw [h]

theorem constRegs_congr {K : List (String × List (BitVec 64))} {s s' : State} (h : s'.syms = s.syms) :
    constRegs K s' = constRegs K s := by
  simp only [constRegs, symAddr_congr h]

theorem stripConsts_narrowC (sig : Sig) (e : Elem) (n bytes m : Nat) (K : List (String × List (BitVec 64)))
    (s : State) : stripConsts K (narrowC sig e n bytes m K s) = narrow sig e n bytes m (stripConsts K s) := by
  have hl : (constRegs K s).length = K.length := List.length_map _
  simp only [stripConsts, narrowC, State.withRegions_rd, State.withRegions_wr, State.withRegions_withRegions,
    List.length_append, hl, Nat.add_sub_cancel, List.take_left', State.withRegions_self]

theorem narrowC_rd_drop (sig : Sig) (e : Elem) (n bytes m : Nat)
    (K : List (String × List (BitVec 64))) (s : State) :
    (narrowC sig e n bytes m K s).rd.drop ((narrowC sig e n bytes m K s).rd.length - K.length) =
      constRegs K s := by
  have hl : (constRegs K s).length = K.length := List.length_map _
  simp only [narrowC, State.withRegions_rd, List.length_append, hl, Nat.add_sub_cancel, List.drop_left']

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m words : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The stack the contract reserves below `sp`, which holds the frame. -/
theorem reserved_below (hS : 0 < stack + bytes) (s : State) :
    (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      abi.reserved (stack + bytes) s := by
  show _ ∈ stackBelow (State.addr s.sp) (stack + bytes)
  rw [show stack + bytes = (stack + bytes - 1) + 1 by omega_using [hS]]; simp [stackBelow]

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrowC`. -/
theorem narrowC_pre (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pre
      (narrowC sig e n bytes m (c₀ :: cs) s) := by
  obtain ⟨hs', hd, hh, ht, hal⟩ := pre_consts.mp hs
  have hn := narrow_pre (nm := nm) hcl hN hloc hb hpre hs'
  obtain ⟨hsp₂, -, -, hf⟩ := narrow_facts (nm := nm) (e := e) (n := n) hcl hN hloc hb hs'
  have hsy := narrowC_syms sig e n bytes m (c₀ :: cs) s
  obtain ⟨hb1, -⟩ := hb
  rw [pre_armL] at hs'
  obtain ⟨⟨hst, -⟩, -, hwr, -, -, -, -⟩ := hs'
  simp only [stripConsts_sp] at hst hsp₂
  simp only [stripConsts_mem, stripConsts_sp] at hf
  have hsb : stack + bytes ≤ s.sp.toNat := by omega_using [hst]
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega_using [hsb])
  -- The frame is within the stack the contract reserves, which the tables are apart from.
  have htR : ∀ t ∈ constRegs (c₀ :: cs) s, ∀ {a k : Nat}, a ≤ stack + bytes →
      stack + bytes - a + k ≤ stack + bytes →
      t.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 a, k⟩ := fun t ht' _ _ ha hk =>
    ((ht t ht').2.2 _ (reserved_below (by omega_using [hb1]) s)).sub_right (Offset.sub_below _ ha hk)
  refine pre_consts.mpr ⟨?_, ?_, ?_, fun t ht' => ?_, by rw [constRegs_congr hsy]; exact hal⟩
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
      rw [hsp]
      exact htR _ (List.mem_map_of_mem hc) (by omega_using []) (by omega_using [hb1])
  rw [constRegs_congr hsy] at ht'
  refine ⟨(ht t ht').1, ?_, ?_⟩
  · -- The writable regions: the buffers and the buffer in the frame.
    intro r hr
    rw [narrowC_wr] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, armArgs_stripConsts, stripConsts_sp, stripConsts_mem, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · refine (ht t ht').2.1 _ ?_
      show a.1 ∈ (stripConsts (c₀ :: cs) s).wr
      rw [hwr]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), hf'⟩,
        rfl⟩
    · show t.Disjoint ⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩
      rw [sa_sub (by omega_using [hb1]) (by omega_using [hsb])]
      exact htR t ht' (by omega_using []) (by omega_using [hb1])
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  · -- The stack the contract with the buffer reserves.
    intro r hr
    have hr' : r ∈ stackBelow (State.addr (s.sp - BitVec.ofNat 32 bytes)) stack := by
      rw [← hsp₂, ← narrowC_sp]; exact hr
    rw [hsp, stackBelow_sub] at hr'
    by_cases h0 : stack = 0
    · simp [h0] at hr'
    · simp only [h0, ite_false, List.mem_singleton] at hr'; subst hr'
      exact htR t ht' (by omega_using []) (by omega_using [])

/-- A run of the code from `narrowC s` is a run of `withStackScratch` from
`s` (`withStackScratch_run`, under `abi.withConsts`). -/
theorem withStackScratchC_run {c : Prog isa} (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s)
    {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowC sig e n bytes m (c₀ :: cs) s) t s₃)
    (ha : abiPreserved (narrowC sig e n bytes m (c₀ :: cs) s) s₃) :
    Exec isa (withStackScratch bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hs', hdrop, -, -, -⟩ := pre_consts.mp hs
  obtain ⟨hrun, hrd', hwr', -, -, -, -, -⟩ := argsState_run hs' hN hb
  obtain ⟨hsp₂, hg, -, -⟩ := narrow_facts (nm := "") (e := e) (n := n) hcl hN hloc hb hs'
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hb
  rw [pre_armL] at hs'
  obtain ⟨⟨hst, -⟩, hrd, hwr, -, -, -, -⟩ := hs'
  simp only [stripConsts_sp] at hst hsp₂
  simp only [stripConsts_gpr] at hg
  have hsb : stack + bytes ≤ s.sp.toNat := by omega_using [hst]
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega_using [hsb])
  have hscr : sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8) =
      State.addr s.sp - BitVec.ofNat 64 (bytes - (4 * m + 8)) := sa_sub (by omega_using [hb1]) (by omega_using [hsb])
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega_using [hb1], hb2, hb3, hb4, by omega_using [hsb]⟩
  -- `setArgs` from the frame's push in `s`: its run without the tables' regions, widened.
  have hset := Exec.widen (Exec.block hrun) (rd := s.rd)
    (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (Covers.append (Covers.of_mem fun r hr => stripConsts_rd_mem hr) (Covers.refl _)) (Covers.refl _)
  -- The regions of `narrowC`: the buffers, the frame's buffer and arguments, and the tables.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨State.addr s.sp - BitVec.ofNat 64 a, k⟩]
        (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hsp]; exact Offset.contains_below _ ha hk (by omega_using [hsb])⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    refine stripConsts_rd_mem (K := c₀ :: cs) ?_
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hlistR : ∀ a ∈ (Sig.lists abi.ptrBits s.mem sig.params (armArgs sig s)).map (fun r => (r, false)),
      a.1 ∈ s.rd := fun a ha => by
    refine stripConsts_rd_mem (K := c₀ :: cs) ?_
    rw [hrd]
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_right _ ha),
      rfl⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    show a.1 ∈ (stripConsts (c₀ :: cs) s).wr
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes m (stripConsts (c₀ :: cs) s)).filter (·.2)).map (·.1))
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, armArgs_stripConsts, stripConsts_sp, stripConsts_mem, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((ha | rfl) | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega_using []) (by omega_using [hb1])
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers ((((oldRegions sig e n bytes m (stripConsts (c₀ :: cs) s)).filter (!·.2)).map (·.1)) ++
      constRegs (c₀ :: cs) s) (s.rd ++ ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.left (Covers.of_mem fun r hr => ?_))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
      simp only [oldRegions, armArgs_stripConsts, stripConsts_sp, stripConsts_mem, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ((ha | rfl) | ha) | rfl
      · exact Covers.left (Covers.of_mem fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
      · simp at hf'
      · exact Covers.left (Covers.of_mem fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
      · exact Covers.right (by simpa only [hsp] using hF (a := bytes) (k := 4 * m + 4) (by omega_using []) (by omega_using [hb1]))
    · have hr' : r ∈ s.rd.drop (s.rd.length - (c₀ :: cs).length) := by rw [hdrop]; exact hr
      exact List.mem_of_mem_drop hr'
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowC sig e n bytes m (c₀ :: cs) s).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) =
      (setArgsState bytes m (allocState bytes (stripConsts (c₀ :: cs) s))).withRegions s.rd
        (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) by
    rw [narrowC, narrow, State.withRegions_withRegions, State.withRegions_withRegions]] at hw
  rw [show (allocState bytes (stripConsts (c₀ :: cs) s)).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) = allocState bytes s from rfl]
    at hset
  -- The pop.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans ((narrowC_sp ..).trans hsp₂)
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, allocState_sp, allocState_wr,
      hsp₃, List.head?_cons, show 0 < bytes by omega_using [hb1], hb2, hb3, hb4, and_self, ite_true,
      List.tail_cons, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hset hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_sp] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl⟩, rfl, rfl⟩
  have hq12 : q ≠ .r12 := fun h => by subst h; simp [preserved] at hq
  show s₃.gpr q = s.gpr q
  rw [ha.1 q hq, narrowC_gpr, hg q hq12]

/-- The public data of a contract does not depend on the readable and
writable regions. -/
theorem pubL_withRegions {s₁ s₂ : State} (r₁ w₁ r₂ w₂ : List Region) :
    (sig.contract abi pre post wa stack leak).pub (s₁.withRegions r₁ w₁) (s₂.withRegions r₂ w₂) ↔
      (sig.contract abi pre post wa stack leak).pub s₁ s₂ := by
  rw [pubL_armL, pubL_armL]; exact Iff.rfl

/-- Code verified for a function whose last argument, on the stack after `m`
words of other stack arguments, is a scratch buffer, and which reads the
tables `c₀ :: cs`, is verified for the function without it
(`Verified.stackScratchWiped`, under `abi.withConsts (c₀ :: cs)`, with the
leak the contract may declare, as on IA-32). -/
theorem Verified.stackScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hw : 4 * words ≤ n * e.size)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hpostOut : ∀ vs mm m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs mm m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs mm m₂ r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratchWiped bytes m words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hpreL : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂ :=
    fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb
  have hlen := armArgs_length sig
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hb
  have hsb : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      stack + bytes ≤ s.sp.toNat := fun s hs => by
    have hs' := (pre_consts.mp hs).1
    rw [pre_armL] at hs'
    obtain ⟨⟨hst, -⟩, -⟩ := hs'
    simp only [stripConsts_sp] at hst
    omega_using [hst]
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩ := by
    intro s hs b hb'
    have h0 := hsb s hs
    have hs' := (pre_consts.mp hs).1
    rw [pre_arm hl] at hs'
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs'
    simp only [stripConsts_sp] at hres
    rw [sa_sub (by omega_using [hb1]) (by omega_using [h0])]
    exact (Region.Disjoint.symm (hres _ (reserved_below (by omega_using [hb1]) s) b (List.mem_append_left _ hb'))).sub_right
      (Offset.sub_below _ (by omega_using []) (by omega_using [hb1]))
  -- Every run is `setArgs`, then the code's run from `narrowC`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∃ t s₃ s₄,
      Exec isa c (narrowC sig e n bytes m (c₀ :: cs) s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post
        (narrowC sig e n bytes m (c₀ :: cs) s) s₃ ∧
      Frame [⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 32 bytes ∧
      Exec isa (withStackScratchWiped bytes m words c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++
          (t ++ wipeTrace (s₃.sp + BitVec.ofNat 32 (4 * m + 8)) words))
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r0 = s₃.gpr .r0 ∧ (popState bytes s s₄).gpr .r1 = s₃.gpr .r1 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowC_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL hs)
    obtain ⟨hsp₂, -, -, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hcl hN hloc
      ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ (pre_consts.mp hs).1
    simp only [stripConsts_sp] at hsp₂
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans ((narrowC_sp ..).trans hsp₂)
    have hwr₃ : s₃.wr = (narrowC sig e n bytes m (c₀ :: cs) s).wr := (Exec.rdwr he).2.1
    have h0 := hsb s hs
    have hbuf : (⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩ : Region) ∈ s₃.wr := by
      rw [hwr₃, narrowC_wr]
      simp [narrow, oldRegions, List.filter_append]
    have hF : (s.sp - BitVec.ofNat 32 bytes).toNat = s.sp.toNat - bytes := sub_toNat' (by omega_using [h0])
    obtain ⟨m', hblk, hfr⟩ := wipeAt_run _ s₃ (4 * m + 8) words hbuf (by omega_using [hb5]) (by omega_using [hw, hb1, hb6])
      (fun k hk' => by
        have hlt := s.sp.isLt
        rw [hsp₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat, sa,
          addr_add (by rw [hF]; omega_using [hb1, h0]), addr_add (by rw [hF]; omega_using [hw, hb1, h0, hk'])]
        exact Offset.contains _ (by omega_using []) (by omega_using [hw, hk']) (by omega_using [hb1, h0]))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowC sig e n bytes m (c₀ :: cs) s)
        { (s₃.setReg .r12 (s₃.sp + BitVec.ofNat 32 (4 * m + 8))).setReg .r2 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h2 : q ≠ .r2 := by rintro rfl; simp [preserved] at hq
      simp only [State.setReg, h12, h2, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ :=
      withStackScratchC_run hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hs he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_, ?_⟩
    · rw [hg]; simp [State.setReg]
    · rw [hg]; simp [State.setReg]
  -- The public data in `narrowC`.
  have hpub : ∀ s₁ s₂,
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₁ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s₂ →
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pub s₁ s₂ →
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub
        (narrowC sig e n bytes m (c₀ :: cs) s₁) (narrowC sig e n bytes m (c₀ :: cs) s₂) := by
    intro s₁ s₂ h₁ h₂ hp
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    refine pub_consts.mpr ⟨(pubL_withRegions _ _ _ _).mpr
      (narrow_pub hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ (pre_consts.mp h₁).1 (pre_consts.mp h₂).1
        ((pubL_withRegions _ _ _ _).mpr hp') hleak.toL), ?_⟩
    rw [symAddr_congr (narrowC_syms ..), symAddr_congr (narrowC_syms ..)]
    exact hsy
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0, hr1⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_consts, post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp (post_consts.mp hq)
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hcl hN hloc
      ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ (pre_consts.mp hs).1
    simp only [armArgs_stripConsts, stripConsts_sp] at hargs
    rw [armArgs_narrowC, hargs, narrowC_mem] at hq'
    rw [hm, hr0, hr1]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    have hag := narrow_agree hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ (pre_consts.mp hs).1
    simp only [armArgs_stripConsts, stripConsts_mem] at hag
    have h₄ := hpost _ _ _ _ _ (hlen s) hag h₃
    refine hpostOut _ _ _ _ _ (hlen s) (fun b hb' a ha' => ?_) h₄
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pubL_arm hl).mp (pub_consts.mp hp).1).1.1,
      hct _ _ _ _ _ _ (narrowC_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL h₁)
        (narrowC_pre hcl hN hloc ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ hpreL h₂) (hpub s₁ s₂ h₁ h₂ hp) f₁ f₂]

end

end VG.Arm
