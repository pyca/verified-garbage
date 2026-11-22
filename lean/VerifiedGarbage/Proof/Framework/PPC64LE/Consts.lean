module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.TCB.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Contracts of code that reads tables of constants (PPC64LE)

As on AArch64 (`Proof/Framework/AArch64/StackScratchConsts.lean`): a
contract under `abi.withConsts K`, whose readable regions end with the
tables `K`, is the one under `abi` for the state without them
(`stripConsts`), with what the tables add (`ConstsOk`): `pre_consts`,
`post_consts` and `pub_consts`.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The regions of the tables `K` in `s`. -/
abbrev constRegs (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  Abi.constRegions (fun name => s.syms name) K

/-- `s` without the regions of the tables `K` at the end of its readable regions. -/
def stripConsts (K : List (String × List (BitVec 64))) (s : State) : State :=
  s.withRegions (s.rd.take (s.rd.length - K.length)) s.wr

/-- What `abi.withConsts K` adds to the calling convention's well-formedness. -/
def ConstsOk (K : List (String × List (BitVec 64))) (st : Nat) (s : State) : Prop :=
  s.rd.drop (s.rd.length - K.length) = constRegs K s ∧ Abi.constsHeld s.mem (fun name => s.syms name) K ∧
    (∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      ∀ r ∈ abi.reserved st s, t.Disjoint r) ∧
    ∀ t ∈ constRegs K s, t.base.toNat % 64 = 0

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
  · split at h
    · cases h; rfl
    · cases h

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

/-- A postcondition under `abi` does not depend on the readable regions. -/
theorem post_strip {K : List (String × List (BitVec 64))} {s s' : State} :
    (sig.contract abi pre post wa st leak).post (stripConsts K s) s' ↔
      (sig.contract abi pre post wa st leak).post s s' := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact Iff.rfl
  | some vals =>
    dsimp only
    rw [args_stripConsts h]
    exact Iff.rfl

/-- The public data under `abi` do not depend on the readable regions. -/
theorem pub_strip {K : List (String × List (BitVec 64))} {s₁ s₂ : State} :
    (sig.contract abi pre post wa st leak).pub (stripConsts K s₁) (stripConsts K s₂) ↔
      (sig.contract abi pre post wa st leak).pub s₁ s₂ := by
  dsimp only [Sig.contract]
  cases h : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact Iff.rfl
  | some vals =>
    dsimp only
    rw [args_stripConsts h, args_stripConsts h]
    exact Iff.rfl

/-- A contract with the tables `consts` at the end of the readable regions,
from the contract `K` without them: `K` of the state without their regions
(`stripConsts`), what they add (`ConstsOk`), and their addresses public. As
`abi.withConsts` has them, for a function that reads tables of constants,
such as a curve's constants that the elliptic-curve functions copy into
their working space. -/
def _root_.VG.Contract.withTables (K : Contract isa) (consts : List (String × List (BitVec 64))) :
    Contract isa where
  pre s := K.pre (stripConsts consts s) ∧ ConstsOk consts 0 s
  post s s' := K.post (stripConsts consts s) s'
  pub s₁ s₂ := K.pub (stripConsts consts s₁) (stripConsts consts s₂) ∧ ∀ c ∈ consts, s₁.syms c.1 = s₂.syms c.1

/-- A contract with tables implies the one under `abi.withConsts`, if the
contract without them implies the one under `abi`. -/
theorem withTables_implies {K : Contract isa} (h : K.Implies (sig.contract abi pre post wa 0 leak))
    (sat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa 0 leak).pre s) :
    (K.withTables (c₀ :: cs)).Implies (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa 0 leak) :=
  { pre := fun _ hs => ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (post_strip.mp (h.post (stripConsts (c₀ :: cs) s) s'
      (pre_consts.mp hs).1 hp))
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨h.pub (stripConsts (c₀ :: cs) s₁) (stripConsts (c₀ :: cs) s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_strip.mpr (pub_consts.mp hp).1), (pub_consts.mp hp).2⟩
    sat := sat }

end

section
variable {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {name : String}
  {ws : List (BitVec 64)}

/-- The readable regions are those without the tables, then the tables'. -/
theorem ConstsOk.rd_strip (h : ConstsOk K st s) {L : List Region} (hL : (stripConsts K s).rd = L) :
    s.rd = L ++ constRegs K s := by
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, h.1]
  exact congrArg (· ++ constRegs K s) hL

/-- A table lies within the address space. -/
theorem ConstsOk.fit (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    (s.syms name).toNat + 8 * ws.length ≤ 2 ^ 64 :=
  (h.2.2.1 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)).1

/-- A table lies apart from every writable region. Stated with the table's
words a variable, so that a caller's concrete table is never compared with
another form of `8 * ws.length`, which the kernel would evaluate (the table). -/
theorem ConstsOk.disjoint_wr (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {r : Region} (hr : r ∈ s.wr) :
    Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2.1 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)).2.1 r hr

/-- The table is readable. -/
theorem ConstsOk.mem_rd (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    (⟨s.syms name, 8 * ws.length⟩ : Region) ∈ s.rd := by
  have hm' : (⟨s.syms name, 8 * ws.length⟩ : Region) ∈ s.rd.drop (s.rd.length - K.length) := by
    rw [h.1]; exact List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc
  exact List.mem_of_mem_drop hm'

/-- `w` bytes at offset `x` in the table are readable. -/
theorem ConstsOk.inRegions (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {x w : Nat}
    (hx : x + w ≤ 8 * ws.length) (hw : 0 < w) (wr : List Region) :
    InRegions (s.rd ++ wr) (s.syms name + BitVec.ofNat 64 x) w :=
  ⟨_, List.mem_append_left _ (h.mem_rd hc), Offset.contains_base _ hx (by have := h.fit hc; omega_using [hx, hw, this])⟩

/-- Word `i` of the table. -/
theorem ConstsOk.readW (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {i : Nat} (hi : i < ws.length) :
    s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0 :=
  h.2.1 _ hc i hi

end

end VG.PPC64LE
