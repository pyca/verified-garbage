module

public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.Sig
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Contracts of code that reads tables of constants (RISC-V)

As on PPC64LE (`Proof/Framework/PPC64LE/Consts.lean`): a
contract under `abi.withConsts K`, whose readable regions end with the
tables `K`, is the one under `abi` for the state without them
(`stripConsts`), with what the tables add (`ConstsOk`): `pre_consts`,
`post_consts` and `pub_consts`.
-/

@[expose] public section

namespace VG.RISCV64

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
    · rintro ⟨⟨hw, hd, hh, ht, hal⟩, hrd, hwr, hpw, hres, hnw, hpr⟩
      exact ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht, hal⟩
    · rintro ⟨⟨hw, hrd, hwr, hpw, hres, hnw, hpr⟩, hd, hh, ht, hal⟩
      exact ⟨⟨hw, hd, hh, ht, hal⟩, hrd, hwr, hpw, hres, hnw, hpr⟩

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
variable {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {name : String}
  {ws : List (BitVec 64)}

/-- A table lies within the address space. -/
theorem ConstsOk.fit (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    (s.syms name).toNat + 8 * ws.length ≤ 2 ^ 64 :=
  (h.2.2.1 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)).1

/-- A table's address is a multiple of 64. -/
theorem ConstsOk.aligned (h : ConstsOk K st s) (hc : (name, ws) ∈ K) : (s.syms name).toNat % 64 = 0 :=
  h.2.2.2 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)

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
  ⟨_, List.mem_append_left _ (h.mem_rd hc), Offset.contains_base _ hx (by have := h.fit hc; omega)⟩

/-- Word `i` of the table. -/
theorem ConstsOk.readW (h : ConstsOk K st s) (hc : (name, ws) ∈ K) {i : Nat} (hi : i < ws.length) :
    s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0 :=
  h.2.1 _ hc i hi

end

section
variable {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State}

/-- What the contract says of a function's one table: its words. -/
theorem ConstsOk.held1 (h : ConstsOk [(name, ws)] st s) :
    ∀ i < ws.length, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0 :=
  h.2.1 _ List.mem_cons_self

/-- The code may read it. -/
theorem ConstsOk.rd1 (h : ConstsOk [(name, ws)] st s) : (⟨s.syms name, 8 * ws.length⟩ : Region) ∈ s.rd :=
  h.mem_rd List.mem_cons_self

/-- No writable region overlaps it. -/
theorem ConstsOk.wr1 (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

end

/-- A readable region of the state without the tables is one of the state. -/
theorem stripConsts_rd_mem {K : List (String × List (BitVec 64))} {s : State} {r : Region}
    (h : r ∈ (stripConsts K s).rd) : r ∈ s.rd := List.mem_of_mem_take h

end VG.RISCV64
