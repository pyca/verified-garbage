module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import Batteries.Data.List.Basic
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Taint tracking for PPC64LE, with public slots in the writable regions

Untrusted: everything here is checked by Lean.

`VG.PPC64LE.taint` keeps memory secret, so a value saved to memory and loaded
back is secret, even when it is the same in both runs. Code that calls a
function which saves the callee-saved registers in its working space and
restores them from there (the bitsliced block functions, which use every
register) then finds them secret after the call, even when they held public
pointers and counts, as a mode's loop does.

As on x86-64 (`VG.X86_64.Taint`), this domain adds *public slots*: byte
ranges of the writable regions `s.wr` (identified by index) that hold the same
bytes in both runs. A load whose bytes are all within a public slot gives a
public value. To keep them sound in the presence of stores of secrets, the
analysis knows lower bounds on the lengths of the writable regions (`lens`,
whose regions are then pairwise disjoint and the same in both runs; a bound of
`0` means the length is unknown and the region has no slots) and which
registers point at a known offset into which region (`bases`). A store through
such a register, at a known offset, can only change bytes of its own region at
that offset; a store of a secret anywhere else forgets every slot (a store of a
public value through public registers writes the same bytes at the same
address in both runs, and keeps them).

`addi` and `subi` of a register with a known base move the base; `mr` (`or d,
n, n`) copies it. Frames (`push`, `pop`, `alloc`, `free`) are not analysed.
-/

@[expose] public section

namespace VG.PPC64LE.SlotTaint

open VG.PPC64LE

structure T where
  regs : RegSet Reg
  /-- Lower bounds on the lengths of the writable regions `s.wr`, in order (one per region;
  `0` if unknown); `[]` if nothing is known about the regions. -/
  lens : List Nat := []
  /-- `(r, i, k)`: register `r` holds the address of byte `k` of writable region `i`. -/
  bases : List (Reg × Nat × Nat) := []
  /-- `(i, o, n)`: the `n` bytes at offset `o` of writable region `i` are public. -/
  slots : List (Nat × Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

/-- Writable region `i`. -/
def region (s : State) (i : Nat) : Region := s.wr.getD i ⟨0, 0⟩

/-- The address of byte `k` of writable region `i`. -/
def byteAddr (s : State) (i k : Nat) : Addr := (region s i).base + BitVec.ofNat 64 k

/-- What `τ` says about each state on its own. -/
def Wf (τ : T) (s : State) : Prop :=
  (τ.lens ≠ [] →
    List.Forall₂ (fun r l => l ≤ r.len) s.wr τ.lens ∧ s.wr.Pairwise Region.Disjoint ∧ ∀ r ∈ s.wr, r.len ≤ 2 ^ 64) ∧
  (∀ p ∈ τ.bases, s.gpr p.1 = (region s p.2.1).base + BitVec.ofNat 64 p.2.2)

/-- Every slot lies within its region. -/
def SlotsOk (τ : T) : Prop := ∀ sl ∈ τ.slots, sl.2.1 + sl.2.2 ≤ τ.lens.getD sl.1 0

def SlotsAgree (τ : T) (s₁ s₂ : State) : Prop :=
  ∀ sl ∈ τ.slots, ∀ k, sl.2.1 ≤ k → k < sl.2.1 + sl.2.2 →
    s₁.mem (byteAddr s₁ sl.1 k) = s₂.mem (byteAddr s₂ sl.1 k)

structure Agree (τ : T) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  regs : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r
  wr : τ.lens ≠ [] → s₁.wr = s₂.wr
  wf₁ : Wf τ s₁
  wf₂ : Wf τ s₂
  ok : SlotsOk τ
  slots : SlotsAgree τ s₁ s₂

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

/-- The known region bases after writing `d`. -/
def kill (τ : T) (d : Reg) : List (Reg × Nat × Nat) := τ.bases.filter (·.1 != d)

/-- `d` written, with a public value iff `p` and no known base. -/
def wr (τ : T) (d : Reg) (p : Bool) : T := { τ with regs := set τ d p, bases := kill τ d }

/-- The known region bases after `addi d, n, imm`. -/
def addiBases (τ : T) (d n : Reg) (imm : Nat) : List (Reg × Nat × Nat) :=
  kill τ d ++ (τ.bases.filter (·.1 == n)).map fun p => (d, p.2.1, p.2.2 + imm)

/-- The known region bases after `subi d, n, imm` (no further back than the region's base). -/
def subiBases (τ : T) (d n : Reg) (imm : Nat) : List (Reg × Nat × Nat) :=
  kill τ d ++ (τ.bases.filter fun p => p.1 == n && decide (imm ≤ p.2.2)).map fun p => (d, p.2.1, p.2.2 - imm)

/-- The known region bases after `mr d, n`. -/
def movBases (τ : T) (d n : Reg) : List (Reg × Nat × Nat) :=
  kill τ d ++ (τ.bases.filter (·.1 == n)).map fun p => (d, p.2)

/-- The region and offset of `n + off`, if known. -/
def addrOf (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (τ.bases.find? (·.1 == n)).map fun p => (p.2.1, p.2.2 + off)

/-- The `w` bytes at `n + off` are within a public slot. -/
def slotPub (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOf τ n off with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && decide (sl.2.1 ≤ d) && decide (d + w ≤ sl.2.1 + sl.2.2)
  | none => false

/-- The public slots after storing `w` bytes at `n + off`, a public value iff `p`. -/
def storeSlots (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ n off with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      let kept := τ.slots.filter fun sl => p || sl.1 != i || decide (d + w ≤ sl.2.1) || decide (sl.2.1 + sl.2.2 ≤ d)
      if p then (i, d, w) :: kept else kept
    else if p then τ.slots else []
  | none => if p then τ.slots else []

def storeStep (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  if pub τ n then some { τ with slots := storeSlots τ n off w p } else none

def step (τ : T) : Instr → Option T
  | .add d n m | .sub d n m | .mul d n m | .mulhu d n m | .addc d n m | .subc d n m =>
    some (wr τ d (pub τ n && pub τ m))
  -- They read the carry bit, which is secret (see `Taint`).
  | .adde d .. | .addze d _ | .sube d .. => some (wr τ d false)
  | .logic op d n m =>
    if op = .or ∧ n = m then some { τ with regs := set τ d (pub τ n), bases := movBases τ d n }
    else some (wr τ d (pub τ n && pub τ m))
  | .addi d n imm => some { τ with regs := set τ d (pub τ n), bases := addiBases τ d n imm }
  | .subi d n imm => some { τ with regs := set τ d (pub τ n), bases := subiBases τ d n imm }
  | .ori d n _ | .oris d n _ | .rotr _ d n _ | .lsr _ d n _ | .lsl d n _ => some (wr τ d (pub τ n))
  | .li d _ | .lis d _ | .addSp d _ => some (wr τ d true)
  | .load sz t n off => if pub τ n then some (wr τ t (slotPub τ n off sz.bytes)) else none
  | .lbz t n off => if pub τ n then some (wr τ t (slotPub τ n off 1)) else none
  | .store sz t n off => storeStep τ n off sz.bytes (pub τ t)
  | .stb t n off => storeStep τ n off 1 (pub τ t)
  | .loadRev _ t a b => if pub τ a && pub τ b then some (wr τ t false) else none
  | .storeRev _ t a b =>
    if pub τ a && pub τ b then some { τ with slots := if pub τ t then τ.slots else [] } else none
  | .mflr d => some (wr τ d false)
  | .mtlr _ => some τ
  | .push _ | .pop _ | .alloc _ | .free _ | .adrSym .. => none

def condPub (τ : T) : Cond → Bool
  | .zero _ r | .nonzero _ r => pub τ r

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && τ.lens == σ.lens && τ.bases.all (σ.bases.contains ·) &&
    τ.slots.all (σ.slots.contains ·)

/-! ## Soundness -/

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ.regs := Iff.rfl

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r :=
  h.regs r (pub_iff.mp hr)

theorem regs_set {τ : T} {s₁ s₂ : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} {p : Bool} {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    ∀ r ∈ set τ d p, (s₁.write d v₁).gpr r = (s₂.write d v₂).gpr r := by
  intro r hr
  simp only [State.write]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hr
    by_cases hrd : r = d
    · simp only [hrd, ↓reduceIte, hv hp]
    · simp only [hrd, ↓reduceIte, h r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hr
    simp only [hr.1, ↓reduceIte, h r hr.2]

/-! ### Region bases, slots and memory -/

theorem write_ne {s : State} {d r : Reg} {v : BitVec 64} (h : r ≠ d) : (s.write d v).gpr r = s.gpr r := by
  simp only [State.write, h, ↓reduceIte]

theorem write_self {s : State} {d : Reg} {v : BitVec 64} : (s.write d v).gpr d = v := by
  simp only [State.write, ↓reduceIte]

/-- The bases a state's registers have, kept by a state with the same regions. -/
def BasesOk (bs : List (Reg × Nat × Nat)) (s : State) : Prop :=
  ∀ p ∈ bs, s.gpr p.1 = (region s p.2.1).base + BitVec.ofNat 64 p.2.2

theorem kill_bases {τ : T} {s s' : State} (hw : Wf τ s) (hwr : s'.wr = s.wr) {d : Reg}
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) : BasesOk (kill τ d) s' := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [hg _ hp.2, hw.2 p hp.1]
  simp only [region, hwr]

theorem kill_write {τ : T} {s : State} (hw : Wf τ s) (d : Reg) (v : BitVec 64) :
    BasesOk (kill τ d) (s.write d v) :=
  kill_bases (s' := s.write d v) hw rfl fun _ h => write_ne h

theorem movBases_ok {τ : T} {s : State} (hw : Wf τ s) (d n : Reg) :
    BasesOk (movBases τ d n) (s.write d (s.gpr n)) := by
  intro p hp
  simp only [movBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
  rcases hp with hp | ⟨q, ⟨hq, he⟩, rfl⟩
  · exact kill_write hw d _ p hp
  · simp only [write_self]
    rw [← he]
    exact hw.2 q hq

theorem byteAddr_add (s : State) (i d k : Nat) :
    byteAddr s i d + BitVec.ofNat 64 k = byteAddr s i (d + k) := by
  simp only [byteAddr, BitVec.ofNat_add]
  rw [BitVec.add_assoc]

theorem addiBases_ok {τ : T} {s : State} (hw : Wf τ s) (d n : Reg) (imm : Nat) :
    BasesOk (addiBases τ d n imm) (s.write d (s.gpr n + BitVec.ofNat 64 imm)) := by
  intro p hp
  simp only [addiBases, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
  rcases hp with hp | ⟨q, ⟨hq, he⟩, rfl⟩
  · exact kill_write hw d _ p hp
  · simp only [write_self]
    rw [← he, hw.2 q hq]
    exact byteAddr_add s _ _ _

theorem subiBases_ok {τ : T} {s : State} (hw : Wf τ s) (d n : Reg) (imm : Nat) :
    BasesOk (subiBases τ d n imm) (s.write d (s.gpr n - BitVec.ofNat 64 imm)) := by
  intro p hp
  simp only [subiBases, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hp
  rcases hp with hp | ⟨q, ⟨hq, he, hk⟩, rfl⟩
  · exact kill_write hw d _ p hp
  · simp only [write_self]
    rw [← he, hw.2 q hq, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat hk]
    rfl

theorem addrOf_some {τ : T} {n : Reg} {off i d : Nat} (h : addrOf τ n off = some (i, d)) :
    ∃ k, (n, i, k) ∈ τ.bases ∧ d = k + off := by
  unfold addrOf at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hq
  have hb := List.find?_some hq
  simp only [beq_iff_eq] at hb
  exact ⟨q.2.2, by rw [← hb]; exact hm, rfl⟩

theorem addr_of_addrOf {τ : T} {s : State} (hw : Wf τ s) {n : Reg} {off i d : Nat}
    (h : addrOf τ n off = some (i, d)) : s.gpr n + BitVec.ofNat 64 off = byteAddr s i d := by
  obtain ⟨k, hb, rfl⟩ := addrOf_some h
  rw [hw.2 _ hb]
  exact byteAddr_add s i k off

theorem lens_ne {τ : T} {i n : Nat} (h : 0 < n) (hn : n ≤ τ.lens.getD i 0) : τ.lens ≠ [] := by
  rintro h'; simp only [h', List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
      not_false_eq_true, getElem?_neg, Option.getD_none, Nat.le_zero_eq] at hn; omega

/-- Slots live in regions of the same address in both runs. -/
theorem Agree.byteAddr_eq {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {sl : Nat × Nat × Nat}
    (h : sl ∈ τ.slots) {k : Nat} (hk : k < sl.2.1 + sl.2.2) :
    byteAddr s₁ sl.1 k = byteAddr s₂ sl.1 k := by
  have := ha.ok sl h
  simp only [byteAddr, region, ha.wr (lens_ne (n := sl.2.1 + sl.2.2) (by omega) this)]

/-- A load of `w` bytes from a public slot. -/
theorem Agree.load {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} {off w : Nat}
    (hp : slotPub τ n off w = true) :
    ∀ k < w, s₁.mem (s₁.gpr n + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      s₂.mem (s₂.gpr n + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  unfold slotPub at hp
  split at hp <;> [skip; cases hp]
  rename_i i d h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨sl, hsl, ⟨rfl, ho⟩, hd⟩ := hp
  intro k hk
  rw [addr_of_addrOf ha.wf₁ h, addr_of_addrOf ha.wf₂ h, byteAddr_add, byteAddr_add]
  exact ha.slots sl hsl _ (by omega) (by omega)

theorem forall₂_length {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) : rs.length = ls.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem forall₂_getD {rs : List Region} {ls : List Nat}
    (h : List.Forall₂ (fun r l => l ≤ r.len) rs ls) (i : Nat) : ls.getD i 0 ≤ (rs.getD i ⟨0, 0⟩).len := by
  induction h generalizing i with
  | nil => simp only [List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
             not_false_eq_true, getElem?_neg, Option.getD_none, Std.le_refl]
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem region_len {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) (i : Nat) :
    τ.lens.getD i 0 ≤ (region s i).len :=
  forall₂_getD (hw.1 hne).1 i

theorem region_mem {τ : T} {s : State} (hw : Wf τ s) (hne : τ.lens ≠ []) {i : Nat}
    (hi : 0 < τ.lens.getD i 0) : ∃ h : i < s.wr.length, region s i = s.wr[i] := by
  have hl := forall₂_length (hw.1 hne).1
  have : i < τ.lens.length := by
    by_contra h'
    rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)] at hi; simp only [Option.getD_none, Nat.lt_irrefl] at hi
  have hi' : i < s.wr.length := hl ▸ this
  exact ⟨hi', by simp only [region, List.getD_eq_getElem?_getD,
                   List.getElem?_eq_getElem hi', Option.getD_some]⟩

/-- A store of `n` bytes at offset `d` of region `i` does not change byte `k`
of region `j`, if that is another region or outside `[d, d + n)`. -/
theorem write_other {τ : T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k)
    (V : BitVec (8 * n)) :
    s.mem.write (byteAddr s i d) n V (byteAddr s j k) = s.mem (byteAddr s j k) := by
  have hne := lens_ne (n := d + n) (by omega) hd
  obtain ⟨-, hdisj, hbound⟩ := hw.1 hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega)
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact hbound _ (List.getElem_mem _)
  have hbj : (region s j).len ≤ 2 ^ 64 := by rw [hrj]; exact hbound _ (List.getElem_mem _)
  apply Mem.write_apply
  intro hlt
  by_cases hji : j = i
  · subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d :=
      Offset.add_sub_add_left _ _ _
    exact Offset.not_lt_sub_ofNat hsep (by omega) hn (by omega) (h ▸ hlt)
  · have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)

theorem write_same {m₁ m₂ : Mem} {A X : Addr} {n : Nat} (V : BitVec (8 * n)) (h : m₁ X = m₂ X) :
    m₁.write A n V X = m₂.write A n V X := by
  simp only [Mem.write]; split <;> [rfl; exact h]

theorem storeSlots_ok {τ : T} (hok : SlotsOk τ) (n : Reg) (off w : Nat) (p : Bool) :
    SlotsOk { τ with slots := storeSlots τ n off w p } := by
  intro sl hsl
  simp only [storeSlots] at hsl
  split at hsl
  · split at hsl
    · split at hsl
      · rcases List.mem_cons.mp hsl with rfl | hsl
        · assumption
        · exact hok sl (List.mem_filter.mp hsl).1
      · exact hok sl (List.mem_filter.mp hsl).1
    · split at hsl <;> [exact hok sl hsl; cases hsl]
  · split at hsl <;> [exact hok sl hsl; cases hsl]

@[simp] theorem byteAddr_withMem (s : State) (m : Mem) : byteAddr { s with mem := m } = byteAddr s :=
  rfl

/-- A store of `w` bytes at `n + off`, of the same value in both runs if `p`. -/
theorem Agree.store {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {n : Reg} {off : Nat}
    (hn : pub τ n = true) {w : Nat} (hw : 0 < w) {V₁ V₂ : BitVec (8 * w)} {p : Bool}
    (hv : p = true → V₁ = V₂) :
    Agree { τ with slots := storeSlots τ n off w p }
      { s₁ with mem := s₁.mem.write (s₁.gpr n + BitVec.ofNat 64 off) w V₁ }
      { s₂ with mem := s₂.mem.write (s₂.gpr n + BitVec.ofNat 64 off) w V₂ } where
  sp := ha.sp
  regs := ha.regs
  wr := ha.wr
  wf₁ := ha.wf₁
  wf₂ := ha.wf₂
  ok := storeSlots_ok ha.ok n off w p
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr_withMem]
    have hA : s₁.gpr n + BitVec.ofNat 64 off = s₂.gpr n + BitVec.ofNat 64 off := by rw [ha.reg hn]
    have same : sl ∈ τ.slots → p = true →
        s₁.mem.write (s₁.gpr n + BitVec.ofNat 64 off) w V₁ (byteAddr s₁ sl.1 k) =
          s₂.mem.write (s₂.gpr n + BitVec.ofNat 64 off) w V₂ (byteAddr s₂ sl.1 k) := fun h hp => by
      rw [hA, hv hp, ha.byteAddr_eq h hk₂]
      exact write_same _ (ha.byteAddr_eq h hk₂ ▸ ha.slots sl h k hk₁ hk₂)
    simp only [storeSlots] at hsl
    split at hsl
    · rename_i i d had
      have e₁ := addr_of_addrOf ha.wf₁ had
      have e₂ := addr_of_addrOf ha.wf₂ had
      split at hsl
      · rename_i hfit
        have hsl' : (p = true ∧ sl = (i, d, w)) ∨ (sl ∈ τ.slots ∧
            (p = true ∨ sl.1 ≠ i ∨ d + w ≤ sl.2.1 ∨ sl.2.1 + sl.2.2 ≤ d)) := by
          split at hsl
          · rename_i hp
            rcases List.mem_cons.mp hsl with h | h
            · exact .inl ⟨hp, h⟩
            · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at h
              exact .inr h
          · simp only [List.mem_filter, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, or_assoc] at hsl
            exact .inr hsl
        rcases hsl' with ⟨hp, rfl⟩ | ⟨h, hsep⟩
        · simp only at hk₁ hk₂
          simp only [e₁, e₂, Mem.write, hv hp]
          have hd : ∀ s : State, byteAddr s i k - byteAddr s i d = BitVec.ofNat 64 (k - d) :=
            fun s => (Offset.add_sub_add_left _ _ _).trans (Offset.ofNat_sub_ofNat (by omega))
          have hlt : (BitVec.ofNat 64 (k - d)).toNat < w := by
            rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
          rw [hd, hd]; simp only [hlt, ite_true]
        · by_cases hp : p = true
          · exact same h hp
          have hsep : sl.1 ≠ i ∨ k < d ∨ d + w ≤ k := by
            rcases hsep with h' | h' | h' | h'
            · exact absurd h' hp
            · exact .inl h'
            · exact .inr (.inr (by omega))
            · exact .inr (.inl (by omega))
          have hk := ha.ok sl h
          rw [e₁, e₂, write_other ha.wf₁ hw hfit (by omega) hsep,
            write_other ha.wf₂ hw hfit (by omega) hsep]
          exact ha.slots sl h k hk₁ hk₂
      · split at hsl <;> [exact same hsl ‹_›; cases hsl]
    · split at hsl <;> [exact same hsl ‹_›; cases hsl]

/-- A store of a public value at a public address keeps every slot (both
runs write the same bytes at the same address); one of a secret forgets them. -/
theorem Agree.storeAny {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) {A₁ A₂ : Addr}
    (hA : A₁ = A₂) {w : Nat} {V₁ V₂ : BitVec (8 * w)} {p : Bool} (hv : p = true → V₁ = V₂) :
    Agree { τ with slots := if p then τ.slots else [] }
      { s₁ with mem := s₁.mem.write A₁ w V₁ } { s₂ with mem := s₂.mem.write A₂ w V₂ } where
  sp := ha.sp
  regs := ha.regs
  wr := ha.wr
  wf₁ := ha.wf₁
  wf₂ := ha.wf₂
  ok sl h := by
    by_cases hp : p = true
    · simp only [hp, ite_true] at h; exact ha.ok sl h
    · simp only [hp, Bool.false_eq_true, ite_false, List.not_mem_nil] at h
  slots sl h k hk₁ hk₂ := by
    by_cases hp : p = true
    · simp only [hp, ite_true] at h
      simp only [byteAddr_withMem]
      rw [hA, hv hp, ha.byteAddr_eq h hk₂]
      exact write_same _ (ha.byteAddr_eq h hk₂ ▸ ha.slots sl h k hk₁ hk₂)
    · simp only [hp, Bool.false_eq_true, ite_false, List.not_mem_nil] at h

/-- A write of `d`, public iff `p`, with the bases `bs`. -/
theorem Agree.write {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) {bs : List (Reg × Nat × Nat)}
    (hb₁ : BasesOk bs (s₁.write d v₁)) (hb₂ : BasesOk bs (s₂.write d v₂)) :
    Agree { τ with regs := set τ d p, bases := bs } (s₁.write d v₁) (s₂.write d v₂) where
  sp := ha.sp
  regs := regs_set ha.regs hv
  wr := ha.wr
  wf₁ := ⟨ha.wf₁.1, hb₁⟩
  wf₂ := ⟨ha.wf₂.1, hb₂⟩
  ok := ha.ok
  slots := ha.slots

theorem Agree.wrW {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) : Agree (SlotTaint.wr τ d p) (s₁.write d v₁) (s₂.write d v₂) :=
  ha.write d hv (kill_write ha.wf₁ d v₁) (kill_write ha.wf₂ d v₂)

/-- A carrying instruction writes the register as `write` does, and the carry
bit, which `Agree` does not relate. -/
theorem Agree.carry {τ : T} {s₁ s₂ : State} {d : Reg} {v₁ v₂ : Nat}
    (ha : Agree τ (s₁.write d (BitVec.ofNat 64 v₁)) (s₂.write d (BitVec.ofNat 64 v₂))) :
    Agree τ (s₁.writeCarry d v₁) (s₂.writeCarry d v₂) :=
  ⟨ha.sp, ha.regs, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots⟩

theorem Agree.withLr {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (l₁ l₂ : BitVec 64) :
    Agree τ { s₁ with lr := l₁ } { s₂ with lr := l₂ } :=
  ⟨ha.sp, ha.regs, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots⟩

theorem addr_eq {s : State} {bytes : Nat} {n : Reg} {off : Nat} {a : Addr}
    (h : addr s bytes n off = some a) : a = s.gpr n + BitVec.ofNat 64 off := by
  unfold addr at h
  split at h <;> [cases h; cases h]
  rfl

theorem addrX_eq {s : State} {a b : Reg} {ea : Addr} (h : addrX s a b = some ea) :
    ea = s.gpr a + s.gpr b := by
  unfold addrX at h
  split at h <;> [cases h; cases h]
  rfl

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop | alloc | free | adrSym => simp only [step, reduceCtorEq] at hs
  | addSp d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.wrW d fun _ => by rw [ha.sp]⟩
  | add d n m | sub d n m | mul d n m | mulhu d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.wrW d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | addc d n m | subc d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, Agree.carry (ha.wrW d fun hp => ?_)⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | adde d n m | addze d n | sube d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, Agree.carry (ha.wrW d fun h => by cases h)⟩
  | logic op d n m =>
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    simp only [step] at hs
    split at hs
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hs
      simp only [BitVec.or_self]
      exact ⟨rfl, ha.write d (fun hp => by rw [ha.reg hp]) (movBases_ok ha.wf₁ d n) (movBases_ok ha.wf₂ d n)⟩
    · cases hs
      refine ⟨rfl, ha.wrW d fun hp => ?_⟩
      simp only [Bool.and_eq_true] at hp
      rw [ha.reg hp.1, ha.reg hp.2]
  | addi d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.write d (fun hp => by rw [ha.reg hp]) (addiBases_ok ha.wf₁ d n imm)
      (addiBases_ok ha.wf₂ d n imm)⟩
  | subi d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.write d (fun hp => by rw [ha.reg hp]) (subiBases_ok ha.wf₁ d n imm)
      (subiBases_ok ha.wf₂ d n imm)⟩
  | li d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.wrW d fun _ => rfl⟩
  | lsl d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.wrW d fun hp => by rw [ha.reg hp]⟩
  | rotr sz d n sh | lsr sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.wrW d fun hp => by simp only [State.read, ha.reg hp]⟩
  | lis d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.wrW d fun _ => rfl⟩
  | ori d n imm | oris d n imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.wrW d fun hp => by rw [ha.reg hp]⟩
  | mflr d =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.wrW d fun h => by cases h⟩
  | mtlr r =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.withLr _ _⟩
  | load sz t n off | lbz t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, ha₁, v₁, hv₁, rfl⟩ := e₁; obtain ⟨a₂, ha₂, v₂, hv₂, rfl⟩ := e₂
    refine ha.wrW t fun hp => ?_
    rw [addr_eq ha₁] at hv₁; rw [addr_eq ha₂] at hv₂
    simp only [State.load] at hv₁ hv₂
    split at hv₁ <;> [skip; cases hv₁]
    split at hv₂ <;> [skip; cases hv₂]
    cases hv₁; cases hv₂
    rw [← ha.reg hn]
    refine congrArg _ (Mem.read_congr fun k hk => ?_)
    have := ha.load hp k hk
    rwa [← ha.reg hn] at this
  | store sz t n off | stb t n off =>
    simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, ha₁, e₁⟩ := e₁; obtain ⟨a₂, ha₂, e₂⟩ := e₂
    rw [addr_eq ha₁] at e₁; rw [addr_eq ha₂] at e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    all_goals first
    | exact ha.store hn (w := 1) (by decide) fun hp => by rw [ha.reg hp]
    | exact ha.store hn (by cases sz <;> decide) fun hp => by rw [ha.reg hp]
  | loadRev sz t a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.reg hn.1, ha.reg hn.2], ?_⟩
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
      exact ha.wrW t fun h => by cases h
  | storeRev sz t a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.reg hn.1, ha.reg hn.2], ?_⟩
    cases sz <;>
    · simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
      obtain ⟨a₁, ha₁, e₁⟩ := e₁; obtain ⟨a₂, ha₂, e₂⟩ := e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      have hA : a₁ = a₂ := by
        rw [addrX_eq ha₁, addrX_eq ha₂, ha.reg hn.1, ha.reg hn.2]
      exact ha.storeAny hA fun hp => by simp only [State.read, ha.reg hp]

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : condPub τ c = true) : eval c s₁ = eval c s₂ := by
  cases c <;> simp only [condPub] at hc <;> simp [eval, State.read, ha.reg hc]

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (List.mem_filter.mp hp).1⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.1 (he ▸ hne)
  · simp only [meet, he, ↓reduceIte, ne_eq, not_true_eq_false] at hne

theorem Wf.meet_right {τ₁ τ₂ : T} {s : State} (h : Wf τ₂ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (by simpa only [List.contains_eq_mem,
                                                 decide_eq_true_eq] using (List.mem_filter.mp hp).2)⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact h.1 hne
  · simp only [meet, he, ↓reduceIte, ne_eq, not_true_eq_false] at hne

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  sp := h.sp
  regs r hr := h.regs r (RegSet.mem_inter.mp hr).1
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [exact h.wr hne; exact absurd rfl hne]
  wf₁ := h.wf₁.meet_left
  wf₂ := h.wf₂.meet_left
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact he ▸ h.ok sl (List.mem_filter.mp hsl).1
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (List.mem_filter.mp hsl).1; cases hsl]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  sp := h.sp
  regs r hr := h.regs r (RegSet.mem_inter.mp hr).2
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [rename_i he; exact absurd rfl hne]
    exact h.wr (he ▸ hne)
  wf₁ := h.wf₁.meet_right
  wf₂ := h.wf₂.meet_right
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact h.ok sl (by simpa only [List.contains_eq_mem,
        decide_eq_true_eq] using (List.mem_filter.mp hsl).2)
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (by simpa only [List.contains_eq_mem,
                                             decide_eq_true_eq] using (List.mem_filter.mp hsl).2); cases hsl]

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨hr, hl⟩, hb⟩, hs⟩ := hle
  exact ⟨h.sp, fun r h' => h.regs r (RegSet.mem_of_subset hr h'), fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.1 (hl ▸ hne), fun p hp => h.wf₁.2 p (hb p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.1 (hl ▸ hne), fun p hp => h.wf₂.2 p (hb p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl)⟩

/-- A call leaves unknown values in `r0`, `r11` and `r12` (and `LR`, which is
not tracked), and changes no memory or region. -/
def callStep (τ : T) : T where
  regs := ((τ.regs.erase .r0).erase .r11).erase .r12
  lens := τ.lens
  bases := τ.bases.filter fun p => p.1 != .r0 && p.1 != .r11 && p.1 != .r12
  slots := τ.slots

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : some (callStep τ) = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  cases hs
  simp only [isa, call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have hb : ∀ s : State, Wf τ s → BasesOk (callStep τ).bases { s with
      lr := s.unknowns 0
      gpr := fun r => if r = .r0 then s.unknowns 1 else if r = .r11 then s.unknowns 2
        else if r = .r12 then s.unknowns 3 else s.gpr r
      unknowns := fun n => s.unknowns (n + 4) } := fun s hw p hp => by
    simp only [callStep, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
    obtain ⟨hp, ⟨h0, h11⟩, h12⟩ := hp
    simp only [h0, h11, h12, ite_false]
    exact hw.2 p hp
  refine ⟨rfl, ⟨ha.sp, fun r hr => ?_, ha.wr, ⟨ha.wf₁.1, hb s₁ ha.wf₁⟩, ⟨ha.wf₂.1, hb s₂ ha.wf₂⟩, ha.ok,
    ha.slots⟩⟩
  simp only [callStep, RegSet.mem_erase] at hr
  obtain ⟨h12, h11, h0, hr⟩ := hr
  simp only [h0, h11, h12, ite_false]
  exact ha.regs r hr

end VG.PPC64LE.SlotTaint

namespace VG.PPC64LE

/-- Taint tracking for PPC64LE with public slots in the writable regions. -/
def slotTaint : VG.Taint isa where
  T := SlotTaint.T
  Agree := SlotTaint.Agree
  step := SlotTaint.step
  step_sound := SlotTaint.step_sound
  condPub := SlotTaint.condPub
  cond_sound := SlotTaint.cond_sound
  meet := SlotTaint.meet
  meet_left := SlotTaint.meet_left
  meet_right := SlotTaint.meet_right
  le := SlotTaint.le
  le_sound := SlotTaint.le_sound
  call τ := some (SlotTaint.callStep τ)
  call_sound := SlotTaint.call_sound
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  -- Frames are not analysed.
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

/-- The taint in which the registers `rs` are public, the writable regions
are at least `lens` long, and each register of `bs` holds the base address of
its region. -/
def SlotTaint.mk' (rs : List Reg) (lens : List Nat) (bs : List (Reg × Nat)) : SlotTaint.T :=
  { regs := RegSet.ofList rs, lens := lens, bases := bs.map fun p => (p.1, p.2, 0) }

theorem SlotTaint.agree_mk' {rs : List Reg} {lens : List Nat} {bs : List (Reg × Nat)} {s₁ s₂ : State}
    (hsp : s₁.sp = s₂.sp) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hwr : s₁.wr = s₂.wr)
    (hl : List.Forall₂ (fun r l => l ≤ r.len) s₁.wr lens) (hd : s₁.wr.Pairwise Region.Disjoint)
    (hlen : ∀ r ∈ s₁.wr, r.len ≤ 2 ^ 64)
    (hb₁ : ∀ p ∈ bs, s₁.gpr p.1 = (SlotTaint.region s₁ p.2).base)
    (hb₂ : ∀ p ∈ bs, s₂.gpr p.1 = (SlotTaint.region s₂ p.2).base) :
    SlotTaint.Agree (SlotTaint.mk' rs lens bs) s₁ s₂ where
  sp := hsp
  regs r h := hr r (RegSet.mem_ofList.mp h)
  wr _ := hwr
  wf₁ := ⟨fun _ => ⟨hl, hd, hlen⟩, fun p hp => by
    simp only [SlotTaint.mk', List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hb₁ q hq, BitVec.add_zero]⟩
  wf₂ := ⟨fun _ => ⟨hwr ▸ hl, hwr ▸ hd, hwr ▸ hlen⟩, fun p hp => by
    simp only [SlotTaint.mk', List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hb₂ q hq, BitVec.add_zero]⟩
  ok _ h := by cases h
  slots _ h := by cases h

end VG.PPC64LE
