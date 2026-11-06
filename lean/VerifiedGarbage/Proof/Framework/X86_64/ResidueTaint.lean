module

public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep

/-!
# Taint tracking through stack frames, for returning without residue (x86-64)

`rtaint` is the x86-64 taint analysis (`X86_64.taint`) extended to the stack
a function uses: the `stack` bytes below the stack pointer on entry (the
*window*). It follows the frames code allocates (`alloc` and `free`; frames
of pushed registers are not handled) as writable regions at the head of `wr`,
whose public bytes the base analysis tracks as slots, and the calls and
returns of the code, whose return addresses it keeps apart from the frames
(`ras`). The bytes of the window outside every writable region are equal in
both runs but those listed in `sec` (window indices from its base, the stack
pointer on entry minus `stack`): when a frame is freed, its bytes that are
not public are added to `sec`. So at the end of a function, the bytes of its
window that may differ between two runs are those `sec` lists: those its
code must zero to leave no residue.

Instructions are the base analysis's (`X86_64.taint.step`), with the same
soundness proof, and must not write the stack pointer.
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint

/-! ## Intervals of window indices -/

/-- Index `j` is in one of the intervals `(lo, n)` of `l`. -/
def InSec (l : List (Nat × Nat)) (j : Nat) : Prop := ∃ p ∈ l, p.1 ≤ j ∧ j < p.1 + p.2

/-- `[a, a + n)` minus `[c, c + m)`, as at most two intervals. -/
def sub1 (c m : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  let a := p.1
  let e := p.1 + p.2
  (if a < min e c then [(a, min e c - a)] else []) ++
    (if max a (c + m) < e then [(max a (c + m), e - max a (c + m))] else [])

/-- The intervals of `ps` minus every interval of `l`. -/
def gaps (l : List (Nat × Nat)) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc q => acc.flatMap (sub1 q.1 q.2)) ps

theorem mem_sub1 {c m j : Nat} {p : Nat × Nat} :
    (∃ q ∈ sub1 c m p, q.1 ≤ j ∧ j < q.1 + q.2) ↔ (p.1 ≤ j ∧ j < p.1 + p.2 ∧ ¬ (c ≤ j ∧ j < c + m)) := by
  simp only [sub1, List.mem_append]
  constructor
  · rintro ⟨q, hq, h₁, h₂⟩
    rcases hq with hq | hq <;> split at hq <;> simp at hq <;> subst hq <;> simp at h₁ h₂ <;> omega
  · rintro ⟨h₁, h₂, h₃⟩
    by_cases hc : j < c
    · refine ⟨(p.1, min (p.1 + p.2) c - p.1), .inl ?_, by simp; omega, by simp; omega⟩
      simp only [show p.1 < min (p.1 + p.2) c by omega, ↓reduceIte, List.mem_singleton]
    · refine ⟨(max p.1 (c + m), p.1 + p.2 - max p.1 (c + m)), .inr ?_, by simp; omega, by simp; omega⟩
      simp only [show max p.1 (c + m) < p.1 + p.2 by omega, ↓reduceIte, List.mem_singleton]

theorem mem_gaps {j : Nat} : ∀ (l ps : List (Nat × Nat)),
    InSec (gaps l ps) j ↔ InSec ps j ∧ ¬ InSec l j
  | [], ps => by simp [gaps, InSec]
  | q :: l, ps => by
    show InSec (gaps l (ps.flatMap (sub1 q.1 q.2))) j ↔ _
    rw [mem_gaps l]
    simp only [InSec, List.mem_flatMap, List.mem_cons]
    constructor
    · rintro ⟨⟨r, ⟨p, hp, hr⟩, h⟩, hn⟩
      have := mem_sub1.mp ⟨r, hr, h⟩
      exact ⟨⟨p, hp, this.1, this.2.1⟩, fun ⟨p', hp', h'⟩ => by
        rcases hp' with rfl | hp'
        · exact this.2.2 h'
        · exact hn ⟨p', hp', h'⟩⟩
    · rintro ⟨⟨p, hp, h⟩, hn⟩
      obtain ⟨r, hr, h'⟩ := mem_sub1.mpr ⟨h.1, h.2, fun h' => hn ⟨q, .inl rfl, h'⟩⟩
      exact ⟨⟨r, ⟨p, hp, hr⟩, h'⟩, fun ⟨p', hp', h'⟩ => hn ⟨p', .inr hp', h'⟩⟩

/-! ## The domain -/

structure FT where
  /-- `false`: nothing is known (`meet` of incompatible taints). -/
  ok : Bool
  t : Taint.T
  /-- How many of the writable regions, at their head, are frames. -/
  nfr : Nat
  /-- The stack pointer on entry minus the current one. -/
  depth : Nat
  /-- The bytes of the window below the current stack pointer. -/
  room : Nat
  /-- Window indices that may differ between the runs, outside writable regions. -/
  sec : List (Nat × Nat)
  /-- Window indices of the return addresses of the calls in progress, innermost first. -/
  ras : List Nat
  deriving DecidableEq, Lean.ToExpr

/-- The base of the window. -/
def wb (s : State) (τ : FT) : Addr := s.gpr .rsp - BitVec.ofNat 64 τ.room

/-- The address of window index `j`. -/
def wa (s : State) (τ : FT) (j : Nat) : Addr := wb s τ + BitVec.ofNat 64 j

/-- The 8 bytes at window index `j`. -/
def raSlot (s : State) (τ : FT) (j : Nat) : Region := ⟨wa s τ j, 8⟩

structure RInv (τ : FT) (s₁ s₂ : State) : Prop where
  base : Taint.Agree τ.t s₁ s₂
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  unk : s₁.unknowns = s₂.unknowns
  wr : s₁.wr = s₂.wr
  lens : τ.t.lens = [] → s₁.wr = []
  nfr : τ.nfr ≤ s₁.wr.length
  room : τ.room ≤ (s₁.gpr .rsp).toNat
  top : (s₁.gpr .rsp).toNat + τ.depth < 2 ^ 64
  frames : ∀ i < τ.nfr, Region.Sub (region s₁ i) ⟨s₁.gpr .rsp, τ.depth⟩
  others : ∀ i, τ.nfr ≤ i → i < s₁.wr.length →
    (region s₁ i).Disjoint ⟨wb s₁ τ, τ.room + τ.depth⟩
  rasIn : ∀ j ∈ τ.ras, τ.room ≤ j ∧ j + 8 ≤ τ.room + τ.depth
  rasSorted : τ.ras.Pairwise fun a b => a + 8 ≤ b
  rasFr : ∀ j ∈ τ.ras, ∀ i < τ.nfr, (region s₁ i).Disjoint (raSlot s₁ τ j)
  dead : ∀ j < τ.room + τ.depth, ¬ InSec τ.sec j →
    (∀ r ∈ s₁.wr, ¬ r.Contains (wa s₁ τ j) 1) → s₁.mem (wa s₁ τ j) = s₂.mem (wa s₂ τ j)

def Agree (τ : FT) (s₁ s₂ : State) : Prop := τ.ok = true → RInv τ s₁ s₂

/-- No knowledge. -/
def none' : FT := ⟨false, {regs := .empty, flags := false}, 0, 0, 0, [], []⟩

/-! ## Transfer functions -/

def step (τ : FT) (i : Instr) : Option FT :=
  if τ.ok && !isa.writesSp i then
    match X86_64.taint.step τ.t i with
    | some t' => if t'.lens == τ.t.lens then some { τ with t := t' } else none
    | none => none
  else none

def meet (τ₁ τ₂ : FT) : FT :=
  if τ₁.ok && τ₂.ok && τ₁.nfr == τ₂.nfr && τ₁.depth == τ₂.depth && τ₁.room == τ₂.room &&
      τ₁.ras == τ₂.ras && τ₁.t.lens == τ₂.t.lens then
    { τ₁ with t := Taint.meet τ₁.t τ₂.t, sec := τ₁.sec ++ τ₂.sec }
  else none'

def le (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && τ.nfr == σ.nfr && τ.depth == σ.depth && τ.room == σ.room && τ.ras == σ.ras &&
    Taint.leK τ.t σ.t && σ.sec.all (τ.sec.contains ·))

/-- The base taint after a write of the stack pointer by a call or a return. -/
def killSp (t : Taint.T) : Taint.T := { t with bases := kill t .rsp, lo := .empty }

def callF (τ : FT) : Option FT :=
  if τ.ok && 8 ≤ τ.room then
    some { τ with t := killSp τ.t, depth := τ.depth + 8, room := τ.room - 8, ras := (τ.room - 8) :: τ.ras }
  else none

def retF (τ : FT) : Option FT :=
  if τ.ok && τ.ras.head? == some τ.room && 8 ≤ τ.depth then
    some { τ with t := killSp τ.t, depth := τ.depth - 8, room := τ.room + 8, ras := τ.ras.tail }
  else none

/-- The base taint with a frame of `b` bytes pushed at the head of the
writable regions, whose public bytes are `fs` (slots of region 0). -/
def shiftIn (t : Taint.T) (b : Nat) (fs : List (Nat × Nat × Nat)) : Taint.T :=
  { t with
    lens := b :: t.lens
    bases := (.rsp, 0, 0) :: (kill t .rsp).map fun p => (p.1, p.2.1 + 1, p.2.2)
    slots := fs ++ t.slots.map fun sl => (sl.1 + 1, sl.2)
    lo := .empty }

/-- The base taint with the frame at the head of the writable regions popped. -/
def shiftOut (t : Taint.T) : Taint.T :=
  { t with
    lens := t.lens.tail
    bases := (kill t .rsp).filterMap fun p => if p.2.1 = 0 then none else some (p.1, p.2.1 - 1, p.2.2)
    slots := t.slots.filterMap fun sl => if sl.1 = 0 then none else some (sl.1 - 1, sl.2)
    lo := .empty }

/-- `[a, a + n)` cut into pieces of at most 16 bytes, from `a` up (`fuel` pieces at most). -/
def split16 : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | f + 1, a, n + 1 => if n + 1 ≤ 16 then [(a, n + 1)] else (a, 16) :: split16 f (a + 16) (n + 1 - 16)

/-- The public bytes of a new frame of `b` bytes at window index `a`, as slots
of region 0 of at most 16 bytes (the base analysis drops a whole slot when a
secret is stored into any of its bytes). -/
def newSlots (sec : List (Nat × Nat)) (a b : Nat) : List (Nat × Nat × Nat) :=
  ((gaps sec [(a, b)]).flatMap fun p => split16 (p.2 / 16 + 1) p.1 p.2).map fun p => (0, p.1 - a, p.2)

def pushF (τ : FT) : Instr → Option FT
  | .alloc b =>
    if τ.ok && 0 < b && b < 4096 && b % 8 == 0 && b ≤ τ.room then
      let fs := newSlots τ.sec (τ.room - b) b
      some { τ with t := shiftIn τ.t b fs, nfr := τ.nfr + 1, depth := τ.depth + b, room := τ.room - b }
    else none
  | _ => none

/-- The window intervals of the public slots of region 0 of a frame at window index `a`. -/
def frameSlots (t : Taint.T) (a : Nat) : List (Nat × Nat) :=
  t.slots.filterMap fun sl => if sl.1 = 0 then some (a + sl.2.1, sl.2.2) else none

def popF (τ : FT) : Instr → Option FT
  | .free b =>
    if τ.ok && 1 ≤ τ.nfr && τ.t.lens.head? == some b && b ≤ τ.depth && τ.ras.all (τ.room + b ≤ ·) then
      let sec' := τ.sec ++ gaps (frameSlots τ.t τ.room) [(τ.room, b)]
      some ⟨true, shiftOut τ.t, τ.nfr - 1, τ.depth - b, τ.room + b, sec', τ.ras⟩
    else none
  | _ => none

/-! ## Soundness: instructions -/

open VG.X86_64.Residue (Pres Pres.none' Pres.some' Pres.map' Pres.bind')

macro "uk_leaf" : tactic => `(tactic| first
  | exact Pres.none'
  | (apply Pres.some'; rfl)
  | (apply Pres.map'; intro _; rfl)
  | (apply Pres.map'; intro _; split <;> rfl))

syntax "uk_go" : tactic
macro_rules
  | `(tactic| uk_go) => `(tactic| first
    | uk_leaf
    | (apply Pres.bind'; intro _; uk_go)
    | (split <;> uk_go))

theorem exec_unknowns_pres (i : Instr) (s : State) :
    Pres (fun x => x.unknowns = s.unknowns) (exec i s) := by
  cases i
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] <;> uk_go
  case evLoad d _ | evMadd52Load _ d _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov, State.store64,
      State.store32, State.store8, State.store16, State.store128, State.store256, State.store512,
      State.storeMasked512, State.storeMasked512B]
  all_goals uk_go

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns :=
  exec_unknowns_pres i s s' h

theorem exec_frame {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  have e : execBlock isa [i] s = some (s', (addrs i s).map Leak.addr) := by
    simp only [execBlock, isa, h, Option.map_some, List.append_nil]
  obtain ⟨-, hw, hf⟩ := execBlock_regions e
  exact ⟨hw, hf⟩

theorem wa_eq {s₁ s₂ : State} {τ : FT} (h : s₁.gpr .rsp = s₂.gpr .rsp) (j : Nat) : wa s₁ τ j = wa s₂ τ j := by
  simp only [wa, wb, h]

theorem step_sound {τ τ' : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  unfold step at hs
  split at hs <;> [rename_i hok; cases hs]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hok, hsp⟩ := hok
  split at hs <;> [rename_i t' ht; cases hs]
  split at hs <;> [rename_i hl; cases hs]
  cases hs
  have hl : t'.lens = τ.t.lens := by simpa using hl
  have inv := ha hok
  obtain ⟨had, hb⟩ := X86_64.taint.step_sound inv.base ht e₁ e₂
  have r₁ := exec_rsp hsp e₁
  have r₂ := exec_rsp hsp e₂
  obtain ⟨w₁, f₁⟩ := exec_frame e₁
  obtain ⟨w₂, f₂⟩ := exec_frame e₂
  refine ⟨had, fun _ => ⟨hb, by rw [r₁, r₂, inv.rsp], by rw [exec_unknowns e₁, exec_unknowns e₂, inv.unk],
    by rw [w₁, w₂, inv.wr], fun h => by rw [w₁]; exact inv.lens (hl ▸ h), by rw [w₁]; exact inv.nfr,
    by rw [r₁]; exact inv.room, by rw [r₁]; exact inv.top, ?_, ?_, inv.rasIn, inv.rasSorted, ?_, ?_⟩⟩
  · intro i hi; simp only [region, w₁, r₁]; exact inv.frames i hi
  · intro i h₁ h₂; simp only [region, w₁, wb, r₁]; rw [w₁] at h₂; exact inv.others i h₁ h₂
  · intro j hj i hi; simp only [region, raSlot, wa, wb, w₁, r₁]; exact inv.rasFr j hj i hi
  · intro j hj hn hw
    have d := inv.dead j hj hn
    simp only [wa, wb] at hw d ⊢
    rw [w₁, r₁] at hw
    rw [r₁, r₂, f₁ _ hw, f₂ _ (by rw [← inv.wr, ← inv.rsp]; exact hw)]
    exact d hw

/-! ## Soundness: branches, joins and order -/

theorem cond_sound {τ : FT} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (h : (τ.ok && τ.t.flags) = true) : eval c s₁ = eval c s₂ := by
  simp only [Bool.and_eq_true] at h
  exact Taint.cond_sound (ha h.1).base h.2

theorem inSec_append_left {l₁ l₂ : List (Nat × Nat)} {j : Nat} (h : ¬ InSec (l₁ ++ l₂) j) : ¬ InSec l₁ j :=
  fun ⟨p, hp, h'⟩ => h ⟨p, List.mem_append_left _ hp, h'⟩

theorem inSec_append_right {l₁ l₂ : List (Nat × Nat)} {j : Nat} (h : ¬ InSec (l₁ ++ l₂) j) : ¬ InSec l₂ j :=
  fun ⟨p, hp, h'⟩ => h ⟨p, List.mem_append_right _ hp, h'⟩

theorem meet_left {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, hl⟩ := hc
    intro _
    have inv := h h1
    exact { inv with
      base := Taint.meet_left inv.base
      lens := fun e => inv.lens (by simpa [Taint.meet, hl] using e)
      dead := fun j hj hn hw => inv.dead j hj (inSec_append_left hn) hw }
  · intro h; cases h

theorem meet_right {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, hn⟩, hd⟩, hr⟩, hra⟩, hl⟩ := hc
    intro _
    have inv := h h2
    have e : ({ τ₁ with t := Taint.meet τ₁.t τ₂.t, sec := τ₁.sec ++ τ₂.sec } : FT) =
        { τ₂ with t := Taint.meet τ₁.t τ₂.t, sec := τ₁.sec ++ τ₂.sec, ok := τ₁.ok } := by
      cases τ₁; cases τ₂; simp_all
    rw [e]
    exact { inv with
      base := Taint.meet_right inv.base
      lens := fun e => inv.lens (by simpa [Taint.meet, hl] using e)
      dead := fun j hj hn hw => inv.dead j hj (inSec_append_right hn) hw }
  · intro h; cases h

theorem le_sound {τ σ : FT} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  intro hτ
  simp only [le, hτ, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨hs, hn⟩, hd⟩, hr⟩, hra⟩, hb⟩, hsec⟩ := hle
  have inv := h hs
  have hbase := Taint.le_sound (Taint.leK_eq ▸ hb) inv.base
  have hl : τ.t.lens = σ.t.lens := by
    have hb' := hb
    rw [Taint.leK_eq] at hb'; simp only [Taint.le, Bool.and_eq_true, beq_iff_eq] at hb'; exact hb'.1.1.1.1.2
  have e : ∀ s, wa s τ = wa s σ := fun s => by funext j; simp only [wa, wb, hr]
  have e' : ∀ s, raSlot s τ = raSlot s σ := fun s => by funext j; simp only [raSlot, e]
  refine ⟨hbase, inv.rsp, inv.unk, inv.wr, fun x => inv.lens (hl ▸ x), hn ▸ inv.nfr, hr ▸ inv.room,
    hd ▸ inv.top, hn ▸ hd ▸ inv.frames, ?_, hra ▸ hr ▸ hd ▸ inv.rasIn, hra ▸ inv.rasSorted, ?_, ?_⟩
  · intro i h₁ h₂; simp only [wb, hr, hd]; exact inv.others i (hn ▸ h₁) h₂
  · rw [e', hra, hn]; exact inv.rasFr
  · intro j hj hnot hw
    rw [e] at hw ⊢; rw [e]
    refine inv.dead j (hr ▸ hd ▸ hj) (fun ⟨p, hp, h'⟩ => hnot ⟨p, hsec p hp, h'⟩) hw

end VG.X86_64.RTaint
