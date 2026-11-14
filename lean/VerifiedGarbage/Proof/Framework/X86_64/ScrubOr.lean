module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock

/-! # Scrubbing where the residue analysis follows the code, else wiping the whole stack -/

/-!
`withScrubOrAll` scrubs an instance of a generic function after its residue
analysis where it has one, and otherwise with every granule of its stack
wiped (`Scrub.withScrubAll`). `withScrubAllM` wipes every granule too, but
for code that leaves the same MXCSR in two runs along the same path
(`Mx.mx`) it appends no instruction that writes MXCSR (`mxFix`), at any
level: code that saves, loads and restores MXCSR around the multiplications
of Intel's MCDT list, in a register or in memory, whether or not every path
does (an early return before Intel's prologue, or a short input that skips
it, which `mxClass` rejects), is cleared at the level of the registers it
writes (`levelForE`), and so needs no AVX-512 feature unless it writes
`zmm16`–`zmm31`, and no stack for `mxFix`.
-/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- `r` scrubbed after the residue analysis `a` where an instance of a
generic function has one (`withScrub`), and otherwise with every granule of
its stack wiped (`Scrub.withScrubAll`): for the instances whose code the
analysis does not follow, of a function with a small stack. -/
def withScrubOrAll {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | some a => withScrub r hpost pubs hpub (some a)
  | none => withScrubAll r hpost

/-! ## MXCSR along a path

`Mx.mx` follows what two runs of some code along the same path agree on,
besides MXCSR: the low 32 bits of some registers, and the 4 bytes at some
displacements from some registers (`Mx.F`). `stmxcsr` stores MXCSR, a `mov`
of an immediate, a load of such bytes and an `and` with an immediate keep a
register agreed on, and a store of one stores such bytes; every `ldmxcsr`
loads bytes agreed on (Intel's MCDT prologue its `0x1FBF`, and the epilogue
what the prologue saved, in a register or in memory), so MXCSR agrees all
along. A branch's direction is in the trace, so two runs with the same
trace take the same path, and leave the same MXCSR if they started with the
same (`Mx.mxSame_of`): whatever the path, unlike `mxClass`, which needs the
same function of MXCSR on entry on every path. -/

namespace Mx

open VG.X86_64.RTaint (storeW writesMem)

/-- A fact two runs agree on: the low 32 bits of a register, or the 4 bytes
at `d` from a register. -/
inductive F where
  | reg (r : Reg)
  | slot (b : Reg) (d : Int)
  deriving DecidableEq

/-- An operand without an index, with a displacement of 32 bits. -/
def plain (m : MemOp) : Bool := m.index.isNone && decide (-2 ^ 31 ≤ m.disp ∧ m.disp < 2 ^ 31)

def slotOf (m : MemOp) : F := .slot m.base m.disp

def Hold (s₁ s₂ : State) : F → Prop
  | .reg r => (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32
  | .slot b d => s₁.mem.readW (s₁.gpr b + BitVec.ofInt 64 d) 32 = s₂.mem.readW (s₂.gpr b + BitVec.ofInt 64 d) 32

/-- MXCSR and the facts `fs` agree. -/
def Inv (fs : List F) (s₁ s₂ : State) : Prop := s₁.mxcsr = s₂.mxcsr ∧ ∀ f ∈ fs, Hold s₁ s₂ f

/-- Whether a fact survives `i`: it writes neither the register nor (or its
base register) the bytes. -/
def keep (i : Instr) : F → Bool
  | .reg r => !Taint.clobbers i r
  | .slot b d => !Taint.clobbers i b && match storeW i with
    | some (m, w) => plain m && m.base == b && decide (w ≤ 64) && decide (-2 ^ 31 ≤ d ∧ d < 2 ^ 31) &&
        decide (m.disp + w ≤ d ∨ d + 4 ≤ m.disp)
    | none => !writesMem i

/-- The facts `i` establishes, given `fs` before it. -/
def adds (fs : List F) : Instr → List F
  | .stmxcsr m => if plain m then [slotOf m] else []
  | .mov32 r (.imm _) => [.reg r]
  | .mov32 r (.mem m) => if plain m && fs.contains (slotOf m) then [.reg r] else []
  | .alu32 .and r (.imm _) => if fs.contains (.reg r) then [.reg r] else []
  | .store32 m r => if plain m && fs.contains (.reg r) then [slotOf m] else []
  | _ => []

/-- `ldmxcsr` loads bytes agreed on. -/
def ldOk (fs : List F) : Instr → Bool
  | .ldmxcsr m => plain m && fs.contains (slotOf m)
  | _ => true

def step (fs : List F) (i : Instr) : Option (List F) :=
  if ldOk fs i then some (adds fs i ++ fs.filter (keep i)) else none

def blk : List F → List Instr → Option (List F)
  | fs, [] => some fs
  | fs, i :: is => (step fs i).bind (blk · is)

/-- The facts on registers other than `rsp`, which calls and frames keep. -/
def regs (fs : List F) : List F := fs.filter fun f => match f with
  | .reg r => r != .rsp
  | .slot .. => false

/-- The facts after `c`, given `fs` before it, if every `ldmxcsr` in it
loads bytes agreed on. A loop's are those after its body from some of `fs`
that its body keeps: `fs`, less what an iteration and then another drop, or
none. -/
def mx : Prog isa → List F → Option (List F)
  | .block is, fs => blk fs is
  | .seq x y, fs => (mx x fs).bind (mx y)
  | .ite _ t e, fs =>
    match mx t fs, mx e fs with
    | some a, some b => some (a.filter b.contains)
    | _, _ => none
  | .loop b _, fs =>
    match mx b fs with
    | none => none
    | some g₁ =>
      match mx b (fs.filter g₁.contains) with
      | none => none
      | some g₂ =>
        match mx b ((fs.filter g₁.contains).filter g₂.contains) with
        | some g₃ =>
          if ((fs.filter g₁.contains).filter g₂.contains).all g₃.contains then some g₃ else mx b []
        | none => mx b []
  | .call _ b, fs => (mx b (regs fs)).map regs
  | .frame _ b j, fs => (mx b (regs fs)).map fun g => regs (g.filter (keep j))
  | .icall .., _ => none

theorem inv_sub {fs gs : List F} {s₁ s₂ : State} (h : ∀ f ∈ gs, f ∈ fs) (hi : Inv fs s₁ s₂) : Inv gs s₁ s₂ :=
  ⟨hi.1, fun f hf => hi.2 f (h f hf)⟩

theorem mem_of_all {gs fs : List F} (h : gs.all fs.contains = true) : ∀ f ∈ gs, f ∈ fs := fun f hf => by
  simpa using List.all_eq_true.mp h f hf

theorem ea_plain {m : MemOp} (h : plain m = true) (s : State) : s.ea m = s.gpr m.base + BitVec.ofInt 64 m.disp := by
  simp only [plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  simp only [State.ea, h.1]

/-- A store of `w ≤ 64` bytes at `e` from a register misses the 4 bytes at
`d` from it, if the two do not overlap. -/
theorem disj (p : Addr) {d e : Int} {k w : Nat} (hk : k < 4) (hw : w ≤ 64) (hd : -2 ^ 31 ≤ d ∧ d < 2 ^ 31)
    (he : -2 ^ 31 ≤ e ∧ e < 2 ^ 31) (h : e + w ≤ d ∨ d + 4 ≤ e) :
    ¬ ((p + BitVec.ofInt 64 d + BitVec.ofNat 64 k) - (p + BitVec.ofInt 64 e)).toNat < w := by
  have := p.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- What a fact `keep` keeps refers to the same register and bytes after `i`. -/
theorem keep_slot {i : Instr} {b : Reg} {d : Int} (h : keep i (.slot b d) = true) {s s' : State}
    (e : exec i s = some s') :
    s'.gpr b = s.gpr b ∧
      s'.mem.readW (s.gpr b + BitVec.ofInt 64 d) 32 = s.mem.readW (s.gpr b + BitVec.ofInt 64 d) 32 := by
  simp only [keep, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨exec_gpr h.1 e, ?_⟩
  revert h
  cases hw : storeW i with
  | none =>
    intro h
    have := h.2
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
    rw [RTaint.exec_mem this e]
  | some p =>
    obtain ⟨m, w⟩ := p
    intro h
    have h2 := h.2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨⟨hpl, hb⟩, hw64⟩, hd⟩, hdj⟩ := h2
    have hea := ea_plain hpl s
    rw [hb] at hea
    apply Mem.readW_congr
    intro k hk
    apply RTaint.exec_store hw e
    rw [hea]
    have he : -2 ^ 31 ≤ m.disp ∧ m.disp < 2 ^ 31 := by
      simp only [plain, Bool.and_eq_true, decide_eq_true_eq] at hpl; exact hpl.2
    exact disj _ (by omega) hw64 hd he hdj

theorem keep_hold {i : Instr} {f : F} (h : keep i f = true) {s₁ s₂ s₁' s₂' : State}
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') (hf : Hold s₁ s₂ f) : Hold s₁' s₂' f := by
  cases f with
  | reg r =>
    have hc : Taint.clobbers i r = false := by simpa [keep] using h
    simp only [Hold, exec_gpr hc e₁, exec_gpr hc e₂]; exact hf
  | slot b d =>
    obtain ⟨g₁, m₁⟩ := keep_slot h e₁
    obtain ⟨g₂, m₂⟩ := keep_slot h e₂
    simp only [Hold, g₁, g₂, m₁, m₂]; exact hf

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem adds_hold {fs : List F} {i : Instr} {f : F} (hf : f ∈ adds fs i) {s₁ s₂ s₁' s₂' : State}
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') (hi : Inv fs s₁ s₂) : Hold s₁' s₂' f := by
  unfold adds at hf
  split at hf
  · -- stmxcsr
    rename_i m
    split at hf
    · rename_i hp
      simp only [List.mem_singleton] at hf; subst hf
      simp only [reduceExec, State.store32] at e₁ e₂
      split at e₁ <;> cases e₁
      split at e₂ <;> cases e₂
      simp only [Hold, slotOf, ← ea_plain hp, Mem.readW_writeW_self32]
      exact hi.1
    · cases hf
  · -- mov32 r imm
    simp only [List.mem_singleton] at hf; subst hf
    simp only [reduceExec, readSrc32, Option.map_some, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    simp only [Hold, State.setReg32, State.setReg, ↓reduceIte]
  · -- mov32 r [m]
    rename_i r m
    split at hf
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      simp only [List.mem_singleton] at hf; subst hf
      simp only [reduceExec, readSrc32, State.load32] at e₁ e₂
      split at e₁ <;> cases e₁
      split at e₂ <;> cases e₂
      have := hi.2 _ hc.2
      simp only [Hold, slotOf, ← ea_plain hc.1] at this
      simp only [Hold, State.setReg32, State.setReg, ↓reduceIte, sw32, this]
    · cases hf
  · -- and r imm
    rename_i r k
    split at hf
    · rename_i hc
      simp only [List.contains_iff_mem] at hc
      simp only [List.mem_singleton] at hf; subst hf
      simp only [reduceExec, execAlu32, readSrc32, Option.bind_some, Option.some.injEq] at e₁ e₂
      subst e₁ e₂
      have := hi.2 _ hc
      simp only [Hold] at this
      simp only [Hold, State.setReg32, State.setReg, arithFlags, State.setFlags, ↓reduceIte, sw32, this]
    · cases hf
  · -- store32 m r
    rename_i m r
    split at hf
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      simp only [List.mem_singleton] at hf; subst hf
      simp only [reduceExec, State.store32] at e₁ e₂
      split at e₁ <;> cases e₁
      split at e₂ <;> cases e₂
      have := hi.2 _ hc.2
      simp only [Hold] at this
      simp only [Hold, slotOf, ← ea_plain hc.1, Mem.readW_writeW_self32, this]
    · cases hf
  · cases hf

theorem step_ok {fs fs' : List F} {i : Instr} (h : step fs i = some fs') {s₁ s₂ s₁' s₂' : State}
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') (hi : Inv fs s₁ s₂) : Inv fs' s₁' s₂' := by
  unfold step at h
  split at h
  · rename_i hl
    cases h
    refine ⟨?_, fun f hf => ?_⟩
    · cases hm : loadsMxcsr i
      · rw [exec_mxcsr hm e₁, exec_mxcsr hm e₂]; exact hi.1
      · cases i <;> simp only [loadsMxcsr, reduceCtorEq] at hm
        rename_i m
        simp only [ldOk, Bool.and_eq_true, List.contains_iff_mem] at hl
        simp only [reduceExec, State.load32] at e₁ e₂
        have := hi.2 _ hl.2
        simp only [Hold, slotOf, ← ea_plain hl.1] at this
        split at e₁ <;> simp only [Option.bind_some, Option.bind_none, reduceCtorEq] at e₁
        split at e₂ <;> simp only [Option.bind_some, Option.bind_none, reduceCtorEq] at e₂
        split at e₁ <;> cases e₁
        split at e₂ <;> cases e₂
        exact this
    · rcases List.mem_append.mp hf with hf | hf
      · exact adds_hold hf e₁ e₂ hi
      · obtain ⟨hf, hk⟩ := List.mem_filter.mp hf
        exact keep_hold hk e₁ e₂ (hi.2 f hf)
  · cases h

theorem blk_ok : ∀ {is : List Instr} {fs fs' : List F} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak},
    blk fs is = some fs' → execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
    Inv fs s₁ s₂ → Inv fs' s₁' s₂'
  | [], _, _, _, _, _, _, _, _, h, b₁, b₂, hi => by
    simp only [blk, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at b₁ b₂
    obtain ⟨rfl, -⟩ := b₁; obtain ⟨rfl, -⟩ := b₂; subst h; exact hi
  | i :: is, fs, fs', s₁, s₂, s₁', s₂', t₁, t₂, h, b₁, b₂, hi => by
    simp only [blk, Option.bind_eq_some_iff] at h
    obtain ⟨g, hg, h⟩ := h
    simp only [execBlock] at b₁ b₂
    split at b₁
    · cases b₁
    · rename_i x₁ hx₁
      split at b₂
      · cases b₂
      · rename_i x₂ hx₂
        simp only [Option.map_eq_some_iff] at b₁ b₂
        obtain ⟨⟨u₁, v₁⟩, c₁, d₁⟩ := b₁
        obtain ⟨⟨u₂, v₂⟩, c₂, d₂⟩ := b₂
        simp only [Prod.mk.injEq] at d₁ d₂
        obtain ⟨rfl, -⟩ := d₁; obtain ⟨rfl, -⟩ := d₂
        exact blk_ok h c₁ c₂ (step_ok hg hx₁ hx₂ hi)

/-- The facts after a loop, from an invariant `I`: some of the facts before
it, which its body keeps. -/
def LoopOk : Prog isa → List F → List F → Prop
  | .loop b _, fs, g => ∃ I : List F, I.all fs.contains = true ∧ mx b I = some g ∧ I.all g.contains = true
  | _, _, _ => False

theorem loopOk_of {b : Prog isa} {c : Cond} {fs g : List F} (h : mx (.loop b c) fs = some g) :
    LoopOk (.loop b c) fs g := by
  simp only [mx] at h
  have hn : ∀ g', mx b [] = some g' → LoopOk (.loop b c) fs g' := fun g' h' => ⟨[], rfl, h', rfl⟩
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i g₃ h₃
        split at h
        · rename_i hs
          cases h
          refine ⟨_, ?_, h₃, hs⟩
          simp only [List.all_eq_true, List.contains_iff_mem, List.mem_filter]
          exact fun _ h => h.1.1
        · exact hn _ h
      · exact hn _ h

theorem call_mx {s s₁ : State} (h : isa.call s = some s₁) : s₁.mxcsr = s.mxcsr := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_mx {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.mxcsr = s₂.mxcsr := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

/-- The facts on registers other than `rsp` survive what keeps those registers. -/
theorem regs_inv {fs : List F} {a₁ a₂ b₁ b₂ : State} (hm₁ : b₁.mxcsr = a₁.mxcsr) (hm₂ : b₂.mxcsr = a₂.mxcsr)
    (hg₁ : ∀ r, r ≠ .rsp → b₁.gpr r = a₁.gpr r) (hg₂ : ∀ r, r ≠ .rsp → b₂.gpr r = a₂.gpr r)
    (hi : Inv fs a₁ a₂) : Inv (regs fs) b₁ b₂ := by
  refine ⟨by rw [hm₁, hm₂, hi.1], fun f hf => ?_⟩
  obtain ⟨hf, hk⟩ := List.mem_filter.mp hf
  cases f with
  | reg r =>
    have hr : r ≠ .rsp := by simpa using hk
    simp only [Hold, hg₁ r hr, hg₂ r hr]; exact hi.2 _ hf
  | slot _ _ => simp at hk

/-- Two runs of `c` whose traces agree, extended by `r₁` and `r₂`, from
states that agree on MXCSR and the facts `fs`: their traces are the same,
and they agree on MXCSR and the facts after `c`. -/
theorem mx_ok {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      ∀ fs fs', (mx c fs = some fs' ∨ LoopOk c fs fs') → Inv fs s₁ s₂ → t₁ = t₂ ∧ Inv fs' s₁' s₂' := by
  induction e₁ with
  | block h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false] at hc
    cases e₂ with
    | block h₂ =>
      have hl := (execBlock_length h₁).trans (execBlock_length h₂).symm
      exact ⟨(UpperLock.append_cancel hl ht).1, blk_ok hc h₁ h₂ hi⟩
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx, Option.bind_eq_some_iff] at hc
    obtain ⟨g, hg, hc⟩ := hc
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨hx, ix⟩ := ihx x₂ ht fs g (.inl hg) hi
      subst hx
      obtain ⟨hy, iy⟩ := ihy y₂ (List.append_cancel_left ht) g fs' (.inl hc) ix
      subst hy
      exact ⟨rfl, iy⟩
  | iteT hc₁ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx] at hc
    split at hc
    · rename_i a b ha hb
      cases hc
      cases e₂ with
      | iteT _ x₂ =>
        simp only [List.cons_append, List.cons.injEq, true_and] at ht
        obtain ⟨h, i'⟩ := ih x₂ ht fs a (.inl ha) hi
        exact ⟨by rw [h], inv_sub (fun f hf => (List.mem_filter.mp hf).1) i'⟩
      | iteF _ _ => exact (UpperLock.branch_ne ht).elim
    · cases hc
  | iteF hc₁ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx] at hc
    split at hc
    · rename_i a b ha hb
      cases hc
      cases e₂ with
      | iteF _ x₂ =>
        simp only [List.cons_append, List.cons.injEq, true_and] at ht
        obtain ⟨h, i'⟩ := ih x₂ ht fs b (.inl hb) hi
        refine ⟨by rw [h], inv_sub (fun f hf => ?_) i'⟩
        have := (List.mem_filter.mp hf).2
        simpa using this
      | iteT _ _ => exact (UpperLock.branch_ne ht.symm).elim
    · cases hc
  | loopExit x₁ hc₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    obtain ⟨I, hI, hb, -⟩ : LoopOk _ fs fs' := hc.elim loopOk_of id
    have hi' := inv_sub (mem_of_all hI) hi
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, i'⟩ := ih x₂ ht I fs' (.inl hb) hi'
      subst h
      exact ⟨rfl, i'⟩
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ih x₂ ht I fs' (.inl hb) hi'
      subst h
      simp at ht
  | loopNext x₁ hc₁ l₁ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    obtain ⟨I, hI, hb, hIg⟩ : LoopOk _ fs fs' := hc.elim loopOk_of id
    have hi' := inv_sub (mem_of_all hI) hi
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ihx x₂ ht I fs' (.inl hb) hi'
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, ix⟩ := ihx x₂ ht I fs' (.inl hb) hi'
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨h', il⟩ := ihl l₂ ht' fs' fs' (.inr ⟨I, hIg, hb, hIg⟩) ix
      subst h'
      exact ⟨rfl, il⟩
  | call hc₁ x₁ hr₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx, Option.map_eq_some_iff] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      have ht0 := ht
      simp only [List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.cons.injEq] at ht
      have hin := regs_inv (call_mx hc₁) (call_mx hc₂)
        (fun r hr => by rw [call_gpr hc₁ r, ite_eq_right hr]) (fun r hr => by rw [call_gpr hc₂ r, ite_eq_right hr]) hi
      obtain ⟨h, i'⟩ := ih x₂ ht.2 _ g (.inl hg) hin
      subst h
      refine ⟨(UpperLock.append_cancel (by simp) ht0).1, regs_inv (ret_mx hr₁) (ret_mx hr₂)
        (fun r hr => by rw [(ret_gpr hr₁ r).2, ite_eq_right hr]) (fun r hr => by rw [(ret_gpr hr₂ r).2, ite_eq_right hr]) ?_⟩
      exact ⟨i'.1, fun f hf => i'.2 f hf⟩
  | @frame i j _ _ _ _ _ _ hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx, Option.map_eq_some_iff] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      have ht0 := ht
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := UpperLock.append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      obtain ⟨k₁, -, -, pg₁, -⟩ := push_eq hp₁
      obtain ⟨k₂, -, -, pg₂, -⟩ := push_eq hp₂
      obtain ⟨-, -, -, qg₁, -⟩ := pop_eq hq₁
      obtain ⟨-, -, -, qg₂, -⟩ := pop_eq hq₂
      have hin := regs_inv (push_mxcsr hp₁) (push_mxcsr hp₂) pg₁ pg₂ hi
      obtain ⟨h, i'⟩ := ih x₂ ht _ g (.inl hg) hin
      subst h
      refine ⟨(UpperLock.append_cancel ?_ ht0).1, ⟨by rw [pop_mxcsr hq₁, pop_mxcsr hq₂, i'.1], fun f hf => ?_⟩⟩
      · simp only [List.length_append, List.length_map, addrs_length _ _ State.zero]
      · obtain ⟨hf, hk⟩ := List.mem_filter.mp hf
        obtain ⟨hf, hj⟩ := List.mem_filter.mp hf
        cases f with
        | reg r =>
          have hr : r ≠ .rsp := by simpa using hk
          have hc : Taint.clobbers j r = false := by simpa [keep] using hj
          simp only [Hold, qg₁ r hr hc, qg₂ r hr hc]; exact i'.2 _ hf
        | slot _ _ => simp at hk
  | icall _ _ _ _ _ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx, reduceCtorEq] at hc
  | icallNext _ _ _ _ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht fs fs' hc hi
    simp only [LoopOk, or_false, mx, reduceCtorEq] at hc

/-- Code whose every `ldmxcsr` loads what `mx` follows leaves the same
MXCSR in two runs along the same trace from the same MXCSR. -/
theorem mxSame_of {c : Prog isa} (h : (mx c []).isSome = true) : MxSame c := by
  intro s₁ s₂ t s₁' s₂' e₁ e₂ hm
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp h
  exact (mx_ok e₁ e₂ (r₁ := []) (r₂ := []) rfl [] g (.inl hg) ⟨hm, fun _ h => by cases h⟩).2.1

end Mx

/-- `r`, scrubbed as `scrubRegE` does, but without `mxFix` (`scrub`'s `f`
below `evex`), for code that leaves the same MXCSR in two runs along the
same trace (`hmx`): at the level `evex` too, which then clears every SSE
register (`hxe`), and needs no stack of its own. -/
def scrubRegF {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : MxSame r.code)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hw : r.written = []) (hxe : v = .evex → ∀ x, x ∈ xsOf r.code ks) : Registration api target :=
  have main : Verified target (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code .avx) r.contract ∧
      NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
        (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code .avx) r.contract
        (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    exact Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8)
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun _ => hmx) hrb' hp hr (tailOk_of _ _ _)
      (xs_of _ _) hxe (fun _ _ e => absurd e (by decide)) (gs_of _ _)
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code .avx
    contract := r.contract
    verified := main.1
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith
    residue := some ⟨main.2⟩ }

/-- The level `scrubRegF` clears the vector registers at for `code`: as
`levelFor`, or `evex` for code that writes `zmm16`–`zmm31`. -/
def levelForE (code : Prog isa) : VecLevel :=
  if code.all (fun i => decide (i.vecLevelR ≤ VecLevel.avx.level)) then levelFor code else .evex

/-- `r` with every granule of its stack wiped and the vector registers
cleared at the level `levelForE` of its code, for code that leaves the same
MXCSR in two runs along the same trace (`hmx`), if `scrubRegF`'s side
conditions hold and the clearing needs no CPU feature its code does not;
otherwise `r` itself. -/
def withScrubAllF {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hmx : MxSame r.code) : Registration api target :=
  let v := levelForE r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if hx : v = .evex → r.code.all (fun i => !writesVec i) = false then
    let r' := scrubRegF r v (allKs (chunks r.stack)) hd hst h8 hlv hmx hrb hpost (resOk_all _ _ h8) hw
      (fun e x => by unfold xsOf; rw [hx e]; exact mem_xregs x)
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r

/-- `r` with every granule of its stack wiped and the vector registers
cleared at the level `levelForE` of its code (`withScrubAllF`), if every
`ldmxcsr` in it loads what `Mx.mx` follows, so that it leaves the same MXCSR
in two runs along the same trace (`Mx.mxSame_of`); otherwise `r` itself. -/
def withScrubAllR {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  if hmx : (Mx.mx r.code []).isSome = true then withScrubAllF r hpost (Mx.mxSame_of hmx) else r

/-- `withScrubAllR` where it applies, else `Scrub.withScrubAll`. -/
def withScrubAllM {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let r' := withScrubAllR r hpost
  if r'.residue.isSome then r' else withScrubAll r hpost

/-- `withScrubOrAll`, with `withScrubAllM` where the instance has no analysis. -/
def withScrubOrAllM {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | some a => withScrub r hpost pubs hpub (some a)
  | none => withScrubAllM r hpost

/-- `withScrub` where its side conditions hold; otherwise, for code whose
every `ldmxcsr` loads what `Mx.mx` follows, the same clearing without
`mxFix` (`scrubRegF`, as `withScrubAllF` does) at the level `levelForE` of
its code, wiping the granules the residue analysis `a` finds may hold
secrets, if the clearing needs no CPU feature the code does not; otherwise
`r` itself. -/
def withScrubM {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  let r₁ := withScrub r hpost pubs hpub a
  if r₁.residue.isSome then r₁ else
  match a with
  | none => r
  | some a =>
    let v := levelForE r.code
    if hfit : pubsFit api.sig pubs = true then
    if hmx : (Mx.mx r.code []).isSome = true then
    if hd : r.code.x86_64Depth ≤ r.stack then
    if hst : r.stack + 8 < 2 ^ 64 then
    if h8 : r.stack % 8 = 0 then
    if hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true then
    if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
        api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
    if hw : r.written = [] then
    if hx : v = .evex → r.code.all (fun i => !writesVec i) = false then
      let r₂ := scrubRegF r v a.ks hd hst h8 hlv (Mx.mxSame_of hmx) hrb hpost
        (by obtain ⟨_, hc⟩ := a.ok; exact resOk_reg r a.ks hfit hpub hc) hw
        (fun e x => by unfold xsOf; rw [hx e]; exact mem_xregs x)
      if (Code.requiresDedup isa.requires r₂.code).all
          (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r₂ else r
    else r else r else r else r else r else r else r else r else r

end VG.X86_64.RScrub
