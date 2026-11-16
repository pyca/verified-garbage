module

import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Passes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.TripleDes.X86_64.Bitsliced
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Machine
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Bytes
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout

/-! ### `TripleDes.X86_64.Bitsliced.BatchIO`, which only this module used -/

section

/-! ### `TripleDes.X86_64.Bitsliced.Copy`, which only this module used -/

section

/-!
# Copying words

`copy_ok`: the loop of `copyBody src dst` copies `n ≥ 1` words from `A` (in
`src`) to `B` (in `dst`), where the two areas do not overlap, and changes
nothing else in memory. `src` and `dst` are `rsi` and `rdi`, in either
order; `rdx` counts the words left.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-- Word `i` from `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

structure CopyPre (A B : Addr) (n : Nat) (s : State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc]
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

structure CopyInv (src dst : Reg) (A B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i < n
  src : s.gpr src = wAt A i
  dst : s.gpr dst = wAt B i
  cnt : s.gpr .rdx = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

structure CopyPost (src dst : Reg) (A B : Addr) (n : Nat) (s₀ s : State) : Prop where
  src : s.gpr src = wAt A n
  dst : s.gpr dst = wAt B n
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega_using [hi]) (by omega_using [hi, hn])

theorem copy_ok {src dst : Reg} (hsd : (src = .rsi ∧ dst = .rdi) ∨ (src = .rdi ∧ dst = .rsi))
    {A B : Addr} {n : Nat} {s₀ : State} (hpre : CopyPre A B n s₀) (s : State) (i : Nat)
    (hs : CopyInv src dst A B n s₀ i s) :
    WP isa (.loop (.block (copyBody src dst)) .ne) s (CopyPost src dst A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => CopyInv src dst A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega_arith]; exact hs, by omega_arith⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  obtain hsrc : src ≠ .rax ∧ src ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain hdst : dst ≠ .rax ∧ dst ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain hsd' : src ≠ dst := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  -- mov rax, [src]
  let v := s₀.mem.readW (wAt A j) 64
  obtain hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  let s₁ := s.setReg .rax v
  obtain e₁ : exec (.mov .rax (.mem { base := src, disp := 0 })) s = some s₁ := by
    obtain hea : s.ea { base := src, disp := 0 } = wAt A j := by
      show s.gpr src + BitVec.ofInt 64 0 = _
      rw [inv.src]; simp; rfl
    obtain hr : InRegions (s.rd ++ s.wr) (wAt A j) 8 := by rw [inv.rd, inv.wr]; exact hpre.read j hj
    simp only [exec, readSrc, State.load64, hea, hr, ite_true, hv, Option.map_some]
    rfl
  -- store [dst], rax
  obtain hea₂ : s₁.ea { base := dst, disp := 0 } = wAt B j := by
    show s₁.gpr dst + BitVec.ofInt 64 0 = _
    simp only [s₁, gpr_setReg_of_ne (s := s) v hdst.1, inv.dst]; simp; rfl
  obtain hw : InRegions s₁.wr (wAt B j) 8 := by
    simp only [s₁, wr_setReg, inv.wr]; exact hpre.write j hj
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (wAt B j) v }
  obtain e₂ : exec (.store { base := dst, disp := 0 } .rax) s₁ = some s₂ := by
    simp only [exec, State.store64, hea₂, hw, ite_true, s₁, gpr_setReg_self]
    rfl
  -- add rsi, 8; add rdi, 8; sub rdx, 1
  obtain e₃ := exec_addImm s₂ .rsi 8
  let s₃ := (arithFlags s₂ (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₂.gpr .rsi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₂.gpr .rsi) ((8 : BitVec 32).signExtend 64)
        (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64))).setReg .rsi
      (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
  obtain e₄ := exec_addImm s₃ .rdi 8
  let s₄ := (arithFlags s₃ (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₃.gpr .rdi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₃.gpr .rdi) ((8 : BitVec 32).signExtend 64)
        (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64))).setReg .rdi
      (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
  let c := s₄.gpr .rdx
  let r := c - (1 : BitVec 32).signExtend 64
  let s₅ := (arithFlags s₄ r (decide (c.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow c ((1 : BitVec 32).signExtend 64) r)).setReg .rdx r
  have e₅ : exec (.alu .sub .rdx (.imm 1)) s₄ = some s₅ := rfl
  obtain run : runBlock isa (copyBody src dst) s = some s₅ := by
    rw [copyBody, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  -- the facts about s₅
  obtain g₅ : ∀ x, x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → x ≠ .rax → s₅.gpr x = s.gpr x := by
    intro x h1 h2 h3 h4
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, h1, h2, h3, h4]
  obtain rsi₅ : s₅.gpr .rsi = s.gpr .rsi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  obtain rdi₅ : s₅.gpr .rdi = s.gpr .rdi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  obtain rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, r, c]
  obtain mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := by
    simp [s₅, s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  obtain rd₅ : s₅.rd = s.rd := by simp [s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  obtain wr₅ : s₅.wr = s.wr := by simp [s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  obtain zf₅ : s₅.zf = some (s.gpr .rdx - 1 == 0) := by
    simp only [s₅, zf_setReg, zf_arithFlags, r, c]
    simp [s₄, s₃, s₂, s₁, gpr_setReg]
  obtain src₅ : s₅.gpr src = wAt A (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rsi₅, inv.src, wAt_succ]
    · rw [rdi₅, inv.src, wAt_succ]
  obtain dst₅ : s₅.gpr dst = wAt B (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rdi₅, inv.dst, wAt_succ]
    · rw [rsi₅, inv.dst, wAt_succ]
  obtain copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact inv.copied x (by omega_arith)
  obtain frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (wAt_in hj hpre.fitA)
  obtain regs₅ : ∀ x, x ≠ .rax → x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → s₅.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => (g₅ x h2 h3 h4 h1).trans (inv.regs x h1 h2 h3 h4)
  obtain cntv : s.gpr .rdx - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [inv.cnt, show n - j = m by omega_arith]
    exact cnt_sub m (by omega_arith)
  by_cases h1 : m = 1
  · left
    refine ⟨?_, ?_⟩
    · show s₅.zf.map (!·) = some false
      rw [zf₅, cntv, h1]; rfl
    · refine ⟨?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd, wr₅.trans inv.wr⟩
      · rw [src₅]; congr 1; omega_arith
      · rw [dst₅]; congr 1; omega_arith
      · intro x hx; exact copied₅ x (by omega_arith)
  · right
    refine ⟨?_, m - 1, by omega_arith, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd,
      wr₅.trans inv.wr⟩, by omega_arith⟩
    · show s₅.zf.map (!·) = some true
      rw [zf₅, cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by have := hpre.fitA; omega_arith)] at this
        omega_arith
      rw [this]; rfl
    · omega_arith
    · rw [src₅]; congr 1; omega_arith
    · rw [dst₅]; congr 1; omega_arith
    · rw [rdx₅, cntv]; congr 1; omega_arith
    · intro x hx; exact copied₅ x (by omega_arith)

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end


/-!
# The start and end of a batch

The batch's size (`batchSize`), the copies of its blocks into and out of
the state words (`copyIn`, `copyOut`), counting the passes
(`passesStart`), and the advance of the data pointer and the count of
blocks left (`batchEnd`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-! ## Storing registers in scratch slots -/

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < 128)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => st p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, sl s' p.1 = s.gpr p.2) ∧ (∀ x < 128, (∀ p ∈ l, p.1 ≠ x) → sl s' x = sl s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    obtain hp := hl p List.mem_cons_self
    obtain e := exec_st (r := p.2) h hp
    let s₁ : State := { s with mem := stMem s p.1 (s.gpr p.2) }
    obtain h₁ : Room s₁ := h.congr rfl rfl
    obtain hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    obtain hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', zf', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', zf', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)),
          sl_st s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)),
        sl_st s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-! ## The batch's size -/

theorem batchSize_ok {s : State} (h : Room s) :
    WP isa batchSize s (fun s' => sl s' batchSlot = BitVec.ofNat 64 (min (sl s leftSlot).toNat 64) ∧
      (∀ x < 128, x ≠ batchSlot → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
  let m := sl s leftSlot
  let s₁ := s.setReg .rax m
  obtain e₁ : exec (ld .rax leftSlot) s = some s₁ := exec_ld h (by decide) .rax
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (64 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((64 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((64 : BitVec 32).signExtend 64) (s₁.gpr .rax - (64 : BitVec 32).signExtend 64))
  obtain run₁ : runBlock isa [ld .rax leftSlot, .alu .cmp .rax (.imm 64)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, cmp_run]
  obtain rax₁ : t₁.gpr .rax = m := by simp [t₁, s₁, gpr_setReg]
  obtain cf₁ : t₁.cf = some (decide (m.toNat < 64)) := by
    simp only [t₁, cf_arithFlags, s₁, gpr_setReg_self]; rfl
  obtain ht₁ : Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg]) (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  -- the value of `rax` after the branch, and the rest
  obtain finish : ∀ t : State, Room t → t.gpr .rax = BitVec.ofNat 64 (min m.toNat 64) →
      (∀ x < 128, sl t x = sl s x) → t.gpr .rcx = s.gpr .rcx → t.gpr .rsp = s.gpr .rsp →
      t.rd = s.rd → t.wr = s.wr → Frame [scratchR s] s.mem t.mem →
      WP isa (.block [st batchSlot .rax]) t (fun s' =>
        sl s' batchSlot = BitVec.ofNat 64 (min (sl s leftSlot).toNat 64) ∧
        (∀ x < 128, x ≠ batchSlot → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
        s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
    intro t ht hrax hsl hc hsp hrd hwr hf
    obtain e := exec_st (r := Reg.rax) ht (by decide : batchSlot < 128)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine ⟨?_, fun x hx hne => ?_, hc, hsp, hrd, hwr, ?_⟩
    · rw [sl_st t (by decide) _ (by decide)]; simp [hrax, m]
    · rw [sl_st t (by decide) _ hx]; simp [hne, hsl x hx]
    · have f := stMem_frame (s := t) (by decide : batchSlot < 128) (t.gpr .rax)
      rw [show scratchR t = scratchR s by simp only [scratchR, hc]] at f
      exact hf.trans f
  obtain sl₁ : ∀ x < 128, sl t₁ x = sl s x := by
    intro x _; simp only [t₁, sl_arithFlags, s₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  obtain c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  obtain sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  obtain rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  obtain wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  obtain f₁ : Frame [scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  apply WP.seq
  apply WP.ite (decide (m.toNat < 64)) cf₁
  · intro hlt
    apply WP.block_nil
    refine finish t₁ ht₁ ?_ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    rw [rax₁]
    have : m.toNat < 64 := by simpa using hlt
    rw [Nat.min_eq_left (by omega_using [this]), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro hge
    have : ¬ m.toNat < 64 := by simpa using hge
    obtain e := exec_movImm t₁ .rax 64
    let t₂ := t₁.setReg .rax ((64 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨t₂, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine finish t₂ (ht₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])) ?_
      (fun x hx => by simp only [t₂, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]; exact sl₁ x hx)
      (by simp [t₂, gpr_setReg, c₁]) (by simp [t₂, gpr_setReg, sp₁]) (by simp [t₂, rd_setReg, rd₁])
      (by simp [t₂, wr_setReg, wr₁]) (by simp only [t₂, mem_setReg]; exact f₁)
    rw [Nat.min_eq_right (by omega_using [this])]
    simp [t₂, gpr_setReg]

/-! ## Copying the batch in and out -/

/-- The state words' area. -/
abbrev stateA (s : State) : Addr := wAt (s.gpr .rcx) 8

theorem wAt_stateA (c : Addr) (j : Nat) : wAt (wAt c 8) j = wordAddr c (stSlot j) := by
  simp only [wAt, wordAddr, stSlot, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega_using []

/-- What the prologue of the copies leaves: the public words in `r8`–`r11`,
the data pointer in `rsi`, the state's in `rdi`, the count in `rdx`. -/
structure KeepPost (s t : State) : Prop where
  r8 : t.gpr .r8 = sl s schedSlot
  r9 : t.gpr .r9 = sl s dataSlot
  r10 : t.gpr .r10 = sl s leftSlot
  r11 : t.gpr .r11 = sl s batchSlot
  rsi : t.gpr .rsi = sl s dataSlot
  rdi : t.gpr .rdi = stateA s
  rdx : t.gpr .rdx = sl s batchSlot
  rcx : t.gpr .rcx = s.gpr .rcx
  rsp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem keep_ok {s : State} (h : Room s) :
    ∃ t, runBlock isa (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]) s
      = some t ∧ KeepPost s t := by
  let t₁ := s.setReg .r8 (sl s schedSlot)
  let t₂ := t₁.setReg .r9 (sl s dataSlot)
  let t₃ := t₂.setReg .r10 (sl s leftSlot)
  let t₄ := t₃.setReg .r11 (sl s batchSlot)
  let t₅ := t₄.setReg .rsi (sl s dataSlot)
  let t₆ := t₅.setReg .rdi (s.gpr .rcx)
  obtain e₁ : exec (ld .r8 schedSlot) s = some t₁ := exec_ld h (by decide) .r8
  obtain h₁ : Room t₁ := h.congr (by simp [t₁, gpr_setReg]) (by simp [t₁, wr_setReg])
  obtain e₂ : exec (ld .r9 dataSlot) t₁ = some t₂ := by
    rw [exec_ld h₁ (by decide) .r9, sl_setReg _ (by decide)]
  obtain h₂ : Room t₂ := h₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])
  obtain e₃ : exec (ld .r10 leftSlot) t₂ = some t₃ := by
    rw [exec_ld h₂ (by decide) .r10, sl_setReg _ (by decide), sl_setReg _ (by decide)]
  obtain h₃ : Room t₃ := h₂.congr (by simp [t₃, gpr_setReg]) (by simp [t₃, wr_setReg])
  obtain e₄ : exec (ld .r11 batchSlot) t₃ = some t₄ := by
    rw [exec_ld h₃ (by decide) .r11, sl_setReg _ (by decide), sl_setReg _ (by decide),
      sl_setReg _ (by decide)]
  obtain e₅ : exec (rr .rsi .r9) t₄ = some t₅ := by
    simp only [rr, exec, readSrc, Option.map_some, t₅]
    simp [t₄, t₃, t₂, gpr_setReg]
  obtain e₆ : exec (rr .rdi .rcx) t₅ = some t₆ := by
    simp only [rr, exec, readSrc, Option.map_some, t₆]
    simp [t₅, t₄, t₃, t₂, t₁, gpr_setReg]
  obtain e₇ := exec_addImm t₆ .rdi 64
  let t₇ := (arithFlags t₆ (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (t₆.gpr .rdi).toNat + ((64 : BitVec 32).signExtend 64).toNat))
      (addOverflow (t₆.gpr .rdi) ((64 : BitVec 32).signExtend 64)
        (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64))).setReg .rdi
      (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
  let t₈ := t₇.setReg .rdx (t₇.gpr .r11)
  have e₈ : exec (rr .rdx .r11) t₇ = some t₈ := rfl
  refine ⟨t₈, ?_, ?_⟩
  · simp only [keepIn, List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
        mem_arithFlags, rd_arithFlags, wr_arithFlags, stateA, wAt]

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

/-- The data words of the batch: readable and writable, apart from the scratch buffer. -/
structure DataOk (s : State) (D : Addr) (k : Nat) : Prop where
  read : ∀ i < k, InRegions (s.rd ++ s.wr) (wAt D i) 8
  write : ∀ i < k, InRegions s.wr (wAt D i) 8
  sep : (⟨D, 8 * k⟩ : Region).Disjoint (scratchR s)
  fit : 8 * k < 2 ^ 64

theorem state_in (s : State) {k : Nat} (hk : k ≤ 64) :
    Region.Sub ⟨stateA s, 8 * k⟩ (scratchR s) := by
  simp only [stateA, wAt, scratchR]
  exact Offset.sub_base _ (by omega_using [hk])

theorem copyIn_ok {s : State} (h : Room s) {k : Nat} (hk : sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : DataOk s (sl s dataSlot) k) :
    WP isa copyIn s (fun s' => (∀ j < k, words s' j = s.mem.readW (wAt (sl s dataSlot) j) 64) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem) := by
  obtain ⟨t, run, kp⟩ := keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  apply WP.seq
  obtain pre : CopyPre (sl s dataSlot) (stateA s) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr]; exact hd.read i hi
    · rw [kp.wr, stateA, wAt_stateA]
      exact ⟨scratchR s, h.scratch, slot_in_scratch s (by unfold stSlot; omega_using [h64, hi])⟩
    · exact (hd.sep.sub_right (state_in s h64))
  obtain inv : CopyInv .rsi .rdi (sl s dataSlot) (stateA s) k t 0 t := by
    refine ⟨by omega_using [h1], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rsi, wAt_zero]
    · rw [kp.rdi, wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (copy_ok (Or.inl ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  obtain hu : Room u := h.congr (by rw [pu.regs _ (by decide) (by decide) (by decide) (by decide), kp.rcx])
    (by rw [pu.wr, kp.wr])
  obtain r8 := pu.regs .r8 (by decide) (by decide) (by decide) (by decide)
  obtain r9 := pu.regs .r9 (by decide) (by decide) (by decide) (by decide)
  obtain r10 := pu.regs .r10 (by decide) (by decide) (by decide) (by decide)
  obtain r11 := pu.regs .r11 (by decide) (by decide) (by decide) (by decide)
  obtain rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  obtain rsp := pu.regs .rsp (by decide) (by decide) (by decide) (by decide)
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ := stores_ok hu
    [(schedSlot, .r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)] (by decide) (by decide)
  refine WP.of_runBlock ⟨v, runv, ?_⟩
  obtain ufr : Frame [scratchR s] s.mem u.mem := by
    rw [← kp.mem]
    exact pu.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scratchR s, List.mem_singleton_self _, state_in s h64⟩
  obtain slu : ∀ x < 128, 72 ≤ x → sl u x = sl s x := by
    intro x hx hl
    simp only [sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [stateA, wAt, wordAddr]
    exact Offset.disjoint _ (by omega_using [h64, hl]) (by omega_using [hx]) (by omega_using [h64])
  obtain wu : ∀ j < k, words u j = s.mem.readW (wAt (sl s dataSlot) j) 64 := by
    intro j hj
    obtain e := pu.copied j hj
    rw [stateA, wAt_stateA, kp.mem] at e
    simp only [words, sl, rcx, kp.rcx]
    exact e
  obtain notIn : ∀ x, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → x ≠ batchSlot →
      ∀ p ∈ [(schedSlot, Reg.r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)], p.1 ≠ x := by
    intro x a b c d p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b;
      exact Ne.symm c; exact Ne.symm d]
  obtain cu : u.gpr .rcx = s.gpr .rcx := rcx.trans kp.rcx
  refine ⟨fun j hj => ?_, fun x hx hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [words]
    rw [keepv _ (by unfold stSlot; omega_using [h64, hj]) (notIn _ (by unfold stSlot schedSlot; omega_using [h64, hj])
      (by unfold stSlot dataSlot; omega_using [h64, hj]) (by unfold stSlot leftSlot; omega_using [h64, hj])
      (by unfold stSlot batchSlot; omega_using [h64, hj]))]
    exact wu j hj
  · by_cases a : x = schedSlot
    · subst a; rw [setv (schedSlot, .r8) (by simp), r8, kp.r8]
    by_cases b : x = dataSlot
    · subst b; rw [setv (dataSlot, .r9) (by simp), r9, kp.r9]
    by_cases c : x = leftSlot
    · subst c; rw [setv (leftSlot, .r10) (by simp), r10, kp.r10]
    by_cases d : x = batchSlot
    · subst d; rw [setv (batchSlot, .r11) (by simp), r11, kp.r11]
    rw [keepv x hx (notIn x a b c d), slu x hx hl]
  · rw [gv, cu]
  · rw [gv, rsp, kp.rsp]
  · rw [rdv, pu.rd, kp.rd]
  · rw [wrv, pu.wr, kp.wr]
  · rw [show scratchR u = scratchR s by simp only [scratchR, cu]] at fv
    exact ufr.trans fv

structure OutPost (s : State) (k : Nat) (s' : State) : Prop where
  data : ∀ j < k, s'.mem.readW (wAt (sl s dataSlot) j) 64 = words s j
  slots : ∀ x < 128, sl s' x = sl s x
  r8 : s'.gpr .r8 = sl s schedSlot
  r10 : s'.gpr .r10 = sl s leftSlot
  r11 : s'.gpr .r11 = sl s batchSlot
  rsi : s'.gpr .rsi = wAt (sl s dataSlot) k
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨sl s dataSlot, 8 * k⟩] s.mem s'.mem

theorem copyOut_ok {s : State} (h : Room s) {k : Nat} (hk : sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : DataOk s (sl s dataSlot) k) :
    WP isa copyOut s (OutPost s k) := by
  obtain ⟨t, run, kp⟩ := keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  obtain pre : CopyPre (stateA s) (sl s dataSlot) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr, stateA, wAt_stateA]
      exact ⟨scratchR s, List.mem_append_right _ h.scratch, slot_in_scratch s (by unfold stSlot; omega_using [h64, hi])⟩
    · rw [kp.wr]; exact hd.write i hi
    · exact (hd.sep.sub_right (state_in s h64)).symm
  obtain inv : CopyInv .rdi .rsi (stateA s) (sl s dataSlot) k t 0 t := by
    refine ⟨by omega_using [h1], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rdi, wAt_zero]
    · rw [kp.rsi, wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (copy_ok (Or.inr ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  obtain rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun j hj => ?_, fun x hx => ?_, ?_, ?_, ?_, pu.dst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pu.copied j hj, kp.mem, stateA, wAt_stateA]; rfl
  · simp only [sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sep.sub_right (Offset.sub_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 1024)
      (by omega_using [hx]))).symm
  · rw [pu.regs .r8 (by decide) (by decide) (by decide) (by decide), kp.r8]
  · rw [pu.regs .r10 (by decide) (by decide) (by decide) (by decide), kp.r10]
  · rw [pu.regs .r11 (by decide) (by decide) (by decide) (by decide), kp.r11]
  · rw [rcx, kp.rcx]
  · rw [pu.regs .rsp (by decide) (by decide) (by decide) (by decide), kp.rsp]
  · rw [pu.rd, kp.rd]
  · rw [pu.wr, kp.wr]
  · rw [← kp.mem]; exact pu.frame

/-! ## The end of a batch -/

theorem batchEnd_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa batchEnd s = some s' ∧ sl s' schedSlot = s.gpr .r8 ∧
      sl s' dataSlot = s.gpr .rsi ∧ sl s' leftSlot = s.gpr .r10 - s.gpr .r11 ∧
      s'.zf = some (s.gpr .r10 - s.gpr .r11 == 0) ∧
      (∀ x < 128, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → sl s' x = sl s x) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ :=
    stores_ok h [(schedSlot, .r8), (dataSlot, .rsi)] (by decide) (by decide)
  obtain hv : Room v := h.congr (by rw [gv]) wrv
  let d := s.gpr .r10 - s.gpr .r11
  let v₁ := v.setReg .rax (v.gpr .r10)
  have e₁ : exec (rr .rax .r10) v = some v₁ := rfl
  let v₂ := (arithFlags v₁ (v₁.gpr .rax - v₁.gpr .r11) (decide ((v₁.gpr .rax).toNat < (v₁.gpr .r11).toNat))
    (subOverflow (v₁.gpr .rax) (v₁.gpr .r11) (v₁.gpr .rax - v₁.gpr .r11))).setReg .rax
    (v₁.gpr .rax - v₁.gpr .r11)
  have e₂ : exec (.alu .sub .rax (.reg .r11)) v₁ = some v₂ := rfl
  obtain h₂ : Room v₂ := hv.congr (by simp [v₂, v₁, gpr_setReg]) (by simp [v₂, v₁, wr_setReg, wr_arithFlags])
  obtain e₃ := exec_st (r := Reg.rax) h₂ (by decide : leftSlot < 128)
  obtain rax₂ : v₂.gpr .rax = d := by simp [v₂, v₁, gpr_setReg, gv, d]
  refine ⟨{ v₂ with mem := stMem v₂ leftSlot (v₂.gpr .rax) }, ?_, ?_, ?_, ?_, ?_, fun x hx a b c => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show runBlock isa ([st schedSlot .r8, st dataSlot .rsi] ++
      ([rr .rax .r10, .alu .sub .rax (.reg .r11), st leftSlot .rax] : List Instr)) s = _
    exact runBlock_cat_some runv (by
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
        runStep_some, runBlock_nil])
  · rw [sl_st v₂ (by decide) _ (by decide)]
    simp only [show schedSlot ≠ leftSlot by decide, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      sl_arithFlags]
    rw [setv (schedSlot, .r8) (by simp)]
  · rw [sl_st v₂ (by decide) _ (by decide)]
    simp only [show dataSlot ≠ leftSlot by decide, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      sl_arithFlags]
    rw [setv (dataSlot, .rsi) (by simp)]
  · rw [sl_st v₂ (by decide) _ (by decide)]; simp only [ite_true, rax₂, d]
  · simp [v₂, v₁, gpr_setReg, gv]
  · rw [sl_st v₂ (by decide) _ hx]
    simp only [c, ite_false, v₂, v₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx), sl_arithFlags]
    exact keepv x hx (by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b])
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, rd_setReg, rd_arithFlags, rdv]
  · simp [v₂, v₁, wr_setReg, wr_arithFlags, wrv]
  · have f := stMem_frame (s := v₂) (by decide : leftSlot < 128) (v₂.gpr .rax)
    rw [show scratchR v₂ = scratchR s by simp [scratchR, v₂, v₁, gpr_setReg, gv]] at f
    obtain m₂ : v₂.mem = v.mem := by simp [v₂, v₁, mem_setReg, mem_arithFlags]
    rw [m₂] at f
    exact fv.trans f

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end

/-! ### `TripleDes.X86_64.Bitsliced.Transpose`, which only this module used -/

section

/-!
# The transposition of the state, by evaluation

The transposition only moves and XORs bits of the 64 state words (slots
0–63), and masks them with constants: the lane domain evaluates it on
words of atoms (bit `t` of word `i` is atom `64 i + t`), and the check
that bit `p` of word `j` is then atom `64 p + j` proves that it transposes
any 64 words (`transpose_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The spill slots and the state words. -/
def stateCfg : Cfg := { base := .rcx, slots := 72, ext := .rsp, exts := 0 }

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 8 ≤ k ∧ k < 72 then some (inWord (k - 8)) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot (stSlot j) == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    check (lanes 64 12) stateCfg (fun _ => none) (instrs transposeProg.lit) transEnv transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

/-- The spill slots and the state words (slots 0–71). -/
def stateR (s : State) : Region := ⟨s.gpr .rcx, 576⟩

theorem transpose_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ transpose_check
  rw [transpose_code] at he
  obtain hok : Ok stateCfg s :=
    Ok.of_region h.scratch rfl (by show 8 * 72 ≤ 1024; decide) (by decide) rfl
  obtain hrel : Rel (LaneRel 12 (assign (words s) (2 ^ 12))) stateCfg (fun _ => none) transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl => ?_), (fun _ _ hj => ?_)⟩
    swap
    · exact absurd hj (by simp [stateCfg])
    simp only [transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      obtain e : sl s j = words s (j - 8) := by
        simp only [words, stSlot]; rw [show 8 + (j - 8) = j by omega_using [hk]]
      show LaneRel 12 _ _ (s.mem.readW (wordAddr (s.gpr .rcx) j) 64)
      rw [show s.mem.readW (wordAddr (s.gpr .rcx) j) 64 = sl s j from rfl, e]
      exact inWord_rel (words s) (by omega_using [hk])
    · cases hsl
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  obtain hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  obtain hs := p.rel.slot (stSlot j) _ (by unfold stSlot; show 8 + j < 72; omega_using [hj]) (beq_iff_eq.mp hpj)
  obtain bits := outWord_rel (fun q hq a ha => by simp at ha; omega_using [hj, hq, ha]) hs
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hsj : words s' j = s'.mem.readW (wordAddr (s'.gpr stateCfg.base) (stSlot j)) 64 := rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
    decide_true, Bool.true_and]
  exact bitOf_word (words s) b j hj

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end


/-!
# A batch

A batch of `k = min(n, 64)` blocks is copied into the state words,
transposed (lane `b` is then IP of block `b`), put through the three
passes, transposed back and copied out: each block becomes its TDEA
encryption or decryption (`batch_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW)

/-- What ECB does to one block. -/
def blockOut (K : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock K
  | .decrypt => decryptBlock K

theorem ipLane_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ x < 64, W x = W' x) (b : Nat) :
    ipLane W b = ipLane W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht,
    hW _ (VG.Proof.TripleDes.Bitslice.ipWord_lt t ht)]

/-! ## The data words -/

theorem DataOk.congr {s s' : State} {D : Addr} {k : Nat} (h : DataOk s D k)
    (hc : s'.gpr .rcx = s.gpr .rcx) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk s' D k where
  read := by rw [hrd, hwr]; exact h.read
  write := by rw [hwr]; exact h.write
  sep := by simp only [scratchR, hc]; exact h.sep
  fit := h.fit

theorem word_sub {D : Addr} {b k : Nat} (hb : b < k) :
    Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * k⟩ :=
  Offset.sub_base D (by omega_using [hb])

/-- A data word of the batch is unchanged by writes to the scratch buffer. -/
theorem DataOk.readW {s : State} {D : Addr} {k : Nat} (h : DataOk s D k) {b : Nat} (hb : b < k)
    {m m' : Mem} (hf : Frame [scratchR s] m m') : m'.readW (wAt D b) 64 = m.readW (wAt D b) 64 :=
  hf.readW (r := ⟨wAt D b, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_left (word_sub hb))
    (by decide)

/-! ## Transposing -/

theorem state_toScratch {s : State} {m m' : Mem} (h : Frame [stateR s] m m') :
    Frame [scratchR s] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scratchR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem transpose_ok' {s : State} (h : Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s', run, w, rd, wr, c, sp, f⟩ := transpose_ok h
  refine ⟨s', run, w, fun x hx hl => ?_, rd, wr, c, sp, state_toScratch f⟩
  simp only [sl, c]
  refine f.readW (r := ⟨Straight.wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 576) (by omega_using [hl]) (by omega_using [hx])

/-! ## The batch -/

/-- What a batch needs: the scratch buffer, a block left, the batch's data
words, and the schedule's words, readable and apart from the scratch buffer. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  pos : 1 ≤ (sl s leftSlot).toNat
  data : DataOk s (sl s dataSlot) (min (sl s leftSlot).toNat 64)
  sched : ∀ i < 48, Apart s (sl s schedSlot + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨sl s schedSlot, 384⟩ : Region).Disjoint (scratchR s)

structure BatchPost (d : Direction) (s : State) (k : Nat) (s' : State) : Prop where
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ b < k, blockAt s'.mem (wAt (sl s dataSlot) b) =
    blockOut (scheduleAt s.mem (sl s schedSlot)) d (blockAt s.mem (wAt (sl s dataSlot) b))
  data : sl s' dataSlot = wAt (sl s dataSlot) k
  left : sl s' leftSlot = sl s leftSlot - BitVec.ofNat 64 k
  zf : s'.zf = some (sl s leftSlot - BitVec.ofNat 64 k == 0)
  sched : sl s' schedSlot = sl s schedSlot
  saved : ∀ x < 78, 72 ≤ x → sl s' x = sl s x
  frame : Frame [scratchR s, ⟨sl s dataSlot, 8 * k⟩] s.mem s'.mem

/-- The result of a block, from the three passes between IP and FP. -/
theorem blockOut_cores (K : Schedule) (d : Direction) (B : Block) :
    blockOut K d B = encodeBlock (permute fp (match d with
      | .encrypt => VG.Proof.TripleDes.desCore (componentSchedule K 2) .encrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .decrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 0) .encrypt (permute ip (decodeBlock B))))
      | .decrypt => VG.Proof.TripleDes.desCore (componentSchedule K 0) .decrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .encrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 2) .decrypt
              (permute ip (decodeBlock B)))))) := by
  cases d
  · exact VG.Proof.TripleDes.encryptBlock_eq_cores K B
  · exact VG.Proof.TripleDes.decryptBlock_eq_cores K B

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) :
    WP isa (batch d) s (BatchPost d s (min (sl s leftSlot).toNat 64)) := by
  have hpos := h.pos
  generalize hk : min (sl s leftSlot).toNat 64 = k
  obtain hk1 : 1 ≤ k := by omega_using [hpos, hk]
  obtain hk64 : k ≤ 64 := by omega_using [hk]
  obtain hdata : DataOk s (sl s dataSlot) k := hk ▸ h.data
  let D := sl s dataSlot
  let S := sl s schedSlot
  let L : List Region := [scratchR s, ⟨D, 8 * k⟩]
  have inL : scratchR s ∈ L := List.mem_cons_self
  obtain dL : (⟨D, 8 * k⟩ : Region) ∈ L := List.mem_cons_of_mem _ List.mem_cons_self
  rw [batch]
  -- the batch's size
  apply WP.seq
  apply WP.mono (batchSize_ok h.room)
  rintro s₁ ⟨bs₁, sl₁, c₁, sp₁, rd₁, wr₁, f₁⟩
  rw [hk] at bs₁
  obtain h₁ : Room s₁ := h.room.congr c₁ wr₁
  obtain D₁ : sl s₁ dataSlot = D := sl₁ _ (by decide) (by decide)
  -- the copy in
  apply WP.seq
  apply WP.mono (copyIn_ok h₁ bs₁ hk1 hk64 (by rw [D₁]; exact hdata.congr c₁ rd₁ wr₁))
  rintro s₂ ⟨w₂, sl₂, c₂, sp₂, rd₂, wr₂, f₂⟩
  obtain h₂ : Room s₂ := h₁.congr c₂ wr₂
  -- the transposition, and the count of passes
  apply WP.seq
  obtain ⟨t₃, run₃, w₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := transpose_ok' h₂
  obtain ht₃ : Room t₃ := h₂.congr c₃ wr₃
  let u₃ := t₃.setReg .rax ((3 : BitVec 32).signExtend 64)
  obtain hu₃ : Room u₃ := ht₃.congr (by simp [u₃, gpr_setReg]) (by simp [u₃, wr_setReg])
  obtain e₃ := exec_st (r := Reg.rax) hu₃ (by decide : passSlot < 128)
  let s₃ : State := { u₃ with mem := stMem u₃ passSlot (u₃.gpr .rax) }
  refine WP.of_runBlock ⟨s₃, runBlock_cat_some run₃ (by
    rw [passesStart, runBlock_cons, exec_movImm, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil]), ?_⟩
  obtain uc₃ : u₃.gpr .rcx = t₃.gpr .rcx := by simp [u₃, gpr_setReg]
  obtain c₃' : s₃.gpr .rcx = s₂.gpr .rcx := uc₃.trans c₃
  obtain slu₃ : ∀ x < 128, sl s₃ x = if x = passSlot then (3 : BitVec 32).signExtend 64 else sl t₃ x := by
    intro x hx
    rw [sl_st u₃ (by decide) _ hx, sl_setReg _ (by decide)]
    simp [u₃, gpr_setReg]
  obtain h₃ : Room s₃ := hu₃.congr rfl rfl
  obtain rd₃' : s₃.rd = s₂.rd := by simp [s₃, u₃, rd_setReg, rd₃]
  obtain wr₃' : s₃.wr = s₂.wr := by simp [s₃, u₃, wr_setReg, wr₃]
  obtain sp₃' : s₃.gpr .rsp = s₂.gpr .rsp := by simp [s₃, u₃, gpr_setReg, sp₃]
  obtain f₃' : Frame [scratchR s₂] s₂.mem s₃.mem := by
    obtain f := stMem_frame (s := u₃) (by decide : passSlot < 128) (u₃.gpr .rax)
    rw [show scratchR u₃ = scratchR s₂ by simp only [scratchR, uc₃, c₃]] at f
    exact f₃.trans (by simpa only [u₃, mem_setReg] using f)
  obtain words₃ : ∀ j < 64, words s₃ j = transposeW (words s₂) j := by
    intro j hj
    simp only [words]
    obtain hp : stSlot j ≠ passSlot := by unfold stSlot passSlot; omega_using [hj]
    rw [slu₃ _ (by unfold stSlot; omega_using [hj])]
    simp only [hp, ↓reduceIte]
    exact w₃ j hj
  obtain misc₃ : ∀ x < 128, 72 ≤ x → x ≠ passSlot → sl s₃ x = sl s₂ x := by
    intro x hx hl hp
    rw [slu₃ x hx]
    simp only [hp, ↓reduceIte]
    exact sl₃ x hx hl
  -- slots of the batch's start that the passes keep
  obtain keep₃ : ∀ x < 128, 72 ≤ x → x ≠ batchSlot → x ≠ passSlot → sl s₃ x = sl s x := by
    intro x hx hl hb hp
    rw [misc₃ x hx hl hp, sl₂ x hx hl, sl₁ x hx hb]
  obtain S₃ : sl s₃ schedSlot = S := keep₃ _ (by decide) (by decide) (by decide) (by decide)
  obtain cs₃ : s₃.gpr .rcx = s.gpr .rcx := c₃'.trans (c₂.trans c₁)
  obtain rds₃ : s₃.rd = s.rd := rd₃'.trans (rd₂.trans rd₁)
  obtain wrs₃ : s₃.wr = s.wr := wr₃'.trans (wr₂.trans wr₁)
  obtain scr₁ : scratchR s₁ = scratchR s := by simp only [scratchR, c₁]
  obtain scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, c₂, c₁]
  obtain fs₃ : Frame [scratchR s] s.mem s₃.mem := by
    rw [scr₁] at f₂; rw [scr₂] at f₃'
    exact (f₁.trans f₂).trans f₃'
  -- the passes
  apply WP.seq
  obtain hS₃ : ∀ i < 48, Apart s₃ (sl s₃ schedSlot + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [S₃]; exact (h.sched i hi).congr cs₃ rds₃ wrs₃
  obtain inv₃ : PassesInv d s₃ 3 s₃ :=
    ⟨h₃, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl,
      by rw [slu₃ _ (by decide)]; rfl, fun _ _ _ _ _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (passes_ok d hS₃ 3 s₃ inv₃)
  intro s₄ q₄
  have h₄ : Room s₄ := q₄.room
  -- the transposition back
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, sl₅, rd₅, wr₅, c₅, sp₅, f₅⟩ := transpose_ok' h₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain h₅ : Room s₅ := h₄.congr c₅ wr₅
  obtain cs₅ : s₅.gpr .rcx = s.gpr .rcx := c₅.trans (q₄.rcx.trans cs₃)
  obtain rds₅ : s₅.rd = s.rd := rd₅.trans (q₄.rd.trans rds₃)
  obtain wrs₅ : s₅.wr = s.wr := wr₅.trans (q₄.wr.trans wrs₃)
  obtain keep₅ : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
      sl s₅ x = sl s₃ x := fun x hx hl a b c e => (sl₅ x hx hl).trans (q₄.misc x hx hl a b c e)
  obtain D₅ : sl s₅ dataSlot = D := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  obtain B₅ : sl s₅ batchSlot = BitVec.ofNat 64 k := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      misc₃ _ (by decide) (by decide) (by decide), sl₂ _ (by decide) (by decide), bs₁]
  -- the copy out
  apply WP.seq
  apply WP.mono (copyOut_ok h₅ B₅ hk1 hk64 (by rw [D₅]; exact hdata.congr cs₅ rds₅ wrs₅))
  intro s₆ o₆
  obtain h₆ : Room s₆ := h₅.congr o₆.rcx o₆.wr
  -- the end
  obtain ⟨s₇, run₇, sch₇, dat₇, left₇, zf₇, oth₇, c₇, sp₇, rd₇, wr₇, f₇⟩ := batchEnd_ok h₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  obtain cs₆ : s₆.gpr .rcx = s.gpr .rcx := o₆.rcx.trans cs₅
  obtain L₅ : sl s₅ leftSlot = sl s leftSlot := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  obtain diff : s₆.gpr .r10 - s₆.gpr .r11 = sl s leftSlot - BitVec.ofNat 64 k := by
    rw [o₆.r10, o₆.r11, L₅, B₅]
  -- the whole frame
  obtain frame : Frame L s.mem s₇.mem := by
    obtain a : Frame L s.mem s₃.mem := frame_into fs₃ inL
    obtain b : Frame L s₃.mem s₄.mem := by
      have := q₄.frame; simp only [scratchR, cs₃] at this; exact frame_into this inL
    obtain c : Frame L s₄.mem s₅.mem := by
      have := f₅; simp only [scratchR, q₄.rcx, cs₃] at this; exact frame_into this inL
    obtain e : Frame L s₅.mem s₆.mem := by
      have := o₆.frame; rw [D₅] at this; exact frame_into this dL
    obtain g : Frame L s₆.mem s₇.mem := by
      have := f₇; simp only [scratchR, cs₆] at this; exact frame_into this inL
    exact (((a.trans b).trans c).trans e).trans g
  refine ⟨c₇.trans cs₆, sp₇.trans (o₆.rsp.trans (sp₅.trans (q₄.rsp.trans (sp₃'.trans
    (sp₂.trans sp₁))))), rd₇.trans (o₆.rd.trans rds₅), wr₇.trans (o₆.wr.trans wrs₅), ?_,
    by rw [dat₇, o₆.rsi, D₅], by rw [left₇, diff], by rw [zf₇, diff],
    by rw [sch₇, o₆.r8, keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      S₃],
    fun x hx hl => ?_, frame⟩
  · -- every block of the batch
    intro b hb
    obtain hb64 : b < 64 := by omega_using [hk, hb]
    let K₃ := scheduleAt s₃.mem (sl s₃ schedSlot)
    obtain K₃eq : K₃ = scheduleAt s.mem S := by
      simp only [K₃, S₃]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S fs₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep)
    -- lane `b` after the first transposition: IP of the block
    obtain lane₃ : ipLane (words s₃) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_congr words₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb64 fun j hj => ?_
      simp only [words] at w₂ ⊢
      rw [w₂ b hb, D₁, hdata.readW hb f₁]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    obtain word₇ : s₇.mem.readW (wAt D b) 64 = transposeW (words s₄) b := by
      obtain e₇ : s₇.mem.readW (wAt D b) 64 = s₆.mem.readW (wAt D b) 64 := by
        have := (hdata.congr cs₆ (o₆.rd.trans rds₅) (o₆.wr.trans wrs₅)).readW hb f₇
        exact this
      rw [e₇, ← D₅, o₆.data b hb, w₅ b hb64]
    rw [blockOut_cores, ← K₃eq]
    apply blockAt_of_readW
    intro j hj
    rw [word₇, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj, ipLane_congr q₄.words b,
      chain_lane d _ _ hb64, lane₃]
    rfl
  · have ne : ∀ y, 78 ≤ y → x ≠ y := fun y hy e => by omega_using [hpos, hk, hk1, hk64, bs₁, c₁, sp₁, D₁, c₂, sp₂, c₃, sp₃, uc₃, c₃', sp₃', S₃, cs₃, c₅, sp₅, cs₅, D₅, B₅, sch₇, dat₇, left₇, c₇, sp₇, cs₆, L₅, diff, hx, hl, hy, e]
    rw [oth₇ x (by omega_using [hx]) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)), o₆.slots x (by omega_using [hx]),
      keep₅ x (by omega_using [hx]) hl (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)),
      keep₃ x (by omega_using [hx]) hl (ne _ (by decide)) (ne _ (by decide))]

end VG.Proof.TripleDes.X86_64.Bitsliced
