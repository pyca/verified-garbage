module

-- separate module: a taint domain for any RISC-V code that keeps public values in its frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Slots
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Taint tracking for RISC-V, with a public stack frame

Untrusted: everything here is checked by Lean.

`VG.RISCV64.taint` keeps memory secret, so a value saved to the stack and
loaded back is secret, even when it is the same in both runs (a loop count, a
parameter). This domain adds *public bytes* of the frame that `s3` points
to: bit `k` of `slots` says that the byte at `s3 + k` (for `k` below
`window`) is the same in both runs. A load through `s3` of bytes that are
all public gives a public value. A store through `s3` within the window
makes the bytes it writes public or secret, as its value; a store through
another register keeps the slots only if its value and `s3` are public
(then both runs write the same value to the same address), and otherwise
forgets them all, since it may write the frame. Writing `s3` forgets them
too.
-/

@[expose] public section

namespace VG.RISCV64.FrameTaint

open VG.RISCV64.Taint (pub set)

/-- The bytes `[s3, s3 + window)` are tracked. -/
def window : Nat := 4096

structure T where
  regs : RegSet Reg
  slots : Nat := 0
  deriving DecidableEq, Lean.ToExpr

/-- Whether the `w` bytes at `s3 + d` are all public. -/
def covers (S d w : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight S d) (Nat.sub (Nat.pow 2 w) 1))
  (Nat.sub (Nat.pow 2 w) 1)

/-- The bytes `[d, d + w)` made public (`p`) or secret. -/
def setBits (S d w : Nat) (p : Bool) : Nat :=
  if p then Nat.lor S (Slots.bits d w) else Nat.xor S (Nat.land S (Slots.bits d w))

/-- `d` written, public iff `p`. -/
def wr (τ : T) (d : Reg) (p : Bool) : T :=
  ⟨set τ.regs d p, if d = .s3 then 0 else τ.slots⟩

/-- A store of `w` bytes through `n` at offset `off`, of a value public iff `p`. -/
def store (τ : T) (n : Reg) (off w : Nat) (p : Bool) : T :=
  if n = .s3 ∧ off + w < window then ⟨τ.regs, setBits τ.slots off w p⟩
  else ⟨τ.regs, if p && pub τ.regs .s3 then τ.slots else 0⟩

/-- The value of a load of `w` bytes through `n` at offset `off` is public. -/
def loadPub (τ : T) (n : Reg) (off w : Nat) : Bool :=
  decide (n = .s3) && decide (off + w ≤ window) && covers τ.slots off w

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  Taint.Agree τ.regs s₁ s₂ ∧ ∀ k < window, τ.slots.testBit k = true →
    s₁.mem (s₁.gpr .s3 + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .s3 + BitVec.ofNat 64 k)

def step (τ : T) : Instr → Option T
  | .add d n m | .sub d n m | .addw d n m | .subw d n m | .sltu d n m | .mul d n m
  | .mulhu d n m | .logic _ d n m | .shiftReg _ _ d n m =>
    some (wr τ d (pub τ.regs n && pub τ.regs m))
  | .addi d n _ | .addiw d n _ | .logicImm _ d n _ | .shift _ _ d n _ => some (wr τ d (pub τ.regs n))
  | .li d _ | .lui d _ | .addSp d _ => some (wr τ d true)
  | .load wd t n off => if pub τ.regs n then some (wr τ t (loadPub τ n off wd.bytes)) else none
  | .store wd t n off => if pub τ.regs n then some (store τ n off wd.bytes (pub τ.regs t)) else none
  | .lla d _ => some (wr τ d false)
  | .push .. | .pop .. | .alloc .. | .free .. => none

def condPub (τ : T) (c : Cond) : Bool := Taint.condPub τ.regs c

/-! ## Soundness -/
theorem covers_testBit {S d w : Nat} (h : covers S d w = true) {j : Nat} (hj : j < w) :
    S.testBit (d + j) = true := by
  unfold covers at h
  have e := Nat.eq_of_beq_eq_true h
  change (S >>> d) &&& (2 ^ w - 1) = 2 ^ w - 1 at e
  have := congrArg (fun x => Nat.testBit x j) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, decide_eq_true hj,
    Bool.and_true] at this
  exact this

theorem testBit_setBits_out {S d w k : Nat} (p : Bool) (h : ¬(d ≤ k ∧ k < d + w)) :
    (setBits S d w p).testBit k = S.testBit k := by
  have hb : (Slots.bits d w).testBit k = false := by
    rw [Slots.testBit_bits]; simpa using h
  unfold setBits
  cases p
  · show (Nat.xor S (Nat.land S (Slots.bits d w))).testBit k = _
    rw [show Nat.xor S (Nat.land S (Slots.bits d w)) = S ^^^ (S &&& Slots.bits d w) from rfl,
      Nat.testBit_xor, Nat.testBit_and, hb]
    simp
  · show (Nat.lor S (Slots.bits d w)).testBit k = _
    rw [show Nat.lor S (Slots.bits d w) = S ||| Slots.bits d w from rfl, Nat.testBit_or, hb]
    simp

theorem testBit_setBits_in {S d w k : Nat} (p : Bool) (h : d ≤ k ∧ k < d + w) :
    (setBits S d w p).testBit k = p := by
  have hb : (Slots.bits d w).testBit k = true := by
    rw [Slots.testBit_bits]; simpa using h
  unfold setBits
  cases p
  · show (Nat.xor S (Nat.land S (Slots.bits d w))).testBit k = _
    rw [show Nat.xor S (Nat.land S (Slots.bits d w)) = S ^^^ (S &&& Slots.bits d w) from rfl,
      Nat.testBit_xor, Nat.testBit_and, hb]
    cases S.testBit k <;> rfl
  · show (Nat.lor S (Slots.bits d w)).testBit k = _
    rw [show Nat.lor S (Slots.bits d w) = S ||| Slots.bits d w from rfl, Nat.testBit_or, hb]
    simp

theorem Agree.write {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    Agree (wr τ d p) (s₁.write d v₁) (s₂.write d v₂) := by
  refine ⟨Taint.Agree.write h.1 d hv, fun k hk hb => ?_⟩
  simp only [wr] at hb
  by_cases hd : d = .s3
  · simp [hd] at hb
  · rw [ite_eq_right hd] at hb
    have e₁ : (s₁.write d v₁).gpr .s3 = s₁.gpr .s3 := by simp [State.write, Ne.symm hd]
    have e₂ : (s₂.write d v₂).gpr .s3 = s₂.gpr .s3 := by simp [State.write, Ne.symm hd]
    simp only [State.write] at e₁ e₂ ⊢
    rw [e₁, e₂]
    exact h.2 k hk hb

/-- The byte at `s3 + k`, as a byte of an access at `s3 + off`. -/
theorem sub_off {r : Addr} {k off w : Nat} (hk : k < window) (ho : off + w < window) :
    ((r + BitVec.ofNat 64 k - (r + BitVec.ofNat 64 off)).toNat < w ↔ off ≤ k ∧ k < off + w) := by
  rw [Offset.add_sub_add_left]
  simp only [window] at hk ho
  constructor
  · intro h
    refine Decidable.byContradiction fun c => ?_
    exact Offset.not_lt_sub_ofNat (n := w) (by omega) (by omega) (by omega) (by omega) h
  · rintro ⟨c, d⟩
    rw [Offset.ofNat_sub_ofNat c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

theorem read_eq {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {n : Reg} {off w : Nat}
    (hn : pub τ.regs n = true) (hp : loadPub τ n off w = true) :
    s₁.mem.read (s₁.gpr n + BitVec.ofNat 64 off) w = s₂.mem.read (s₂.gpr n + BitVec.ofNat 64 off) w := by
  simp only [loadPub, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨rfl, hw⟩, hc⟩ := hp
  rw [h.1.reg hn]
  refine Mem.read_congr fun i hi => ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have := h.2 (off + i) (by omega) (covers_testBit hc hi)
  rwa [h.1.reg hn] at this

/-- A store keeps `Agree` with the slots `store` gives. -/
theorem store_sound {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {n : Reg} {off w : Nat}
    (hn : pub τ.regs n = true) {p : Bool} {v₁ v₂ : BitVec (8 * w)} (hv : p = true → v₁ = v₂) :
    Agree (store τ n off w p) { s₁ with mem := s₁.mem.write (s₁.gpr n + BitVec.ofNat 64 off) w v₁ }
      { s₂ with mem := s₂.mem.write (s₂.gpr n + BitVec.ofNat 64 off) w v₂ } := by
  have ha : s₁.gpr n = s₂.gpr n := h.1.reg hn
  unfold store
  split
  · rename_i c
    obtain ⟨rfl, hw⟩ := c
    refine ⟨h.1, fun k hk hb => ?_⟩
    simp only [Mem.write]
    have so := sub_off (w := w) (k := k) (off := off) (r := s₁.gpr .s3) hk hw
    have so₂ := sub_off (w := w) (k := k) (off := off) (r := s₂.gpr .s3) hk hw
    by_cases r : off ≤ k ∧ k < off + w
    · rw [testBit_setBits_in p r] at hb
      rw [ite_eq_left (so.mpr r), ite_eq_left (so₂.mpr r), hv hb, Offset.add_sub_add_left,
        Offset.add_sub_add_left]
    · rw [testBit_setBits_out p r] at hb
      rw [ite_eq_right (fun e => r (so.mp e)), ite_eq_right (fun e => r (so₂.mp e))]
      exact h.2 k hk hb
  · refine ⟨h.1, fun k hk hb => ?_⟩
    by_cases q : (p && pub τ.regs .s3) = true
    · rw [ite_eq_left q] at hb
      simp only [Bool.and_eq_true] at q
      have h30 := h.1.reg q.2
      have e := h.2 k hk hb
      rw [h30] at e
      simp only [Mem.write]
      rw [ha, h30, hv q.1, e]
    · rw [ite_eq_right q] at hb
      simp at hb

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop | alloc | free => simp only [step, reduceCtorEq] at hs
  | lla d name =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | addSp d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.write d fun _ => by rw [ha.1.1]⟩
  | add d n m | sub d n m | addw d n m | subw d n m | sltu d n m | mul d n m | mulhu d n m
  | logic op d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.1.reg hp.1, ha.1.reg hp.2]
  | addi d n imm | addiw d n imm | logicImm op d n imm | li d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    first
    | exact ⟨rfl, ha.write d fun hp => by rw [ha.1.reg hp]⟩
    | exact ⟨rfl, ha.write d fun _ => rfl⟩
  | shift op sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    cases sz <;>
    · simp only [exec] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      rename_i h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
      cases e₁; cases e₂
      exact ⟨rfl, ha.write d fun hp => by rw [ha.1.reg hp]⟩
  | shiftReg op sz d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    cases sz <;>
    · simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
      refine ⟨rfl, ha.write d fun hp => ?_⟩
      simp only [Bool.and_eq_true] at hp
      rw [ha.1.reg hp.1, ha.1.reg hp.2]
  | lui d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun _ => rfl⟩
  | load wd t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, addr, State.load, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Option.ite_none_right_eq_some, Option.some.injEq] at e₁ e₂
    obtain ⟨a₁, ⟨-, rfl⟩, v₁, ⟨-, rfl⟩, rfl⟩ := e₁
    obtain ⟨a₂, ⟨-, rfl⟩, v₂, ⟨-, rfl⟩, rfl⟩ := e₂
    exact ha.write t fun hp => by rw [read_eq ha hn hp]
  | store wd t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, addr, State.store, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
      Option.some.injEq] at e₁ e₂
    obtain ⟨a₁, ⟨-, rfl⟩, -, rfl⟩ := e₁
    obtain ⟨a₂, ⟨-, rfl⟩, -, rfl⟩ := e₂
    exact store_sound ha hn fun hp => by rw [ha.1.reg hp]

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : condPub τ c = true) : eval c s₁ = eval c s₂ :=
  Taint.cond_sound ha.1 hc

/-- A frame's push stores to memory: the slots are forgotten. -/
def push (τ : T) : Instr → Option T
  | .push _ | .alloc _ => some ⟨τ.regs, 0⟩
  | _ => none

/-- A frame's pop loads a secret. -/
def pop (τ : T) : Instr → Option T
  | .pop r => some (wr τ r false)
  | .free _ => some τ
  | _ => none

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [push, reduceCtorEq] at hs <;> cases hs <;>
  · simp only [isa, RISCV64.push] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨by simp [addrs, h.1.1], ⟨by simp [h.1.1], h.1.2⟩, fun k _ hb => by simp at hb⟩

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (h : Agree τ b₁ b₂)
    (hs : pop τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [pop, reduceCtorEq] at hs
  case free =>
    cases hs
    simp only [isa, RISCV64.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, ⟨by simp [h.1.1], h.1.2⟩, h.2⟩
  rename_i r
  cases hs
  simp only [isa, RISCV64.pop] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have w := h.write r (v₁ := b₁.mem.read (b₁.sp + 8) 8) (v₂ := b₂.mem.read (b₂.sp + 8) 8)
    (p := false) fun h => by cases h
  exact ⟨by simp [addrs, h.1.1], ⟨by simp [h.1.1], w.1.2⟩, w.2⟩

end VG.RISCV64.FrameTaint

namespace VG.RISCV64

/-- Taint tracking for RISC-V, with public bytes of the frame at `s3`. -/
def frameTaint : VG.Taint isa where
  T := FrameTaint.T
  Agree := FrameTaint.Agree
  step := FrameTaint.step
  step_sound := FrameTaint.step_sound
  condPub := FrameTaint.condPub
  cond_sound := FrameTaint.cond_sound
  meet τ₁ τ₂ := ⟨τ₁.regs.inter τ₂.regs, Nat.land τ₁.slots τ₂.slots⟩
  meet_left h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).1⟩, fun k hk hb => h.2 k hk (by
    rw [show Nat.land _ _ = _ &&& _ from rfl, Nat.testBit_and, Bool.and_eq_true] at hb; exact hb.1)⟩
  meet_right h := ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).2⟩, fun k hk hb => h.2 k hk (by
    rw [show Nat.land _ _ = _ &&& _ from rfl, Nat.testBit_and, Bool.and_eq_true] at hb; exact hb.2)⟩
  le τ σ := τ.regs.subset σ.regs && Nat.beq (Nat.land τ.slots σ.slots) τ.slots
  le_sound hle h := by
    simp only [Bool.and_eq_true] at hle
    refine ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_of_subset hle.1 hr)⟩, fun k hk hb => h.2 k hk ?_⟩
    have e := Nat.eq_of_beq_eq_true hle.2
    rw [← e] at hb
    change Nat.testBit ((_ : Nat) &&& (_ : Nat)) k = true at hb
    rw [Nat.testBit_and, Bool.and_eq_true] at hb
    exact hb.2
  -- A call leaves unknown values in `ra` and `t0`–`t6`, and no memory or
  -- `s3` changes; a return changes nothing.
  call τ := some ⟨Taint.callErase τ.regs, τ.slots⟩
  call_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, ⟨h.1.1, fun r hr => ?_⟩, fun k hk hb => ?_⟩
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hr⟩ := Taint.mem_callErase.mp hr
      cases r <;> first | exact absurd rfl ‹_› | exact h.1.2 _ hr
    · exact h.2 k hk hb
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  push := FrameTaint.push
  push_sound := FrameTaint.push_sound
  pop := FrameTaint.pop
  pop_sound := FrameTaint.pop_sound

end VG.RISCV64
