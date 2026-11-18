module

public import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Argon2.AArch64.Memory
public import VerifiedGarbage.Impl.Argon2.AArch64.Parameters
public import VerifiedGarbage.Proof.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Argon2.AArch64.DeriveSaved`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.DeriveFrame`, which this module and modules that import it used -/

section

/-! Compose the saved-register frames and the 272-byte local allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def frameStart (s : State) : List Reg → State
  | [] => allocated 272 s
  | r :: rs => frameStart (pushed r s) rs

def frameEnd (s : State) : List Reg → State
  | [] => freed 272 s
  | r :: rs => popped r (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.sp = (frameStart s rs).sp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).sp = s.sp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · change t.sp + BitVec.ofNat 64 272 = s.sp
      rw [sp]; exact BitVec.sub_add_cancel _ _
    · change t.wr.tail = s.wr
      rw [wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed r s) sp wr
    constructor
    · change (frameEnd t rs).sp + 16 = s.sp
      rw [innerSp]; exact BitVec.sub_add_cancel _ _
    · change (frameEnd t rs).wr.tail = s.wr
      rw [innerWr]; rfl

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

/-- The frames saving `rs` around the allocation of 272 bytes: each pop reads
its register from the body's memory, which the frames inside it, released
before it, do not reach, and the postcondition holds whatever memory `m`
that differs from the body's only in the frames, the `272 + 16 * rs.length`
bytes below the stack pointer, and whatever unknowns `u`. -/
theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.sp = (frameStart s rs).sp ∧ t.wr = (frameStart s rs).wr ∧
        ∀ m u, Frame [below s.sp (272 + 16 * rs.length)] t.mem m →
          Q { frameEnd t rs with mem := m, unknowns := u }) :
    WP isa (Impl.Argon2.AArch64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.alloc (by decide) (by simpa using space) (run.mono fun _ h => h.2.2)
  | cons r rs ih =>
    have pushedBound : (pushed r s).sp.toNat = s.sp.toNat - 16 := by
      change (s.sp - 16).toNat = s.sp.toNat - 16
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        change 16 ≤ s.sp.toNat
        simp only [List.length_cons] at space; omega_using [space])]
      rfl
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega_using [space]
    have hk : 272 + 16 * (r :: rs).length = (272 + 16 * rs.length) + 16 := by
      simp only [List.length_cons]; omega_using []
    have hn : 272 + 16 * rs.length + 16 < 2 ^ 64 := by
      have := s.sp.isLt; simp only [List.length_cons] at space; omega_using [space, this]
    apply WP.frame (by simp only [List.length_cons] at space; omega_using [space])
    apply ih (pushed r s) (fun t => ∀ m u, Frame [⟨s.sp - 16, 16⟩] t.mem m →
      Q { popped r t with mem := m, unknowns := u }) innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    refine ⟨sp, wr, fun m₁ u₁ f₁ m₂ u₂ f₂ => ?_⟩
    rw [hk] at result
    -- The saved register is in this frame, which the inner frames' release
    -- does not reach.
    obtain ⟨esp, -⟩ := frameEnd_metadata (pushed r s) t rs sp wr
    have f₁' : Frame [below (s.sp - 16) (272 + 16 * rs.length)] t.mem m₁ := f₁
    have hslot : m₁.read (frameEnd t rs).sp 8 = (frameEnd t rs).mem.read (frameEnd t rs).sp 8 := by
      rw [esp, frameEnd_mem]
      show m₁.read (s.sp - 16) 8 = t.mem.read (s.sp - 16) 8
      refine f₁'.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) (fun R hR => ?_) (by decide)
      simp only [List.mem_singleton] at hR; subst hR
      exact frame_not_below s.sp hn
    have e : popped r { frameEnd t rs with mem := m₁, unknowns := u₁ } =
        { popped r (frameEnd t rs) with mem := m₁, unknowns := u₁ } := by
      simp only [popped]
      rw [show ({ frameEnd t rs with mem := m₁, unknowns := u₁ } : State).mem.read
          ({ frameEnd t rs with mem := m₁, unknowns := u₁ } : State).sp 8 =
            (frameEnd t rs).mem.read (frameEnd t rs).sp 8 from hslot]
      rfl
    rw [e]
    refine result m₂ u₂ ((Frame.sub f₁' fun R hR => ?_).trans (Frame.sub f₂ fun R hR => ?_))
    · simp only [List.mem_singleton] at hR; subst hR
      exact ⟨_, List.mem_singleton_self _, below_body s.sp _⟩
    · simp only [List.mem_singleton] at hR; subst hR
      exact ⟨_, List.mem_singleton_self _, below_frame s.sp _ hn⟩

end VG.Proof.Argon2.AArch64.Derive

end

end

/-! Merged from `Proof.Argon2.AArch64.DeriveFrameState`. -/

@[expose] public section

section
/-! Exact stack depth and memory modified by the entry-point prologue. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (frameStart s rs).sp = s.sp - BitVec.ofNat 64 (272 + 16 * rs.length) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [frameStart, ih]
    change s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length) = _
    rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.sp - BitVec.ofNat 64 n) (by simp only [List.length_cons]; omega_using [])

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) :
    (frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (pushed x s)

theorem frameStart_rd (s : State) (rs : List Reg) : (frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (pushed r s)

theorem frameStart_frame (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) :
    Frame [below s.sp (272 + 16 * rs.length)] s.mem (frameStart s rs).mem := by
  induction rs generalizing s with
  | nil => exact Frame.refl _ _
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega_using [space]
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega_using [space]
    have outer : Frame [below s.sp 16] s.mem (pushed r s).mem := by
      change Frame [⟨s.sp - 16, 16⟩] s.mem (s.mem.writeW (s.sp - 16) (s.gpr r))
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by simpa only [BitVec.add_zero] using
          Offset.contains_base (s.sp - 16) (d := 0) (n := 8) (k := 16) (by decide) (by decide))
    have inner := ih (pushed r s) innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons]; omega_using []) (by
        have := s.sp.isLt; omega_using [space])⟩
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change Region.Sub ⟨s.sp - 16 - BitVec.ofNat 64 (272 + 16 * rs.length), 272 + 16 * rs.length⟩
        (below s.sp (272 + 16 * (r :: rs).length))
      simp only [List.length_cons, below]
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + (272 + 16 * rs.length) = 272 + 16 * (rs.length + 1) by omega_using []]
      exact Region.sub_prefix (by omega_using [])

end VG.Proof.Argon2.AArch64.Derive
end

/-! Each saved register occupies the low eight bytes of its 16-byte slot. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem frameStart_word (s : State) (rs : List Reg)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat) (j : Nat) (bound : j < rs.length) :
    (frameStart s rs).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    have enough : 16 ≤ s.sp.toNat := by simp only [List.length_cons] at space; omega_using [space]
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      change 272 + 16 * rs.length ≤ (s.sp - 16).toNat
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact enough)]
      change 272 + 16 * rs.length ≤ s.sp.toNat - 16
      simp only [List.length_cons] at space; omega_using [space]
    cases j with
    | zero =>
      have inner := frameStart_frame (pushed r s) rs innerSpace
      have unchanged : (frameStart (pushed r s) rs).mem.readW (pushed r s).sp 64 =
          (pushed r s).mem.readW (pushed r s).sp 64 := inner.readW
        (r := ⟨(pushed r s).sp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := s.sp.isLt
          simp only [List.length_cons] at space; omega_using [space]) (by decide)
      change (frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 = s.gpr r
      change (frameStart (pushed r s) rs).mem.readW (s.sp - 16) 64 =
        (pushed r s).mem.readW (s.sp - 16) 64 at unchanged
      rw [unchanged]
      exact Mem.readW_writeW_self64 ..
    | succ j =>
      have jBound : j < rs.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using bound
      have word := ih (pushed r s) innerSpace j (by simpa using bound)
      change (frameStart (pushed r s) rs).mem.readW
        (s.sp - 16 - BitVec.ofNat 64 (16 * (j + 1))) 64 = s.gpr rs[j] at word
      rw [BitVec.sub_sub, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 + 16 * (j + 1) = 16 * (j + 1 + 1) by omega_using []] at word
      exact word
end VG.Proof.Argon2.AArch64.Derive

end

end

/-! ### `Argon2.AArch64.DeriveAbi`, which this module and modules that import it used -/

section

/-! Decode the reviewed ARM64 contract without requiring normalized upper bits. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.sp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .x0).setWidth 32).toNat ((s.gpr .x5).setWidth 32).toNat
  ((s.gpr .x6).setWidth 32).toNat ((s.gpr .x7).setWidth 32).toNat (abiWord s 72).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨abiWord s 8, (abiWord s 16).toNat⟩, ⟨abiWord s 24, (abiWord s 32).toNat⟩]
def abiMatrix (s : State) : Region := ⟨abiWord s 40, (abiWord s 48).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨abiWord s 56, 16384⟩
def abiOutput (s : State) : Region := ⟨abiWord s 64, (abiWord s 72).toNat⟩
def abiArguments (s : State) : Region := ⟨s.sp, 80⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (abiInputs s).map (·, false) ++ [(abiMatrix s, true), (abiWork s, true), (abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 400 ≤ (s.sp).toNat
  wrap : (s.sp).toNat + 80 ≤ 2 ^ 64
  rd : s.rd = abiInputs s ++ [abiArguments s]
  wr : s.wr = [abiMatrix s, abiWork s, abiOutput s]
  pairs : (abiBuffers s ++ [(abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [below (s.sp) 400],
    ∀ b ∈ abiBuffers s ++ [(abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .x0).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (abiParams s) (s.gpr .x2).toNat (s.gpr .x4).toNat
    (abiWord s 16).toNat (abiWord s 32).toNat
  threads : 1 ≤ ((abiWord s 0).setWidth 32).toNat ∧ ((abiWord s 0).setWidth 32).toNat < 2 ^ 24
  blocks : (abiWord s 48).toNat = (abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.pairedNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  all_goals simp only [BitVec.add_zero] at *
  constructor
  all_goals sig_eval [abiInputs, abiArguments, abiMatrix, abiWork, abiOutput, abiBuffers,
    abiWord, abiParams, below]
  all_goals try simp only [BitVec.add_zero]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.AArch64.Derive

end

end

/-! ### `Argon2.AArch64.Parameters`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.DivideLoop`, which this module and modules that import it used -/

section

/-! # Fixed-time division as a loop

`Divide.loopCode` runs `bit 31` thirty-two times, doubling x0 after each step
so that step `k` takes bit `31 - k` of the numerator, and counts x15 down. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

/-- `changed`, and the consumed numerator and the counter. -/
def loopChanged : List Reg := [.x3, .x4, .x6, .x8, .x5, .x9, .x0, .x15]

/-- After `k` steps, of the numerator and divisor in `s₀`. -/
structure LoopInv (s₀ : State) (k : Nat) (s : State) : Prop where
  bound : k ≤ 32
  shifted : (s.gpr .x0).toNat = (s₀.gpr .x0).toNat * 2 ^ k
  divisor : s.gpr .x1 = s₀.gpr .x1
  count : s.gpr .x15 = BitVec.ofNat 64 (32 - k)
  remainder : (s.gpr .x4).toNat < (s₀.gpr .x1).toNat
  equation : (s₀.gpr .x0).toNat / 2 ^ (32 - k) =
    (s.gpr .x5).toNat * (s₀.gpr .x1).toNat + (s.gpr .x4).toNat
  keeps : Keeps loopChanged s₀ s

theorem advance_ok (s : State) :
    WP isa (.block loopAdvance) s fun t =>
      t.gpr .x0 = s.gpr .x0 + s.gpr .x0 ∧ t.gpr .x15 = s.gpr .x15 - 1 ∧
      Keeps [.x0, .x15] s t := by
  apply WP.of_runBlock
  simp only [loopAdvance, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 1 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · rfl
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

/-- Bit 31 of the shifted numerator is the numerator's bit `31 - k`. -/
theorem shifted_bit (x : BitVec 64) (N k : Nat) (hk : k < 32) (hx : x.toNat = N * 2 ^ k) :
    (x.getLsbD 31).toNat = N / 2 ^ (31 - k) % 2 := by
  rw [← BitVec.testBit_toNat, Nat.toNat_testBit, hx,
    show 2 ^ 31 = 2 ^ (31 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega_using [hk],
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]

theorem prefix_split (N k : Nat) (hk : k < 32) :
    N / 2 ^ (32 - (k + 1)) = 2 * (N / 2 ^ (32 - k)) + N / 2 ^ (31 - k) % 2 := by
  have h := Nat.mod_add_div (N / 2 ^ (31 - k)) 2
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (31 - k).succ = 32 - k by omega_using [hk]] at h
  rw [show 32 - (k + 1) = 31 - k by omega_using []]
  omega_using [h]

theorem loopBody_ok (s₀ : State) (hn : (s₀.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s₀.gpr .x1).toNat) (hd' : (s₀.gpr .x1).toNat < 2 ^ 32)
    (k : Nat) (hk : k < 32) (s : State) (h : LoopInv s₀ k s) :
    WP isa loopBody s (LoopInv s₀ (k + 1)) := by
  have hqmul := Nat.le_mul_of_pos_right (s.gpr .x5).toNat hd
  have hprefix := Nat.div_le_self (s₀.gpr .x0).toNat (2 ^ (32 - k))
  have he := h.equation
  have hq : (s.gpr .x5).toNat < 2 ^ 32 := by omega_using [hn, hqmul, hprefix, he]
  have hr : (s.gpr .x4).toNat < 2 ^ 32 := Nat.lt_trans h.remainder hd'
  unfold loopBody
  refine WP.seq ((bit_ok s 31 (by decide) hr hq (by rw [h.divisor]; exact hd')).mono ?_)
  rintro a ⟨ha4, ha5, ka⟩
  refine (advance_ok a).mono ?_
  rintro t ⟨dbl, cnt, kt⟩
  have bit := shifted_bit (s.gpr .x0) (s₀.gpr .x0).toNat k hk h.shifted
  have hs := VG.Proof.Argon2.divide_step h.equation h.remainder
    (Bool.toNat_le ((s.gpr .x0).getLsbD 31))
  have a0 : a.gpr .x0 = s.gpr .x0 := ka.regs .x0 (by decide)
  have a1 : a.gpr .x1 = s.gpr .x1 := ka.regs .x1 (by decide)
  rw [h.divisor] at ha4 ha5
  refine ⟨by omega_using [hk], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have small : (s₀.gpr .x0).toNat * 2 ^ (k + 1) < 2 ^ 64 := by
      have : 2 ^ (k + 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
      calc (s₀.gpr .x0).toNat * 2 ^ (k + 1) < 2 ^ 32 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_le hn this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by decide
    rw [Nat.pow_succ, ← Nat.mul_assoc] at small
    rw [dbl, a0, BitVec.toNat_add, h.shifted, Nat.mod_eq_of_lt (by omega_using [small]), Nat.pow_succ,
      ← Nat.mul_assoc]
    omega_using []
  · rw [kt.regs .x1 (by decide), a1, h.divisor]
  · rw [cnt, ka.regs .x15 (by decide), h.count,
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hk])]
    congr 1
  · rw [kt.regs .x4 (by decide), ha4]; exact hs.2
  · rw [kt.regs .x4 (by decide), kt.regs .x5 (by decide), ha4, ha5, prefix_split _ k hk, ← bit]
    exact hs.1
  · exact h.keeps.trans ((ka.mono (by decide)).trans (kt.mono (by decide)))

theorem loopSetup_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32) (hd : 0 < (s.gpr .x1).toNat) :
    WP isa (.block loopSetup) s (LoopInv s 0) := by
  apply WP.of_runBlock
  simp only [loopSetup, setup, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, Nat.pow_zero, Nat.mul_one]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; exact hd
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]
    change (s.gpr .x0).toNat / 2 ^ 32 = 0 * (s.gpr .x1).toNat + 0
    rw [Nat.div_eq_of_lt hn, Nat.zero_mul, Nat.zero_add]
  · constructor
    · intro r hr
      simp only [loopChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]
    all_goals rfl

theorem loopCode_ok (s : State) (hn : (s.gpr .x0).toNat < 2 ^ 32)
    (hd : 0 < (s.gpr .x1).toNat) (hd' : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa loopCode s fun t =>
      (t.gpr .x5).toNat = (s.gpr .x0).toNat / (s.gpr .x1).toNat ∧
      (t.gpr .x4).toNat = (s.gpr .x0).toNat % (s.gpr .x1).toNat ∧
      Keeps loopChanged s t := by
  unfold loopCode
  refine WP.seq ((loopSetup_ok s hn hd).mono ?_)
  intro a ha
  refine (WP.loop (M := isa) (fun n u => ∃ k, n = 32 - k ∧ k < 32 ∧ LoopInv s k u) ?_ 32 a
    ⟨0, rfl, by decide, ha⟩)
  rintro n u ⟨k, rfl, hk, h⟩
  refine (loopBody_ok s hn hd hd' k hk u h).mono ?_
  intro t next
  have flag : eval (.nonzero .x .x15) t = some (decide (32 - (k + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, next.count]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ne_eq]
    refine not_congr ⟨fun eq => ?_, fun eq => by rw [eq]; rfl⟩
    have num := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [] : 32 - (k + 1) < 2 ^ 64),
      show (0 : BitVec 64).toNat = 0 from rfl] using num
  by_cases done : k + 1 = 32
  · refine .inl ⟨?_, ?_⟩
    · simpa only [show 32 - (k + 1) = 0 by omega_using [done], ne_eq, not_true_eq_false, decide_false] using flag
    · have he := next.equation
      rw [done, Nat.sub_self, Nat.pow_zero, Nat.div_one] at he
      obtain ⟨hq, hr⟩ := VG.Proof.Argon2.divide_result hd he next.remainder
      exact ⟨hq, hr, next.keeps⟩
  · refine .inr ⟨?_, 32 - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, done], next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega_using [hk, done] : 32 - (k + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.Divide

end

end

/-! Merged from `Proof.Argon2.AArch64.ParametersSteps`. -/

@[expose] public section

section
/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8) :
    WP isa (.block Impl.Argon2.AArch64.Parameters.args) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 176) 64 ∧
      t.gpr .x1 = (s.mem.readW (off (s.gpr .x19) 184) 64) * 4 ∧ Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    addr, Size.bytes, Size.bits, show 0 < 4096 from by decide,
    show 176 % 8 = 0 ∧ 176 < 4096 * 8 from by decide,
    show 184 % 8 = 0 ∧ 184 < 4096 * 8 from by decide, and_self,
    memoryRead, lanesRead, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.Parameters.finish) s fun t =>
    t.gpr .x21 = s.gpr .x5 * 4 ∧ Divide.Keeps [.x21, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.finish,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, show 0 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
    all_goals rfl

end VG.Proof.Argon2.AArch64.Parameters
end

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .x19) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.x0, .x1, .x15] ++ Divide.changed ++ [.x21, .x15]

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.AArch64.Parameters.code s fun t =>
      t.gpr .x21 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps changed s t := by
  unfold Impl.Argon2.AArch64.Parameters.code
  refine WP.seq ((args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .x1 = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .x0).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega_using [lanesBound]
  have d : (a.gpr .x1).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.loopCode_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega_using [positive]) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .x5 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [changed])).trans
    ((kb.mono (by simp only [changed, Divide.changed, Divide.loopChanged]; decide)).trans (kt.mono (by simp [changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.AArch64.Parameters

end

end

/-! Merged from `Proof.Argon2.AArch64.DeriveNormalize`. -/

@[expose] public section

section
/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem normalize_ok (s : State) (d : Nat)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.mov32, Impl.Argon2.AArch64.Instructions.store,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    aligned, bound, and_self, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, read, write, BitVec.setWidth_eq,
    BitVec.or_self, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : Normalized s t d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .x19 (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : Normalized s t d) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveStore`. -/
section
/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x r .x19 d]) s (Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store,
    addr, Size.bytes, Size.bits, aligned, bound, and_self, write,
    BitVec.setWidth_eq, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveStores`. -/
section
/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .x19 + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (args.map fun arg => (⟨s.gpr .x19 + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem Saved.other_word {s t : State} {args : List (Nat × Reg)} (h : Saved s t args)
    (e : Nat) (bound : e + 8 ≤ 2 ^ 64)
    (separate : ∀ arg ∈ args, e + 8 ≤ arg.1 ∨ arg.1 + 8 ≤ e)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (encoding : ∀ arg ∈ args, arg.1 % 8 = 0 ∧ arg.1 < 32768)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .str .x arg.2 .x19 arg.1)) s fun t =>
      Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.str .x arg.2 .x19 arg.1] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (encoding arg (List.mem_cons_self ..)).1
      (encoding arg (List.mem_cons_self ..)).2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => encoding a (List.mem_cons_of_mem arg ha)) (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · rw [hu.mem]; unfold saveMemory; rw [ht.regs, ht.mem, List.foldl_cons]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..
    refine ⟨saved, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hu.other_word a.1 (bounds a (List.mem_cons_self ..)) headSep
        (fun b hb => bounds b (List.mem_cons_of_mem a hb))]
      exact ht.word
    · rw [values a ha, ht.regs]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveScratch`. -/
section
/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  regs : ∀ r, r ≠ .x24 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block [.ldr .x .x24 .x19 248]) s (ScratchLoaded s) := by
  refine (Instructions.load_ok s .x24 .x19 248 (by decide) (by decide) read).mono ?_
  rintro t ⟨value, kept⟩
  refine ⟨value, ?_, kept.mem, kept.rd, kept.wr, kept.sp⟩
  intro r hr
  exact kept.regs r (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveEntry`. -/
section
/-! Normalize the four register-passed u32 parameters. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

structure Entered (s t : State) : Prop where
  values : ∀ r ∈ [Reg.x0, .x5, .x6, .x7], t.gpr r = ((s.gpr r).setWidth 32).setWidth 64
  regs : ∀ r, r ∉ [Reg.x0, .x5, .x6, .x7] → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem entry_ok (s : State) :
    WP isa (.block (([.x0, .x5, .x6, .x7] : List Reg).flatMap
      (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r))) s (Entered s) := by
  apply WP.of_runBlock
  simp only [List.flatMap_cons, List.flatMap_nil, Impl.Argon2.AArch64.Instructions.mov32,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, BitVec.or_self, RegUpd.gpr_write,
    reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
end VG.Proof.Argon2.AArch64.Derive
end

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def arguments : List (Nat × Reg) :=
  [(72, .x5), (80, .x4), (88, .x3), (96, .x2), (104, .x1), (112, .x0), (176, .x6), (184, .x7)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r ∈ [Reg.x0, .x5, .x6, .x7] then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : Entered s t) (r : Reg) :
    t.gpr r = argumentValue s r := by
  unfold argumentValue
  split
  · next hr => exact h.values r hr
  · next hr => exact h.regs r hr

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x19, 192⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block Impl.Argon2.AArch64.Derive.setup) s (SetupDone s) := by
  change WP isa (.block ((([.x0, .x5, .x6, .x7] : List Reg).flatMap
    (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r)) ++
    (arguments.map fun arg => .str .x arg.2 .x19 arg.1) ++
    ([.ldr .x .x24 .x19 248] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ arguments, InRegions a.wr (a.gpr .x19 + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.regs .x19 (by decide)]
    apply frameWrite
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega_using [this])⟩
  refine (stores_values_ok arguments a (by decide) write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .x19 = s.gpr .x19 := by rw [saved.regs, entered.regs .x19 (by decide)]
  have scratchWord : b.mem.readW (b.gpr .x19 + 248) 64 = s.mem.readW (s.gpr .x19 + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .x19 + 248) 64 = a.mem.readW (a.gpr .x19 + 248) 64 at kept
    rw [kept, entered.regs .x19 (by decide), entered.mem]
  refine (scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .x19 (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    ?_⟩
  · exact loaded.sp.trans (saved.sp.trans entered.sp)
  · intro arg ha
    rw [loaded.mem, loaded.regs .x19 (by decide), values arg ha]
    exact entered.argument arg.2
  · intro r hr hb hx
    have other : ∀ r ∈ FillCompress.loopRegs, r ∉ [Reg.x0, .x5, .x6, .x7] := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r (other r hr)
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.regs .x19 (by decide)] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DerivePrologue`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DerivePrivatePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DerivePrepare`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveNormalizeArgs`. -/
section
/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = normalizedWord s d
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (ds.map fun d => (⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (encoding : ∀ d ∈ ds, d % 8 = 0 ∧ d < 32768)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.AArch64.Derive.normalizeArgs ds) s (NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (normalize_ok s d (encoding d (by simp)).1 (encoding d (by simp)).2 (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.sp, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((normalize_ok s d (encoding d (List.mem_cons_self ..)).1
        (encoding d (List.mem_cons_self ..)).2 (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t (fun x hx => encoding x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .x19 (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .x19 (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .x19 (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.AArch64.Derive
end

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedOffsets : List Nat := [192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .x19, 192⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : SetupDone s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  normalized : ∀ d ∈ normalizedOffsets, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : Prepared s t) (d : Nat)
    (afterFrame : 192 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 192)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : ∀ d ∈ 248 :: normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ normalizedOffsets, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepareLocal s (Prepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (normalizeArgs_ok normalizedOffsets a (by decide)
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .x19 (by decide)).trans setup.bp,
    normalized.sp.trans setup.sp,
    (normalized.regs .x24 (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ arguments, ∀ d ∈ normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold normalizedWord
    have afterFrame : ∀ d ∈ normalizedOffsets, 192 ≤ d := by decide
    have bound : ∀ d ∈ normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveCopyArgs`. -/
section
/-! Merged from `Proof.Argon2.AArch64.DeriveCopyArg`. -/
section
/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def copySource (j : Nat) : Nat := 384 + 8 * j
def copyDestination (j : Nat) : Nat := 192 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (copyDestination j))
    (s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64)
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem copyArg_ok (s : State) (j : Nat)
    (bound : j < 10) (bp : s.gpr .x19 = s.sp)
    (read : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8)
    (write : InRegions s.wr (s.sp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.AArch64.Derive.copyArg j)) s (CopiedArg s · j) := by
  have sourceAlign : copySource j % 8 = 0 := by unfold copySource; omega_using []
  have sourceBound : copySource j < 32768 := by unfold copySource; omega_using [bound]
  have destAlign : copyDestination j % 8 = 0 := by unfold copyDestination; omega_using []
  have destBound : copyDestination j < 32768 := by unfold copyDestination; omega_using [bound]
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Derive.copyArg,
    show 384 + 8 * j = copySource j from rfl,
    show 192 + 8 * j = copyDestination j from rfl,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    State.store, addr, Size.bytes, Size.bits,
    sourceAlign, sourceBound, destAlign, destBound, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    bp, read, write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem CopiedArg.frame {s t : State} {j : Nat} (h : CopiedArg s t j) :
    Frame [⟨s.sp + BitVec.ofNat 64 (copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : CopiedArg s t j) :
    t.mem.readW (t.sp + BitVec.ofNat 64 (copyDestination j)) 64 =
      s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64 := by
  rw [h.sp, h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.AArch64.Derive
end

/-! Copy all stack arguments without modifying their caller-owned storage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure CopiedArgs (s t : State) (js : List Nat) : Prop where
  values : ∀ j ∈ js, t.mem.readW (t.sp + BitVec.ofNat 64 (copyDestination j)) 64 =
    s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (js.map fun j => (⟨s.sp + BitVec.ofNat 64 (copyDestination j), 8⟩ : Region)) s.mem t.mem

theorem CopiedArgs.other_word {s t : State} {js : List Nat} (h : CopiedArgs s t js)
    (d : Nat) (bound : d + 8 ≤ 2 ^ 64)
    (separate : ∀ j ∈ js, d + 8 ≤ copyDestination j ∨ copyDestination j + 8 ≤ d)
    (bounds : ∀ j ∈ js, copyDestination j + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.sp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 := by
  rw [h.sp]
  apply h.frame.readW (r := ⟨s.sp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate j hj) bound (bounds j hj)

theorem copyArgs_ok (js : List Nat) (s : State) (bp : s.gpr .x19 = s.sp) (bounds : ∀ j ∈ js, j < 10)
    (distinct : js.Nodup)
    (read : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8)
    (write : ∀ j ∈ js, InRegions s.wr (s.sp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (js.flatMap Impl.Argon2.AArch64.Derive.copyArg)) s (CopiedArgs s · js) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons j js ih =>
    have nodup := List.nodup_cons.mp distinct
    have jBound := bounds j (List.mem_cons_self ..)
    have tailBounds : ∀ x ∈ js, x < 10 := fun x hx => bounds x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine (copyArg_ok s j jBound bp (read j (List.mem_cons_self ..)) (write j (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (by rw [ht.regs .x19 (by decide), ht.sp]; exact bp) tailBounds nodup.2
      (fun x hx => by rw [ht.rd, ht.wr, ht.sp]; exact read x (List.mem_cons_of_mem _ hx))
      (fun x hx => by rw [ht.wr, ht.sp]; exact write x (List.mem_cons_of_mem _ hx))).mono ?_
    intro u hu
    refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
      hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hu.other_word (copyDestination x) (by unfold copyDestination; omega_using [jBound]) (by
          intro y hy
          have ne : y ≠ x := fun eq => nodup.1 (eq ▸ hy)
          unfold copyDestination; omega_using [ne]) (by
          intro y hy; have := tailBounds y hy; unfold copyDestination; omega_using [this])]
        exact ht.word
      · rw [hu.values x hx, ht.sp, ht.mem]
        apply Mem.readW_writeW_sep ?_ (by decide)
        have xBound := tailBounds x hx
        exact Offset.sep _ (Or.inr (by unfold copyDestination copySource; omega_using [jBound]))
          (by unfold copySource; omega_using [xBound]) (by unfold copyDestination; omega_using [jBound])
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.sp] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

end VG.Proof.Argon2.AArch64.Derive
end

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def privateWrites (s : State) : List Region := [⟨s.sp, 192⟩, ⟨s.sp + 192, 80⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .x19 = s.sp
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.sp + 440) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  stackWords : ∀ j < 10, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (copyDestination j)) 64 =
    let w := s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64
    if j < 1 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (privateWrites s) s.mem t.mem

theorem private_prepare_local_ok (s : State) (bp : s.gpr .x19 = s.sp) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa (.seq (.block Impl.Argon2.AArch64.Derive.copyArgs) Impl.Argon2.AArch64.Derive.prepareLocal) s (PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega_using [hd])⟩
  unfold Impl.Argon2.AArch64.Derive.copyArgs
  refine WP.seq ((copyArgs_ok (List.range 10) s bp
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold copyDestination; omega_using [this]))).mono ?_)
  intro a copied
  have sp := copied.sp
  have base : a.gpr .x19 = s.sp := (copied.regs .x19 (by decide)).trans bp
  refine (prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [base] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 192 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, base]
      have bound : ∀ d ∈ 248 :: normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, base]
      have bound : ∀ d ∈ normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  have copiedValues (j : Nat) (hj : j < 10) :
      a.mem.readW (s.sp + BitVec.ofNat 64 (copyDestination j)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (copySource j)) 64 := by
    have word := copied.values j (List.mem_range.mpr hj)
    rw [sp] at word
    exact word
  refine ⟨prepared.bp.trans base, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 7 (by decide)
    change a.mem.readW (a.sp + 248) 64 = s.mem.readW (s.sp + 440) 64 at word
    rw [prepared.scratch, base]
    rw [sp] at word
    exact word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have notAx : ∀ arg ∈ arguments, arg.2 ≠ .x8 := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 1
    · have slot : ∀ j < 1, copyDestination j ∈ normalizedOffsets := by
        intro j hj
        have zero : j = 0 := by omega_using [hj]
        subst j
        decide
      rw [prepared.normalized _ (slot j small), base, copiedValues j hj, ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold copyDestination; omega_using [])
        (by unfold copyDestination; omega_using [hj]) (by
          intro d hd
          have upper : ∀ d ∈ normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold copyDestination; omega_using [small, this])]
      rw [base]
      exact copiedValues j hj
  · intro r hr hb hx
    have notAx : ∀ r ∈ FillCompress.loopRegs, r ≠ .x8 := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega_using [bound])
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [base]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [base]
        have bounds : ∀ d ∈ normalizedOffsets, 192 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.sp + 192, 80⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 192 + (d - 192) by omega_using [lo], BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega_using [hi])

end VG.Proof.Argon2.AArch64.Derive

namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem base_ok (s : State) : WP isa (.block [.addSp .x19 0]) s fun t =>
    t.gpr .x19 = s.sp ∧ Divide.Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 0 < 4096 from by decide,
    ite_true, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.sp, 272⟩] s.wr)
    (read : ∀ j < 10, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa Impl.Argon2.AArch64.Derive.prepare s (PrivatePrepared s) := by
  unfold Impl.Argon2.AArch64.Derive.prepare
  refine WP.seq ((base_ok s).mono ?_)
  rintro a ⟨base, kept⟩
  refine (private_prepare_local_ok a (base.trans kept.sp.symm)
    (by rw [kept.sp, kept.wr]; exact locals)
    (by rw [kept.sp, kept.rd, kept.wr]; exact read)).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans kept.sp, prepared.sp.trans kept.sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans kept.rd, prepared.wr.trans kept.wr, ?_⟩
  · rw [prepared.scratch, kept.sp, kept.mem]
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have other : ∀ arg ∈ arguments, arg.2 ∉ [Reg.x19] := by decide
    rw [kept.regs arg.2 (other arg ha)]
  · intro j hj
    rw [prepared.stackWords j hj, kept.sp, kept.mem]
  · intro r hr hb hx
    exact (prepared.regs r hr hb hx).trans (kept.regs r (by simpa only [List.mem_singleton] using hb))
  · have frame := prepared.frame
    simp only [privateWrites, kept.sp, kept.mem] at frame
    exact frame
end VG.Proof.Argon2.AArch64.Derive
end

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def prologueState (s : State) : State := frameStart s Impl.Argon2.AArch64.Derive.saved

theorem prologue_sp (s : State) : (prologueState s).sp = s.sp - BitVec.ofNat 64 384 :=
  frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(frameStart s rs).sp, 272⟩ : Region) ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed r s)

theorem prologue_locals (s : State) : Covers [⟨(prologueState s).sp, 272⟩] (prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (prologueState s).sp + BitVec.ofNat 64 (copySource j) =
      s.sp + BitVec.ofNat 64 (8 * j) := by
  rw [prologue_sp]
  unfold copySource
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : AbiEnvironment s) :
    ∀ j < 10, InRegions ((prologueState s).rd ++ (prologueState s).wr)
      ((prologueState s).sp + BitVec.ofNat 64 (copySource j)) 8 := by
  intro j hj
  rw [prologue_source]
  refine ⟨abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change abiArguments s ∈ (frameStart s Impl.Argon2.AArch64.Derive.saved).rd
    rw [frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold abiArguments
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem prologue_word {s : State} (h : AbiEnvironment s) (j : Nat) (hj : j < 10) :
    (prologueState s).mem.readW ((prologueState s).sp + BitVec.ofNat 64 (copySource j)) 64 =
      abiWord s (8 * j) := by
  rw [prologue_source]
  have frame := frameStart_frame s Impl.Argon2.AArch64.Derive.saved (by
    have space := h.stack; change 384 ≤ s.sp.toNat; omega_using [space])
  apply frame.readW (r := abiArguments s) ?_ ?_ (by decide)
  · unfold abiArguments
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold abiArguments
    exact Offset.base_disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : AbiEnvironment s) :
    WP isa Impl.Argon2.AArch64.Derive.prepare (prologueState s) (PrivatePrepared (prologueState s)) :=
  private_prepare_ok _ (prologue_locals s) (prologue_reads h)

end VG.Proof.Argon2.AArch64.Derive
end

/-! Merged from `Proof.Argon2.AArch64.DeriveMetadata`. -/
section
/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_stack_word {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (j : Nat) (hj : j < 10) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 (copyDestination j)) 64 =
      let word := abiWord s (8 * j)
      if j < 1 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ arguments) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold argumentValue
  unfold prologueState
  rw [frameStart_reg s _ arg.2]

theorem private_local_write {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega_using [bound])⟩

theorem private_local_read {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .x19 + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Parameters.Ready (abiParams s) t := by
  refine ⟨private_local_read prepared 176 8 (by decide), private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := private_argument_word prepared (176, .x6) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      (((s.gpr .x6).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((s.gpr .x6).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := private_argument_word prepared (184, .x7) (by decide)
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      (((s.gpr .x7).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((s.gpr .x7).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.AArch64.Derive
end

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .x19 = s.sp - BitVec.ofNat 64 384 := prepared.bp.trans (prologue_sp s)

theorem private_sp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.sp = s.sp - BitVec.ofNat 64 384 := prepared.sp.trans (prologue_sp s)

theorem private_stack_minimum {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : 16 ≤ t.sp.toNat := by
  rw [private_sp prepared, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def]
    change 384 ≤ s.sp.toNat
    have := h.stack; omega_using [this])]
  change 16 ≤ s.sp.toNat - 384
  have := h.stack; omega_using [this]

theorem private_frame_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Region.Sub ⟨t.gpr .x19, 272⟩ (below (s.sp) 400) := by
  rw [private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : Region.Sub (below (t.sp) n) (below (s.sp) 400) := by
  rw [private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega_using [bound]) (by omega_using [bound])

theorem private_frame_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (⟨t.gpr .x19, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) (n : Nat) (bound : n ≤ 16) :
    (below (t.sp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : (⟨t.gpr .x19, 272⟩ : Region).Disjoint (below (t.sp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega_using [bound])

theorem private_work_member {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : abiWork s ∈ t.wr := by
  apply private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.AArch64.Derive
