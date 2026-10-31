module

import VerifiedGarbage.Proof.Cast5.RISCV64.Scan
import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# CAST5 on RISC-V: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`s0`–`s3` (`spread`), scans `VG_CAST5_S1234` and combines the four values
into `f` (`byType comb`), makes the Feistel step (`feistel`), and moves the
round's number modulo 3 and the count of rounds left on (`next`), as on
PPC64LE (`Proof/Cast5/PPC64LE/Round.lean`). The code's words are the low
words of registers (`lo`); `Kmᵢ` is read a byte at a time (`loadLE32_ok`),
and of `Krᵢ` only its low byte, whose low five bits are the rotation's.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64

/-! ## Choosing by the type -/

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t < 3)
    (hv : s.gpr typ = BitVec.ofNat 64 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  · exact WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => hQ _ (Keep.refl _ _) rfl)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (imm := 1) (by decide) fun u hu => WP.block_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => hQ _ k hu.mem)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (imm := 1) (by decide) fun u hu => WP.block_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide))
      (fun _ => hQ _ k hu.mem)

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t < 3) {kmw d : Spec.Cast5.Word}
    (hR : lo (s.gpr xR) = d) (hin : InRegions (s.rd ++ s.wr) (s.gpr km) 4)
    (hv : s.mem.readW (s.gpr km) 32 = kmw) :
    WP isa (.block (Impl.Cast5.RISCV64.mix t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.mix t kmw d ∧ Keep [vI, tmp] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;>
  · simp only [Impl.Cast5.RISCV64.mix]
    rw [WP.block_append_iff]
    refine WP.mono (ByteLoad.loadLE32_ok (d := vI) (tmp := tmp) (n := km) (off := 0) (by decide) (by decide)
      (by decide) (by decide) (by rw [BitVec.add_zero]; exact hin)) fun u e => ?_
    subst e
    c5run [hv]
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
    · simp only [lo_add, lo_sub, lo_xor, lo_ext, hR]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [hr.1, hr.2, ite_false]

/-- Bit `b` of `k` as the rotation's mask: zero if it is set, all ones if not. -/
theorem rotMask_eq (k : BitVec 64) {b : Nat} (hb : b < 64) :
    (k <<< (63 - b)) >>> 63 - 1#64 = if k.getLsbD b then 0 else BitVec.allOnes 64 := by
  have e : (k <<< (63 - b)) >>> 63 = if k.getLsbD b then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h0 : i = 0
    · subst h0
      have e1 : 63 - (63 - b) = b := by omega
      rw [Nat.add_zero, e1, decide_eq_true (show 63 < 64 by decide),
        decide_eq_false (show ¬ 63 < 63 - b by omega)]
      cases k.getLsbD b <;> decide
    · rw [decide_eq_false (show ¬ 63 + i < 64 by omega), Bool.false_and]
      have : ∀ c : Bool, (if c then 1#64 else 0#64).getLsbD i = false := fun c => by
        cases c <;> simp [BitVec.getLsbD_one, h0]
      exact (this _).symm
  rw [e]
  split <;> decide

/-- Step `b` of the rotation of `a` (the low word of `vI`) by `k` (`vKr`):
the rotation by `2 ^ b` if bit `b` of `k` is set. -/
theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a : BitVec 32} {k : BitVec 64}
    (hI : lo (s.gpr vI) = a) (hK : s.gpr vKr = k) :
    WP isa (.block (rotateStep b)) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (2 ^ b * (k.toNat / 2 ^ b % 2)) ∧ u.gpr vKr = k ∧
      Keep [msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
  have hn : 32 - 2 ^ b < 32 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  have hp : 2 ^ b < 32 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  have hr : a <<< 2 ^ b ||| a >>> (32 - 2 ^ b) = a.rotateLeft (2 ^ b) := rotl_shifts a hp
  unfold rotateStep
  c5run [hK, hn, hp, show 63 - b < 64 by omega]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  rw [rotMask_eq k (by omega)]
  simp only [lo_xor, lo_and, lo_or, lo_sext, hI]
  rw [hr]
  have hb' : k.getLsbD b = (k.toNat / 2 ^ b % 2 == 1) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp [Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (k.toNat / 2 ^ b) with h | h
  · have hg : k.getLsbD b = false := by rw [hb', h]; rfl
    rw [hg, h, Nat.mul_zero, show lo (if false = true then 0 else BitVec.allOnes 64) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes, BitVec.xor_comm a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
  · have hg : k.getLsbD b = true := by rw [hb', h]; rfl
    rw [hg, h, Nat.mul_one]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]

theorem rotate_ok (s : State) {a : BitVec 32} {kr : Byte} (hI : lo (s.gpr vI) = a)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 1)
    (hv : s.mem (s.gpr km + BitVec.ofNat 64 64) = kr) :
    WP isa (.block rotate) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (kr.toNat % 32) ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
  have e : rotate = [.load .b vKr km 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.load .b vKr km 64]) s fun u =>
      u.gpr vKr = kr.setWidth 64 ∧ lo (u.gpr vI) = a ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
    refine wp_lbu (by decide) rfl hin fun u hu => WP.block_nil ?_
    refine ⟨by rw [hu.gpr, hv], by rw [hu.other _ (by decide)]; exact hI, ⟨fun r hr => hu.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), hu.rd, hu.wr⟩, hu.mem⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  have hk : (kr.setWidth 64).toNat = kr.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := kr.isLt; omega)
  refine ⟨?_, ((((p₀.trans p₁).trans p₂).trans p₃).trans p₄).trans p₅ |>.mono fun r hr => ?_,
    by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  · rw [a₅]
    simp only [Proof.Cast5.rotateLeft_rotateLeft, hk]
    rw [← BitVec.rotateLeft_mod_eq_rotateLeft]
    congr 1
    simp only [Nat.reducePow, Nat.div_one, Nat.one_mul]
    omega
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with ((((h | h | h | h | h) | h | h | h | h) | h | h | h | h) | h | h | h | h) | h | h | h | h <;>
      simp only [h, true_or, or_true]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
abbrev idxOf (i : BitVec 32) (k : Nat) : Nat := i.toNat / 2 ^ (8 * k) % 256

theorem idxOf_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idxOf i k) = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, idxOf]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] <;> omega

theorem and255_toNat (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The low word of a sign-extended word is that word. -/
theorem sext32_toNat_mod (y : BitVec 32) : (sext32 y).toNat % 256 = y.toNat % 256 := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have := y.isLt
  by_cases h : y.msb = true <;> simp [h] <;> omega

theorem sext32_toNat {y : BitVec 32} (h : y.toNat < 2 ^ 31) : (sext32 y).toNat = y.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have : y.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have := y.isLt
  simp [*]; omega

theorem ushr24_lt (x : BitVec 64) : (x.setWidth 32 >>> 24).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (x.setWidth 32).isLt
  omega

theorem spread_ok (s : State) {i : BitVec 32} (hI : lo (s.gpr vI) = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, (u.gpr (idxReg k)).toNat = idxOf i k) ∧ Keep [.s0, .s1, .s2, .s3] s u ∧ u.mem = s.mem := by
  unfold spread
  c5run
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · have hi : i.toNat = (s.gpr .t5).toNat % 2 ^ 32 := by
      rw [← hI, BitVec.toNat_setWidth]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [idxReg_0, idxReg_1, idxReg_2, idxReg_3, reduceCtorEq, ↓reduceIte, and255_toNat,
        sext32_toNat_mod, sext32_toNat (ushr24_lt _), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_setWidth, idxOf, Nat.reduceMul, Nat.reducePow, hi] <;>
      omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t < 3) :
    WP isa (.block (Impl.Cast5.RISCV64.comb t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.comb t (lo (s.gpr .s7)) (lo (s.gpr .s6)) (lo (s.gpr .s5))
        (lo (s.gpr .s4)) ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.RISCV64.comb
    c5run
    refine ⟨?_, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [hr, ite_false], rfl, rfl⟩⟩
    simp only [lo_add, lo_sub, lo_xor]
    rfl

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr xL = s.gpr xR ∧ u.gpr xR = s.gpr vI ^^^ s.gpr xL ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧ Keep [vI, xL, xR, km] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    c5run
    refine ⟨fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The number modulo 3 of the round after the one numbered `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 2 then 0 else t + 1) else (if t = 0 then 2 else t - 1)

theorem nextT_lt {up : Bool} {t : Nat} (ht : t < 3) : nextT up t < 3 := by
  unfold nextT; split <;> split <;> omega

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t < 3) (hv : s.gpr typ = BitVec.ofNat 64 t) :
    WP isa (next up) s fun u =>
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep [tmp, typ, left] s u ∧ u.mem = s.mem := by
  cases up <;>
  refine WP.mono (WP.keep [tmp, typ, left] (Q := fun u => u.gpr typ = BitVec.ofNat 64 (nextT _ t) ∧
    u.gpr left = s.gpr left - 1#64 ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩ <;>
  unfold next <;> rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · refine WP.seq (WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide)))
    c5run
    c5run [nextT]
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  all_goals refine WP.seq (WP.seq (wp_subi (imm := 2) (by decide) fun u hu => WP.block_nil ?_))
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    have ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    have ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    have ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run
    c5run [ul, nextT, hu.mem]

/-! ## The round -/

/-- `f` of a round numbered `t` modulo 3 with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in the low words of `(a6, a7)`; `Kmᵢ` at
`km` and `Krᵢ` at `km + 64` (of which the low byte's low five bits matter);
the round's number modulo 3 in `typ`; and the table `VG_CAST5_S1234` at
`tbl`, readable and 64-byte aligned. -/
structure RoundPre (s : State) (kmw krw l r : Spec.Cast5.Word) (t : Nat) : Prop where
  xL : lo (s.gpr xL) = l
  xR : lo (s.gpr xR) = r
  inM : InRegions (s.rd ++ s.wr) (s.gpr km) 4
  valM : s.mem.readW (s.gpr km) 32 = kmw
  inR : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 1
  valR : (s.mem (s.gpr km + BitVec.ofNat 64 64)).toNat % 32 = krw.toNat % 32
  ht : t < 3
  typ : s.gpr typ = BitVec.ofNat 64 t
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.gpr tbl).toNat % 64 = 0
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234

/-- The registers a round writes. -/
def roundRegs : List Reg := [tmp, wd, .t2, ep, .s4, .s5, .s6, .s7, .s0, .s1, .s2, .s3, vI, vKr, msk,
  xL, xR, km, typ, left]

theorem round_ok (s : State) (up : Bool) {kmw krw l r : Spec.Cast5.Word} {t : Nat}
    (h : RoundPre s kmw krw l r t) :
    WP isa (round up) s fun u =>
      lo (u.gpr xL) = r ∧ lo (u.gpr xR) = l ^^^ fT t kmw krw r ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep roundRegs s u ∧ u.mem = s.mem := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (WP.mono (byType_ok s Impl.Cast5.RISCV64.mix (Q := fun v => lo (v.gpr vI) =
      Proof.Cast5.mix t kmw r ∧ Keep [tmp, vI] s v ∧ v.mem = s.mem) ht h.typ fun u uk um => ?_) fun v hv => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = s.gpr q := uk.gpr (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.xR)
      (by rw [uk.2.1, uk.2.2, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.trans vk).mono (by decide), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [tmp, vI]) : v.gpr q = s.gpr q := vk.gpr hq
  -- The rotation and the indices.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok v v1 (by rw [vk.2.1, vk.2.2, gv _ (by decide)]; exact h.inR) rfl)
    fun w ⟨w1, wk, wm⟩ => ?_
  rw [vm, gv _ (by decide), h.valR] at w1
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t kmw r).rotateLeft (krw.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  have kw := vk.trans wk
  refine WP.mono (spread_ok w w1) fun x ⟨xi, xk, xm⟩ => ?_
  have kx := kw.trans xk
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have tx : x.gpr tbl = s.gpr tbl := kx.gpr (by decide)
  -- The scan.
  have sp : ScanPre x :=
    { idx := fun k hk => by rw [xi k hk]; exact Nat.mod_lt _ (by decide)
      tal := by rw [tx]; exact h.tal
      trd := by rw [tx, kx.2.1, kx.2.2]; exact h.trd }
  refine WP.seq (WP.mono (scan_ok x sp) fun y ⟨ya, yk, ym⟩ => ?_)
  have ky := kx.trans yk
  have my : y.mem = s.mem := ym.trans mx
  have ty : y.gpr typ = BitVec.ofNat 64 t := by rw [ky.gpr (by decide)]; exact h.typ
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.RISCV64.comb (Q := fun z => lo (z.gpr vI) = fT t kmw krw r ∧
      Keep [tmp, vI] y z ∧ z.mem = y.mem) ht ty fun u uk um => ?_) fun z ⟨z1, zk, zm⟩ => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = y.gpr q := uk.gpr (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, uk.trans zk, zm.trans um⟩
    have ent' (k : Nat) (hk : k < 4) : lo (y.gpr (accReg k)) = Proof.Cast5.tableEnt Spec.Cast5.S4 Spec.Cast5.S3
        Spec.Cast5.S2 Spec.Cast5.S1 (idxOf i k) k := by
      rw [ya k hk, mx, xi k hk, tx, lo_ext]
      exact ent_table h.held (Nat.mod_lt _ (by decide)) hk
    have a0 : lo (y.gpr .s4) = _ := ent' 0 (by decide)
    have a1 : lo (y.gpr .s5) = _ := ent' 1 (by decide)
    have a2 : lo (y.gpr .s6) = _ := ent' 2 (by decide)
    have a3 : lo (y.gpr .s7) = _ := ent' 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [Proof.Cast5.tableEnt, idxOf_byte i (show 0 < 4 by decide), idxOf_byte i (show 1 < 4 by decide),
      idxOf_byte i (show 2 < 4 by decide), idxOf_byte i (show 3 < 4 by decide)]
  have kz := ky.trans zk
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, akm, ak, am⟩ => ?_)
  have ka := kz.trans ak
  refine WP.mono (next_ok a up ht (by rw [ka.gpr (by decide)]; exact h.typ)) fun b ⟨bt, bl, bk, bm⟩ => ?_
  have kb := ka.trans bk
  have gb (q : Reg) (hq : q ∉ [tmp, typ, left]) : b.gpr q = a.gpr q := bk.gpr hq
  refine ⟨by rw [gb _ (by decide), a2, kz.gpr (by decide)]; exact h.xR, ?_, ?_, bt,
    by rw [bl, ka.gpr (by decide)], kb.mono (by decide), by rw [bm, am, zm, my]⟩
  · rw [gb _ (by decide), a3, lo_xor, z1, kz.gpr (by decide), h.xL, BitVec.xor_comm]
  · rw [gb _ (by decide), akm, kz.gpr (by decide)]

end VG.Proof.Cast5.RISCV64
