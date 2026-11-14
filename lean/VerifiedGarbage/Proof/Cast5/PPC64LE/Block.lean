module

import VerifiedGarbage.Proof.Cast5.PPC64LE.Scan
import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Cast5

/-! ### `Cast5.PPC64LE.Round`, which only this module used -/

section

/-!
# CAST5 on PPC64LE: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r14`–`r17` (`spread`), scans `VG_CAST5_S1234` and combines the four values
into `f` (`byType comb`), makes the Feistel step (`feistel`), and moves the
round's number modulo 3 and the count of rounds left on (`next`). The
code's words are the low words of registers (`lo`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE

/-! ## Choosing by the type -/

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t < 3)
    (hv : s.gpr typ = BitVec.ofNat 64 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl
  · exact WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => hQ _ (Keep.refl _ _) rfl)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => hQ _ k hu.mem)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_)
    have k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide))
      (fun _ => hQ _ k hu.mem)

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t < 3) {kmw d : Spec.Cast5.Word}
    (hR : lo (s.gpr xR) = d) (hin : InRegions (s.rd ++ s.wr) (s.gpr km) 4)
    (hv : s.mem.readW (s.gpr km) 32 = kmw) :
    WP isa (.block (Impl.Cast5.PPC64LE.mix t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.mix t kmw d ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.PPC64LE.mix
    c5run [hin, hv]
    refine ⟨?_, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [hr, ite_false], rfl, rfl⟩⟩
    simp only [lo_add, lo_sub, lo_xor, lo_ext, hR]
    rfl

/-- Bit `b` of `k` as the rotation's mask: zero if it is set, all ones if not. -/
theorem rotMask_eq (k : BitVec 64) {b : Nat} (hb : b < 64) :
    (k <<< (63 - b)) >>> 63 - 1#64 = if k.getLsbD b then 0 else BitVec.allOnes 64 := by
  have e : (k <<< (63 - b)) >>> 63 = if k.getLsbD b then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h0 : i = 0
    · subst h0
      have e1 : 63 - (63 - b) = b := by omega_using [hb]
      rw [Nat.add_zero, e1, decide_eq_true (show 63 < 64 by decide),
        decide_eq_false (show ¬ 63 < 63 - b by omega_using [])]
      cases k.getLsbD b <;> decide
    · rw [decide_eq_false (show ¬ 63 + i < 64 by omega_using [h0]), Bool.false_and]
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
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  have hr : a.rotateRight (32 - 2 ^ b) = a.rotateLeft (2 ^ b) :=
    Proof.Cast5.rotateRight_eq_rotateLeft a (Nat.pow_pos (by decide)) (by
      rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
        subst h <;> decide)
  unfold rotateStep
  c5run [hK, hn, show 63 - b < 64 by omega_using []]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  rw [rotMask_eq k (by omega_using [hb])]
  simp only [lo_xor, lo_and, lo_ext, hI]
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

theorem rotate_ok (s : State) {a kr : BitVec 32} (hI : lo (s.gpr vI) = a)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 4)
    (hv : s.mem.readW (s.gpr km + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (kr.toNat % 32) ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
  have e : rotate = [.load .w vKr km 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.load .w vKr km 64]) s fun u =>
      u.gpr vKr = kr.setWidth 64 ∧ lo (u.gpr vI) = a ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
    c5run [hin, hv]
    exact ⟨hI, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [hr.1, ite_false], rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  have hk : (kr.setWidth 64).toNat = kr.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := kr.isLt; omega_using [])
  refine ⟨?_, ((((p₀.trans p₁).trans p₂).trans p₃).trans p₄).trans p₅ |>.mono fun r hr => ?_,
    by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  · rw [a₅]
    simp only [Proof.Cast5.rotateLeft_rotateLeft, hk]
    rw [← BitVec.rotateLeft_mod_eq_rotateLeft]
    congr 1
    simp only [Nat.reducePow, Nat.div_one, Nat.one_mul]
    omega_using []
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
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] <;> omega_using []

theorem and255_toNat (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem spread_ok (s : State) {i : BitVec 32} (hI : lo (s.gpr vI) = i) (h255 : s.gpr c255 = 255#64) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, (u.gpr (idxReg k)).toNat = idxOf i k) ∧ Keep [.r14, .r15, .r16, .r17] s u ∧ u.mem = s.mem := by
  unfold spread
  c5run [h255]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · have hi : i.toNat = (s.gpr .r28).toNat % 2 ^ 32 := by
      rw [← hI, BitVec.toNat_setWidth]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
      simp only [idxReg_0, idxReg_1, idxReg_2, idxReg_3, reduceCtorEq, ↓reduceIte, and255_toNat,
        BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, idxOf, Nat.reduceMul,
        Nat.reducePow, hi] <;>
      omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t < 3) :
    WP isa (.block (Impl.Cast5.PPC64LE.comb t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.comb t (lo (s.gpr .r21)) (lo (s.gpr .r20)) (lo (s.gpr .r19))
        (lo (s.gpr .r18)) ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.PPC64LE.comb
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

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t < 3) (hv : s.gpr typ = BitVec.ofNat 64 t) :
    WP isa (next up) s fun u =>
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep [tmp, typ, left] s u ∧ u.mem = s.mem := by
  cases up <;>
  refine WP.mono (WP.keep [tmp, typ, left] (Q := fun u => u.gpr typ = BitVec.ofNat 64 (nextT _ t) ∧
    u.gpr left = s.gpr left - 1#64 ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩ <;>
  unfold next <;> rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
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
  all_goals refine WP.seq (WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_))
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

/-- What a round needs: `(L, R)` in the low words of `(r8, r9)`; `Kmᵢ` at
`km` and `Krᵢ` at `km + 64`; the round's number modulo 3 in `typ`; zero and
255 in their registers; and the table `VG_CAST5_S1234` at `tbl`, readable. -/
structure RoundPre (s : State) (kmw krw l r : Spec.Cast5.Word) (t : Nat) : Prop where
  xL : lo (s.gpr xL) = l
  xR : lo (s.gpr xR) = r
  inM : InRegions (s.rd ++ s.wr) (s.gpr km) 4
  valM : s.mem.readW (s.gpr km) 32 = kmw
  inR : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr km + BitVec.ofNat 64 64) 32 = krw
  ht : t < 3
  typ : s.gpr typ = BitVec.ofNat 64 t
  zero : s.gpr .r0 = 0
  c255 : s.gpr c255 = 255#64
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234

/-- The registers a round writes. -/
def roundRegs : List Reg := [tmp, wd, num, ep, .r18, .r19, .r20, .r21, .r14, .r15, .r16, .r17, vI, vKr, msk,
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
  refine WP.seq (WP.mono (byType_ok s Impl.Cast5.PPC64LE.mix (Q := fun v => lo (v.gpr vI) =
      Proof.Cast5.mix t kmw r ∧ Keep [tmp, vI] s v ∧ v.mem = s.mem) ht h.typ fun u uk um => ?_) fun v hv => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = s.gpr q := uk.gpr (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.xR)
      (by rw [uk.2.1, uk.2.2, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.trans vk), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [tmp, vI]) : v.gpr q = s.gpr q := vk.gpr hq
  -- The rotation and the indices.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok v v1 (kr := krw) (by rw [vk.2.1, vk.2.2, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ => ?_
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t kmw r).rotateLeft (krw.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  have kw := vk.trans wk
  refine WP.mono (spread_ok w w1 (by rw [kw.gpr (by decide)]; exact h.c255)) fun x ⟨xi, xk, xm⟩ => ?_
  have kx := kw.trans xk
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have tx : x.gpr tbl = s.gpr tbl := kx.gpr (by decide)
  -- The scan.
  have sp : ScanPre x :=
    { idx := fun k hk => by rw [xi k hk]; exact Nat.mod_lt _ (by decide)
      zero := by rw [kx.gpr (by decide)]; exact h.zero
      trd := by rw [tx, kx.2.1, kx.2.2]; exact h.trd }
  refine WP.seq (WP.mono (scan_ok x sp) fun y ⟨ya, yk, ym⟩ => ?_)
  have ky := kx.trans yk
  have my : y.mem = s.mem := ym.trans mx
  have ty : y.gpr typ = BitVec.ofNat 64 t := by rw [ky.gpr (by decide)]; exact h.typ
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.PPC64LE.comb (Q := fun z => lo (z.gpr vI) = fT t kmw krw r ∧
      Keep [tmp, vI] y z ∧ z.mem = y.mem) ht ty fun u uk um => ?_) fun z ⟨z1, zk, zm⟩ => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = y.gpr q := uk.gpr (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, uk.trans zk, zm.trans um⟩
    have ent' (k : Nat) (hk : k < 4) : lo (y.gpr (accReg k)) = Proof.Cast5.tableEnt Spec.Cast5.S4 Spec.Cast5.S3
        Spec.Cast5.S2 Spec.Cast5.S1 (idxOf i k) k := by
      rw [ya k hk, mx, xi k hk, tx, lo_ext]
      exact ent_table h.held (Nat.mod_lt _ (by decide)) hk
    have a0 : lo (y.gpr .r18) = _ := ent' 0 (by decide)
    have a1 : lo (y.gpr .r19) = _ := ent' 1 (by decide)
    have a2 : lo (y.gpr .r20) = _ := ent' 2 (by decide)
    have a3 : lo (y.gpr .r21) = _ := ent' 3 (by decide)
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

end VG.Proof.Cast5.PPC64LE

end

end


/-!
# CAST5 on PPC64LE: the block function

`crypt up pr` encrypts (`up`) or decrypts the block at `pr` in place, with
the schedule at `sch` and the number of rounds in `rnd` (`crypt_ok`): it
loads the halves, runs the rounds in a loop (`rounds_ok`), each from the
state of the rounds (`RInv`), and stores them. It writes no memory but the
block's.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)

/-- `fT` of round `i`'s number modulo 3 is the spec's `f`. -/
theorem fT_eq (i : Nat) (km kr d : Spec.Cast5.Word) : fT (i % 3) km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]; rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- What the block function needs: the block at `p` in `pr` (a register
the rounds keep), writable; the schedule at `kb` in `sch`, readable; the
number of rounds `n` in `rnd`; zero and 255 in their registers; and the
table `VG_CAST5_S1234` at `tbl`, readable. -/
structure BPre (s : State) (pr : Reg) (p kb : Addr) (n : Nat) : Prop where
  ptr : s.gpr pr = p
  prOk : pr ∉ roundRegs ∧ pr ≠ .r0
  sched : s.gpr sch = kb
  rounds : s.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  zero : s.gpr .r0 = 0
  c255 : s.gpr c255 = 255#64
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234
  inP : ∃ r ∈ s.wr, ∀ off, off + 4 ≤ 8 → r.Contains (p + BitVec.ofNat 64 off) 4
  inK : (⟨kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : kb.toNat + 128 ≤ 2 ^ 64

section
variable {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
include h

theorem BPre.inK' {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.inK, Offset.contains_base _ hw (by have := h.kfit; omega_arith)⟩

theorem BPre.inP' {off : Nat} (hw : off + 4 ≤ 8) : InRegions s.wr (p + BitVec.ofNat 64 off) 4 :=
  let ⟨r, hr, hc⟩ := h.inP; ⟨r, hr, hc off hw⟩

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its number modulo 3 `t` and `left` rounds left. -/
structure RInv (s : State) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : Addr) (t nl : Nat)
    (u : State) : Prop where
  vL : lo (u.gpr xL) = lr.1
  vR : lo (u.gpr xR) = lr.2
  vkm : u.gpr km = kp
  vtyp : u.gpr typ = BitVec.ofNat 64 t
  vleft : u.gpr left = BitVec.ofNat 64 nl
  keep : Keep roundRegs s u
  mem : u.mem = s.mem

/-- The subkeys of round `i` (`1 … 16`) at `kp`. -/
theorem key_at (s : State) (kb : Addr) {j : Nat} (hj : j < 32) :
    s.mem.readW (kb + BitVec.ofNat 64 (4 * j)) 32 = (Spec.Cast5.scheduleAt s.mem kb).getD j 0 :=
  (Proof.Cast5.scheduleAt_getD _ _ hj).symm

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {nl i : Nat}
    (hu : RInv s lr (kb + BitVec.ofNat 64 (4 * (i - 1))) (i % 3) nl u) (up : Bool)
    (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ nl ∧ nl < 2 ^ 64) :
    WP isa (round up) u fun v =>
      RInv s (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr)
        (if up then kb + BitVec.ofNat 64 (4 * (i - 1)) + 4#64 else kb + BitVec.ofNat 64 (4 * (i - 1)) - 4#64)
        (nextT up (i % 3)) (nl - 1) v := by
  have g (q : Reg) (hq : q ∉ roundRegs := by decide) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have e64 : u.gpr km + BitVec.ofNat 64 64 = kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.vkm, Offset.add_add]; congr 2; omega_arith
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem kb).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem kb).getD (15 + i) 0) lr.1 lr.2 (i % 3) :=
    { xL := hu.vL
      xR := hu.vR
      inM := by rw [hu.vkm, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valM := by rw [hu.vkm, hu.mem]; exact key_at s kb (by omega_arith)
      inR := by rw [e64, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valR := by rw [e64, hu.mem]; exact key_at s kb (by omega_arith)
      ht := Nat.mod_lt _ (by decide)
      typ := hu.vtyp
      zero := by rw [g _]; exact h.zero
      c255 := by rw [g _]; exact h.c255
      trd := by rw [g tbl, hu.keep.2.1, hu.keep.2.2]; exact h.trd
      held := by rw [g tbl, hu.mem]; exact h.held }
  refine WP.mono (round_ok u up pre) fun v ⟨v1, v2, vkm, vt, vl, vk, vm⟩ => ⟨v1, ?_, ?_, vt, ?_,
    (hu.keep.trans vk).mono (by decide), vm.trans hu.mem⟩
  · rw [v2, show (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr).2 =
      lr.1 ^^^ Spec.Cast5.f i lr.2 _ _ from rfl, fT_eq]
  · rw [vkm, hu.vkm]
  · rw [vl, hu.vleft]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i`, and the halves before it `fold i`. -/
theorem rounds_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → Addr) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 64 (4 * (idx i - 1)))
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4#64 else kpf i - 4#64) ∧
      idx (i + 1) % 3 = nextT up (idx i % 3))
    (h0 : RInv s (fold 0) (kpf 0) (idx 0 % 3) n u) :
    WP isa (.loop (round up) (.nonzero .d left)) u fun v => ∃ kp t, RInv s (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧
      RInv s (fold i) (kpf i) (idx i % 3) (n - i) v) ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (hidx i hi) (by omega_arith)) fun w hw => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  have ev : isa.eval (.nonzero .d left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
    rw [eval_nonzero, hw.vleft]
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    rw [ev, show n - i - 1 = 0 by omega_arith]; rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · rw [ev]
      congr 1
      have : BitVec.ofNat 64 (n - i - 1) ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw

/-! ## The block function -/

theorem _root_.VG.PPC64LE.Upd.keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem rev32_eq (x : BitVec 32) : rev32 x = byteRev32 x := rfl

theorem BPre.ne {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {r : Reg}
    (hr : r ∈ roundRegs) : pr ≠ r := fun e => h.prOk.1 (e ▸ hr)

/-- The halves into `xL`, `xR`. -/
theorem load_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [xL, tmp, xR] s u → u.mem = s.mem →
      lo (u.gpr xL) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).1 →
      lo (u.gpr xR) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).2 → WP isa (.block is) u Q) :
    WP isa (.block (([.loadRev .w xL pr zero, .addi tmp pr 4, .loadRev .w xR tmp zero] : List Instr) ++ is)) s Q := by
  have in0 : InRegions (s.rd ++ s.wr) p 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 0) (by decide)
    exact ⟨g, List.mem_append_right _ hg, by simpa using hc⟩
  have in4 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 4) (by decide)
    exact ⟨g, List.mem_append_right _ hg, hc⟩
  have dec := Proof.Cast5.decodeBlock_blockAt s.mem p
  refine wp_lwbrx (ea := p) h.prOk.2 (by rw [h.ptr, h.zero]; simp) in0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  have p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.other _ (h.ne (by decide)), h.ptr]
  refine wp_lwbrx (ea := p + BitVec.ofNat 64 4) (by decide) (by rw [p₂, h₂.other _ (by decide), h₁.other _ (by decide), h.zero]; simp) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact in4) fun u₃ h₃ => ?_
  refine k u₃ ((h₁.keep.trans (h₂.keep.trans h₃.keep)).mono (by decide)) (by rw [h₃.mem, h₂.mem, h₁.mem])
    ?_ ?_
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, dec, lo_ext, rev32_eq]
  · rw [h₃.gpr, h₂.mem, h₁.mem, dec, lo_ext, rev32_eq]

theorem startEnc_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startEnc pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * 0)) ((0 + 1) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_mr fun u₁ h₁ => wp_mr fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ => wp_nil ?_
  exact
    { vL := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, uk.gpr (by decide), h.sched]; simp
      vtyp := by rw [h₃.gpr]
      vleft := by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), uk.gpr (by decide), h.rounds]
      keep := (((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).mono (by decide)
      mem := by rw [h₃.mem, h₂.mem, h₁.mem, um] }

theorem startDec_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startDec pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * ((n - 0) - 1))) ((n - 0) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_lsl (by decide) fun u₁ h₁ => wp_add fun u₂ h₂ => wp_subi (by decide) (by decide) fun u₃ h₃ =>
    wp_mr fun u₄ h₄ => wp_lsr (by decide) fun u₅ h₅ => wp_subi (by decide) (by decide) fun u₆ h₆ => wp_nil ?_
  have r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  have r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  have kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  have tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
  exact
    { vL := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), kmv]
        rcases h.nv with rfl | rfl
        · rw [show (BitVec.ofNat 64 12 <<< 2) = BitVec.ofNat 64 48 by decide, Offset.add_ofNat_sub _ (by decide)]
        · rw [show (BitVec.ofNat 64 16 <<< 2) = BitVec.ofNat 64 64 by decide, Offset.add_ofNat_sub _ (by decide)]
      vtyp := by rw [tv]; rcases h.nv with rfl | rfl <;> decide
      vleft := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide), r4]
      keep := (((((((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
        h₆.keep)).mono (by decide)
      mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, um] }

/-- What the block function does: the block at `p` is `out`, and nothing
else in memory changed. -/
structure BPost (s : State) (p : Addr) (out : Spec.Cast5.Block) (t : State) : Prop where
  blk : Spec.Cast5.blockAt t.mem p = out
  frame : Frame [⟨p, 8⟩] s.mem t.mem
  keep : Keep roundRegs s t

theorem finish_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : Addr} {t : Nat} (hu : RInv s lr kp t 0 u) :
    WP isa (.block (finish pr)) u (BPost s p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have g (q : Reg) (hq : q ∉ roundRegs) : u.gpr q = s.gpr q := hu.keep.gpr hq
  have hp : u.gpr pr = p := by rw [g _ h.prOk.1, h.ptr]
  have h0 : u.gpr .r0 = 0 := by rw [g _ (by decide), h.zero]
  have o0 : InRegions u.wr p 4 := by rw [hu.keep.2.2]; simpa using h.inP' (off := 0) (by decide)
  have o4 : InRegions u.wr (p + BitVec.ofNat 64 4) 4 := by rw [hu.keep.2.2]; exact h.inP' (by decide)
  refine wp_stwbrx (ea := p) h.prOk.2 (by rw [hp, h0]; simp) o0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  have p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.gpr, hp]
  refine wp_stwbrx (ea := p + BitVec.ofNat 64 4) (by decide)
    (by rw [p₂, h₂.other _ (by decide), h₁.gpr, h0]; simp) (by rw [h₂.wr, h₁.wr]; exact o4) fun u₃ h₃ => ?_
  refine wp_nil ⟨?_, ?_, ?_⟩
  · rw [h₃.mem, h₂.mem, h₁.mem, h₂.other _ (by decide), h₁.gpr, rev32_eq, rev32_eq, hu.mem,
      Proof.Cast5.blockAt_write]
    exact congrArg _ (Prod.ext hu.vR hu.vL)
  · rw [h₃.mem, h₂.mem, h₁.mem, hu.mem]
    have f1 := (Frame.refl [(⟨p, 8⟩ : Region)] s.mem).writeW List.mem_cons_self
      (rev32 ((u.gpr xR).setWidth 32)) (Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))
    rw [BitVec.add_zero] at f1
    exact f1.writeW List.mem_cons_self _
      (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [h₃.gpr, h₂.other r fun e => hr (e ▸ by decide), h₁.gpr]; exact hu.keep.gpr hr
    · rw [h₃.rd, h₂.rd, h₁.rd]; exact hu.keep.2.1
    · rw [h₃.wr, h₂.wr, h₁.wr]; exact hu.keep.2.2

theorem crypt_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool) :
    WP isa (crypt up pr) s (BPost s p (cipher up (Spec.Cast5.scheduleAt s.mem kb) n
      (Spec.Cast5.blockAt s.mem p))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 64 (4 * (n - i - 1)))
      (fun i => decFold _ n i _) (fun i hi => by omega_arith) (fun i hi => rfl)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - i - 1 = n - (i + 1) - 1 + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 64 (4 * i))
      (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu)
      fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
    · simp only [nextT, ite_true]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.PPC64LE
