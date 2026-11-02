module

-- separate module: its proofs take about 8 s, which `VJoint.lean`'s edits need not re-check
public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
public import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.WnafWide.Word
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
import VerifiedGarbage.Proof.X448.RISCV64.Field
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit

/-!
# Ed448's verification on RISCV64: the digits

`TB` holds 468 entries of four bytes (`TbIs`): bit `n` of `S` and of `k` in
lanes 0 and 1, and their width-5 digits `WnafWide.digitAt false` at `n` in
lanes 2 and 3. `bitsZero` zeroes them (`bitsZero_ok`), `bitsOf` writes the
bits of a scalar into a lane (`bitsOf_ok`), and `recode` its digits
(`recode_ok`), by `WnafWide`'s recoding: at position `n`, with the five bits
`h % 32` of `h = k / 2ⁿ` and the carry `c`, the digit is `rawDigit false
(h % 32 + c + 16)`, which `digit_word` computes as the code does, and the
next carry follows (`carry_word`).

`cp7` copies seven doublewords between two places of the working space
(`cp7_ok`), which keeps the element (`cp7_V`). `baseTable` writes the affine
odd multiples `[2 i + 1]B` of `PublicTable` at `BT` (`baseTable_ok`,
`BaseOk`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.Ed448.WnafWide (digitAt localDigit carryNext residual half radix)
open VG.Proof.Ed448.WnafWide (look rawDigit)

/-- Bit `i` of `k` (`WnafWide.bit`). -/
local notation "wbit" => Proof.Ed448.WnafWide.bit

/-! ## The arithmetic -/

/-- The digit as the code computes it from the sum. -/
def digitW (x : BitVec 64) : BitVec 64 :=
  let r := x &&& BitVec.ofInt 64 31
  (r - ((r >>> 4) <<< 5)) &&& (BitVec.ofNat 64 0 - (r &&& BitVec.ofInt 64 1))

theorem digitW_sum : ∀ n < 80, digitW (BitVec.ofNat 64 n) = rawDigit false n := by decide

theorem digit_word {bits c : Nat} (hb : bits < 32) (hc : c ≤ 32) :
    digitW (BitVec.ofNat 64 bits + BitVec.ofNat 64 c + BitVec.ofNat 64 16) =
      BitVec.ofInt 64 (localDigit false bits c) := by
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, digitW_sum _ (by omega)]
  exact Proof.Ed448.WnafWide.rawDigit_ok false (bits := bits) (c := c) hb hc

theorem and_one_ofNat {x : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofInt 64 1 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofInt 64 1).toNat = 1 := rfl
  have h2 : x % 2 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt h2, Nat.and_one_is_mod]

theorem carry_word {bits c : Nat} (hb : bits < 32) (hc : c ≤ 32) :
    (BitVec.ofNat 64 c + (BitVec.ofNat 64 bits &&& BitVec.ofInt 64 1) + BitVec.ofNat 64 16 -
      BitVec.ofInt 64 (localDigit false bits c)) >>> 1 = BitVec.ofNat 64 (carryNext false bits c) := by
  rw [and_one_ofNat (by omega), ← Proof.Ed448.WnafWide.rawDigit_ok false hb hc]
  exact Proof.Ed448.WnafWide.rawCarry_ok false hb hc

/-- Five bits, as the code ORs them together. -/
theorem bits_word : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2, ∀ b4 < 2,
    (((BitVec.ofNat 64 b0 ||| BitVec.ofNat 64 b1 <<< 1) ||| BitVec.ofNat 64 b2 <<< 2) |||
      BitVec.ofNat 64 b3 <<< 3) ||| BitVec.ofNat 64 b4 <<< 4 =
      BitVec.ofNat 64 (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4) := by decide

theorem look5 (k n : Nat) :
    look k n 5 = wbit k n + 2 * wbit k (n + 1) + 4 * wbit k (n + 2) + 8 * wbit k (n + 3) + 16 * wbit k (n + 4) := by
  simp only [Proof.Ed448.WnafWide.look_succ, Proof.Ed448.WnafWide.look_zero, Nat.add_zero, Nat.pow_zero,
    Nat.one_mul, Nat.pow_succ]
  omega

theorem look5_mod (k n : Nat) : look k n 5 = k / 2 ^ n % 32 := rfl

theorem ofInt_byte (d : Int) : ((BitVec.ofInt 64 d).setWidth 8) = BitVec.ofInt 8 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h0 : 0 ≤ d % ((2 ^ 64 : Nat) : Int) := Int.emod_nonneg _ (by decide)
  have h1 : 0 ≤ d % ((2 ^ 8 : Nat) : Int) := Int.emod_nonneg _ (by decide)
  have h2 := Int.emod_emod_of_dvd d (show ((2 ^ 8 : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) by decide)
  omega

/-! ## The entries -/

/-- The entries' bytes are `f`. -/
def TbIs (b : Addr) (m : Mem) (f : Nat → Nat) : Prop :=
  ∀ h < 1872, m (b + BitVec.ofNat 64 (TB + h)) = BitVec.ofNat 8 (f h)

/-- Bit `h / 4` of `k`, below 456, into lane `e`. -/
def tbSet (e k : Nat) (f : Nat → Nat) (h : Nat) : Nat :=
  if h % 4 = e ∧ h / 4 < 456 then (k >>> (h / 4)) &&& 1 else f h

/-- The digits at `n' < n` of lane `e`'s scalar `k` into lane `e + 2`. -/
def recCur (e k : Nat) (f : Nat → Nat) (n h : Nat) : Nat :=
  if h % 4 = e + 2 ∧ h / 4 < n then (BitVec.ofInt 8 (digitAt false k (h / 4))).toNat else f h

/-- The entries after `bitsOf` and `recode` of `S` and `K`. -/
def digV (S K h : Nat) : Nat :=
  if h % 4 = 0 then wbit S (h / 4) else if h % 4 = 1 then wbit K (h / 4)
  else if h % 4 = 2 then (BitVec.ofInt 8 (digitAt false S (h / 4))).toNat
  else (BitVec.ofInt 8 (digitAt false K (h / 4))).toNat

theorem setWidth8_ofNat' {x : Nat} (hx : x < 256) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x :=
  stb_byte (toNat_imm (by omega_arith))

theorem wp_sra {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

section
variable {b : Addr}

/-! ## Zeroing -/

/-- After `j` entries of the fill, from `s0`. -/
structure ZInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a6, .t0] s0 s
  a6 : s.gpr .a6 = b + BitVec.ofNat 64 (OUT + 4 * j)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (468 - j)
  frame : Frame [⟨b + BitVec.ofNat 64 TB, 4 * j⟩] s0.mem s.mem
  vals : ∀ h < 4 * j, s.mem (b + BitVec.ofNat 64 (TB + h)) = BitVec.ofNat 8 0

theorem zeroStep_ok {s0 s : State} (hc : VCtx b s0) (h7 : s0.gpr .a4 = BitVec.ofNat 64 0)
    {j : Nat} (hj : j < 468) (h : ZInv b s0 j s) :
    WP isa (.block [.store .b .a4 .a6 (TB - OUT), .store .b .a4 .a6 (TB - OUT + 1), .store .b .a4 .a6 (TB - OUT + 2),
        .store .b .a4 .a6 (TB - OUT + 3), .addi .a6 .a6 4, .addi .t0 .t0 (-1)]) s fun t =>
      ZInv b s0 (j + 1) t ∧ (t.gpr .t0 != 0) = decide (468 - (j + 1) ≠ 0) := by
  have hT : TB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  have hcs : VCtx b s := hc.of_rest h.rest (by decide) (by decide)
  have a : ∀ i < 4, s.gpr .a6 + BitVec.ofNat 64 (TB - OUT + i) = b + BitVec.ofNat 64 (TB + (4 * j + i)) :=
    fun i _ => by rw [h.a6, Offset.add_add]; congr 2; omega_arith
  have e7 : s.gpr .a4 = BitVec.ofNat 64 0 := by rw [h.rest.gpr _ (by decide), h7]
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (4 * j + 0))) (by decide) (a 0 (by decide))
    (hcs.inW (by omega_arith)) fun s1 u1 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (4 * j + 1))) (by decide)
    (by rw [u1.gpr]; exact a 1 (by decide)) (by rw [u1.wr]; exact hcs.inW (by omega_arith)) fun s2 u2 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (4 * j + 2))) (by decide)
    (by rw [u2.gpr, u1.gpr]; exact a 2 (by decide)) (by rw [u2.wr, u1.wr]; exact hcs.inW (by omega_arith)) fun s3 u3 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (4 * j + 3))) (by decide)
    (by rw [u3.gpr, u2.gpr, u1.gpr]; exact a 3 (by decide)) (by rw [u3.wr, u2.wr, u1.wr]; exact hcs.inW (by omega_arith))
    fun s4 u4 => ?_
  refine wp_addi (by decide) fun s5 u5 => wp_subi (by decide) fun s6 u6 => WP.block_nil ?_
  have hg4 : s4.gpr = s.gpr := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  have hm6 : s6.mem = (((s.mem.writeW (b + BitVec.ofNat 64 (TB + (4 * j + 0))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TB + (4 * j + 1))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TB + (4 * j + 2))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TB + (4 * j + 3))) (BitVec.ofNat 8 0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, u2.gpr, u1.gpr, e7, setWidth8_ofNat' (by decide)]
  have r11' : s6.gpr .t0 = BitVec.ofNat 64 (468 - (j + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), hg4, h.t0, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
  have hr6 : Rest [.a6, .t0] s s6 := ((u1.rest _).trans ((u2.rest _).trans ((u3.rest _).trans (u4.rest _)))).trans
    ((u5.rest (by decide)).trans (u6.rest (by decide)))
  refine ⟨⟨h.rest.trans hr6, ?_, r11', ?_, fun h' hh => ?_⟩, by rw [r11', ofNat_ne_zero (by omega_arith)]⟩
  · rw [u6.other _ (by decide), u5.gpr, hg4, h.a6, Offset.add_add, Nat.mul_succ, Nat.add_assoc]
  · rw [hm6]
    refine ((((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hm6]
    simp only [VG.WriteBytes.writeW8_apply]
    have ne : ∀ i < 4, h' ≠ 4 * j + i → b + BitVec.ofNat 64 (TB + h') ≠ b + BitVec.ofNat 64 (TB + (4 * j + i)) :=
      fun i _ hne => Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    rcases Nat.lt_or_ge h' (4 * j) with hl | hl
    · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)),
        iteF (ne 1 (by decide) (by omega_arith)), iteF (ne 0 (by decide) (by omega_arith))]
      exact h.vals h' hl
    · rcases (by omega_arith : h' = 4 * j + 0 ∨ h' = 4 * j + 1 ∨ h' = 4 * j + 2 ∨ h' = 4 * j + 3) with e | e | e | e <;>
        subst e
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)),
          iteF (ne 1 (by decide) (by omega_arith)), iteT rfl]
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)), iteT rfl]
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteT rfl]
      · rw [iteT rfl]

theorem bitsZero_ok {s : State} (hc : VCtx b s) :
    WP isa bitsZero s fun t => VCtx b t ∧ Rest [.a4, .a6, .t0] s t ∧
      Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s.mem t.mem ∧ TbIs b t.mem fun _ => 0 := by
  unfold bitsZero
  refine WP.seq (wp_addi (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a4, .a6, .t0] s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hc3 : VCtx b s3 := hc.of_rest hr3 (by decide) (by decide)
  have h0 : ZInv b s3 0 s3 := ⟨Rest.refl _ _, by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.a0, BitVec.add_zero, Nat.mul_zero, Nat.add_zero],
    by rw [u3.other _ (by decide), u2.gpr], Frame.refl _ _, fun h hh => absurd hh (by omega_arith)⟩
  have h7 : s3.gpr .a4 = BitVec.ofNat 64 0 := by rw [u3.gpr]
  refine WP.mono (Q := ZInv b s3 468) (WP.loop (M := isa)
    (fun m s' => ∃ j, m = 468 - j ∧ j < 468 ∧ ZInv b s3 j s') ?_ 468 s3 ⟨0, rfl, by decide, h0⟩) fun t ht => ?_
  · rintro m s' ⟨j, rfl, hj, hf⟩
    refine WP.mono (zeroStep_ok hc3 h7 hj hf) fun s'' ⟨hf', hz⟩ => ?_
    by_cases h468 : j + 1 = 468
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h468], by rw [h468] at hf'; exact hf'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 468 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hf'⟩
  · exact ⟨hc3.of_rest ht.rest (by decide) (by decide), hr3.trans (ht.rest.mono (by decide)),
      by rw [← hm3]; exact ht.frame, fun h hh => ht.vals h hh⟩

/-! ## Bits -/

/-- The entries after the bits of the first `i` bytes and `j` bits of byte `i`
at `sc` (in `m0`) into lane `e`, over `f`. -/
def tbCur (m0 : Mem) (sc : Addr) (e : Nat) (f : Nat → Nat) (i j : Nat) (h : Nat) : Nat :=
  if h % 4 = e ∧ (h / 32 < i ∨ h / 32 = i ∧ h % 32 / 4 < j) then rawBit m0 sc (h / 4) else f h

/-- While storing the bits of byte `i`, from `s1` (with the byte in `a4`). -/
structure DBJInv (b : Addr) (m0 : Mem) (sc : Addr) (e : Nat) (f : Nat → Nat) (i : Nat) (s1 : State) (j : Nat)
    (s : State) : Prop where
  rest : Rest [.a5] s1 s
  frame : Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s1.mem s.mem
  tab : TbIs b s.mem (tbCur m0 sc e f i j)

theorem dbitStep_ok {m0 : Mem} {sc : Addr} {e : Nat} (he : e < 4) {f : Nat → Nat} {i j : Nat} (hi : i < 57)
    (hj : j < 8) {s1 s : State} (hc : VCtx b s1) (h7 : (s1.gpr .a4).toNat = (m0 (sc + BitVec.ofNat 64 i)).toNat)
    (h9 : s1.gpr .a6 = b + BitVec.ofNat 64 (OUT + 32 * i)) (h : DBJInv b m0 sc e f i s1 j s) :
    WP isa (.block [.shift .sll .d .a5 .a4 (63 - j), .shift .srl .d .a5 .a5 63,
        .store .b .a5 .a6 (TB - OUT + 4 * j + e)]) s
      (DBJInv b m0 sc e f i s1 (j + 1)) := by
  have hT : TB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  have e7 : (s.gpr .a4).toNat = (m0 (sc + BitVec.ofNat 64 i)).toNat := by rw [h.rest.gpr _ (by decide), h7]
  have e9 : s.gpr .a6 = b + BitVec.ofNat 64 (OUT + 32 * i) := by rw [h.rest.gpr _ (by decide), h9]
  have hcs : VCtx b s := hc.of_rest h.rest (by decide) (by decide)
  refine wp_sll (by omega_arith) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have e8 : (s3.gpr .a5).toNat = ((m0 (sc + BitVec.ofNat 64 i)).toNat >>> j) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega_arith), e7]
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (32 * i + 4 * j + e))) (by omega_arith)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), e9, Offset.add_add]; congr 2; omega_arith)
    (by rw [u3.wr, u2.wr]; exact hcs.inW (by omega_arith)) fun s4 u4 => WP.block_nil ⟨?_, ?_, fun h' hh => ?_⟩
  · exact h.rest.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest _)))
  · rw [u4.mem, u3.mem, u2.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  · rw [u4.mem, VG.WriteBytes.writeW8_apply, u3.mem, u2.mem]
    by_cases e0 : h' = 32 * i + 4 * j + e
    · subst e0
      rw [iteT rfl, stb_byte e8, tbCur, ite_eq_left (by omega_arith), rawBit,
        show (32 * i + 4 * j + e) / 4 / 8 = i by omega_arith, show (32 * i + 4 * j + e) / 4 % 8 = j by omega_arith]
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)), h.tab h' hh]
      congr 1
      unfold tbCur
      by_cases c : h' % 4 = e ∧ (h' / 32 < i ∨ h' / 32 = i ∧ h' % 32 / 4 < j)
      · rw [ite_eq_left c, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c, ite_eq_right (by omega_arith)]

/-- The loop invariant of `bitsOf` from `s0`, before byte `i`. -/
structure DBInv (b : Addr) (sc : Addr) (e : Nat) (f : Nat → Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : VCtx b s
  rest : Rest [.a1, .a4, .a5, .a6, .t0] s0 s
  a1 : s.gpr .a1 = sc + BitVec.ofNat 64 i
  a6 : s.gpr .a6 = b + BitVec.ofNat 64 (OUT + 32 * i)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (57 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s0.mem s.mem
  tab : TbIs b s.mem (tbCur s0.mem sc e f i 0)

theorem dbitsBody_ok {src e : Nat} (hsrc : 1064 ≤ src) (hsrc' : src + 57 ≤ 2048) (he : e < 4) {f : Nat → Nat}
    {s0 : State} {i : Nat} (hi : i < 57) {s : State} (h : DBInv b (b + BitVec.ofNat 64 src) e f s0 i s) :
    WP isa (.block (bitsBody e)) s fun s' => DBInv b (b + BitVec.ofNat 64 src) e f s0 (i + 1) s' ∧
      (s'.gpr .t0 != 0) = decide (57 - (i + 1) ≠ 0) := by
  have hT : TB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  unfold bitsBody
  simp only [List.cons_append, List.nil_append]
  refine wp_lbz (a := b + BitVec.ofNat 64 (src + i)) (by decide)
    (by rw [h.a1, BitVec.add_zero, Offset.add_add]) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  have hc1 : VCtx b s1 := h.ctx.of_rest (u1.rest (ws := [.a4]) (by decide)) (by decide) (by decide)
  have hx : (s1.gpr .a4).toNat = (s0.mem (b + BitVec.ofNat 64 src + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)), Offset.add_add]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact Offset.disjoint b (d := src + i) (n := 1) (e := TB) (k := 1872) (by omega_arith) (by omega_arith)
      (by omega_arith) _ (Region.contains_self _ _) hcon
  refine WP.append (wp_range_flatMap (M := isa) (DBJInv b s0.mem (b + BitVec.ofNat 64 src) e f i s1)
    (fun j s' hj h' => dbitStep_ok he hi hj hc1 hx (by rw [u1.other _ (by decide), h.a6]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun h' hh => by rw [u1.mem]; exact h.tab h' hh⟩) fun s2 h2 => ?_
  refine wp_addi (by decide) fun s3 u3 => wp_addi (by decide) fun s4 u4 =>
    wp_subi (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.a1, .a4, .a5, .a6, .t0] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have r11' : s5.gpr .t0 = BitVec.ofNat 64 (57 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.t0, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  refine ⟨⟨h.ctx.of_rest hr5 (by decide) (by decide), h.rest.trans hr5, ?_, ?_, r11', ?_, fun h' hh => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.a1, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.a6, Offset.add_add, Nat.mul_succ, Nat.add_assoc]
  · rw [hm5]
    exact h.frame.trans (by rw [← u1.mem]; exact h2.frame)
  · rw [hm5, h2.tab h' hh]
    congr 1
    unfold tbCur
    by_cases c : h' % 4 = e ∧ (h' / 32 < i ∨ h' / 32 = i ∧ h' % 32 / 4 < 8)
    · rw [ite_eq_left c, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right c, ite_eq_right (by omega_arith)]
  · rw [r11', ofNat_ne_zero (by omega_arith)]

theorem bitsOf_ok {s : State} (hc : VCtx b s) {src e : Nat} (hsrc : 1064 ≤ src) (hsrc' : src + 57 ≤ 2048)
    (he : e < 4) {f : Nat → Nat} (hf : TbIs b s.mem f) :
    WP isa (bitsOf src e) s fun t => VCtx b t ∧ Rest [.a1, .a4, .a5, .a6, .t0] s t ∧
      Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s.mem t.mem ∧
      TbIs b t.mem (tbSet e (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 src) 57)) f) := by
  have hO : OUT = 2048 := rfl
  unfold bitsOf
  refine WP.seq (wp_addi (by decide) fun s1 u1 => wp_addi (by omega_arith) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a1, .a6, .t0] s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have h0 : DBInv b (b + BitVec.ofNat 64 src) e f s3 0 s3 :=
    ⟨hc.of_rest hr3 (by decide) (by decide), Rest.refl _ _,
      by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hc.ctx.a3, BitVec.add_zero],
      by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.a0, BitVec.add_zero, Nat.mul_zero, Nat.add_zero],
      by rw [u3.gpr], Frame.refl _ _, fun h' hh => by
        rw [hm3, hf h' hh]; congr 1; unfold tbCur; rw [ite_eq_right (by omega_arith)]⟩
  refine WP.mono (Q := DBInv b (b + BitVec.ofNat 64 src) e f s3 57) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 57 - i ∧ i < 57 ∧ DBInv b (b + BitVec.ofNat 64 src) e f s3 i s') ?_ 57 s3
      ⟨0, rfl, by decide, h0⟩) fun t ht => ⟨ht.ctx, (hr3.mono (by decide)).trans ht.rest, by
        rw [← hm3]; exact ht.frame, fun h' hh => ?_⟩
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (dbitsBody_ok hsrc hsrc' he hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h57 : i + 1 = 57
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h57], by rw [h57] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 57 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hb'⟩
  · rw [ht.tab h' hh]
    congr 1
    unfold tbCur tbSet
    by_cases c : h' % 4 = e ∧ h' / 4 < 456
    · rw [ite_eq_left (by omega_arith), ite_eq_left c, hm3, rawBit, Proof.Ed448.scalar_bit s.mem _ (by omega_arith)]
    · rw [ite_eq_right (by omega_arith), ite_eq_right c]


/-! ## Recoding -/

theorem recodeBody_eq (e : Nat) : recodeBody e =
    [.load .b .a4 .a6 (TB - OUT + e),
      .load .b .a5 .a6 (TB - OUT + 4 * 1 + e), .shift .sll .d .a5 .a5 1, .logic .or .a4 .a4 .a5,
      .load .b .a5 .a6 (TB - OUT + 4 * 2 + e), .shift .sll .d .a5 .a5 2, .logic .or .a4 .a4 .a5,
      .load .b .a5 .a6 (TB - OUT + 4 * 3 + e), .shift .sll .d .a5 .a5 3, .logic .or .a4 .a4 .a5,
      .load .b .a5 .a6 (TB - OUT + 4 * 4 + e), .shift .sll .d .a5 .a5 4, .logic .or .a4 .a4 .a5,
      .add .a5 .a4 .a7, .addi .a5 .a5 16, .logicImm .and .a5 .a5 31,
      .logicImm .and .t3 .a5 1, .shift .srl .d .t4 .a5 4, .shift .sll .d .t4 .t4 5, .sub .t4 .a5 .t4,
      .li .t5 0, .sub .t5 .t5 .t3, .logic .and .t4 .t4 .t5,
      .store .b .t4 .a6 (TB - OUT + e + 2),
      .logicImm .and .t3 .a4 1, .add .a7 .a7 .t3, .addi .a7 .a7 16, .sub .a7 .a7 .t4, .shift .srl .d .a7 .a7 1,
      .addi .a6 .a6 4, .addi .t0 .t0 (-1)] := rfl

theorem half_false : half false = 16 := rfl
theorem radix_false : radix false = 32 := rfl

/-- The loop invariant of `recode e` from `s0`, before position `n`. -/
structure RInv (b : Addr) (e k : Nat) (f : Nat → Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  ctx : VCtx b s
  rest : Rest [.a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5] s0 s
  a6 : s.gpr .a6 = b + BitVec.ofNat 64 (OUT + 4 * n)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (464 - n)
  carry : ∃ c ≤ 32, s.gpr .a7 = BitVec.ofNat 64 c ∧ residual false k n + 16 = k / 2 ^ n + c
  frame : Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s0.mem s.mem
  tab : TbIs b s.mem (recCur e k f n)

theorem _root_.VG.RISCV64.Steps.Upd.at {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (r : Reg) :
    s'.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · rw [ite_eq_left h, h, u.gpr]
  · rw [ite_eq_right h, u.other _ h]

theorem recodeBody_ok {e k : Nat} (he : e < 2) {f : Nat → Nat} (hf : ∀ i < 468, f (4 * i + e) = wbit k i)
    {s0 : State} {n : Nat} (hn : n < 464) {s : State} (h : RInv b e k f s0 n s) :
    WP isa (.block (recodeBody e)) s fun s' => RInv b e k f s0 (n + 1) s' ∧
      (s'.gpr .t0 != 0) = decide (464 - (n + 1) ≠ 0) := by
  have hT : TB = 2104 := rfl
  have hO : OUT = 2048 := rfl
  obtain ⟨c, hc, hc7, hres⟩ := h.carry
  rw [recodeBody_eq]
  -- The five bits.
  have ad : ∀ j < 5, s.gpr .a6 + BitVec.ofNat 64 (TB - OUT + 4 * j + e) =
      b + BitVec.ofNat 64 (TB + (4 * (n + j) + e)) := fun j _ => by
    rw [h.a6, Offset.add_add]; congr 2; omega_arith
  have rb : ∀ j < 5, (s.mem (b + BitVec.ofNat 64 (TB + (4 * (n + j) + e)))).toNat = wbit k (n + j) := fun j _ => by
    rw [h.tab _ (by omega_arith), recCur, ite_eq_right (by omega_arith), hf _ (by omega_arith), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Proof.Ed448.WnafWide.bit_lt _ _) (by decide))]
  have inr : ∀ j < 5, InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (TB + (4 * (n + j) + e))) 1 := fun j _ =>
    h.ctx.inR (by omega_arith)
  refine wp_lbz (a := b + BitVec.ofNat 64 (TB + (4 * (n + 0) + e))) (by omega_arith) (by simpa using ad 0 (by decide))
    (inr 0 (by decide)) fun s1 u1 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (TB + (4 * (n + 1) + e))) (by omega_arith)
    (by rw [u1.other _ (by decide)]; exact ad 1 (by decide))
    (by rw [u1.rd, u1.wr]; exact inr 1 (by decide)) fun s2 u2 => wp_sll (by decide) fun s3 u3 => wp_or fun s4 u4 => ?_
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have w4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]
  have a4' : s4.gpr .a6 = s.gpr .a6 := by
    simp only [reduceCtorEq, u4.at, u3.at, u2.at, u1.at, ↓reduceIte]
  refine wp_lbz (a := b + BitVec.ofNat 64 (TB + (4 * (n + 2) + e))) (by omega_arith)
    (by rw [a4']; exact ad 2 (by decide))
    (by rw [w4]; exact inr 2 (by decide)) fun s5 u5 => wp_sll (by decide) fun s6 u6 => wp_or fun s7 u7 => ?_
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, m4]
  have w7 : s7.rd ++ s7.wr = s.rd ++ s.wr := by rw [u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, w4]
  have a7' : s7.gpr .a6 = s.gpr .a6 := by
    simp only [reduceCtorEq, u7.at, u6.at, u5.at, ↓reduceIte, a4']
  refine wp_lbz (a := b + BitVec.ofNat 64 (TB + (4 * (n + 3) + e))) (by omega_arith)
    (by rw [a7']; exact ad 3 (by decide))
    (by rw [w7]; exact inr 3 (by decide)) fun s8 u8 => wp_sll (by decide) fun s9 u9 => wp_or fun s10 u10 => ?_
  have m10 : s10.mem = s.mem := by rw [u10.mem, u9.mem, u8.mem, m7]
  have w10 : s10.rd ++ s10.wr = s.rd ++ s.wr := by rw [u10.rd, u10.wr, u9.rd, u9.wr, u8.rd, u8.wr, w7]
  have a10' : s10.gpr .a6 = s.gpr .a6 := by
    simp only [reduceCtorEq, u10.at, u9.at, u8.at, ↓reduceIte, a7']
  refine wp_lbz (a := b + BitVec.ofNat 64 (TB + (4 * (n + 4) + e))) (by omega_arith)
    (by rw [a10']; exact ad 4 (by decide))
    (by rw [w10]; exact inr 4 (by decide)) fun s11 u11 => wp_sll (by decide) fun s12 u12 => wp_or fun s13 u13 => ?_
  have m13 : s13.mem = s.mem := by rw [u13.mem, u12.mem, u11.mem, m10]
  have hbits : s13.gpr .a4 = BitVec.ofNat 64 (look k n 5) := by
    simp only [reduceCtorEq, u13.at, u12.at, u11.at, u10.at, u9.at, u8.at, u7.at, u6.at, u5.at,
      u4.at, u3.at, u2.at, u1.at, ↓reduceIte, m10, m7, m4, u1.mem]
    rw [rb 0 (by decide), rb 1 (by decide), rb 2 (by decide), rb 3 (by decide), rb 4 (by decide),
      bits_word _ (Proof.Ed448.WnafWide.bit_lt _ _) _ (Proof.Ed448.WnafWide.bit_lt _ _) _
      (Proof.Ed448.WnafWide.bit_lt _ _) _ (Proof.Ed448.WnafWide.bit_lt _ _) _ (Proof.Ed448.WnafWide.bit_lt _ _), look5,
      Nat.add_zero]
  have hlt : look k n 5 < 32 := Nat.mod_lt _ (by decide)
  have h7 : s13.gpr .a7 = BitVec.ofNat 64 c := by
    rw [← hc7]
    simp only [reduceCtorEq, u13.at, u12.at, u11.at, u10.at, u9.at, u8.at, u7.at, u6.at, u5.at,
      u4.at, u3.at, u2.at, u1.at, ↓reduceIte]
  have a13' : s13.gpr .a6 = s.gpr .a6 := by
    simp only [reduceCtorEq, u13.at, u12.at, u11.at, ↓reduceIte, a10']
  have t13 : s13.gpr .t0 = s.gpr .t0 := by
    simp only [reduceCtorEq, u13.at, u12.at, u11.at, u10.at, u9.at, u8.at, u7.at, u6.at, u5.at,
      u4.at, u3.at, u2.at, u1.at, ↓reduceIte]
  -- The digit.
  refine wp_add fun s14 u14 => wp_addi (by decide) fun s15 u15 => wp_andi (by decide) fun s16 u16 =>
    wp_andi (by decide) fun s17 u17 => wp_srl (by decide) fun s18 u18 => wp_sll (by decide) fun s19 u19 =>
    wp_sub fun s20 u20 => wp_li (by decide) fun s21 u21 => wp_sub fun s22 u22 => wp_and fun s23 u23 => ?_
  have hd : s23.gpr .t4 = BitVec.ofInt 64 (localDigit false (look k n 5) c) := by
    rw [← digit_word hlt hc, ← hbits, ← h7]
    simp only [reduceCtorEq, u23.at, u22.at, u21.at, u20.at, u19.at, u18.at, u17.at, u16.at,
      u15.at, u14.at, ↓reduceIte, digitW]
  have m23 : s23.mem = s.mem := by
    rw [u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, m13]
  have w23 : s23.wr = s.wr := by
    rw [u23.wr, u22.wr, u21.wr, u20.wr, u19.wr, u18.wr, u17.wr, u16.wr, u15.wr, u14.wr, u13.wr, u12.wr, u11.wr,
      u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  have a23' : s23.gpr .a6 = s.gpr .a6 := by
    simp only [reduceCtorEq, u23.at, u22.at, u21.at, u20.at, u19.at, u18.at, u17.at, u16.at,
      u15.at, u14.at, ↓reduceIte, a13']
  refine wp_sb (a := b + BitVec.ofNat 64 (TB + (4 * n + (e + 2)))) (by omega_arith)
    (by rw [a23', h.a6, Offset.add_add]; congr 2; omega_arith) (by rw [w23]; exact h.ctx.inW (by omega_arith))
    fun s24 u24 => ?_
  -- The carry.
  refine wp_andi (by decide) fun s25 u25 => wp_add fun s26 u26 => wp_addi (by decide) fun s27 u27 =>
    wp_sub fun s28 u28 => wp_srl (by decide) fun s29 u29 => wp_addi (by decide) fun s30 u30 =>
    wp_subi (by decide) fun s31 u31 => WP.block_nil ?_
  have g24 : s24.gpr = s23.gpr := u24.gpr
  have hq : residual false k n + half false = k / 2 ^ n + c := by rw [half_false]; exact hres
  have hdig : localDigit false (look k n 5) c = digitAt false k n := by
    rw [look5_mod, ← radix_false]; exact Proof.Ed448.WnafWide.local_digit false hq
  have hc' : s31.gpr .a7 = BitVec.ofNat 64 (carryNext false (look k n 5) c) := by
    rw [← carry_word hlt hc, ← hbits, ← h7, ← hd]
    simp only [reduceCtorEq, u31.at, u30.at, u29.at, u28.at, u27.at, u26.at, u25.at, g24,
      u23.at, u22.at, u21.at, u20.at, u19.at, u18.at, u17.at, u16.at, u15.at, u14.at, ↓reduceIte]
  have hr31 : Rest [.a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5] s s31 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans
      ((u9.rest (by decide)).trans ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
      ((u13.rest (by decide)).trans ((u14.rest (by decide)).trans ((u15.rest (by decide)).trans ((u16.rest (by decide)).trans
      ((u17.rest (by decide)).trans ((u18.rest (by decide)).trans ((u19.rest (by decide)).trans ((u20.rest (by decide)).trans
      ((u21.rest (by decide)).trans ((u22.rest (by decide)).trans ((u23.rest (by decide)).trans ((u24.rest _).trans
      ((u25.rest (by decide)).trans ((u26.rest (by decide)).trans ((u27.rest (by decide)).trans ((u28.rest (by decide)).trans
      ((u29.rest (by decide)).trans ((u30.rest (by decide)).trans ((u31.rest (by decide))))))))))))))))))))))))))))))))
  have hm31 : s31.mem = s.mem.writeW (b + BitVec.ofNat 64 (TB + (4 * n + (e + 2))))
      (BitVec.ofInt 8 (digitAt false k n)) := by
    rw [u31.mem, u30.mem, u29.mem, u28.mem, u27.mem, u26.mem, u25.mem, u24.mem, m23, hd, ofInt_byte, hdig]
  have r11' : s31.gpr .t0 = BitVec.ofNat 64 (464 - (n + 1)) := by
    have : s30.gpr .t0 = s.gpr .t0 := by
      simp only [reduceCtorEq, u30.at, u29.at, u28.at, u27.at, u26.at, u25.at, g24,
        u23.at, u22.at, u21.at, u20.at, u19.at, u18.at, u17.at, u16.at, u15.at, u14.at, ↓reduceIte, t13]
    rw [u31.gpr, this, h.t0, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  have a31 : s31.gpr .a6 = b + BitVec.ofNat 64 (OUT + 4 * (n + 1)) := by
    have : s29.gpr .a6 = s.gpr .a6 := by
      simp only [reduceCtorEq, u29.at, u28.at, u27.at, u26.at, u25.at, g24, ↓reduceIte, a23']
    rw [u31.other _ (by decide), u30.gpr, this, h.a6, Offset.add_add, Nat.mul_succ, Nat.add_assoc]
  refine ⟨⟨h.ctx.of_rest hr31 (by decide) (by decide), h.rest.trans hr31, a31, r11',
    ⟨_, (by rw [← radix_false]; exact Proof.Ed448.WnafWide.carry_bounds false (by rw [radix_false]; exact hc)), hc', ?_⟩,
    ?_, fun h' hh => ?_⟩, by rw [r11', ofNat_ne_zero (by omega_arith)]⟩
  · have hs := Proof.Ed448.WnafWide.carry_step false hq
    rw [half_false, radix_false] at hs
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, look5_mod]
    exact hs
  · rw [hm31]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  · rw [hm31, VG.WriteBytes.writeW8_apply]
    by_cases e0 : h' = 4 * n + (e + 2)
    · subst e0
      rw [iteT rfl, recCur, ite_eq_left (by omega_arith), show (4 * n + (e + 2)) / 4 = n by omega_arith,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)), h.tab h' hh]
      congr 1
      unfold recCur
      by_cases cnd : h' % 4 = e + 2 ∧ h' / 4 < n
      · rw [ite_eq_left cnd, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right cnd, ite_eq_right (by omega_arith)]

theorem recode_ok {s : State} (hc : VCtx b s) {e k : Nat} (he : e < 2) {f : Nat → Nat}
    (hf : ∀ i < 468, f (4 * i + e) = wbit k i) (hft : TbIs b s.mem f) :
    WP isa (recode e) s fun t => VCtx b t ∧ Rest [.a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5] s t ∧
      Frame [⟨b + BitVec.ofNat 64 TB, 1872⟩] s.mem t.mem ∧ TbIs b t.mem (recCur e k f 464) := by
  unfold recode
  refine WP.seq (wp_addi (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a6, .a7, .t0] s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have h0 : RInv b e k f s3 0 s3 :=
    ⟨hc.of_rest hr3 (by decide) (by decide), Rest.refl _ _,
      by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.a0, BitVec.add_zero, Nat.mul_zero,
        Nat.add_zero],
      by rw [u3.gpr], ⟨16, by decide, by rw [u3.other _ (by decide), u2.gpr], by
        simp only [Impl.Ed448.WnafWide.residual, Nat.pow_zero, Nat.div_one]⟩,
      Frame.refl _ _, fun h' hh => by
        rw [hm3, hft h' hh]; congr 1; unfold recCur; rw [ite_eq_right (by omega_arith)]⟩
  refine WP.mono (Q := RInv b e k f s3 464) (WP.loop (M := isa)
    (fun m s' => ∃ n, m = 464 - n ∧ n < 464 ∧ RInv b e k f s3 n s') ?_ 464 s3 ⟨0, rfl, by decide, h0⟩)
    fun t ht => ⟨ht.ctx, (hr3.mono (by decide)).trans ht.rest, by rw [← hm3]; exact ht.frame, ht.tab⟩
  rintro m s' ⟨n, rfl, hn, hb⟩
  refine WP.mono (recodeBody_ok he hf hn hb) fun s'' ⟨hb', hz⟩ => ?_
  by_cases h464 : n + 1 = 464
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h464], by rw [h464] at hb'; exact hb'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 464 - (n + 1), by omega_arith, n + 1, rfl, by omega_arith, hb'⟩

end


/-! ## Copies and the base table -/


open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Proof.X448.RISCV64.R64 (dw al8 V_eq val7_congr)

section
variable {b : Addr}

/-! ## Copies -/

/-- After the first `k` doublewords of a copy from `ps` to `pd`. -/
structure CInv (b : Addr) (s0 : State) (ps pd k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 pd, 56⟩] s0.mem s.mem
  vals : ∀ i < k, dw s.mem b (pd + 8 * i) = dw s0.mem b (ps + 8 * i)

theorem cp7_ok {s : State} (hc : VCtx b s) {rs rd : Reg} {so d ps pd : Nat} (hrs : rs ≠ .a4) (hrd : rd ≠ .a4)
    (hso : so + 48 < 2048) (hd : d + 48 < 2048)
    (hs : s.gpr rs + BitVec.ofNat 64 so = b + BitVec.ofNat 64 ps)
    (hdd : s.gpr rd + BitVec.ofNat 64 d = b + BitVec.ofNat 64 pd)
    (hps : ps % 8 = 0) (hpd : pd % 8 = 0) (hps' : ps + 56 ≤ 8184) (hpd' : pd + 56 ≤ 8184)
    (hsep : ps + 56 ≤ pd ∨ pd + 56 ≤ ps) :
    WP isa (.block (cp7 rs so rd d)) s fun t => VCtx b t ∧ Rest [.a4] s t ∧
      Frame [⟨b + BitVec.ofNat 64 pd, 56⟩] s.mem t.mem ∧
      ∀ i < 7, dw t.mem b (pd + 8 * i) = dw s.mem b (ps + 8 * i) := by
  have as : ∀ k, s.gpr rs + BitVec.ofNat 64 (so + 8 * k) = b + BitVec.ofNat 64 (ps + 8 * k) := fun k => by
    rw [← Offset.add_add, hs, Offset.add_add]
  have ad : ∀ k, s.gpr rd + BitVec.ofNat 64 (d + 8 * k) = b + BitVec.ofNat 64 (pd + 8 * k) := fun k => by
    rw [← Offset.add_add, hdd, Offset.add_add]
  refine WP.mono (wp_range_flatMap (M := isa) (CInv b s ps pd)
    (fun k t hk ht => ?_) 7 (Nat.le_refl _) s ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩)
    fun t ht => ⟨hc.of_rest ht.rest (by decide) (by decide), ht.rest, ht.frame, ht.vals⟩
  have hct : VCtx b t := hc.of_rest ht.rest (by decide) (by decide)
  refine wp_ld (by omega) (by rw [ht.rest.gpr _ (by simpa using hrs)]; exact as k)
    (al8 hc.ctx.al (by omega)) (hct.inR (by omega)) fun t1 u1 => ?_
  refine wp_sd (by omega) (by rw [u1.other _ hrd, ht.rest.gpr _ (by simpa using hrd)]; exact ad k)
    (al8 hc.ctx.al (by omega)) (by rw [u1.wr]; exact hct.inW (by omega)) fun t2 u2 => WP.block_nil ?_
  have src : t.mem.readW (b + BitVec.ofNat 64 (ps + 8 * k)) 64 = s.mem.readW (b + BitVec.ofNat 64 (ps + 8 * k)) 64 :=
    ht.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨ht.rest.trans ((u1.rest (by decide)).trans (Mupd.rest u2 _)), ?_, fun i hi => ?_⟩
  · rw [u2.mem, u1.mem]
    exact ht.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · simp only [dw]
    rw [u2.mem, u1.mem, u1.gpr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact ht.vals i hi
    · rw [Mem.readW_writeW_self64, src]

/-- The copy keeps the element. -/
theorem cp7_V {m m' : Mem} {ps pd : Nat} (h : ∀ i < 7, dw m' b (pd + 8 * i) = dw m b (ps + 8 * i)) :
    V m' b pd = V m b ps := by
  rw [V_eq, V_eq]; exact val7_congr h

/-! ## The base table -/

/-- Entry `i < 8` of the base table: `PublicTable.entry i`, affine. -/
def BaseOk (b : Addr) (m : Mem) : Prop :=
  ∀ i < 8, V m b (BT + 112 * i) = (Impl.Ed448.PublicTable.entry i).1.val ∧
    V m b (BT + 112 * i + 56) = (Impl.Ed448.PublicTable.entry i).2.val

/-- The table's base. -/
abbrev btb (b : Addr) : Addr := b + BitVec.ofNat 64 BT

theorem btb_V (m : Mem) (o : Nat) : V m (btb b) o = V m b (BT + o) := by
  rw [V_eq, V_eq]
  refine val7_congr fun i _ => ?_
  simp only [R64.ew, dw]
  rw [btb, Offset.add_add, Nat.add_assoc]

/-- After the first `n` entries. -/
structure BTInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨btb b, 112 * n⟩] s0.mem s.mem
  vals : ∀ i < n, V s.mem (btb b) (112 * i) = (Impl.Ed448.PublicTable.entry i).1.val ∧
    V s.mem (btb b) (112 * i + 56) = (Impl.Ed448.PublicTable.entry i).2.val

theorem bentry_step {s0 : State} (hc : Ctx (btb b) s0) {i : Nat} (hi : i < 8) {s : State}
    (h : BTInv b s0 i s) :
    WP isa (.block (constField (112 * i) (Impl.Ed448.PublicTable.entry i).1.val ++
      constField (112 * i + 56) (Impl.Ed448.PublicTable.entry i).2.val)) s (BTInv b s0 (i + 1)) := by
  have hc1 : Ctx (btb b) s := hc.of_rest h.rest (by decide)
  refine WP.append (constField_ok hc1 (o := 112 * i) (by omega) (by omega) (fe_lt _))
    fun t ⟨rt, ft, vt⟩ => ?_
  refine WP.mono (constField_ok (hc1.of_rest rt (by decide)) (o := 112 * i + 56) (by omega) (by omega)
    (fe_lt _)) fun u ⟨ru, fu, vu⟩ => ⟨h.rest.trans (rt.trans ru), ?_, fun j hj => ?_⟩
  · have F1 : Frame [⟨btb b, 112 * (i + 1)⟩] s0.mem s.mem :=
      h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩
    have F2 : Frame [⟨btb b, 112 * (i + 1)⟩] s.mem t.mem :=
      ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)⟩
    have F3 : Frame [⟨btb b, 112 * (i + 1)⟩] t.mem u.mem :=
      fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)⟩
    exact F1.trans (F2.trans F3)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨e1, e2⟩ := h.vals j hj
      refine ⟨?_, ?_⟩
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e1
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e2
    · exact ⟨by rw [slot_keep fu (by omega) (by omega) (by omega)]; exact vt, vu⟩

theorem baseTable_ok {s : State} (hc : VCtx b s) :
    WP isa (.block baseTable) s fun t => VCtx b t ∧ Rest [.a4] s t ∧
      Frame [⟨b + BitVec.ofNat 64 BT, 896⟩] s.mem t.mem ∧ BaseOk b t.mem := by
  have hBT : BT = 5320 := rfl
  simp only [baseTable, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s1 u1 => wp_addi (by decide) fun s2 u2 => wp_addi (by decide) fun s3 u3 => ?_
  have e3 : s3.gpr .a3 = btb b := by
    rw [u3.gpr, u2.gpr, u1.gpr, hc.ctx.a3, Offset.add_add, Offset.add_add, btb, hBT]
  have hr3 : Rest [.a3] s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx (btb b) s3 := ⟨e3, al8 hc.ctx.al (by decide), fun d n hdn => by
    rw [hr3.wr, Offset.add_add]; exact hc.inW (by omega)⟩
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine WP.append (wp_range_flatMap (M := isa) (BTInv b s3) (fun i t hi h => bentry_step hc3 hi h)
    8 (Nat.le_refl _) s3 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩) fun t ht => ?_
  refine wp_subi (by decide) fun u1' v1 => wp_subi (by decide) fun u2' v2 => wp_subi (by decide) fun u v3 =>
    WP.block_nil ?_
  have ha3 : u.gpr .a3 = b := by
    rw [v3.gpr, v2.gpr, v1.gpr, ht.rest.gpr _ (by decide), e3, btb, hBT]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hch : Rest [.a3, .a4] s u := (hr3.mono (ws' := [.a3, .a4]) (by decide)).trans ((ht.rest.mono (by decide)).trans
      ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))))
  have hru : Rest [.a4] s u := ⟨fun r hr => by
    by_cases h3 : r = .a3
    · subst h3; rw [ha3, hc.ctx.a3]
    · exact hch.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact fun h => h.elim h3 hr), hch.rd, hch.wr, hch.sp⟩
  refine ⟨hc.of_rest hru (by decide) (by decide), hru, ?_, fun i hi => ?_⟩
  · rw [v3.mem, v2.mem, v1.mem, ← hm3]; exact ht.frame
  · rw [v3.mem, v2.mem, v1.mem, ← btb_V, show BT + 112 * i + 56 = BT + (112 * i + 56) by omega, ← btb_V]
    exact ht.vals i hi

end

end VG.Proof.Ed448.RISCV64
