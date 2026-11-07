module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.BE64
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory

/-! # Starting RSA key generation on RISC-V: correctness, constant time

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/KeyInit.lean`), with RISC-V's
comparisons (`sltu`) and the exponent's eight octets stored a byte at a time
(`storeBE`, `wp_storeBE8`), which needs no alignment.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.KeyInit

open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.RsaKeyGen.SearchInit (bytesAt_succ or_eq_zero shl_ofNat add_ofNat)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaKeyGen.RISCV64.KeyInit

/-! ## Comparisons and bits -/

/-- `sltu` of small numbers. -/
theorem ltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [this, h, ↓reduceIte]; rfl
  · simp only [this, h, ↓reduceIte]; rfl

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  change (0#0 ++ m a : BitVec (0 + 8)) = m a
  exact BitVec.zero_width_append _ _

theorem shl8_add (v : Nat) (hv : v < 2 ^ 32) (b : Byte) :
    BitVec.ofNat 64 v <<< 8 + b.setWidth 64 = BitVec.ofNat 64 (256 * v + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : v * 2 ^ 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem shr_ofNat {n : Nat} (hn : n < 2 ^ 64) (k : Nat) :
    BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

/-- `slli 32` then `srli 32`: the low 32 bits. -/
theorem low32 (n : Nat) : BitVec.ofNat 64 n <<< 32 >>> 32 = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 : n % 2 ^ 64 * 2 ^ 32 % 2 ^ 64 = n % 2 ^ 32 * 2 ^ 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right, Nat.mod_mul_right_mod]
  have h2 : n % 2 ^ 32 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [h1, Nat.mul_div_cancel _ (by decide), Nat.mod_eq_of_lt h2]

theorem os2ip_snoc (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · intro h; rw [h]; rfl

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact ofNat64_eq_zero hn

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

/-! ## The exponent's octets -/

/-- After `j` of `e`'s octets: its value so far modulo `2^32` in `t3`, and in
`t4`, below `2^8`, whether it is below `2^32`. -/
def ScanInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .a2 = P + BitVec.ofNat 64 j ∧
    u.gpr .t3 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) ∧
    (u.gpr .t4 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) < 2 ^ 32) ∧
    (u.gpr .t4).toNat < 2 ^ 8 ∧ u.mem = s.mem ∧ Keep [.a2, .a3, .t0, .t1, .t3, .t4] s u

theorem octet_ok {t : State} {P : Addr} {j v : Nat} {acc : BitVec 64}
    (hp : t.gpr .a2 = P + BitVec.ofNat 64 j) (hv : t.gpr .t3 = BitVec.ofNat 64 v) (hacc : t.gpr .t4 = acc)
    (hv32 : v < 2 ^ 32) (hr : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 j) 1) :
    WP isa (.block (octet ++ ([.addi .a3 .a3 (-1)] : List Instr))) t fun u =>
      (u.gpr .a2 = P + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .t3 = BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) % 2 ^ 32) ∧
        u.gpr .t4 = acc ||| BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) / 2 ^ 32) ∧
        u.mem = t.mem ∧ u.gpr .a3 = t.gpr .a3 - BitVec.ofNat 64 1) ∧
      Keep [.a2, .a3, .t0, .t1, .t3, .t4] t u := by
  refine WP.keep [.a2, .a3, .t0, .t1, .t3, .t4] ?_ (by decide +kernel)
  have hb := (t.mem (P + BitVec.ofNat 64 j)).isLt
  have hN : 256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 64 := by omega
  have e5 : P + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (j + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  unfold octet
  brun [hp, hv, hacc, hr, read_one, shl8_add v hv32, shr_ofNat hN, low32, e5]

theorem scan_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (h : ScanInv s P j u) :
    WP isa (.block (octet ++ ([.addi .a3 .a3 (-1)] : List Instr))) u fun v =>
      ScanInv s P (j + 1) v ∧ v.gpr .a3 = u.gpr .a3 - BitVec.ofNat 64 1 := by
  obtain ⟨hx2, hx3, hr4, hlt, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [k.2.1, k.2.2]; exact hrd j hj
  refine WP.mono (octet_ok hx2 hx3 rfl (Nat.mod_lt _ (by decide)) hr)
    fun v ⟨⟨h2, h3, h4, hmv, h6⟩, kv⟩ => ⟨⟨h2, ?_, ?_, ?_, hmv.trans hm, (k.trans kv).mono (by decide)⟩, h6⟩
  · rw [h3, bytesAt_succ, os2ip_snoc, hm]
    congr 1
    omega
  · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
    have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
    rw [h4, or_eq_zero, hr4, bytesAt_succ, os2ip_snoc, hm, ofNat64_eq_zero (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      have : 256 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) +
        (s.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 32 := (Nat.div_eq_zero_iff_lt (by decide)).mp h2
      omega
    · intro h
      exact ⟨by omega, Nat.div_eq_of_lt (by omega)⟩
  · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
    have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
    rw [h4, BitVec.toNat_or, BitVec.toNat_ofNat, hm]
    exact Nat.or_lt_two_pow hlt (by
      rw [Nat.mod_eq_of_lt (by omega)]
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega))

theorem scan_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .a2 = P)
    (hl : s.gpr .a3 = BitVec.ofNat 64 len) (hl64 : len < 2 ^ 64)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa scan s (ScanInv s P len) := by
  unfold scan
  refine WP.seq (WP.mono (WP.keep [.t3, .t4] (Q := fun t => t.gpr .t3 = 0 ∧ t.gpr .t4 = 0 ∧ t.mem = s.mem)
    (by brun [exec_li]; all_goals first | rfl | exact ⟨rfl, rfl⟩ | trivial) (by decide +kernel)) fun t ⟨⟨h3, h4, hm⟩, k⟩ => ?_)
  have h0 : ScanInv s P 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero], by rw [h3]; rfl,
    by rw [h4]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], by rw [h4]; decide, hm, k.mono (by decide)⟩
  have h6 : t.gpr .a3 = BitVec.ofNat 64 len := (k.gpr (by decide)).trans hl
  refine WP.ite (decide (len = 0)) (by rw [eval_zero, h6, ofNat_beq_zero hl64]) (fun hz => ?_) (fun hz => ?_)
  · have hz : len = 0 := of_decide_eq_true hz
    subst hz
    exact WP.block_nil h0
  · have hz : len ≠ 0 := of_decide_eq_false hz
    exact wp_countdown (N := len) hl64 (by omega) (ScanInv s P)
      (fun i hi u hI _ => scan_body hi hrd hI) h0 h6

/-! ## The status -/

/-- The status `vg_rsa_generate_init` returns, of the size and `e`'s value. -/
def initStatus (bits e : Nat) : Nat :=
  if !Spec.RsaKeyGen.exponentValid e then 0
  else if Spec.RsaKeyGen.modulusBits bits = none then 2 else 1

theorem initStatus_val (bits E : Nat) :
    initStatus bits E = if E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 then
      (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 2) else 0 := by
  unfold initStatus Spec.RsaKeyGen.exponentValid Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits
    Spec.RsaKeyGen.minBits
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | simp_all | omega

theorem and_one (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit_and (a b : Prop) [Decidable a] [Decidable b] :
    BitVec.ofNat 64 (if a then 1 else 0) &&& BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (if a ∧ b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem bit_not (a : Prop) [Decidable a] :
    BitVec.ofNat 64 (if a then 1 else 0) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 (if ¬a then 1 else 0) := by
  by_cases ha : a <;> simp only [ha, not_true_eq_false, not_false_eq_true, ↓reduceIte] <;> decide

theorem bit_mod2 (n : Nat) : BitVec.ofNat 64 (n % 2) = BitVec.ofNat 64 (if n % 2 = 1 then 1 else 0) := by
  congr 1; split <;> omega

theorem c8193 : BitVec.ofNat 64 1 <<< 13 + BitVec.ofNat 64 1 = BitVec.ofNat 64 8193 := by decide

/-- `expValid`: `t5` is 1 exactly for a valid exponent. -/
theorem expValid_ok (s : State) {E : Nat} (h3 : s.gpr .t3 = BitVec.ofNat 64 (E % 2 ^ 32))
    (h4 : s.gpr .t4 = 0 ↔ E < 2 ^ 32) (h4b : (s.gpr .t4).toNat < 2 ^ 8) :
    WP isa (.block expValid) s fun t =>
      (t.gpr .t5 = BitVec.ofNat 64 (if E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t0, .t5] s t := by
  refine WP.keep [.t0, .t5] ?_ (by decide +kernel)
  have hV : E % 2 ^ 32 < 2 ^ 64 := by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega
  have h4' : s.gpr .t4 = BitVec.ofNat 64 (s.gpr .t4).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hz : (s.gpr .t4).toNat < 1 ↔ E < 2 ^ 32 := by
    rw [← h4]; constructor
    · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
    · intro h; rw [h]; decide
  generalize (s.gpr .t4).toNat = X at h4' h4b hz
  generalize hVd : E % 2 ^ 32 = V at h3 hV
  unfold expValid
  brun [h3, h4', exec_li, ltu_ofNat (show X < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by decide),
    ltu_ofNat hV (show 3 < 2 ^ 64 by decide), and_one _ hV, bit_mod2, bit_and, bit_not]
  congr 2
  apply propext
  rw [hz]
  subst hVd
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : E % 2 ^ 32 = E := Nat.mod_eq_of_lt h1
    refine ⟨by omega, by omega, h1⟩
  · rintro ⟨h1, h2, h3⟩
    have : E % 2 ^ 32 = E := Nat.mod_eq_of_lt h3
    exact ⟨⟨h3, by omega⟩, by omega⟩

/-- `sizeValid`: `t6` is 1 exactly for a valid size. -/
theorem sizeValid_ok (s : State) {bits : Nat} (h1 : s.gpr .a1 = BitVec.ofNat 64 bits) (hb : bits < 2 ^ 64) :
    WP isa (.block sizeValid) s fun t =>
      (t.gpr .t6 = BitVec.ofNat 64 (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t0, .t6] s t := by
  refine WP.keep [.t0, .t6] ?_ (by decide +kernel)
  unfold sizeValid
  brun [h1, exec_li, c8193, ltu_ofNat hb (show 8193 < 2 ^ 64 by decide), ltu_ofNat hb (show 512 < 2 ^ 64 by decide),
    bit_not, bit_and]
  congr 2
  apply propext
  omega

theorem status_vals (a b : Prop) [Decidable a] [Decidable b] :
    (BitVec.ofNat 64 2 - BitVec.ofNat 64 (if b then 1 else 0)) * BitVec.ofNat 64 (if a then 1 else 0) =
      BitVec.ofNat 64 (if a then (if b then 1 else 2) else 0) ∧
    BitVec.ofNat 64 (if a then 1 else 0) * BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (if a ∧ b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

/-- `status`: the status in `t2` and its bit of 1 in `t1`. -/
theorem status_ok (s : State) (a b : Prop) [Decidable a] [Decidable b]
    (h5 : s.gpr .t5 = BitVec.ofNat 64 (if a then 1 else 0)) (h6 : s.gpr .t6 = BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (.block status) s fun t =>
      (t.gpr .t2 = BitVec.ofNat 64 (if a then (if b then 1 else 2) else 0) ∧
        t.gpr .t1 = BitVec.ofNat 64 (if a ∧ b then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.t1, .t2] s t := by
  refine WP.keep [.t1, .t2] ?_ (by decide +kernel)
  have hv := status_vals a b
  unfold status
  brun [h5, h6, exec_li]
  exact ⟨hv.1, hv.2⟩

/-! ## The words -/

/-- The seven words stored, from their values. -/
def stored (m : Mem) (B : Addr) (w : List (BitVec 64)) : Mem :=
  ((((((m.writeW B (w.getD 0 0)).writeW (off B 8) (w.getD 1 0)).writeW (off B 16) (w.getD 2 0)).writeW
    (off B 24) (w.getD 3 0)).writeW (off B 32) (w.getD 4 0)).writeW (off B 40) (w.getD 5 0)).writeW
    (off B 48) (w.getD 6 0)

/-- The primes' octets, from the size. -/
abbrev plenBV (bits : Nat) : BitVec 64 := (BitVec.ofNat 64 bits >>> 7) <<< 3

/-- 1 exactly for `V = 3`. -/
abbrev threeBV (V : Nat) : BitVec 64 := if (BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3) < BitVec.ofNat 64 1 then 1 else 0

/-- The words' values, if the status is 1. -/
def wordValues (bits V : Nat) : List (BitVec 64) :=
  let P := plenBV bits
  [P <<< 3 + P <<< 5 + (P <<< 4 + P <<< 3) * threeBV V, P, P <<< 15 + P, P <<< 5, 0, 1 <<< 2,
    byteRev64 (BitVec.ofNat 64 V)]

theorem words_ok {s : State} {B : Addr} {bits V : Nat} (ok : Prop) [Decidable ok] (scr : Scr s B 56)
    (h0 : s.gpr .a0 = B) (h1 : s.gpr .a1 = BitVec.ofNat 64 bits) (h3 : s.gpr .t3 = BitVec.ofNat 64 V)
    (ht1 : s.gpr .t1 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    WP isa (.block (words ++ ([.addi .a0 .t2 0] : List Instr))) s fun t =>
      (t.gpr .a0 = s.gpr .t2 ∧
        t.mem = stored s.mem B (if ok then wordValues bits V else List.replicate 7 0)) ∧
      Keep [.a0, .a1, .a3, .a4, .a5, .a6, .t0] s t := by
  refine WP.keep [.a0, .a1, .a3, .a4, .a5, .a6, .t0] ?_ (by decide +kernel)
  have r0 : byteRev64 (0#64 : BitVec 64) = 0#64 := by decide
  unfold words
  rw [List.append_assoc, WP.block_append_iff]
  -- The six words, then `e`'s octets.
  refine WP.mono (Q := fun u : State => u.gpr .a0 = B ∧ u.gpr .t2 = s.gpr .t2 ∧
      u.gpr .a5 = BitVec.ofNat 64 V * BitVec.ofNat 64 (if ok then 1 else 0) ∧ u.wr = s.wr ∧
      u.mem = (((((s.mem.writeW B ((if ok then wordValues bits V else List.replicate 7 0).getD 0 0)).writeW
        (off B 8) ((if ok then wordValues bits V else List.replicate 7 0).getD 1 0)).writeW (off B 16)
        ((if ok then wordValues bits V else List.replicate 7 0).getD 2 0)).writeW (off B 24)
        ((if ok then wordValues bits V else List.replicate 7 0).getD 3 0)).writeW (off B 32)
        ((if ok then wordValues bits V else List.replicate 7 0).getD 4 0)).writeW (off B 40)
        ((if ok then wordValues bits V else List.replicate 7 0).getD 5 0)) ?_ fun u hu => ?_
  · have st0 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (n := 8) (by decide)
    have al0 : B.toNat % 8 = 0 := by simpa only [off, BitVec.add_zero] using scr.al8 (d := 0) (by decide) (by decide)
    by_cases hok : ok <;>
    brun [h0, h1, h3, ht1, hok, exec_li, st0, al0, scr.st (d := 0) (n := 8) (by decide), scr.st (d := 8) (n := 8) (by decide),
      scr.st (d := 16) (n := 8) (by decide), scr.st (d := 24) (n := 8) (by decide),
      scr.st (d := 32) (n := 8) (by decide), scr.st (d := 40) (n := 8) (by decide),
      scr.al8 (d := 0) (by decide) (by decide), scr.al8 (d := 8) (by decide) (by decide),
      scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 24) (by decide) (by decide),
      scr.al8 (d := 32) (by decide) (by decide), scr.al8 (d := 40) (by decide) (by decide), off,
      BitVec.mul_one, BitVec.mul_zero, wordValues, List.getD_cons_zero, List.getD_cons_succ,
      List.replicate_succ, List.replicate_zero, BitVec.add_zero, BitVec.zero_shiftLeft]
    all_goals rfl
  · obtain ⟨hu0, hu2, hu5, huw, hum⟩ := hu
    have hst : InRegions u.wr (u.gpr .a0 + BitVec.ofNat 64 48) 8 := by
      rw [huw, hu0]; simpa only [off] using scr.st (d := 48) (n := 8) (by decide)
    refine VG.RISCV64.BE64.wp_storeBE8 (a := u.gpr .a0 + BitVec.ofNat 64 48) (by decide) (by decide) (by decide) rfl
      hst fun s₁ s' m₁ u₁ => ?_
    have ea : exec (.addi .a0 .t2 0) s' = some (s'.write .a0 (s'.gpr .t2 + BitVec.ofNat 64 0)) :=
      exec_addi_lit (by decide)
    refine VG.RISCV64.Steps.WP.cons ea (WP.block_nil ⟨?_, ?_⟩)
    · rw [RegUpd.gpr_write, ite_eq_left (by decide), BitVec.add_zero, u₁.other _ (by decide), m₁.gpr, hu2]
    · rw [RegUpd.mem_write, u₁.mem, m₁.mem, hum, hu5, hu0]
      unfold stored
      by_cases hok : ok
      · simp only [hok, ↓reduceIte, BitVec.mul_one, wordValues, List.getD_cons_succ, List.getD_cons_zero, off]
      · simp only [hok, ↓reduceIte, BitVec.mul_zero, List.replicate_succ, List.replicate_zero, List.getD_cons_succ,
          List.getD_cons_zero, off, r0]
        rfl

/-! ## The state's words and the exponent's octets -/

open VG.Proof.Ffdh.Control (controller_store_word)

theorem stored_eq (m : Mem) (B : Addr) (w : List (BitVec 64)) : stored m B w =
    ((((((m.writeW (off B (8 * 0)) (w.getD 0 0)).writeW (off B (8 * 1)) (w.getD 1 0)).writeW (off B (8 * 2))
      (w.getD 2 0)).writeW (off B (8 * 3)) (w.getD 3 0)).writeW (off B (8 * 4)) (w.getD 4 0)).writeW
      (off B (8 * 5)) (w.getD 5 0)).writeW (off B (8 * 6)) (w.getD 6 0) := by
  simp only [stored, off, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul]

theorem stored_word (m : Mem) (B : Addr) (w : List (BitVec 64)) {j : Nat} (hj : j < 7) :
    word (stored m B w) B (8 * j) = w.getD j 0 := by
  rw [stored_eq]
  simp only [controller_store_word _ _ _ (show 6 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 5 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 4 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 3 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 2 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 1 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 0 < 16 by decide) (show j < 16 by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    h | h | h | h | h | h | h <;> subst h <;> rfl

theorem stored_words6 (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.wordsAt (stored m B w) B 6 = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0,
      w.getD 5 0] := by
  change [word (stored m B w) B (8 * 0), word (stored m B w) B (8 * 1), word (stored m B w) B (8 * 2),
    word (stored m B w) B (8 * 3), word (stored m B w) B (8 * 4), word (stored m B w) B (8 * 5)] = _
  rw [stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide)]

theorem stored_words7 (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.wordsAt (stored m B w) B 7 = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0,
      w.getD 5 0, w.getD 6 0] := by
  change [word (stored m B w) B (8 * 0), word (stored m B w) B (8 * 1), word (stored m B w) B (8 * 2),
    word (stored m B w) B (8 * 3), word (stored m B w) B (8 * 4), word (stored m B w) B (8 * 5),
    word (stored m B w) B (8 * 6)] = _
  rw [stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide)]

/-- The octets of the last word stored. -/
theorem stored_bytes (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.bytesAt (stored m B w) (B + 48) 8 =
      (List.range 8).map fun i => (w.getD 6 0).extractLsb' (8 * i) 8 := by
  simp only [Spec.Rsa.bytesAt, stored]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Mem.writeW, Mem.write]
  have hx : (B + 48 + BitVec.ofNat 64 i - (B + 48)).toNat = i := by
    rw [BitVec.add_comm (B + 48), BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h48 : off B 48 = B + 48 := rfl
  rw [h48, hx, ite_eq_left (by omega)]
  simp only [BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

theorem rev_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (byteRev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    byteRev64_getLsbD _ (by omega)]
  simp only [hk, decide_true, Bool.true_and]
  congr 1
  omega

theorem rev_bytes {E : Nat} (hE : E < 2 ^ 64) :
    ((List.range 8).map fun i => (byteRev64 (BitVec.ofNat 64 E)).extractLsb' (8 * i) 8) = Spec.Rsa.i2osp E 8 := by
  simp only [Spec.Rsa.i2osp]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [rev_byte _ _ hi, shr_ofNat hE]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hE), show 8 - 1 - i = 7 - i by omega,
    show (256 : Nat) ^ (7 - i) = 2 ^ (8 * (7 - i)) by rw [Nat.pow_mul]]

/-! ## The result -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] ∧ s.wr = [⟨s.gpr .a0, 56⟩] ∧
    (s.gpr .a0).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0

def initPost (s t : State) : Prop :=
  let eB := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
  match Spec.RsaKeyGen.keySearchInit (s.gpr .a1).toNat eB with
  | .error c => ((t.gpr .a0).setWidth 32).toNat = c ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 7 = List.replicate 7 0
  | .ok values => ((t.gpr .a0).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 6 =
        (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0 + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip eB) 8 ∧
      Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first

theorem plen_eq {bits : Nat} (hb : bits < 2 ^ 64) : plenBV bits = BitVec.ofNat 64 (bits / 128 * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem three_eq {V : Nat} (hV : V < 2 ^ 32) : threeBV V = BitVec.ofNat 64 (if V = 3 then 1 else 0) := by
  have hd : (BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.xor_lt_two_pow hV (by decide)
  have he : BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3 = BitVec.ofNat 64 (BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  rw [threeBV, he, ltu_ofNat (by omega) (by decide)]
  congr 2
  apply propext
  rw [show (BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3).toNat < 1 ↔ (BitVec.ofNat 64 V ^^^ BitVec.ofNat 64 3) = 0#64 from
    ⟨fun h => BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega), fun h => by rw [h]; decide⟩,
    BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  · intro h; subst h; rfl

theorem result_post {s t : State} {E : Nat}
    (hE : E = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat))
    (hax : t.gpr .a0 = BitVec.ofNat 64 (initStatus (s.gpr .a1).toNat E))
    (hm : t.mem = stored s.mem (s.gpr .a0) (if initStatus (s.gpr .a1).toNat E = 1 then
      wordValues (s.gpr .a1).toNat (E % 2 ^ 32) else List.replicate 7 0)) :
    initPost s t := by
  unfold initPost Spec.RsaKeyGen.keySearchInit
  dsimp only
  subst hE
  generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = E at *
  generalize hbits : (s.gpr .a1).toNat = bits at hax hm ⊢
  have hb : bits < 2 ^ 64 := by rw [← hbits]; exact BitVec.isLt _
  have hst := initStatus_val bits E
  by_cases hv : Spec.RsaKeyGen.exponentValid E = true
  · rw [ite_eq_right (by rw [hv]; decide)]
    have hvE : E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 := by
      unfold Spec.RsaKeyGen.exponentValid at hv
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      omega
    cases hmb : Spec.RsaKeyGen.modulusBits bits with
    | none =>
      have h2 : initStatus bits E = 2 := by
        unfold initStatus; rw [hv, hmb]; rfl
      refine ⟨by rw [hax, h2]; rfl, ?_⟩
      rw [hm, h2, ite_eq_right (by decide), stored_words7]
      rfl
    | some nlen =>
      have hn : 512 ≤ bits ∧ bits ≤ 8192 ∧ nlen = bits / 128 * 128 := by
        unfold Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits Spec.RsaKeyGen.minBits at hmb
        by_cases h1 : 8192 < bits
        · simp [h1] at hmb
        · by_cases h2 : bits / 128 * 128 < 512
          · simp [h1, h2] at hmb
          · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hmb
            omega
      have h1 : initStatus bits E = 1 := by
        rw [hst, ite_eq_left hvE, ite_eq_left (by omega)]
      have hP : nlen / 16 = bits / 128 * 8 := by omega
      have hL : bits / 128 * 8 ≤ 512 := by omega
      have hL32 : 32 ≤ bits / 128 * 8 := by omega
      refine ⟨by rw [hax, h1]; rfl, 32 * (bits / 128 * 8), ?_, ?_, ?_⟩
      · rw [hm, h1, ite_eq_left rfl, stored_words6]
        simp only [wordValues, plen_eq hb, Nat.mod_eq_of_lt hvE.2.2, three_eq hvE.2.2, List.getD_cons_zero,
          List.getD_cons_succ, hP, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          Spec.RsaKeyGen.keyGenerations, Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeEntropy]
        rw [shl_ofNat _ 15 (by omega), shl_ofNat _ 5 (by omega), shl_ofNat _ 3 (by omega),
          shl_ofNat _ 4 (by omega), add_ofNat, add_ofNat, add_ofNat]
        have m1 : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
        have m0 : (0#64 : BitVec 64) = BitVec.ofNat 64 0 := rfl
        by_cases h3 : E = 3 <;> simp only [h3, ↓reduceIte, List.cons.injEq, and_true] <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
            | trivial
            | rfl
            | (rw [m1, ← BitVec.ofNat_mul, add_ofNat]; congr 1; simp only [Nat.reducePow]; omega)
            | (rw [m0, ← BitVec.ofNat_mul, add_ofNat]; congr 1; simp only [Nat.reducePow]; omega)
            | (congr 1; simp only [Nat.reducePow]; omega)
      · rw [hm, h1, ite_eq_left rfl, stored_bytes]
        simp only [wordValues, List.getD_cons_zero, List.getD_cons_succ, Nat.mod_eq_of_lt hvE.2.2]
        exact rev_bytes (by omega)
      · simp only [List.getD_cons_zero, List.getD_cons_succ, hP]
        unfold Spec.Entropy.RequestValid Spec.RsaKeyGen.primeEntropy
        omega
  · have hv' : Spec.RsaKeyGen.exponentValid E = false := by simpa using hv
    rw [ite_eq_left (by rw [hv']; rfl)]
    have h0 : initStatus bits E = 0 := by
      unfold initStatus; rw [ite_eq_left (by rw [hv']; rfl)]
    refine ⟨by rw [hax, h0]; rfl, ?_⟩
    rw [hm, h0, ite_eq_right (by decide), stored_words7]
    rfl

/-! ## The whole initialization -/

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

abbrev initRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem init_ok {s : State} (scr : Scr s (s.gpr .a0) 56)
    (hrd : ∀ i < (s.gpr .a3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 i) 1) :
    WP isa init s fun t => initPost s t ∧ Keep initRegs s t := by
  let E := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  let bits := (s.gpr .a1).toNat
  unfold init
  refine WP.seq (WP.mono (scan_ok rfl (ofNat_toNat64 _).symm (BitVec.isLt _) hrd)
    fun u ⟨_, h3, h4, h4b, hmu, ku⟩ => ?_)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (expValid_ok u (E := E) h3 h4 h4b) fun v ⟨⟨h5v, hmv⟩, kv⟩ => ?_
  rw [WP.block_append_iff]
  have h1v : v.gpr .a1 = BitVec.ofNat 64 bits := by
    rw [kv.gpr (by decide), ku.gpr (by decide)]; exact (ofNat_toNat64 _).symm
  refine WP.mono (sizeValid_ok v h1v (BitVec.isLt _)) fun w ⟨⟨h6w, hmw⟩, kw⟩ => ?_
  rw [WP.block_append_iff]
  have h5w : w.gpr .t5 = _ := (kw.gpr (by decide)).trans h5v
  refine WP.mono (status_ok w _ _ h5w h6w) fun x ⟨⟨h2x, h1x, hmx⟩, kx⟩ => ?_
  have kux := ((ku.trans kv).trans kw).trans kx
  have scx : Scr x (s.gpr .a0) 56 := scr.congr kux.2.2
  have h0x : x.gpr .a0 = s.gpr .a0 := kux.gpr (by decide)
  have h1x' : x.gpr .a1 = BitVec.ofNat 64 bits := by rw [kx.gpr (by decide), kw.gpr (by decide)]; exact h1v
  have h3x : x.gpr .t3 = BitVec.ofNat 64 (E % 2 ^ 32) := by
    rw [kx.gpr (by decide), kw.gpr (by decide), kv.gpr (by decide)]; exact h3
  refine WP.mono (words_ok _ scx h0x h1x' h3x h1x) fun t ⟨⟨h0t, hmt⟩, kt⟩ => ?_
  refine ⟨result_post (E := E) rfl ?_ ?_, (kux.trans kt).mono (by decide)⟩
  · rw [h0t, h2x, initStatus_val]
  · rw [hmt, hmx, hmw, hmv, hmu]
    congr 2
    rw [initStatus_val]
    apply propext
    constructor
    · intro h; rw [ite_eq_left h.1, ite_eq_left h.2]
    · intro h
      by_cases ha : E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32
      · by_cases hb : bits ≤ 8192 ∧ 512 ≤ bits
        · exact ⟨ha, hb⟩
        · rw [ite_eq_left ha, ite_eq_right hb] at h; cases h
      · rw [ite_eq_right ha] at h; cases h

/-! ## The contract -/

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧
    s.gpr .a3 = t.gpr .a3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, _, hal⟩ := h
  have scr : Scr s (s.gpr .a0) 56 := Scr.of_mem (by rw [hwr]; simp) hroom hal
  have hreads : ∀ i < (s.gpr .a3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := init_ok scr hreads
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide), hp⟩

/-- Two runs agree on the arguments. -/
theorem init_agree {s₁ s₂ : State} (h : initPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨hsp, h0, h1, h2, h3⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init :=
  RelCT.constantTime ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ h => init_agree h) (by taint_decide)).mono (fun _ _ h => h.2.2) fun _ _ h => h)

private def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1024 | .a2 => 0x2000 | .a3 => 3 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 56⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.RsaKeyGen.RISCV64.KeyInit
