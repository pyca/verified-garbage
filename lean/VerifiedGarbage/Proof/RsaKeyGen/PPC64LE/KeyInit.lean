module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory

/-! # Starting RSA key generation on PPC64LE: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.KeyInit

open VG VG.PPC64LE VG.Proof.Bignum
open VG.Proof.Ffdh.PPC64LE (lt_bit shr_zero)
open VG.Proof.RsaKeyGen.SearchInit (bytesAt_succ or_eq_zero shl_ofNat add_ofNat)
open VG.Impl.Bignum.PPC64LE (countLoop)
open VG.Impl.RsaKeyGen.PPC64LE.KeyInit

/-! ## The exponent's octets -/

theorem widen_byte (b : Byte) : BitVec.setWidth 64 (0#0 ++ b) = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft,
    Nat.zero_or]

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

theorem low32 (n : Nat) : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) >>> 0) =
    BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

theorem sub_one {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

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

/-- After `j` of `e`'s octets: its value so far modulo `2^32` in `r9`, and in
`r10`, below `2^8`, whether it is below `2^32`. -/
def ScanInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .r5 = P + BitVec.ofNat 64 j ∧
    u.gpr .r9 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) ∧
    (u.gpr .r10 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) < 2 ^ 32) ∧
    (u.gpr .r10).toNat < 2 ^ 8 ∧ u.mem = s.mem ∧ Keep [.r5, .r6, .r7, .r9, .r10, .r11] s u

theorem octet_ok {t : State} {P : Addr} {j v : Nat} {acc : BitVec 64}
    (hp : t.gpr .r5 = P + BitVec.ofNat 64 j) (hv : t.gpr .r9 = BitVec.ofNat 64 v) (hacc : t.gpr .r10 = acc)
    (hv32 : v < 2 ^ 32) (hr : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 j) 1) :
    WP isa (.block (octet ++ ([.subi .r6 .r6 1] : List Instr))) t fun u =>
      (u.gpr .r5 = P + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .r9 = BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) % 2 ^ 32) ∧
        u.gpr .r10 = acc ||| BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) / 2 ^ 32) ∧
        u.mem = t.mem ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ∧
      Keep [.r5, .r6, .r7, .r9, .r10, .r11] t u := by
  refine WP.keep [.r5, .r6, .r7, .r9, .r10, .r11] ?_ (by decide +kernel)
  have hb := (t.mem (P + BitVec.ofNat 64 j)).isLt
  have hN : 256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 64 := by omega
  unfold octet
  have e5 : P + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (j + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  crunr [hp, hv, hacc, hr, widen_byte, shl8_add v hv32, shr_ofNat hN, low32, e5,
    List.cons_append, List.nil_append]

theorem scan_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (h : ScanInv s P j u) :
    WP isa (.block (octet ++ ([.subi .r6 .r6 1] : List Instr))) u fun v =>
      ScanInv s P (j + 1) v ∧ v.gpr .r6 = u.gpr .r6 - BitVec.ofNat 64 1 := by
  obtain ⟨hx5, hx9, hr10, hlt, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [k.2.1, k.2.2]; exact hrd j hj
  refine WP.mono (octet_ok hx5 hx9 rfl (Nat.mod_lt _ (by decide)) hr)
    fun v ⟨⟨h5, h9, h10, hmv, h6⟩, kv⟩ => ⟨⟨h5, ?_, ?_, ?_, hmv.trans hm, (k.trans kv).mono (by decide)⟩, h6⟩
  · rw [h9, bytesAt_succ, os2ip_snoc, hm]
    congr 1
    omega
  · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
    have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
    rw [h10, or_eq_zero, hr10, bytesAt_succ, os2ip_snoc, hm, ofNat64_eq_zero (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      have : 256 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) +
        (s.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 32 := (Nat.div_eq_zero_iff_lt (by decide)).mp h2
      omega
    · intro h
      exact ⟨by omega, Nat.div_eq_of_lt (by omega)⟩
  · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
    have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
    rw [h10, BitVec.toNat_or, BitVec.toNat_ofNat, hm]
    exact Nat.or_lt_two_pow hlt (by
      rw [Nat.mod_eq_of_lt (by omega)]
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega))

theorem scan_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .r5 = P)
    (hl : s.gpr .r6 = BitVec.ofNat 64 len) (hl64 : len < 2 ^ 64)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa scan s (ScanInv s P len) := by
  unfold scan
  refine WP.seq (WP.mono (WP.keep [.r9, .r10] (Q := fun t => t.gpr .r9 = 0 ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem)
    (by crunr) (by decide +kernel)) fun t ⟨⟨h9, h10, hm⟩, k⟩ => ?_)
  have h0 : ScanInv s P 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero], by rw [h9]; rfl,
    by rw [h10]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], by rw [h10]; decide, hm, k.mono (by decide)⟩
  have h6 : t.gpr .r6 = BitVec.ofNat 64 len := (k.gpr (by decide)).trans hl
  refine WP.ite (decide (len = 0)) (by simp only [VG.PPC64LE.eval, State.read, Size.bits,
      BitVec.setWidth_eq, h6, ofNat_beq_zero hl64]) (fun hz => ?_) (fun hz => ?_)
  · have hz : len = 0 := of_decide_eq_true hz
    subst hz
    exact WP.block_nil h0
  · have hz : len ≠ 0 := of_decide_eq_false hz
    exact VG.Proof.Bignum.PPC64LE.wp_countdown (N := len) hl64 (by omega) (ScanInv s P)
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

theorem and_low14 (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 16383 = BitVec.ofNat 64 (n % 2 ^ 14) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (16383 : Nat) % 2 ^ 64 = 2 ^ 14 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit_and (a b : Prop) [Decidable a] [Decidable b] :
    BitVec.ofNat 64 (if a then 1 else 0) &&& BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (if a ∧ b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem size_bits (bits : Nat) :
    BitVec.ofNat 64 (if bits / 16384 < 1 then 1 else 0) *
      (BitVec.ofNat 64 (if bits % 16384 < 8193 then 1 else 0) - BitVec.ofNat 64 (if bits % 16384 < 512 then 1 else 0)) =
    BitVec.ofNat 64 (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 0) := by
  by_cases h1 : bits / 16384 < 1
  · have hm : bits % 16384 = bits := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    by_cases h2 : bits < 8193 <;> by_cases h3 : bits < 512 <;> by_cases h4 : (bits ≤ 8192 ∧ 512 ≤ bits) <;>
      simp only [h1, h2, h3, h4, ↓reduceIte] <;> first | decide | (exfalso; omega)
  · have h4 : ¬(bits ≤ 8192 ∧ 512 ≤ bits) := by omega
    simp only [h1, h4, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp

theorem bit_mod2 (n : Nat) : BitVec.ofNat 64 (n % 2) = BitVec.ofNat 64 (if n % 2 = 1 then 1 else 0) := by
  congr 1; split <;> omega

/-- `expValid`: `r7` is 1 exactly for a valid exponent. -/
theorem expValid_ok (s : State) {E : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 (E % 2 ^ 32))
    (h10 : s.gpr .r10 = 0 ↔ E < 2 ^ 32) (h10b : (s.gpr .r10).toNat < 2 ^ 8) :
    WP isa (.block expValid) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 64 (if E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r7, .r8, .r12] s t := by
  refine WP.keep [.r7, .r8, .r12] ?_ (by decide +kernel)
  have hV : E % 2 ^ 32 < 2 ^ 63 := by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega
  have h10' : s.gpr .r10 = BitVec.ofNat 64 (s.gpr .r10).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hz : (s.gpr .r10).toNat < 1 ↔ E < 2 ^ 32 := by
    rw [← h10]; constructor
    · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
    · intro h; rw [h]; decide
  generalize (s.gpr .r10).toNat = X at h10' h10b hz
  generalize hVd : E % 2 ^ 32 = V at h9 hV
  have hlt := lt_bit (n := X) (c := 1) (by omega) (by decide)
  have hlt3 := lt_bit (n := V) (c := 3) hV (by decide)
  have e1 : BitVec.ofNat 64 1 - BitVec.ofNat 64 (if V < 3 then 1 else 0) =
      BitVec.ofNat 64 (if V < 3 then 0 else 1) := by split <;> decide
  have e1' : BitVec.ofNat 64 (if V < 3 then 0 else 1) = BitVec.ofNat 64 (if ¬ V < 3 then 1 else 0) := by
    split <;> simp_all
  unfold expValid lt
  crunr [h9, h10', List.cons_append, List.nil_append]
  rw [hlt, and_one _ (by omega), bit_mod2, bit_and, hlt3, e1, e1', bit_and]
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

/-- `sizeValid`: `r8` is 1 exactly for a valid size. -/
theorem sizeValid_ok (s : State) {bits : Nat} (h4 : s.gpr .r4 = BitVec.ofNat 64 bits) (hb : bits < 2 ^ 64) :
    WP isa (.block sizeValid) s fun t =>
      (t.gpr .r8 = BitVec.ofNat 64 (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r8, .r11, .r12] s t := by
  refine WP.keep [.r0, .r8, .r11, .r12] ?_ (by decide +kernel)
  have hl := Nat.mod_lt bits (show 0 < 2 ^ 14 by decide)
  have hd : bits / 2 ^ 14 < 2 ^ 63 := by omega
  unfold sizeValid lt
  crunr [h4, shr_ofNat hb, and_low14 bits hb, lt_bit hd (by decide : 1 < 2 ^ 63),
    lt_bit (show bits % 2 ^ 14 < 2 ^ 63 by omega) (by decide : 8193 < 2 ^ 63),
    lt_bit (show bits % 2 ^ 14 < 2 ^ 63 by omega) (by decide : 512 < 2 ^ 63),
    List.cons_append, List.nil_append]
  exact size_bits bits

/-- `status`: the status in `r12` and its bit of 1 in `r11`. -/
theorem status_vals (a b : Prop) [Decidable a] [Decidable b] :
    (BitVec.ofNat 64 2 - BitVec.ofNat 64 (if b then 1 else 0)) * BitVec.ofNat 64 (if a then 1 else 0) =
      BitVec.ofNat 64 (if a then (if b then 1 else 2) else 0) ∧
    BitVec.ofNat 64 (if a then 1 else 0) * BitVec.ofNat 64 (if b then 1 else 0) =
      BitVec.ofNat 64 (if a ∧ b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem status_ok (s : State) (a b : Prop) [Decidable a] [Decidable b]
    (h7 : s.gpr .r7 = BitVec.ofNat 64 (if a then 1 else 0)) (h8 : s.gpr .r8 = BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (.block status) s fun t =>
      (t.gpr .r12 = BitVec.ofNat 64 (if a then (if b then 1 else 2) else 0) ∧
        t.gpr .r11 = BitVec.ofNat 64 (if a ∧ b then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.r11, .r12] s t := by
  refine WP.keep [.r11, .r12] ?_ (by decide +kernel)
  have hv := status_vals a b
  unfold status
  crunr [h7, h8]
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
abbrev threeBV (V : Nat) : BitVec 64 := ((BitVec.ofNat 64 V ^^^ 3#64) - 1#64) >>> 63

/-- The words' values, if the status is 1. -/
def wordValues (bits V : Nat) : List (BitVec 64) :=
  let P := plenBV bits
  [P <<< 3 + P <<< 5 + (P <<< 4 + P <<< 3) * threeBV V, P, P <<< 15 + P, P <<< 5, 0, 4,
    rev64 (BitVec.ofNat 64 V)]

/-- The state's 56 bytes, which the code may write. -/
def Scr (s : State) (B : Addr) : Prop := ⟨B, 56⟩ ∈ s.wr ∧ B.toNat + 56 ≤ 2 ^ 64

theorem Scr.st {s : State} {B : Addr} (h : Scr s B) (d : Nat) (hd : d + 8 ≤ 56) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.1, Offset.contains_base _ hd (by have := h.2; omega)⟩

theorem Scr.st0 {s : State} {B : Addr} (h : Scr s B) : InRegions s.wr B 8 := by
  simpa only [BitVec.add_zero] using h.st 0 (by decide)

theorem Scr.congr {s t : State} {B : Addr} (h : Scr s B) (hw : t.wr = s.wr) : Scr t B := by
  rw [Scr, hw]; exact h

theorem words_ok {s : State} {B : Addr} {bits V : Nat} (ok : Prop) [Decidable ok] (scr : Scr s B)
    (h3 : s.gpr .r3 = B) (h4 : s.gpr .r4 = BitVec.ofNat 64 bits) (h9 : s.gpr .r9 = BitVec.ofNat 64 V)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    WP isa (.block (words ++ ([.addi .r3 .r12 0] : List Instr))) s fun t =>
      (t.gpr .r3 = s.gpr .r12 ∧
        t.mem = stored s.mem B (if ok then wordValues bits V else List.replicate 7 0)) ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r10] s t := by
  refine WP.keep [.r0, .r3, .r4, .r5, .r6, .r7, .r10] ?_ (by decide +kernel)
  have c1 : (1#64 : BitVec 64) <<< 2 = 4#64 := rfl
  have c0 : (0#64 : BitVec 64) <<< 2 = 0#64 := rfl
  have r0 : rev64 (0#64 : BitVec 64) = 0#64 := rfl
  unfold words stored wordValues
  by_cases hok : ok <;>
  crunr [h3, h4, h9, h11, hok, c1, c0, r0, addrX, scr.st0, scr.st 8 (by decide), scr.st 16 (by decide),
    scr.st 24 (by decide), scr.st 32 (by decide), scr.st 40 (by decide), scr.st 48 (by decide), off,
    List.cons_append, List.nil_append, BitVec.mul_one, BitVec.mul_zero, List.getD_cons_zero,
    List.getD_cons_succ, List.replicate_succ, List.replicate_zero] <;>
  first | rfl | decide

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

theorem rev64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (rev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have cases8 : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases cases8 i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [rev64, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
    BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]

theorem rev_bytes {E : Nat} (hE : E < 2 ^ 64) :
    ((List.range 8).map fun i => (rev64 (BitVec.ofNat 64 E)).extractLsb' (8 * i) 8) = Spec.Rsa.i2osp E 8 := by
  simp only [Spec.Rsa.i2osp]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [rev64_byte _ _ hi, shr_ofNat hE]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hE), show 8 - 1 - i = 7 - i by omega,
    show (256 : Nat) ^ (7 - i) = 2 ^ (8 * (7 - i)) by rw [Nat.pow_mul]]

/-! ## The result -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] ∧ s.wr = [⟨s.gpr .r3, 56⟩] ∧
    (s.gpr .r3).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  let eB := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
  match Spec.RsaKeyGen.keySearchInit (s.gpr .r4).toNat eB with
  | .error c => ((t.gpr .r3).setWidth 32).toNat = c ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 7 = List.replicate 7 0
  | .ok values => ((t.gpr .r3).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 6 =
        (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3 + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip eB) 8 ∧
      Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first

theorem plen_eq {bits : Nat} (hb : bits < 2 ^ 64) : plenBV bits = BitVec.ofNat 64 (bits / 128 * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem three_eq {V : Nat} (hV : V < 2 ^ 32) : threeBV V = BitVec.ofNat 64 (if V = 3 then 1 else 0) := by
  have hd : (BitVec.ofNat 64 V ^^^ 3#64).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.xor_lt_two_pow hV (by decide)
  have he : BitVec.ofNat 64 V ^^^ 3#64 = BitVec.ofNat 64 (BitVec.ofNat 64 V ^^^ 3#64).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  rw [threeBV, he, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, lt_bit (by omega) (by decide)]
  congr 2
  apply propext
  rw [show (BitVec.ofNat 64 V ^^^ 3#64).toNat < 1 ↔ (BitVec.ofNat 64 V ^^^ 3#64) = 0#64 from
    ⟨fun h => BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega), fun h => by rw [h]; decide⟩,
    BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  · intro h; subst h; rfl

theorem result_post {s t : State} {E : Nat}
    (hE : E = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat))
    (hax : t.gpr .r3 = BitVec.ofNat 64 (initStatus (s.gpr .r4).toNat E))
    (hm : t.mem = stored s.mem (s.gpr .r3) (if initStatus (s.gpr .r4).toNat E = 1 then
      wordValues (s.gpr .r4).toNat (E % 2 ^ 32) else List.replicate 7 0)) :
    initPost s t := by
  unfold initPost Spec.RsaKeyGen.keySearchInit
  dsimp only
  subst hE
  generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = E at *
  generalize hbits : (s.gpr .r4).toNat = bits at hax hm ⊢
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

abbrev initRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem init_ok {s : State} (scr : Scr s (s.gpr .r3))
    (hrd : ∀ i < (s.gpr .r6).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 i) 1) :
    WP isa init s fun t => initPost s t ∧ Keep initRegs s t := by
  let E := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  let bits := (s.gpr .r4).toNat
  unfold init
  refine WP.seq (WP.mono (scan_ok rfl (ofNat_toNat64 _).symm (BitVec.isLt _) hrd)
    fun u ⟨_, h9, h10, h10b, hmu, ku⟩ => ?_)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (expValid_ok u (E := E) h9 h10 h10b) fun v ⟨⟨h7v, hmv⟩, kv⟩ => ?_
  rw [WP.block_append_iff]
  have h4v : v.gpr .r4 = BitVec.ofNat 64 bits := by
    rw [kv.gpr (by decide), ku.gpr (by decide)]; exact (ofNat_toNat64 _).symm
  refine WP.mono (sizeValid_ok v h4v (BitVec.isLt _)) fun w ⟨⟨h8w, hmw⟩, kw⟩ => ?_
  rw [WP.block_append_iff]
  have h7w : w.gpr .r7 = _ := (kw.gpr (by decide)).trans h7v
  refine WP.mono (status_ok w _ _ h7w h8w) fun x ⟨⟨h12x, h11x, hmx⟩, kx⟩ => ?_
  have kux := ((ku.trans kv).trans kw).trans kx
  have scx : Scr x (s.gpr .r3) := scr.congr kux.2.2
  have h3x : x.gpr .r3 = s.gpr .r3 := kux.gpr (by decide)
  have h4x : x.gpr .r4 = BitVec.ofNat 64 bits := by rw [kx.gpr (by decide), kw.gpr (by decide)]; exact h4v
  have h9x : x.gpr .r9 = BitVec.ofNat 64 (E % 2 ^ 32) := by
    rw [kx.gpr (by decide), kw.gpr (by decide), kv.gpr (by decide)]; exact h9
  refine WP.mono (words_ok _ scx h3x h4x h9x h11x) fun t ⟨⟨h3t, hmt⟩, kt⟩ => ?_
  refine ⟨result_post (E := E) rfl ?_ ?_, (kux.trans kt).mono (by decide)⟩
  · rw [h3t, h12x, initStatus_val]
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
  s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧
    s.gpr .r6 = t.gpr .r6

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, _⟩ := h
  have scr : Scr s (s.gpr .r3) := ⟨by rw [hwr]; simp, hroom⟩
  have hreads : ∀ i < (s.gpr .r6).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := init_ok scr hreads
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), hp⟩

/-- Two runs agree on the arguments. -/
theorem init_agree {s₁ s₂ : State} (h : initPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨hsp, h3, h4, h5, h6⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init :=
  RelCT.constantTime ((RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ h => init_agree h) (by taint_decide)).mono (fun _ _ h => h.2.2) fun _ _ h => h)

private def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 1024 | .r5 => 0x2000 | .r6 => 3 | _ => 0
  lr := 0
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

end VG.Proof.RsaKeyGen.PPC64LE.KeyInit
