module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.VectorCrypto
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Ffdh.ControlMemory
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.RsaKeyGen.AArch64.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.VectorCrypto
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import Mathlib.Tactic.SplitIfs

/-! # Starting RSA key generation on AArch64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.KeyInit

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 (movi st mov countLoop)
open VG.Impl.RsaKeyGen.AArch64.KeyInit
open VG.Proof.RsaKeyGen.SearchInit (or_eq_zero bytesAt_succ shl_ofNat add_ofNat)

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  change (0#0 ++ m a : BitVec (0 + 8)) = m a
  exact BitVec.zero_width_append _ _

theorem zext_zext (a : Byte) : (a.setWidth 32).setWidth 64 = a.setWidth 64 := by
  ext i hi; simp

theorem exec_addImm_w {s : State} {d n : Reg} :
    exec (.addImm .w d n 0) s = some (s.write .x d (BitVec.setWidth 64 ((s.gpr n).setWidth 32))) := by
  simp only [exec, State.read, State.write, Size.bits, BitVec.add_zero,
    show (0 : Nat) < 4096 by decide, ite_true, BitVec.setWidth_eq]

theorem exec_rev {s : State} {d n : Reg} : exec (.rev d n) s = some (s.write .x d (rev64 (s.gpr n))) := by
  simp only [exec, State.read, Size.bits, BitVec.setWidth_eq]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

/-! ## The exponent's octets -/

theorem shl8_add (v : Nat) (hv : v < 2 ^ 32) (b : Byte) :
    BitVec.ofNat 64 v <<< 8 + b.setWidth 64 = BitVec.ofNat 64 (256 * v + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : v * 2 ^ 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem low32 (n : Nat) : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) =
    BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem shr32 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 32 = BitVec.ofNat 64 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem sub_one {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · rintro rfl; rfl

theorem octet_ok {t : State} {P : Addr} {j v : Nat} {acc : BitVec 64}
    (hp : t.gpr .x2 = P + BitVec.ofNat 64 j) (hv : t.gpr .x9 = BitVec.ofNat 64 v) (hacc : t.gpr .x10 = acc)
    (hv32 : v < 2 ^ 32) (hr : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 j) 1) :
    WP isa (.block (octet ++ ([.subImm .x .x3 .x3 1] : List Instr))) t fun u =>
      (u.gpr .x2 = P + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .x9 = BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) % 2 ^ 32) ∧
        u.gpr .x10 = acc ||| BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) / 2 ^ 32) ∧
        u.gpr .x3 = t.gpr .x3 - BitVec.ofNat 64 1 ∧ u.mem = t.mem) ∧
      Keep [.x2, .x3, .x9, .x10, .x11, .x12] t u := by
  refine WP.keep [.x2, .x3, .x9, .x10, .x11, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  have hb := (t.mem (P + BitVec.ofNat 64 j)).isLt
  unfold octet
  brun [exec_addImm_w, hp, hv, hacc, hr, zext_zext, read_one, BitVec.add_zero, shl8_add v hv32, low32,
    shr32 (show 256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 64 by omega), BitVec.add_assoc]
  rw [BitVec.ofNat_add]

theorem os2ip_snoc (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · intro h; rw [h]; rfl

/-- After `j` of `e`'s octets: its value so far modulo `2^32` in `x9`, and in
`x10` whether it is below `2^32`. -/
def ScanInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .x2 = P + BitVec.ofNat 64 j ∧
    u.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) ∧
    (u.gpr .x10 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) < 2 ^ 32) ∧ u.mem = s.mem ∧
    Keep [.x2, .x3, .x9, .x10, .x11, .x12] s u

theorem scan_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (h : ScanInv s P j u) :
    WP isa (.block (octet ++ ([.subImm .x .x3 .x3 1] : List Instr))) u fun v =>
      ScanInv s P (j + 1) v ∧ v.gpr .x3 = u.gpr .x3 - BitVec.ofNat 64 1 := by
  obtain ⟨hdx, hr9, hr10, hum, ku⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [ku.rd, ku.wr]; exact hrd j hj
  refine WP.mono (octet_ok hdx hr9 rfl (Nat.mod_lt _ (by decide)) hr)
    fun v ⟨⟨hd, h9', h10', h3', hm'⟩, kv⟩ => ⟨⟨hd, ?_, ?_, hm'.trans hum, (ku.trans kv).mono (by decide)⟩, h3'⟩
  · rw [h9', bytesAt_succ, os2ip_snoc, hum]
    congr 1
    omega
  · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
    have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
    rw [h10', or_eq_zero, hr10, bytesAt_succ, os2ip_snoc, hum, ofNat64_eq_zero (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      have : 256 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) +
        (s.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 32 := (Nat.div_eq_zero_iff_lt (by decide)).mp h2
      omega
    · intro h
      refine ⟨by omega, ?_⟩
      apply Nat.div_eq_of_lt
      omega

theorem scan_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .x2 = P)
    (hl : s.gpr .x3 = BitVec.ofNat 64 len) (hl64 : len < 2 ^ 64)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa scan s (ScanInv s P len) := by
  unfold scan
  refine WP.seq (WP.mono (WP.keep [.x9, .x10] (Q := fun t => t.gpr .x9 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem)
    (by brun [imm64 (show 0 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h9, h10, hm⟩, k⟩ => ?_)
  have h0 : ScanInv s P 0 t := ⟨by rw [k.gpr .x2 (by decide), hp, BitVec.add_zero], by rw [h9]; rfl,
    by rw [h10]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], hm, k.mono (by decide)⟩
  have hl' : t.gpr .x3 = BitVec.ofNat 64 len := (k.gpr .x3 (by decide)).trans hl
  refine WP.ite _ (by rw [VG.Proof.MlKem.AArch64.eval_zero, hl', ofNat_beq_zero hl64]) (fun hz => ?_)
    (fun hz => ?_)
  · have hz : len = 0 := of_decide_eq_true hz
    subst hz
    exact WP.block_nil h0
  · have hz : len ≠ 0 := of_decide_eq_false hz
    exact wp_countdown (N := len) hl64 (by omega) (ScanInv s P)
      (fun i hi u hI _ => scan_body hi hrd hI) h0 hl'

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
  all_goals first | rfl | (exfalso; omega) | simp_all

theorem initStatus_lt (bits E : Nat) : initStatus bits E < 2 ^ 64 := by
  rw [initStatus_val]; split <;> (try split) <;> omega

theorem and1 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem status_ok {s : State} {bits E h : Nat} (hx1 : s.gpr .x1 = BitVec.ofNat 64 bits)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (E % 2 ^ 32)) (h10 : s.gpr .x10 = BitVec.ofNat 64 h)
    (hh : h = 0 ↔ E < 2 ^ 32) (hb : bits < 2 ^ 64) (hh64 : h < 2 ^ 64) :
    WP isa (.block status) s fun t => (t.gpr .x13 = BitVec.ofNat 64 (initStatus bits E) ∧
      t.gpr .x17 = 0 ∧ t.mem = s.mem) ∧ Keep [.x13, .x14, .x15, .x16, .x17] s t := by
  have hV : E % 2 ^ 32 < 2 ^ 64 := by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega
  refine WP.keep [.x13, .x14, .x15, .x16, .x17] ?_ (by decide) (by decide) (by decide +kernel)
  unfold status statusSize statusExponent
  have hodd : E % 2 ^ 32 % 2 < 2 ^ 64 := by omega
  brun [hx1, h9, h10, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
    imm64 (show 2 < 65536 by decide), imm64 (show 512 < 65536 by decide), imm64 (show 8193 < 65536 by decide),
    subs_ge hb (show 512 < 2 ^ 64 by decide), subs_ge hb (show 8193 < 2 ^ 64 by decide),
    subs_ge (show 0 < 2 ^ 64 by decide) hh64, and1 hV, sub_one, subs_ge hodd (show 1 < 2 ^ 64 by decide),
    subs_ge (show 1 < 2 ^ 64 by decide) hV]
  rw [initStatus_val]
  by_cases hE : E < 2 ^ 32
  · obtain rfl : h = 0 := hh.mpr hE
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> exfalso <;> omega
  · have h0 : ¬ h ≤ 0 := fun hz => hE (hh.mp (by omega))
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> exfalso <;> omega

/-! ## The words -/

/-- The seven words stored, from their values. -/
def stored (m : Mem) (B : Addr) (w : List (BitVec 64)) : Mem :=
  ((((((m.writeW B (w.getD 0 0)).writeW (off B 8) (w.getD 1 0)).writeW (off B 16) (w.getD 2 0)).writeW
    (off B 24) (w.getD 3 0)).writeW (off B 32) (w.getD 4 0)).writeW (off B 40) (w.getD 5 0)).writeW
    (off B 48) (w.getD 6 0)

/-- The primes' octets, from the size. -/
abbrev plenBV (bits : Nat) : BitVec 64 := (BitVec.ofNat 64 bits >>> 7) <<< 3

/-- The words' values, if the status is 1. -/
def wordValues (bits V : Nat) : List (BitVec 64) :=
  let P := plenBV bits
  [if V = 3 then P <<< 6 else P <<< 3 + P <<< 5, P, (P <<< 15) + P, P <<< 5, 0, 4,
    rev64 (BitVec.ofNat 64 V)]

theorem subs0_carry (x : BitVec 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 0).toNat + (~~~x).toNat + (true).toNat) = decide (x = 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  · rintro rfl
    rw [show (0 : BitVec 64).toNat = 0 from rfl]

theorem xor_ofNat_eq_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = 0) = (a = b) := by
  apply propext
  constructor
  · intro h
    have h' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
      have := congrArg (· ^^^ BitVec.ofNat 64 b) h
      simpa [BitVec.xor_assoc] using this
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; exact BitVec.xor_self

theorem words_ok {s : State} {B : Addr} {bits V st : Nat} (scr : Scr s B 56) (h0 : s.gpr .x0 = B)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 bits) (h9 : s.gpr .x9 = BitVec.ofNat 64 V)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 st) (h17 : s.gpr .x17 = 0) (hV : V < 2 ^ 64) (hst : st < 2 ^ 64) :
    WP isa (.block words) s fun t => (t.gpr .x0 = s.gpr .x13 ∧
      t.mem = stored s.mem B (if st = 1 then wordValues bits V else List.replicate 7 0)) ∧
      Keep [.x0, .x4, .x5, .x6, .x7, .x8, .x11, .x15, .x16] s t := by
  refine WP.keep [.x0, .x4, .x5, .x6, .x7, .x8, .x11, .x15, .x16] ?_ (by decide) (by decide) (by decide +kernel)
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  have e3 := xor_ofNat_eq_zero hV (show 3 < 2 ^ 64 by decide)
  have e1 := xor_ofNat_eq_zero hst (show 1 < 2 ^ 64 by decide)
  have z0 : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl
  unfold words compute Impl.RsaKeyGen.AArch64.KeyInit.mask stores stored wordValues
  rw [z0] at h17
  by_cases hv3 : V = 3 <;> by_cases hs1 : st = 1 <;>
  brun [exec_rev, h0, h1, h9, h13, h17, imm64 (show 1 < 65536 by decide), imm64 (show 3 < 65536 by decide),
    imm64 (show 4 < 65536 by decide), subs0_carry, e3, e1, hv3, hs1, h00, scr.st (d := 8) (by decide),
    scr.st (d := 16) (by decide), scr.st (d := 24) (by decide), scr.st (d := 32) (by decide),
    scr.st (d := 40) (by decide), scr.st (d := 48) (by decide)] <;>
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.replicate_succ, List.replicate_zero] <;>
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

/-- Byte reversal maps byte `j` to byte `7 - j`. -/
theorem rev_byte (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (rev64 v).extractLsb' (8 * j) 8 = v.extractLsb' (8 * (7 - j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', rev64, VG.Proof.VectorCrypto.getLsbD_append_block _ _ _ hr]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

/-- Extracting a byte of a word is division by its radix-256 position. -/
theorem extract_nat (x : Nat) {j : Nat} (hj : j < 8) :
    (BitVec.ofNat 64 x).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (x / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ (8 * j) * 2 ^ (64 - 8 * j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [show (256 : Nat) ^ j = 2 ^ (8 * j) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]

theorem rev_bytes (E : Nat) :
    ((List.range 8).map fun i => (rev64 (BitVec.ofNat 64 E)).extractLsb' (8 * i) 8) = Spec.Rsa.i2osp E 8 := by
  simp only [Spec.Rsa.i2osp]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [rev_byte _ hi, extract_nat _ (by omega)]

/-! ## The result -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧ s.wr = [⟨s.gpr .x0, 56⟩] ∧
    (s.gpr .x0).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  let eB := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  match Spec.RsaKeyGen.keySearchInit (s.gpr .x1).toNat eB with
  | .error c => ((t.gpr .x0).setWidth 32).toNat = c ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 7 = List.replicate 7 0
  | .ok values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 6 =
        (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .x0 + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip eB) 8 ∧
      Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first

theorem plen_eq {bits : Nat} (hb : bits < 2 ^ 64) : plenBV bits = BitVec.ofNat 64 (bits / 128 * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem result_post {s t : State} {E : Nat}
    (hE : E = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (hax : t.gpr .x0 = BitVec.ofNat 64 (initStatus (s.gpr .x1).toNat E))
    (hm : t.mem = stored s.mem (s.gpr .x0) (if initStatus (s.gpr .x1).toNat E = 1 then
      wordValues (s.gpr .x1).toNat (E % 2 ^ 32) else List.replicate 7 0)) :
    initPost s t := by
  unfold initPost Spec.RsaKeyGen.keySearchInit
  dsimp only
  subst hE
  generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) = E at *
  generalize hbits : (s.gpr .x1).toNat = bits at hax hm ⊢
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
        simp only [wordValues, plen_eq hb, Nat.mod_eq_of_lt hvE.2.2, List.getD_cons_zero, List.getD_cons_succ,
          hP, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Spec.RsaKeyGen.keyGenerations,
          Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeEntropy]
        rw [shl_ofNat _ 6 (by omega), shl_ofNat _ 15 (by omega), shl_ofNat _ 5 (by omega),
          shl_ofNat _ 3 (by omega), add_ofNat, add_ofNat]
        by_cases h3 : E = 3 <;> simp only [h3, ↓reduceIte, List.cons.injEq, and_true] <;> and_intros <;>
          first | rfl | trivial | (congr 1; omega)
      · rw [hm, h1, ite_eq_left rfl, stored_bytes]
        simp only [wordValues, List.getD_cons_zero, List.getD_cons_succ, Nat.mod_eq_of_lt hvE.2.2]
        exact rev_bytes E
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

theorem init_ok {s : State} (scr : Scr s (s.gpr .x0) 56)
    (hrd : ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1) :
    WP isa init s fun t => initPost s t ∧
      Keep [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  let E := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  unfold init
  refine WP.seq (WP.mono (scan_ok rfl (ofNat_toNat64 _).symm (BitVec.isLt _) hrd)
    fun u ⟨_, h9, h10, hmu, ku⟩ => ?_)
  rw [WP.block_append_iff]
  have hsu : u.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [ku.gpr .x1 (by decide)]; exact (ofNat_toNat64 _).symm
  have h10' : u.gpr .x10 = BitVec.ofNat 64 (u.gpr .x10).toNat := (ofNat_toNat64 _).symm
  have hh : (u.gpr .x10).toNat = 0 ↔ E < 2 ^ 32 := by
    rw [← h10]; constructor
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    · intro h; rw [h]; rfl
  refine WP.mono (status_ok (E := E) hsu h9 h10' hh (BitVec.isLt _) (BitVec.isLt _))
    fun v ⟨⟨h13, h17, hmv⟩, kv⟩ => ?_
  have hdv : v.gpr .x0 = s.gpr .x0 := by rw [kv.gpr .x0 (by decide), ku.gpr .x0 (by decide)]
  have scv : Scr v (s.gpr .x0) 56 := (scr.congr ku.wr).congr kv.wr
  have h1v : v.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := (kv.gpr .x1 (by decide)).trans hsu
  have h9v : v.gpr .x9 = BitVec.ofNat 64 (E % 2 ^ 32) := (kv.gpr .x9 (by decide)).trans h9
  refine WP.mono (words_ok scv hdv h1v h9v h13 h17
    (by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega) (initStatus_lt _ _))
    fun t ⟨⟨hat, hmt⟩, kt⟩ => ?_
  exact ⟨result_post rfl (hat.trans h13) (by rw [hmt, hmv, hmu]), ((ku.trans kv).trans kt).mono (by decide)⟩

/-! ## The contract -/

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome⟩ := h
  have scr : Scr s (s.gpr .x0) 56 := Scr.of_mem (by rw [hwr]; simp) hroom
  have hreads : ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := init_ok scr hreads
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, hp⟩

def InitInput (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2.1 ∧ s.gpr .x2 = p.2.2.1 ∧ s.gpr .x3 = p.2.2.2

private theorem input_pins : Pins InitInput [.x0, .x1, .x2, .x3] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm,
    h₁.2.2.2.trans h₂.2.2.2.symm]

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have ct : RelCT isa (Two InitInput) init fun _ _ => True :=
    two_taint [.x0, .x1, .x2, .x3] input_pins (by taint_decide)
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hsp, h0, h1, h2, h3⟩ := h
  exact ⟨(s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3), ⟨rfl, rfl, rfl, rfl⟩,
    ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩, hsp⟩

private def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1024 | .x2 => 0x2000 | .x3 => 3 | _ => 0
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

end VG.Proof.RsaKeyGen.AArch64.KeyInit
