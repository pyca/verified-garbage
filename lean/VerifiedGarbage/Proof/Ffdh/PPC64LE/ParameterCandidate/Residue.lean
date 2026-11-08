module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An FFDH parameter candidate on PPC64LE: the generator's congruence

`residue_ok`: `hBad` is zero exactly when array 0 is 11 modulo 24 (for the
generator 2), or 3 or 7 modulo 10 (for 5). The candidate modulo 3 or 5 is
its digits' sum's (`val32_mod`: `2³² ≡ 1`), reduced by the reciprocal
(`modSmall_ok`); modulo 8 it is its low digit's.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.Mont (w32 val32 val32_succ)

/-- The congruence the generator asks of p. -/
def goodRes (g x : Nat) : Prop := if g = 2 then x % 24 = 11 else x % 10 = 3 ∨ x % 10 = 7

/-- The registers `residue` writes. -/
def resRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7]

/-- `hBad` stored over `m`. -/
theorem bad_post {m : Mem} {B : Addr} {t : State} {v : BitVec 64} {P : Prop}
    (tm : t.mem = m.writeW (B + BitVec.ofNat 64 200) v) (hv : v = 0#64 ↔ P) :
    (word t.mem B (8 * hBad) = 0#64 ↔ P) ∧ Frm B [(8 * hBad, 8)] m t.mem := by
  refine ⟨?_, ?_⟩
  · simp only [word, off, hBad, Nat.reduceMul, tm, rw_self]; exact hv
  · rw [tm]
    exact frm_writeW (a := 200) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)

/-- `Ph` survives a change of memory that keeps the header but `hBad`. -/
theorem Ph.keepBad {C : Nat} {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

/-! ## The digits' sum -/

/-- The sum of the `k` digits of 32 bits at `o`. -/
def dsum (m : Mem) (B : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dsum m B o k + w32 m B (o + 4 * k)

theorem dsum_le (m : Mem) (B : Addr) (o : Nat) : ∀ k, dsum m B o k ≤ k * 2 ^ 32
  | 0 => Nat.le_refl _
  | k + 1 => by
    have h1 := dsum_le m B o k
    have h2 : w32 m B (o + 4 * k) < 2 ^ 32 := (m.readW (off B (o + 4 * k)) 32).isLt
    show dsum m B o k + w32 m B (o + 4 * k) ≤ (k + 1) * 2 ^ 32
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- Modulo a divisor of `2³² − 1`, a number is its digits' sum. -/
theorem val32_mod {d : Nat} (hd : 2 ^ 32 % d = 1) (m : Mem) (B : Addr) (o : Nat) :
    ∀ k, val32 m B o k % d = dsum m B o k % d
  | 0 => rfl
  | k + 1 => by
    have hd1 : 1 % d = 1 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · have : d = 0 ∨ d = 1 := by omega
        rcases this with rfl | rfl <;> simp at hd
      · exact Nat.mod_eq_of_lt h
    have hp : 2 ^ (32 * k) % d = 1 := by rw [Nat.pow_mul, Nat.pow_mod, hd, Nat.one_pow, hd1]
    rw [val32_succ, dsum, Nat.add_mod, Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod, val32_mod hd m B o k,
      ← Nat.add_mod]

/-- After `j` digits. -/
def DInv (u : State) (B : Addr) (o : Nat) (j : Nat) (t : State) : Prop :=
  (t.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o j) ∧ t.gpr .r5 = off B (o + 4 * j) ∧ t.mem = u.mem) ∧
    Keep [.r0, .r3, .r4, .r5] u t

theorem digitSum_ok {u : State} {B : Addr} {Z o w : Nat} (hs : Scr u B Z) (h10 : u.gpr .r10 = off B o)
    (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w ≤ 128) (hZ : o + 8 * w ≤ Z) :
    WP isa digitSum u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o (2 * w)) ∧ t.mem = u.mem) ∧ Keep [.r0, .r3, .r4, .r5] u t := by
  unfold digitSum
  refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 0 ∧
      v.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ v.gpr .r5 = off B o ∧ v.mem = u.mem)
    (by prun [h10, h11, BitVec.add_zero]) (by decide)) fun v ⟨⟨v3, v4, v5, vm⟩, kv⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .r4) (N := 2 * w) (by omega) (by omega) (DInv u B o)
    (fun j hj t ⟨⟨t3, t5, tm⟩, kt⟩ tc => ?_)
    ⟨⟨by rw [v3]; rfl, by rw [v5, Nat.mul_zero, Nat.add_zero], vm⟩, kv.mono (by decide)⟩ v4)
    fun t ⟨⟨t3, _, tm⟩, kt⟩ => ⟨⟨t3, tm⟩, kt⟩
  have hld : InRegions (t.rd ++ t.wr) (off B (o + 4 * j)) 4 := by
    exact (hs.congr kt.wr).ld (by omega)
  have hle := dsum_le u.mem B o j
  have hx : w32 u.mem B (o + 4 * j) < 2 ^ 32 := (u.mem.readW (off B (o + 4 * j)) 32).isLt
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 (dsum u.mem B o (j + 1)) ∧
      t'.gpr .r5 = off B (o + 4 * (j + 1)) ∧ t'.mem = u.mem ∧ t'.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1) ?_
    (by decide)) fun t' ⟨⟨a3, a5, am, a4⟩, k'⟩ => ⟨⟨⟨a3, a5, am⟩, (kt.trans k').mono (by decide)⟩, a4⟩
  simp only [List.cons_append, List.nil_append]
  prun [t5, t3, hld, tm, BitVec.add_zero]
  refine ⟨?_, by rw [show o + 4 * j + 4 = o + 4 * (j + 1) by omega]⟩
  have hj' : j * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (dsum u.mem B o j % 2 ^ 64 + w32 u.mem B (o + 4 * j) % 2 ^ 64) % 2 ^ 64 =
    (dsum u.mem B o j + w32 u.mem B (o + 4 * j)) % 2 ^ 64
  omega

/-! ## The remainder by the reciprocal -/

theorem quot3 {S : Nat} (hS : S < 18446744073709551616) :
    S * 12297829382473034411 / 18446744073709551616 / 2 = S / 3 := by omega

theorem quot3_lt {S : Nat} (hS : S < 18446744073709551616) :
    S * 12297829382473034411 / 18446744073709551616 < 18446744073709551616 := by omega

/-- `mod3`'s arithmetic: `S − ⌊S m / 2^(64 + 1)⌋ 3 = S mod 3`. (`BitVec.toNat_sub` sends
`simp` astray here, so the product is rewritten first.) -/
theorem mod3_bv {S : Nat} (hS : S < 2 ^ 64) :
    BitVec.ofNat 64 S - BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (12297829382473034411#64).toNat / 18446744073709551616) >>> 1 *
      3#64 = BitVec.ofNat 64 (S % 3) := by
  have hS' : S < 18446744073709551616 := hS
  have hp : BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (12297829382473034411#64).toNat / 18446744073709551616) >>> 1 *
      3#64 = BitVec.ofNat 64 (S / 3 * 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS]
    rw [show (12297829382473034411 : Nat) % 2 ^ 64 = 12297829382473034411 from rfl, Nat.mod_eq_of_lt (quot3_lt hS'),
      show (2 : Nat) ^ 1 = 2 from rfl, quot3 hS', show (3 : Nat) % 2 ^ 64 = 3 from rfl]
  rw [hp, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (Nat.div_mul_le_self S 3),
    show S - S / 3 * 3 = S % 3 by omega]

theorem mod3_ok {u : State} {S : Nat} (h3 : u.gpr .r3 = BitVec.ofNat 64 S) (hS : S < 2 ^ 64) :
    WP isa (.block mod3) u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (S % 3) ∧ t.mem = u.mem) ∧ Keep [.r3, .r6, .r7] u t := by
  have hc : ((BitVec.signExtend 64 ((0xAAAA : BitVec 16) ++ (0 : BitVec 16)) ||| BitVec.setWidth 64 (0xAAAA : BitVec 16))
      <<< 32 ||| BitVec.setWidth 64 (0xAAAA : BitVec 16) <<< 16 ||| BitVec.setWidth 64 (0xAAAB : BitVec 16)) =
      BitVec.ofNat 64 12297829382473034411 := by decide
  refine WP.keep _ ?_ (by decide)
  simp only [mod3, modSmall]
  prun [h3, exec_lis, exec_ori, exec_oris, exec_mulhu, hc]
  exact mod3_bv hS

theorem quot5 {S : Nat} (hS : S < 18446744073709551616) :
    S * 14757395258967641293 / 18446744073709551616 / 4 = S / 5 := by omega

theorem quot5_lt {S : Nat} (hS : S < 18446744073709551616) :
    S * 14757395258967641293 / 18446744073709551616 < 18446744073709551616 := by omega

/-- `mod5`'s arithmetic: `S − ⌊S m / 2^(64 + 2)⌋ 5 = S mod 5`. (`BitVec.toNat_sub` sends
`simp` astray here, so the product is rewritten first.) -/
theorem mod5_bv {S : Nat} (hS : S < 2 ^ 64) :
    BitVec.ofNat 64 S - BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (14757395258967641293#64).toNat / 18446744073709551616) >>> 2 *
      5#64 = BitVec.ofNat 64 (S % 5) := by
  have hS' : S < 18446744073709551616 := hS
  have hp : BitVec.ofNat 64 ((BitVec.ofNat 64 S).toNat * (14757395258967641293#64).toNat / 18446744073709551616) >>> 2 *
      5#64 = BitVec.ofNat 64 (S / 5 * 5) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS]
    rw [show (14757395258967641293 : Nat) % 2 ^ 64 = 14757395258967641293 from rfl, Nat.mod_eq_of_lt (quot5_lt hS'),
      show (2 : Nat) ^ 2 = 4 from rfl, quot5 hS', show (5 : Nat) % 2 ^ 64 = 5 from rfl]
  rw [hp, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (Nat.div_mul_le_self S 5),
    show S - S / 5 * 5 = S % 5 by omega]

theorem mod5_ok {u : State} {S : Nat} (h3 : u.gpr .r3 = BitVec.ofNat 64 S) (hS : S < 2 ^ 64) :
    WP isa (.block mod5) u fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (S % 5) ∧ t.mem = u.mem) ∧ Keep [.r3, .r6, .r7] u t := by
  have hc : ((BitVec.signExtend 64 ((0xCCCC : BitVec 16) ++ (0 : BitVec 16)) ||| BitVec.setWidth 64 (0xCCCC : BitVec 16))
      <<< 32 ||| BitVec.setWidth 64 (0xCCCC : BitVec 16) <<< 16 ||| BitVec.setWidth 64 (0xCCCD : BitVec 16)) =
      BitVec.ofNat 64 14757395258967641293 := by decide
  refine WP.keep _ ?_ (by decide)
  simp only [mod5, modSmall]
  prun [h3, exec_lis, exec_ori, exec_oris, exec_mulhu, hc]
  exact mod5_bv hS

/-! ## The congruence -/

theorem and7 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem and1 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem flag2 : ∀ b < 3, ∀ c < 8, ((BitVec.ofNat 64 b ^^^ BitVec.ofNat 64 2) |||
    (BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 3) = 0#64 ↔ b = 2 ∧ c = 3) := by decide

theorem flag5 : ∀ b < 5, ∀ c < 2, (((BitVec.ofNat 64 b ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) |||
    (BitVec.ofNat 64 c ^^^ BitVec.ofNat 64 1) = 0#64 ↔ (b = 2 ∨ b = 3) ∧ c = 1) := by decide

/-- The candidate's low digit and digits' sum. -/
theorem low_sum {m : Mem} {B : Addr} {o w : Nat} (hw : 1 ≤ w) :
    wv m B o w % 8 = w32 m B o % 8 ∧ wv m B o w % 2 = w32 m B o % 2 ∧
      wv m B o w % 3 = dsum m B o (2 * w) % 3 ∧ wv m B o w % 5 = dsum m B o (2 * w) % 5 := by
  rw [← Pre.val32_eq_wv]
  refine ⟨?_, ?_, val32_mod (by decide) m B o _, val32_mod (by decide) m B o _⟩ <;>
  · obtain ⟨k, hk⟩ : ∃ k, 2 * w = k + 1 := ⟨2 * w - 1, by omega⟩
    rw [hk, VG.Proof.Mont.val32]
    omega

/-- Generator 2's branch. -/
theorem residue2_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue2 s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 24 = 11) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h10 := hp.r10
  have h11 := hp.r11
  generalize hwd : wOf p.bits = w at h10 h11 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  obtain ⟨l8, -, l3, -⟩ := low_sum (m := s.mem) (B := p.B) (o := slot w 0) (by omega : 1 ≤ w)
  unfold residue2
  refine WP.seq (WP.mono (digitSum_ok h.scr h10 h11 (by omega) hw128 hZ) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 4 := (h.scr.congr kv.wr).ld (by omega)
  refine WP.mono (WP.keep [.r4] (Q := fun a => a.gpr .r4 = BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) ∧
      a.mem = s.mem) ?_ (by decide)) fun a ⟨⟨a4, am⟩, ka⟩ => ?_
  · prun [(kv.gpr .r10 (by decide)).trans h10, hld, vm, BitVec.add_zero]
    rw [BitVec.ofNat_toNat]
  have hS : dsum s.mem p.B (slot w 0) (2 * w) < 2 ^ 64 := by
    have := dsum_le s.mem p.B (slot w 0) (2 * w)
    have : 2 * w * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega
  refine WP.mono (mod3_ok ((ka.gpr .r3 (by decide)).trans v3) hS) fun b ⟨⟨b3, bm⟩, kb⟩ => ?_
  have hb : St p b := h.step (by rw [bm, am]; exact Frm.refl _ _ _) ((kv.trans ka).trans kb)
  refine WP.mono (WP.keep [.r3, .r4, .r6] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      ((BitVec.ofNat 64 (dsum s.mem p.B (slot w 0) (2 * w) % 3) ^^^ BitVec.ofNat 64 2) |||
        ((BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 3))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, (((kv.trans ka).trans kb).trans kt).mono (by decide)⟩
  · simp only [sth, hBad]
    prun [hb.r31, hb.st (d := 200) (by decide), bm, am, b3, (kb.gpr .r4 (by decide)).trans a4]
  · rw [and7, flag2 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)), ← l8, ← l3]
    omega

/-- Generator 5's branch. -/
theorem residue5_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue5 s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 10 = 3 ∨ wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) % 10 = 7) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h10 := hp.r10
  have h11 := hp.r11
  generalize hwd : wOf p.bits = w at h10 h11 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  obtain ⟨-, l2, -, l5⟩ := low_sum (m := s.mem) (B := p.B) (o := slot w 0) (by omega : 1 ≤ w)
  unfold residue5
  refine WP.seq (WP.mono (digitSum_ok h.scr h10 h11 (by omega) hw128 hZ) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have hld : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 4 := (h.scr.congr kv.wr).ld (by omega)
  refine WP.mono (WP.keep [.r4] (Q := fun a => a.gpr .r4 = BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) ∧
      a.mem = s.mem) ?_ (by decide)) fun a ⟨⟨a4, am⟩, ka⟩ => ?_
  · prun [(kv.gpr .r10 (by decide)).trans h10, hld, vm, BitVec.add_zero]
    rw [BitVec.ofNat_toNat]
  have hS : dsum s.mem p.B (slot w 0) (2 * w) < 2 ^ 64 := by
    have := dsum_le s.mem p.B (slot w 0) (2 * w)
    have : 2 * w * 2 ^ 32 ≤ 256 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega
  refine WP.mono (mod5_ok ((ka.gpr .r3 (by decide)).trans v3) hS) fun b ⟨⟨b3, bm⟩, kb⟩ => ?_
  have hb : St p b := h.step (by rw [bm, am]; exact Frm.refl _ _ _) ((kv.trans ka).trans kb)
  refine WP.mono (WP.keep [.r3, .r4, .r6] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      (((BitVec.ofNat 64 (dsum s.mem p.B (slot w 0) (2 * w) % 5) ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) |||
        ((BitVec.ofNat 64 (w32 s.mem p.B (slot w 0)) &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, (((kv.trans ka).trans kb).trans kt).mono (by decide)⟩
  · simp only [sth, hBad]
    prun [hb.r31, hb.st (d := 200) (by decide), bm, am, b3, (kb.gpr .r4 (by decide)).trans a4]
  · rw [and1, flag5 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)), ← l2, ← l5]
    omega

/-- `residue`: `hBad` zero iff array 0 has the generator's congruence. -/
theorem residue_ok {C : Nat} {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ goodRes p.g (wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits))) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  unfold residue
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 p.g - 2#64 ∧ u.mem = s.mem)
    (by simp only [ldh, hGen]; prun [h.r31, h.ld (d := 128) (by decide), h.args.gen']) (by decide))
    fun u ⟨⟨u3, um⟩, ku⟩ => ?_)
  have hu := h.step (by rw [um]; exact Frm.refl _ _ _) ku
  have hpu : Ph p p.bits C u := hp.keepBad (ku.gpr .r10 (by decide)) (ku.gpr .r11 (by decide))
    (ku.gpr .r29 (by decide)) fun d _ => by rw [um]
  have hwv : wv u.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) := by
    rw [um]
  refine WP.ite (u.gpr .r3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hg : p.g = 2 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact hg
      · exact absurd hb (by decide)
    refine WP.mono (residue2_ok hu hpu) fun t ⟨⟨hb', f⟩, k⟩ => ⟨⟨?_, by rw [← um]; exact f⟩, (ku.trans k).mono (by decide)⟩
    rw [hb', hwv, goodRes, ite_eq_left hg]
  · have hg : p.g = 5 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact absurd hb (by decide)
      · exact hg
    refine WP.mono (residue5_ok hu hpu) fun t ⟨⟨hb', f⟩, k⟩ => ⟨⟨?_, by rw [← um]; exact f⟩, (ku.trans k).mono (by decide)⟩
    rw [hb', hwv, goodRes, ite_eq_right (by omega_arith)]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
