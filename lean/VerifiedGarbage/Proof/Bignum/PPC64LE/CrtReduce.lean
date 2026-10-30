module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: the input modulo a prime

`reduceIn_ok`: `c mod p` into array 4 of `p`'s working space, from `c` in
`X`'s array 6, a chunk `C_i` of `w` words at a time from the bottom, by
Montgomery multiplications: with `q ≡ -R^(i+1)` and `T = C_i q R⁻¹ ≡ -C_i R^i`,
`S - T` adds `C_i R^i` to `S`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-! ## The arithmetic -/

/-- `x ≡ 0 (mod p)` from `R x ≡ 0`, for `R` prime to `p`. -/
theorem mod_cancel {R p x : Nat} (hR : Nat.Coprime R p) (h : R * x % p = 0) : x % p = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.Coprime.dvd_of_dvd_mul_left hR.symm (Nat.dvd_of_mod_eq_zero h))

/-- `T ≡ C q R⁻¹` and `q ≡ -R^(i+1)` give `T ≡ -C R^i`. -/
theorem chunk_t {R p T C q i : Nat} (hR : Nat.Coprime R p) (hT : T * R % p = C * q % p)
    (hq : (q + R ^ (i + 1)) % p = 0) : (T + C * R ^ i) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (T + C * R ^ i) = T * R + C * (q + R ^ (i + 1)) - C * q := by
    rw [Nat.pow_succ]; grind
  have h1 : (T * R + C * (q + R ^ (i + 1))) % p = (C * q) % p := by
    rw [Nat.add_mod, hT, Nat.mul_mod C (q + R ^ (i + 1)), hq, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  have h2 : C * q ≤ T * R + C * (q + R ^ (i + 1)) := by rw [Nat.mul_add]; omega
  rw [e]
  exact Nat.sub_mod_eq_zero_of_mod_eq h1

/-- `q' ≡ q R² R⁻¹` and `q ≡ -R^(i+1)` give `q' ≡ -R^(i+2)`. -/
theorem chunk_q {R p q q' r2 i : Nat} (hR : Nat.Coprime R p) (hq' : q' * R % p = q * r2 % p)
    (hr2 : r2 % p = R * R % p) (hq : (q + R ^ (i + 1)) % p = 0) : (q' + R ^ (i + 1 + 1)) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (q' + R ^ (i + 1 + 1)) = q' * R + R * R * (q + R ^ (i + 1)) - R * R * q := by
    rw [show R ^ (i + 1 + 1) = R ^ (i + 1) * R from Nat.pow_succ _ _]; grind
  have h1 : (q' * R + R * R * (q + R ^ (i + 1))) % p = (R * R * q) % p := by
    rw [Nat.add_mod, hq', Nat.mul_mod (R * R) (q + R ^ (i + 1)), hq, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod,
      Nat.mul_mod q r2, hr2, ← Nat.mul_mod, Nat.mul_comm]
  have h2 : R * R * q ≤ q' * R + R * R * (q + R ^ (i + 1)) := by rw [Nat.mul_add]; omega
  rw [e]
  exact Nat.sub_mod_eq_zero_of_mod_eq h1

/-- `q₀ ≡ (p - 1) R² R⁻¹ ≡ -R`. -/
theorem chunk_q0 {R p q r2 : Nat} (hR : Nat.Coprime R p) (hp : 1 ≤ p) (hq : q * R % p = r2 * (p - 1) % p)
    (hr2 : r2 % p = R * R % p) : (q + R ^ (0 + 1)) % p = 0 := by
  refine mod_cancel hR ?_
  have e : R * (q + R ^ (0 + 1)) + R * R * (p - 1) = q * R + R * R * p := by
    rw [Nat.zero_add, Nat.pow_one]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]; grind
  have h1 : (q * R + R * R * p) % p = (R * R * (p - 1)) % p := by
    rw [Nat.add_mod, hq, Nat.mul_mod (R * R) p, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod,
      Nat.mul_mod r2, hr2, ← Nat.mul_mod, Nat.mul_comm]
  rw [← e] at h1
  have := Nat.sub_mod_eq_zero_of_mod_eq h1
  rwa [Nat.add_sub_cancel] at this

/-- `S' = (S + p - T) mod p` adds `C R^i` to `S` when `T ≡ -C R^i`. -/
theorem chunk_s {p S T A C Ri S' : Nat} (hT : T < p) (hS : S % p = A % p) (hTC : (T + C * Ri) % p = 0)
    (hS' : S' = (S + p - T) % p) : S' % p = (A + Ri * C) % p := by
  rw [hS', Nat.mod_mod]
  have e : (S + p - T + (T + C * Ri)) % p = (A + Ri * C) % p := by
    rw [show S + p - T + (T + C * Ri) = S + C * Ri + p by omega, Nat.add_mod_right, Nat.add_mod, hS,
      ← Nat.add_mod, Nat.mul_comm]
  rw [Nat.add_mod, hTC, Nat.add_zero, Nat.mod_mod] at e
  exact e

/-- The number of chunks of `w` words of `K` words. -/
abbrev nChunks (K w : Nat) : Nat := (K + w - 1) / w

theorem lt_nChunks {K w m : Nat} (hw : 1 ≤ w) : m < nChunks K w ↔ m * w < K := by
  unfold nChunks
  rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul]
  omega

theorem nChunks_pos {K w : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) : 0 < nChunks K w :=
  (lt_nChunks hw).mpr (by rw [Nat.zero_mul]; omega)

theorem le_nChunks_mul {K w : Nat} (hw : 1 ≤ w) : K ≤ nChunks K w * w := by
  have := mt (lt_nChunks (K := K) (m := nChunks K w) hw).mpr (Nat.lt_irrefl _)
  omega

theorem nChunks_mul_lt {K w : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) : nChunks K w * w < K + w := by
  have h := (lt_nChunks (K := K) (m := nChunks K w - 1) hw).mp (by have := nChunks_pos hw hK; omega)
  have e : nChunks K w * w = (nChunks K w - 1) * w + w := by
    have := nChunks_pos hw hK
    rw [← Nat.succ_mul]; congr 1; omega
  omega

/-- The first `a` words of a number of `a + b` words below `2^(64 a)`. -/
theorem wv_prefix {m : Mem} {B : Addr} {d a b V : Nat} (h : wv m B d (a + b) = V) (hV : V < 2 ^ (64 * a)) :
    wv m B d a = V := by
  rw [wv_add] at h
  have hl := wv_lt m B d a
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * a) b) with h0 | h0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at h; exact h
  · have : 2 ^ (64 * a) ≤ 2 ^ (64 * a) * wv m B (d + 8 * a) b := Nat.le_mul_of_pos_right _ h0
    omega

/-- The chunks of `k` bytes, of `w ≤ ⌈k / 8⌉` words, fit in `2 ⌈k / 8⌉` words. -/
theorem chunks_le {k w : Nat} (hw : 1 ≤ w) (hwk : w ≤ (k + 7) / 8) :
    w * nChunks ((k + 7) / 8) w ≤ 2 * ((k + 7) / 8) := by
  have := nChunks_mul_lt (K := (k + 7) / 8) hw (by omega)
  rw [Nat.mul_comm]; omega

/-- The input of `k` bytes, in `2 ⌈k / 8⌉` words: its chunks' words hold it. -/
theorem chunks_val {m : Mem} {B : Addr} {d k w V : Nat} (hw : 1 ≤ w) (hwk : w ≤ (k + 7) / 8)
    (h : wv m B d (2 * ((k + 7) / 8)) = V) (hV : V < 256 ^ k) : wv m B d (w * nChunks ((k + 7) / 8) w) = V := by
  have hle := chunks_le hw hwk
  have hK := le_nChunks_mul (K := (k + 7) / 8) hw
  refine wv_prefix (b := 2 * ((k + 7) / 8) - w * nChunks ((k + 7) / 8) w) (by rw [Nat.add_sub_cancel' hle]; exact h) ?_
  refine Nat.lt_of_lt_of_le hV ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm w]; omega)

/-- `r3 := ((r31 - 1) >> 63) ^ 1`: 1 if `r31` is in `[1, 2^63]`, positive as a signed number but for `2^63`. -/
theorem flag_ne_zero (x : BitVec 64) :
    ((x - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1).toNat ≠ 0 ↔ x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63 := by
  have h : ((x - BitVec.ofNat 64 1) >>> 63).toNat = if x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63 then 0 else 1 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  have hy : ∀ y : BitVec 64, y.toNat = 0 ∨ y.toNat = 1 → ((y ^^^ BitVec.ofNat 64 1).toNat ≠ 0 ↔ y.toNat = 0) := by
    intro y hy
    rcases hy with h0 | h1
    · have : y = 0#64 := BitVec.eq_of_toNat_eq h0
      subst this; decide
    · have : y = 1#64 := BitVec.eq_of_toNat_eq h1
      subst this; decide
  rw [hy _ (by rw [h]; split <;> simp), h]
  split <;> simp_all

/-- The remaining words after `j` chunks, as `r31` holds them. -/
theorem flag_iff {K w j : Nat} (hw : 1 ≤ w) (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hw' : w < 2 ^ 40)
    (hj : j < nChunks K w) :
    let x := BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (j + 1))
    (x.toNat ≠ 0 ∧ x.toNat ≤ 2 ^ 63) ↔ j + 1 ≠ nChunks K w := by
  intro x
  have hm := nChunks_mul_lt hw hK
  have hjw : (j + 1) * w ≤ nChunks K w * w := Nat.mul_le_mul_right _ hj
  have hc := (lt_nChunks (K := K) (m := j + 1) hw)
  have e : w * (j + 1) = (j + 1) * w := Nat.mul_comm _ _
  have hx : x.toNat = (2 ^ 64 - (j + 1) * w % 2 ^ 64 + K % 2 ^ 64) % 2 ^ 64 := by
    show (BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (j + 1))).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e]
  rw [hx]
  constructor
  · intro ⟨h1, h2⟩ hn
    rw [hn] at hc
    have := le_nChunks_mul (K := K) hw
    rw [← hn] at this
    omega
  · intro hn
    have hlt : (j + 1) * w < K := hc.mp (by omega)
    omega

/-! ## The pieces -/

/-- `copySub_ok`, with where `r15` ends. -/
theorem copyAdv_ok {s : State} {B : Addr} {Z a b w : Nat} (hs : Scr s B Z)
    (h15 : s.gpr .r15 = off B a) (h14 : s.gpr .r14 = off B b) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (ha : a + 8 * w ≤ Z) (hb : b + 8 * w ≤ Z)
    (hd : a + 8 * w ≤ b ∨ b + 8 * w ≤ a) :
    WP isa Precompute.copyWords s fun t =>
      ((∀ i < w, word t.mem B (b + 8 * i) = word s.mem B (a + 8 * i)) ∧
        Outside B b (8 * w) s.mem t.mem ∧ t.gpr .r15 = off B (a + 8 * w)) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hn := hs.nowrap
  have z : ∀ c, off (off B c) 0 = off B c := fun c => by rw [off_off, Nat.add_zero]
  refine WP.mono (Pub.copyIn_ok (B := off B b) (Z := 8 * w) (P := off B a) (Zp := 8 * w) (dS := 0) (dD := 0)
    (hs.sub hb) (by have := toNat_off_le B a; omega)
    (fun i hi => by rw [off_off]; exact hs.ld (by omega) (by decide))
    (by rw [z]; exact h15) (by rw [z]; exact h14) h11 hw hw' (by omega) (by omega)
    (sep_sub B (by omega) (by omega) hd (by omega))) fun t ⟨⟨_, e15, hw, ho⟩, k⟩ =>
      ⟨⟨fun i hi => by have := hw i hi; rwa [word_off, word_off, Nat.zero_add] at this,
        out_sub ho (by omega) (by omega) (by omega), by rw [e15, off_off, Nat.zero_add]⟩, k⟩

/-- A frame of a part, from one of the whole. -/
theorem out_rebase {B : Addr} {o d n : Nat} {m m' : Mem} (h : Outside B (o + d) n m m') (ho : o < 2 ^ 64) :
    Mont.Outside (off B o) d n m m' := by
  intro x hx
  refine h x ?_
  change ofs (off B o) x < d ∨ d + n ≤ ofs (off B o) x at hx
  change ofs B x < o + d ∨ o + d + n ≤ ofs B x
  rcases ofs_rebase B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- `r30 := r15`. -/
theorem mv30_ok (t : State) :
    WP isa (.block [.addi .r30 .r15 0]) t fun u => (u.gpr .r30 = t.gpr .r15 ∧ u.mem = t.mem) ∧ Keep [.r30] t u :=
  WP.keep _ (by prun [BitVec.add_zero]) (by decide)

theorem shr1_ofNat {w : Nat} (hw : w < 2 ^ 62) : BitVec.ofNat 64 (2 * w) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The count of the words left, and whether any are. -/
theorem tick_ok {t : State} {w : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : w < 2 ^ 62) :
    WP isa (.block [.lsr .d .r3 .r11 1, .sub .r31 .r31 .r3, .subi .r3 .r31 1, .lsr .d .r3 .r3 63, .li .r0 1,
      .logic .xor .r3 .r3 .r0]) t fun u =>
      (u.gpr .r31 = t.gpr .r31 - BitVec.ofNat 64 w ∧
        u.gpr .r3 = (t.gpr .r31 - BitVec.ofNat 64 w - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
        u.mem = t.mem) ∧ Keep [.r0, .r3, .r31] t u := by
  refine WP.keep _ ?_ (by decide)
  prun [h11, shr1_ofNat hw]

/-- A frame of arrays 2–7, from one of some of them. -/
theorem outs_work {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Mont.Outs B rs m m')
    (hr : ∀ r ∈ rs, slot w 2 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8) : Mont.Outside B (slot w 2) (6 * (8 * (w + 2))) m m' :=
  fun x hx => h x fun r hr' => by
    have := hr r hr'
    have e : slot w 8 = slot w 2 + 6 * (8 * (w + 2)) := by unfold slot; omega
    change Mont.ofs B x < slot w 2 ∨ slot w 2 + 6 * (8 * (w + 2)) ≤ Mont.ofs B x at hx
    change Mont.ofs B x < r.1 ∨ r.1 + r.2 ≤ Mont.ofs B x
    omega

/-- A number outside every region of a frame. -/
theorem outs_val32 {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Mont.Outs B rs m m') {d k : Nat}
    (hr : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd : d + 4 * k ≤ 2 ^ 64) :
    val32 m' B d k = val32 m B d k :=
  val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ fun r hr' => by
    have := hr r hr'; rw [Mont.ofs_off B (by omega)]; omega)

/-- The registers `chunkStep` writes. -/
def chunkRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r30, .r31]

/-- Between the chunks of `reduceIn`, after `i` of them: in `p`'s working space
`off BX oA` of `w` words, `p` (`Pv`), `R² mod p` (`R2`), `p - 1`,
`q ≡ -R^(i+1)` in array 5 and `S ≡` the first `w i` words of `X`'s array 6 in
array 4; the next chunk at `r30`, the words left in `r31`. -/
structure ChunkI (s : State) (BX : Addr) (Z oA w wX K Pv R2 i : Nat) (t : State) : Prop where
  scr : Scr t BX Z
  r10 : t.gpr .r10 = off (off BX oA) (slot w 0)
  r21 : t.gpr .r21 = off (off BX oA) (slot w 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem (off BX oA) (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  r30 : t.gpr .r30 = off BX (slot wX 6 + 8 * (w * i))
  r31 : t.gpr .r31 = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * i)
  p0 : val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv
  p1 : val32 t.mem (off BX oA) (slot w 1) (2 * w) = R2
  p8 : val32 t.mem (off BX oA) (slot w 8) (2 * w) = Pv - 1
  qlt : val32 t.mem (off BX oA) (slot w 5) (2 * w) < Pv
  q : (val32 t.mem (off BX oA) (slot w 5) (2 * w) + (2 ^ (64 * w)) ^ (i + 1)) % Pv = 0
  slt : val32 t.mem (off BX oA) (slot w 4) (2 * w) < Pv
  sv : val32 t.mem (off BX oA) (slot w 4) (2 * w) % Pv = wv s.mem BX (slot wX 6) (w * i) % Pv
  out : Outside BX oA (slot w 24) s.mem t.mem
  keep : Keep chunkRegs s t

/-- One chunk. -/
theorem chunkStep_ok {s t : State} {BX : Addr} {Z oA w wX K Pv R2 i : Nat}
    (hA : oA + slot w 24 ≤ Z) (hX : slot wX 6 + 8 * (w * nChunks K w) ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1) (hR2 : R2 < Pv)
    (hR2' : R2 % Pv = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv) (hi : i < nChunks K w)
    (I : ChunkI s BX Z oA w wX K Pv R2 i t) :
    WP isa chunkStep t fun u => ChunkI s BX Z oA w wX K Pv R2 (i + 1) u ∧
      ((u.gpr .r3).toNat ≠ 0 ↔ i + 1 ≠ nChunks K w) := by
  have hn := I.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  have e6 := e 6; have e7 := e 7; have e8 := e 8; have e9 := e 9; have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hsA := I.scr.sub hA
  -- The chunk into array 6, and `r30` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) I.r10 I.r29 6) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = t₁.gpr .r30 ∧ u.mem = t₁.mem) (by prun [BitVec.add_zero])
    (by decide)) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copyAdv_ok (a := slot wX 6 + 8 * (w * i)) (b := oA + slot w 6) (w := w) (I.scr.congr k12.wr)
    (by rw [a15, (k1.gpr _ (by decide)).trans I.r30]) (by rw [k2.gpr _ (by decide), a14, off_off])
    ((k12.gpr _ (by decide)).trans I.r11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₃ ⟨⟨c3, o3, a15'⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (mv30_ok t₃) fun t₄ ⟨⟨a30, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have o3' : Mont.Outside (off BX oA) (slot w 6) (8 * w) t.mem t₄.mem := by
    rw [m4]; exact out_rebase o3 (by omega_arith)
  have W4 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem t₄.mem := o3'.mono (by omega_arith) (by omega_arith)
  -- The chunk's value.
  let C := wv s.mem BX (slot wX 6 + 8 * (w * i)) w
  have v6 : val32 t₄.mem (off BX oA) (slot w 6) (2 * w) = C := by
    rw [Pre.val32_eq_wv, wv_off, m4, wv_congr2 fun j hj => c3 j hj]
    exact I.out.wv (Or.inl (by omega_arith)) (by omega_arith)
  have v0 : val32 t₄.mem (off BX oA) (slot w 0) (2 * w) = Pv := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p0]
  have v1 : val32 t₄.mem (off BX oA) (slot w 1) (2 * w) = R2 := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p1]
  have v8 : val32 t₄.mem (off BX oA) (slot w 8) (2 * w) = Pv - 1 := by
    rw [W4.val32 (Or.inr (by omega_arith)) (by omega_arith), I.p8]
  have v5 : val32 t₄.mem (off BX oA) (slot w 5) (2 * w) = val32 t.mem (off BX oA) (slot w 5) (2 * w) :=
    o3'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have v4 : val32 t₄.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) :=
    o3'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have w0 : w32 t₄.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) :=
    W4.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r31], t₄.gpr r = t.gpr r := fun r hr =>
    k14.gpr r (by revert r hr; decide)
  -- `T := C q R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 7) (a := 6) (b := 5) (hsA.congr k14.wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g .r10 (by decide)).trans I.r10) ((g .r29 (by decide)).trans I.r29) ((g .r11 (by decide)).trans I.r11)
    (by rw [g .r12 (by decide)]; exact I.r12) (by rw [g .r12 (by decide), w0]; exact I.inv)
    (by rw [v5, v0]; exact I.qlt)) fun t₅ ⟨⟨T5, T5e, o5⟩, k5⟩ => ?_)
  rw [v0, v6, v5] at T5e
  rw [v0] at T5
  have W5 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₄.mem t₅.mem :=
    outs_work o5 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u5 : ∀ j, j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 8 →
      val32 t₅.mem (off BX oA) (slot w j) (2 * w) = val32 t₄.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o5 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have w0' : w32 t₅.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) := by
    rw [W5.w32 (Or.inl (by omega_arith)) (by omega_arith), w0]
  have g5 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r30, .r31], t₅.gpr r = t₄.gpr r := fun r hr =>
    k5.gpr r (by revert r hr; decide)
  -- `q := q R² R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 5) (a := 5) (b := 1) (hsA.congr (k14.trans k5).wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g5 .r10 (by decide)).trans ((g .r10 (by decide)).trans I.r10))
    ((g5 .r29 (by decide)).trans ((g .r29 (by decide)).trans I.r29))
    ((g5 .r11 (by decide)).trans ((g .r11 (by decide)).trans I.r11))
    (by rw [g5 .r12 (by decide), g .r12 (by decide)]; exact I.r12)
    (by rw [g5 .r12 (by decide), g .r12 (by decide), w0']; exact I.inv)
    (by rw [u5 1 (by decide), u5 0 (by decide), v1, v0]; exact hR2)) fun t₆ ⟨⟨Q6, Q6e, o6⟩, k6⟩ => ?_)
  rw [u5 0 (by decide), v0, u5 5 (by decide), v5, u5 1 (by decide), v1] at Q6e
  rw [u5 0 (by decide), v0] at Q6
  have W6 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₅.mem t₆.mem :=
    outs_work o6 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u6 : ∀ j, j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 →
      val32 t₆.mem (off BX oA) (slot w j) (2 * w) = val32 t₅.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have g6 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r31], t₆.gpr r = t.gpr r := fun r hr => by
    rw [k6.gpr r (by revert r hr; decide), g5 r (by revert r hr; decide), g r (by revert r hr; decide)]
  have k16 := (k14.trans k5).trans k6
  have b30 : t₆.gpr .r30 = off BX (slot wX 6 + 8 * (w * i) + 8 * w) := by
    rw [k6.gpr .r30 (by decide), g5 .r30 (by decide), a30, a15']
  have hS6 : val32 t₆.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) := by
    rw [u6 4 (by decide), u5 4 (by decide), v4]
  have hT6 : val32 t₆.mem (off BX oA) (slot w 7) (2 * w) = val32 t₅.mem (off BX oA) (slot w 7) (2 * w) :=
    u6 7 (by decide)
  -- `S - T mod p` into array 3.
  refine recP2a_ok (bj := 7) (hsA.congr k16.wr) (by omega_arith) (by decide) (by decide) (by decide) hw2 hw'
    ((g6 .r10 (by decide)).trans I.r10) ((g6 .r21 (by decide)).trans I.r21) ((g6 .r29 (by decide)).trans I.r29)
    ((g6 .r11 (by decide)).trans I.r11) (by rw [u6 0 (by decide), u5 0 (by decide), v0]) hT6 hS6 T5 I.slt
    fun t₇ v3 o7 a10 k7 => ?_
  have hsA7 := hsA.congr (k16.trans k7).wr
  have W7 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₆.mem t₇.mem :=
    outs_work o7 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp only [e] <;> omega_arith)
  -- Back into array 4.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) a10 ((k7.gpr _ (by decide)).trans
    ((g6 .r29 (by decide)).trans I.r29)) 4) fun t₈ ⟨⟨a14', m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k8.gpr _ (by decide)).trans a10)
    ((k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((g6 .r29 (by decide)).trans I.r29))) 3)
    fun t₉ ⟨⟨a15'', m9⟩, k9⟩ => ?_
  have k79 := (k7.trans k8).trans k9
  have r11_9 : t₉.gpr .r11 = BitVec.ofNat 64 (2 * w) := by
    rw [k79.gpr .r11 (by decide), g6 .r11 (by decide), I.r11]
  refine WP.seq (WP.mono (copySub_ok (a := slot w 3) (b := slot w 4) (w := w) (hsA7.congr (k8.trans k9).wr) a15''
    ((k9.gpr _ (by decide)).trans a14') r11_9 (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₁₀ ⟨⟨c10, o10⟩, k10⟩ => ?_)
  have hm9 : t₉.mem = t₇.mem := by rw [m9, m8]
  rw [hm9] at c10 o10
  refine WP.mono (tick_ok (t := t₁₀) ((k10.gpr _ (by decide)).trans r11_9) (by omega_arith)) fun u ⟨⟨b31, b3, mu⟩, ku⟩ => ?_
  have kall := (((k16.trans k79).trans k10).trans ku)
  have o10' : Mont.Outside (off BX oA) (slot w 4) (8 * w) t₇.mem u.mem := by rw [mu]; exact o10
  have W10 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₇.mem u.mem := o10'.mono (by omega_arith) (by omega_arith)
  have Wt : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem u.mem :=
    ((W4.trans W5).trans (W6.trans W7)).trans W10
  have gu : ∀ r ∈ [Reg.r11, .r12, .r21, .r23, .r29], u.gpr r = t.gpr r := fun r hr => by
    rw [ku.gpr r (by revert r hr; decide), k10.gpr r (by revert r hr; decide), k79.gpr r (by revert r hr; decide),
      g6 r (by revert r hr; decide)]
  -- The values.
  have s4 : val32 u.mem (off BX oA) (slot w 4) (2 * w) = (val32 t.mem (off BX oA) (slot w 4) (2 * w) + Pv -
      val32 t₅.mem (off BX oA) (slot w 7) (2 * w)) % Pv := by
    rw [mu, Pre.val32_eq_wv, wv_congr2 fun j hj => c10 j hj, ← Pre.val32_eq_wv, v3]
  have q5 : val32 u.mem (off BX oA) (slot w 5) (2 * w) = val32 t₆.mem (off BX oA) (slot w 5) (2 * w) := by
    rw [o10'.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    exact outs_val32 o7 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp only [e] <;> omega_arith)
      (by omega_arith)
  have hTC := chunk_t hR T5e I.q
  have hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  have hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  refine ⟨⟨I.scr.congr kall.wr, ?_, by rw [gu .r21 (by decide)]; exact I.r21,
    by rw [gu .r29 (by decide)]; exact I.r29, by rw [gu .r11 (by decide)]; exact I.r11,
    by rw [gu .r12 (by decide)]; exact I.r12,
    by rw [gu .r12 (by decide), Wt.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.inv, ?_, ?_,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p0,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p1,
    by rw [Wt.val32 (Or.inr (by omega_arith)) (by omega_arith)]; exact I.p8,
    by rw [q5]; exact Q6, by rw [q5]; exact chunk_q hR Q6e hR2' I.q,
    by rw [s4]; exact Nat.mod_lt _ (by omega_arith), ?_,
    I.out.trans (out_sub (fun x hx => Wt x hx) (by omega_arith) (by omega_arith) (by omega_arith)),
    (I.keep.trans kall).mono (by decide +kernel)⟩, ?_⟩
  · rw [ku.gpr .r10 (by decide), k10.gpr .r10 (by decide), k9.gpr .r10 (by decide), k8.gpr .r10 (by decide), a10]
  · rw [ku.gpr .r30 (by decide), k10.gpr .r30 (by decide), k79.gpr .r30 (by decide), b30, hwi1, Nat.mul_add,
      Nat.add_assoc]
  · rw [b31, k10.gpr .r31 (by decide), k79.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  · rw [s4]
    refine (chunk_s T5 I.sv hTC rfl).trans ?_
    rw [hwi1, wv_add, ← hpow]
  · have hx : t₁₀.gpr .r31 - BitVec.ofNat 64 w = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (i + 1)) := by
      rw [k10.gpr .r31 (by decide), k79.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith
    rw [b3, flag_ne_zero, hx]
    exact flag_iff (by omega_arith) hK hK' (by omega_arith) hi

/-- `p - 1` from `p` in array 8: its low word, odd, less 1. -/
theorem pm1_ok {t : State} {B : Addr} {Z w Pv : Nat} (hs : Scr t B Z) (hZ : slot w 9 ≤ Z) (hw : 1 ≤ w)
    (h14 : t.gpr .r14 = off B (slot w 8)) (h8 : val32 t.mem B (slot w 8) (2 * w) = Pv) (hodd : Pv % 2 = 1) :
    WP isa (.block [.load .d .r3 .r14 0, .subi .r3 .r3 1, .store .d .r3 .r14 0]) t fun u =>
      (val32 u.mem B (slot w 8) (2 * w) = Pv - 1 ∧ Mont.Outside B (slot w 8) 8 t.mem u.mem) ∧ Keep [.r3] t u := by
  have hn := hs.nowrap
  have e8 : slot w 8 = 256 + 8 * (8 * (w + 2)) := rfl
  have e9 : slot w 9 = 256 + 9 * (8 * (w + 2)) := rfl
  refine WP.keep _ ?_ (by decide)
  have hld : t.mem.readW (off B (slot w 8)) 64 = word t.mem B (slot w 8) := rfl
  prun [h14, BitVec.add_zero, hs.ld (show slot w 8 + 8 ≤ Z by omega), hs.st (show slot w 8 + 8 ≤ Z by omega), hld]
  have ow := writeW_outside t.mem B (d := slot w 8) (word t.mem B (slot w 8) - BitVec.ofNat 64 1) (by omega)
  refine ⟨?_, fun x hx => ow x hx⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = 1 + w' := ⟨w - 1, by omega⟩
  have L : ∀ m : Mem, wv m B (slot (1 + w') 8) (1 + w') =
      (word m B (slot (1 + w') 8)).toNat + 2 ^ 64 * wv m B (slot (1 + w') 8 + 8) w' := fun m => by
    rw [wv_add]; simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  subst h8
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, L, L] at *
  rw [word_writeW_self, ow.wv (Or.inr (by omega)) (by omega)]
  have hlow : (word t.mem B (slot (1 + w') 8)).toNat % 2 = 1 := by
    rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left] at hodd
    exact hodd
  generalize word t.mem B (slot (1 + w') 8) = x at hlow ⊢
  have hx : (x - BitVec.ofNat 64 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := x.isLt; omega
  rw [hx]
  omega

/-- `reduceIn`, in `p`'s working space `off BX oA` of `w` words, for `c` the
first `w n` words of `X`'s array 6 (`n` chunks of the `⌈k / 8⌉` words): `c mod p`
into array 4, changing only arrays 2–8. -/
theorem reduceIn_ok {s : State} {BX : Addr} {Z oA w wX k Pv Cv : Nat}
    (hs : Scr s BX Z) (hA : oA + slot w 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hn : w * nChunks ((k + 7) / 8) w ≤ wX)
    (h10 : s.gpr .r10 = off (off BX oA) (slot w 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h25 : s.gpr .r25 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hP : val32 s.mem (off BX oA) (slot w 0) (2 * w) = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hR2 : val32 s.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv)
    (hC : wv s.mem BX (slot wX 6) (w * nChunks ((k + 7) / 8) w) = Cv) :
    WP isa reduceIn s fun t =>
      (val32 t.mem (off BX oA) (slot w 4) (2 * w) = Cv % Pv ∧ val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv ∧
        val32 t.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv ∧ (t.gpr .r12).toNat < 2 ^ 32 ∧
        (w32 t.mem (off BX oA) (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        Outside BX oA (slot w 24) s.mem t.mem ∧ t.gpr .r10 = off (off BX oA) (slot w 0)) ∧ Keep chunkRegs s t := by
  have hn' := hs.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have e9 := e 9; have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have eX8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hsA := hs.sub hA
  generalize hKd : (k + 7) / 8 = K at hn hC
  have hK1 : 1 ≤ K := by omega_arith
  have hK' : K < 2 ^ 40 := by omega_arith
  have hX : slot wX 6 + 8 * (w * nChunks K w) ≤ oA := by omega_arith
  -- `p` into array 8.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 8) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = off (off BX oA) (slot w 0) ∧ u.mem = s₁.mem)
    (by prun [(k1.gpr .r10 (by decide)).trans h10, BitVec.add_zero]) (by decide)) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (a := slot w 0) (b := slot w 8) (w := w) (hsA.congr k12.wr) a15
    ((k2.gpr _ (by decide)).trans a14) ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have k13 := k12.trans k3
  have g3 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₃.gpr r = s.gpr r := fun r hr =>
    k13.gpr r (by revert r hr; decide)
  have v8 : val32 s₃.mem (off BX oA) (slot w 8) (2 * w) = Pv := by
    rw [Pre.val32_eq_wv, wv_congr2 fun j hj => c3 j hj, ← Pre.val32_eq_wv, hP]
  -- `p - 1`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((g3 .r10 (by decide)).trans h10)
    ((g3 .r29 (by decide)).trans h29) 8) fun s₄ ⟨⟨b14, m4⟩, k4⟩ => ?_
  refine WP.mono (pm1_ok (hsA.congr (k13.trans k4).wr) (by omega_arith) (by omega_arith) b14 (by rw [m4]; exact v8) hodd)
    fun s₅ ⟨⟨v8', o5⟩, k5⟩ => ?_
  have k15 := (k13.trans k4).trans k5
  have O5 : Mont.Outside (off BX oA) (slot w 8) (8 * w) s.mem s₅.mem :=
    fun x hx => (o5 x (by omega_arith)).trans ((by rw [m4] : s₄.mem x = s₃.mem x).trans (o3 x hx))
  have g5 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₅.gpr r = s.gpr r := fun r hr =>
    k15.gpr r (by revert r hr; decide)
  have u0 : val32 s₅.mem (off BX oA) (slot w 0) (2 * w) = Pv := by rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have u1 : val32 s₅.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv := by
    rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), hR2]
  have uw : w32 s₅.mem (off BX oA) (slot w 0) = w32 s.mem (off BX oA) (slot w 0) :=
    O5.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have hR2' : 2 ^ (128 * w) % Pv % Pv = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv := by
    rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega_arith
  -- `q := (p - 1) R² R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 5) (a := 1) (b := 8) (hsA.congr k15.wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g5 .r10 (by decide)).trans h10) ((g5 .r29 (by decide)).trans h29) ((g5 .r11 (by decide)).trans h11)
    (by rw [g5 .r12 (by decide)]; exact h12) (by rw [g5 .r12 (by decide), uw]; exact hinv)
    (by rw [v8', u0]; omega_arith)) fun s₆ ⟨⟨Q6, Q6e, o6⟩, k6⟩ => ?_)
  rw [u0, u1, v8'] at Q6e
  rw [u0] at Q6
  have hq0 := chunk_q0 hR (by omega_arith) Q6e hR2'
  have k16 := k15.trans k6
  have u6 : ∀ j, j = 0 ∨ j = 1 ∨ j = 8 →
      val32 s₆.mem (off BX oA) (slot w j) (2 * w) = val32 s₅.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have W6 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) s₅.mem s₆.mem :=
    outs_work o6 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have g6 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₆.gpr r = s.gpr r := fun r hr =>
    k16.gpr r (by revert r hr; decide)
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((g6 .r10 (by decide)).trans h10)
    ((g6 .r29 (by decide)).trans h29) 4) fun s₇ ⟨⟨c14, m7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hsA.congr (k16.trans k7).wr) c14 ((k7.gpr _ (by decide)).trans
    ((g6 .r11 (by decide)).trans h11)) (by omega_arith) hw' (by omega_arith)) fun s₈ ⟨⟨_, z8, o8⟩, k8⟩ => ?_)
  have k18 := (k16.trans k7).trans k8
  rw [m7] at o8
  have v4 : val32 s₈.mem (off BX oA) (slot w 4) (2 * w) = 0 := by
    rw [Pre.val32_eq_wv]; exact (wv_eq_zero_iff _ _ _ _).mpr z8
  have o8' : Mont.Outside (off BX oA) (slot w 4) (8 * w) s₆.mem s₈.mem := o8
  have Wall : Mont.Outside (off BX oA) (slot w 2) (7 * (8 * (w + 2))) s.mem s₈.mem :=
    ((O5.mono (by omega_arith) (by omega_arith)).trans (W6.mono (by omega_arith) (by omega_arith))).trans (o8'.mono (by omega_arith) (by omega_arith))
  have Oall : Outside BX oA (slot w 24) s.mem s₈.mem := out_sub (fun x hx => Wall x hx) (by omega_arith) (by omega_arith) (by omega_arith)
  have g8 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r27, .r28, .r29], s₈.gpr r = s.gpr r := fun r hr =>
    k18.gpr r (by revert r hr; decide)
  -- `r30` and `r31`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r30) (by decide) (by decide) ((g8 .r27 (by decide)).trans h27)
    ((g8 .r28 (by decide)).trans h28) 6) fun s₉ ⟨⟨a30, m9⟩, k9⟩ => ?_
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = BitVec.ofNat 64 K ∧ u.mem = s₉.mem) (by
      prun [(k9.gpr .r25 (by decide)).trans ((k18.gpr .r25 (by decide)).trans h25)]
      rw [← hKd]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith) (by decide)) fun s₁₀ ⟨⟨a31, m10⟩, k10⟩ => ?_
  have k110 := (k18.trans k9).trans k10
  have hm10 : s₁₀.mem = s₈.mem := by rw [m10, m9]
  have v5 : val32 s₈.mem (off BX oA) (slot w 5) (2 * w) = val32 s₆.mem (off BX oA) (slot w 5) (2 * w) :=
    o8'.val32 (Or.inr (by omega_arith)) (by omega_arith)
  have I0 : ChunkI s BX Z oA w wX K Pv (2 ^ (128 * w) % Pv) 0 s₁₀ := by
    refine ⟨hs.congr k110.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm10]; exact Oall,
      k110.mono (by decide +kernel)⟩
    · rw [k10.gpr .r10 (by decide), k9.gpr .r10 (by decide), g8 .r10 (by decide), h10]
    · rw [k10.gpr .r21 (by decide), k9.gpr .r21 (by decide), g8 .r21 (by decide), h21]
    · rw [k10.gpr .r29 (by decide), k9.gpr .r29 (by decide), g8 .r29 (by decide), h29]
    · rw [k10.gpr .r11 (by decide), k9.gpr .r11 (by decide), g8 .r11 (by decide), h11]
    · rw [k10.gpr .r12 (by decide), k9.gpr .r12 (by decide), g8 .r12 (by decide)]; exact h12
    · rw [k10.gpr .r12 (by decide), k9.gpr .r12 (by decide), g8 .r12 (by decide), hm10,
        Wall.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact hinv
    · rw [k10.gpr .r30 (by decide), a30, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
    · rw [a31, Nat.mul_zero]; exact (BitVec.sub_zero _).symm
    · rw [hm10, Wall.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
    · rw [hm10, Wall.val32 (Or.inl (by omega_arith)) (by omega_arith), hR2]
    · rw [hm10, o8'.val32 (Or.inr (by omega_arith)) (by omega_arith), W6.val32 (Or.inr (by omega_arith)) (by omega_arith), v8']
    · rw [hm10, v5]; exact Q6
    · rw [hm10, v5]; exact hq0
    · rw [hm10, v4]; omega_arith
    · rw [hm10, v4, Nat.mul_zero]; rfl
  refine WP.mono (count_loop (cr := .r3) (nChunks_pos (by omega_arith) hK1)
    (fun j u => ChunkI s BX Z oA w wX K Pv (2 ^ (128 * w) % Pv) j u)
    (fun j hj u I => chunkStep_ok hA hX hw2 hw' hK1 hK' hP2 hodd (Nat.mod_lt _ (by omega_arith)) hR2' hj I) I0)
    fun t I => ⟨⟨?_, I.p0, I.p1, I.r12, I.inv, I.out, I.r10⟩, I.keep⟩
  rw [← Nat.mod_eq_of_lt I.slt, I.sv, hC]

end VG.Proof.Bignum.PPC64LE.Crt
