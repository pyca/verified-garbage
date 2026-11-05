module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_ffdh_generate_key_cached` on PPC64LE: the scalar

`scalarC_ok`: x is `rand`'s `p_len` octets cut to the context's width, its
bits and bytes in the header: `GenerateKey`'s cut at the index
`p_len − bytes` with the mask of the first octet's bits. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Impl.Ffdh.PPC64LE.GenerateKey (ptrs cutSetup cutBody)
open VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (cut_ok cutRegs ptrs_ok)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.Bignum (slot)

/-- The mask of the first octet's bits, for `bits` bits. -/
def tbOf (bits : Nat) : Byte := BitVec.ofNat 8 (255 / 2 ^ (8 * ((bits + 7) / 8) - bits))

theorem tbOf_toNat (bits : Nat) : (tbOf bits).toNat = 2 ^ (8 - (8 * ((bits + 7) / 8) - bits)) - 1 := by
  have hd : 8 * ((bits + 7) / 8) - bits < 8 := by omega
  obtain ⟨d, hd'⟩ : ∃ d, d = 8 * ((bits + 7) / 8) - bits := ⟨_, rfl⟩
  rw [← hd'] at hd ⊢
  unfold tbOf; rw [← hd']
  have key : ∀ d < 8, (BitVec.ofNat 8 (255 / 2 ^ d)).toNat = 2 ^ (8 - d) - 1 := by decide
  exact key d hd

/-- The shift loop: `r14 := r14 >> c` for the count `c` in `r17`, from 1. -/
theorem shiftLoop14_ok {s : State} {v c : Nat} (hv : v < 2 ^ 64) (hc : 1 ≤ c) (hc' : c < 64)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 v) (h17 : s.gpr .r17 = BitVec.ofNat 64 c) :
    WP isa (.loop (.block [.lsr .d .r14 .r14 1, .subi .r17 .r17 1]) (.nonzero .d .r17)) s fun t =>
      (t.gpr .r14 = BitVec.ofNat 64 (v / 2 ^ c) ∧ t.mem = s.mem) ∧ Keep [.r14, .r17] s t := by
  refine WP.mono (wp_countdown (body := .block [.lsr .d .r14 .r14 1, .subi .r17 .r17 1]) (cnt := .r17) (N := c)
    (by omega) (by omega) (fun i t => (t.gpr .r14 = BitVec.ofNat 64 (v / 2 ^ i) ∧ t.mem = s.mem) ∧ Keep [.r14, .r17] s t)
    (fun i hi t ⟨⟨a14, am⟩, ak⟩ _ => ?_) ⟨⟨by rw [h14, Nat.pow_zero, Nat.div_one], rfl⟩, Keep.refl _ _⟩ h17)
    fun t h => h
  refine WP.mono (WP.keep [.r14, .r17] (Q := fun u => u.gpr .r14 = BitVec.ofNat 64 (v / 2 ^ (i + 1)) ∧
      u.mem = t.mem ∧ u.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) (by
    prun [a14, ofNat_shr1 _ (show v / 2 ^ i < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv),
      Nat.div_div_eq_div_mul, ← Nat.pow_succ]) (by decide))
    fun u ⟨⟨b14, bm, b17⟩, bk⟩ => ⟨⟨⟨b14, bm.trans am⟩, (ak.trans bk).mono (by decide)⟩, b17⟩

/-- `maskByte`: `r14 :=` the mask of the first octet's bits, from the header's
bits and bytes. -/
theorem maskByte_ok {s : State} {B : Addr} {Z bits : Nat} (hs : Scr s B Z) (hZ : 24 ≤ Z) (h23 : s.gpr .r23 = B)
    (hbw : s.mem.readW (off B hBits) 64 = BitVec.ofNat 64 bits)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8)) (hb : bits < 2 ^ 32) :
    WP isa maskByte s fun t => (t.gpr .r14 = (tbOf bits).setWidth 64 ∧ t.mem = s.mem) ∧ Keep [.r14, .r17, .r18] s t := by
  have l8 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 8) 8 := by rw [h23]; exact hs.ld (d := 8) (n := 8) (by omega)
  have l16 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 16) 8 := by
    rw [h23]; exact hs.ld (d := 16) (n := 8) (by omega)
  have v8 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 bits := by rw [h23]; exact hbw
  have v16 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [h23]; exact hyw
  obtain ⟨d, hd⟩ : ∃ d, d = 8 * ((bits + 7) / 8) - bits := ⟨_, rfl⟩
  have hd8 : d < 8 := by omega
  have htb : (tbOf bits).setWidth 64 = BitVec.ofNat 64 (255 / 2 ^ d) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    unfold tbOf; rw [← hd, BitVec.toNat_ofNat]
    have : 255 / 2 ^ d < 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  rw [htb]
  unfold maskByte
  refine WP.seq (WP.mono (WP.keep [.r14, .r17, .r18] (Q := fun t => t.gpr .r17 = BitVec.ofNat 64 d ∧
      t.gpr .r14 = BitVec.ofNat 64 255 ∧ t.mem = s.mem) (by
    unfold ldh
    prun [hBits, hBytes, l8, l16, v8, v16, ofNat_shl3 (show 8 * ((bits + 7) / 8) < 2 ^ 64 by omega),
      ofNat_sub' (show bits ≤ 8 * ((bits + 7) / 8) by omega) (show 8 * ((bits + 7) / 8) < 2 ^ 64 by omega)]
    rw [hd]) (by decide)) fun s₁ ⟨⟨a17, a14, m1⟩, k1⟩ => ?_)
  refine WP.ite (decide (d = 0)) (eval_zero_ofNat _ _ (by omega) a17) (fun hc => ?_) (fun hc => ?_)
  · have hc' : d = 0 := by simpa using hc
    refine WP.mono (WP.keep [] (Q := fun t => t = s₁) (by prun) (by decide)) fun t ⟨ht, _⟩ => ?_
    subst ht
    exact ⟨⟨by rw [a14, hc', Nat.pow_zero, Nat.div_one], m1⟩, k1⟩
  · have hc' : d ≠ 0 := by simpa using hc
    refine WP.mono (shiftLoop14_ok (by decide) (by omega) (by omega) a14 a17) fun t ⟨⟨t14, tm⟩, kt⟩ =>
      ⟨⟨t14, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩

/-- The registers `scalar` writes. -/
def scalarCRegs : List Reg := [.r0, .r4, .r6, .r14, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25]

/-- `scalar`: x's `k` octets at `X` are `rand`'s at `R` cut to the context's
width `bits` (the header's `hBits`, its bytes in `hBytes`). -/
theorem scalarC_ok {s : State} {B X R : Addr} {Z w k bits : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024) (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * k)
    (hbw : s.mem.readW (off B hBits) 64 = BitVec.ofNat 64 bits)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8))
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hR : s.mem.readW (off B 88) 64 = off R 0)
    (hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hx : Scr s X k) (hsepR : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) :
    WP isa scalar s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits) ∧
        Outside X 0 k s.mem t.mem) ∧ Keep scalarCRegs s t := by
  have hZ := h.hZ
  have hZ' : 256 ≤ Z := Nat.le_trans (by simp only [slot]; omega) hZ
  unfold scalar
  refine WP.seq (WP.mono (maskByte_ok h.hs (by omega) h23 hbw hyw (by omega)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  have g23 : s₁.gpr .r23 = B := (k1.gpr .r23 (by decide)).trans h23
  have hs1 := h.hs.congr k1.wr
  have l16 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r23 + BitVec.ofNat 64 16) 8 := by
    rw [g23]; exact hs1.ld (d := 16) (n := 8) (by omega)
  have v16 : s₁.mem.readW (s₁.gpr .r23 + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [g23, m1]; exact hyw
  have l88 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r23 + BitVec.ofNat 64 88) 8 := by
    rw [g23]; exact hs1.ld (d := 88) (n := 8) (by omega)
  have l64 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r23 + BitVec.ofNat 64 64) 8 := by
    rw [g23]; exact hs1.ld (d := 64) (n := 8) (by omega)
  have v88 : s₁.mem.readW (s₁.gpr .r23 + BitVec.ofNat 64 88) 64 = off R 0 := by rw [g23, m1]; exact hR
  have v64 : s₁.mem.readW (s₁.gpr .r23 + BitVec.ofNat 64 64) 64 = off X 0 := by rw [g23, m1]; exact hX
  have h28' : s₁.gpr .r28 = BitVec.ofNat 64 k := (k1.gpr .r28 (by decide)).trans h28
  refine WP.seq (WP.mono (WP.keep [.r4, .r6, .r22, .r24, .r25] (Q := fun t =>
      t.gpr .r22 = BitVec.ofNat 64 (k - (bits + 7) / 8) ∧ t.gpr .r24 = off R 0 ∧ t.gpr .r25 = off X 0 ∧
      t.gpr .r6 = BitVec.ofNat 64 k ∧ t.gpr .r4 = BitVec.ofNat 64 0 ∧ t.gpr .r14 = s₁.gpr .r14 ∧ t.mem = s₁.mem) (by
    unfold ldh ptrs cutSetup
    prun [hBytes, l16, v16, l88, l64, v88, v64, h28',
      ofNat_sub' (show (bits + 7) / 8 ≤ k by omega) (show k < 2 ^ 64 by omega), BitVec.add_zero]) (by decide))
    fun s₂ ⟨⟨a22, a24, a25, a6, a4, a14', m2⟩, k2⟩ => ?_)
  refine WP.mono (cut_ok (tb := tbOf bits) hk (by omega) (show k - (bits + 7) / 8 < k by omega) (hx.congr (k1.trans k2).wr)
    (fun i hi => by rw [(k1.trans k2).rd, (k1.trans k2).wr]; exact hrdR i hi) hsepR a24 a25 a4 a22
    (by rw [a14', a14]) a6) fun t ⟨⟨tb, tout, _⟩, kt⟩ => ?_
  rw [m2, m1] at tb tout
  exact ⟨⟨tb, tout⟩, ((k1.trans k2).trans kt).mono (by decide)⟩

/-- x's value: `rand`'s mod `2^bits`. -/
theorem scalarC_value {rb : List Byte} {k bits : Nat} (hl : rb.length = k) (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * k) :
    Spec.Rsa.os2ip (cut rb (k - (bits + 7) / 8) (tbOf bits)) = Spec.Rsa.os2ip rb % 2 ^ bits := by
  rw [VG.Proof.Ffdh.KeyScalar.cut_value (n := k - (bits + 7) / 8) (e := (bits + 7) / 8)
    (j := 8 - (8 * ((bits + 7) / 8) - bits)) (by omega) (by omega) (by omega) (tbOf_toNat bits)]
  congr 2
  omega

/-! ## x in range -/

/-- What the attempt's body changes in the working space: the header's
`hI`, `hD` and `hJ`, and the arrays. -/
abbrev attOut (w : Nat) : List (Nat × Nat) := [(32, 24), (slot w 0, 28 * (8 * (w + 2)))]

theorem comb_att {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (combOut w) m m') : Outs B (attOut w) m m' :=
  Outs.cover h fun r hr => by
    simp only [combOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [slot]; omega, by simp only [slot]; omega⟩

theorem body_att {B : Addr} {w : Nat} {m m' : Mem} (h : VG.Proof.Ffdh.PPC64LE.Domain.Body B w m m') :
    Outs B (attOut w) m m' := Outs.of_outside h (by simp [attOut])

theorem attOut_fit {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) : ∀ r ∈ attOut w, r.1 + r.2 ≤ Z := by
  have := h.hZ
  intro r hr
  simp only [attOut, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · show 32 + 24 ≤ Z; have := VG.Proof.Ffdh.PPC64LE.Domain.slot_eq w 28; omega
  · show slot w 0 + 28 * (8 * (w + 2)) ≤ Z; rw [← VG.Proof.Ffdh.PPC64LE.Domain.slot28]; exact this

theorem hdr_of_att {B : Addr} {w x : Nat} {m m' : Mem} (ho : Outs B (attOut w) m m') (hx : x + 8 ≤ 32 ∨ 56 ≤ x)
    (hx' : x + 8 ≤ 256) : m'.readW (off B x) 64 = m.readW (off B x) 64 :=
  ho.word (d := x) (fun r hr => by
    simp only [attOut, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [slot, hdrBytes] <;> omega) (by omega)

/-- The registers `good` writes. -/
def goodRegs : List Reg := combRegs ++ VG.Proof.Ffdh.PPC64LE.Domain.exOutRegs ++ [.r0, .r3]

/-- `good`: the comb's `g^x mod p` or zeros at `O` (the header's word 10),
and the status 1 or 3. -/
theorem goodC_ok {s : State} {B C X O : Addr} {Z w k : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) (ho : Scr s O k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hO : s.mem.readW (off B 80) 64 = off O 0) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs B x) (hpk : P < 256 ^ k)
    (hk28 : xb.length = k) :
    WP isa good s fun t =>
      (Spec.Rsa.bytesAt t.mem O k =
          (if 1 < Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
              Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P < P - 1 then
            Spec.Rsa.i2osp (Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P) k
          else List.replicate k 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if 1 < Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
            Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P < P - 1 then 1 else 3) ∧
        ∃ m, Outs B (attOut w) s.mem m ∧ Outside O 0 k m t.mem) ∧ Keep goodRegs s t := by
  have hZ := h.env.hZ
  have hw := h.env.hw; have hw' := h.env.hw'
  have hP : 0 < P := by have := h.row.one; omega
  unfold good
  refine WP.seq (WP.mono (comb_ok h) fun s₁ ⟨⟨z1, p1, o1, r10⟩, k1⟩ => ?_)
  generalize hz : Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P = z at z1 ⊢
  have hzP : z < P := by rw [← hz, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP
  refine WP.seq (WP.mono (VG.Proof.Ffdh.PPC64LE.Domain.exOut_ok (O := O) (k := k) (h.env.hs.congr k1.wr)
    (ho.congr k1.wr) r10 ((k1.gpr .r29 (by decide)).trans h.env.h29) ((k1.gpr .r11 (by decide)).trans h.env.h11)
    ((k1.gpr .r23 (by decide)).trans h.h23) (by rw [k1.gpr .r28 (by decide), h.h28, hk28]) hw hw' hZ hk hkw
    (by rw [hdr_of_comb o1 (by decide) (by decide)]; exact hO) hsepO
    (by rw [p1]; omega) (by rw [z1, p1]; exact hzP) (by rw [p1]; exact hpk))
    fun s₂ ⟨⟨ob, o2, m, bm, om⟩, k2⟩ => ?_)
  rw [z1, p1] at ob o2
  refine WP.mono (VG.Proof.Ffdh.PPC64LE.Derive.status_ok s₂ (1 < z ∧ z < P - 1) o2) fun t ⟨⟨t3, tm⟩, kt⟩ =>
    ⟨⟨by rw [tm, ob], t3, m, (comb_att o1).trans (body_att bm), by rw [tm]; exact om⟩,
      ((k1.trans k2).trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.Cached
