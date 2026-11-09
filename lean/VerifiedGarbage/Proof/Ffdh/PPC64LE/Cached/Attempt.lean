module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

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

/-- `maskByte`'s first block: `r17 :=` the shift, `8 bytes − bits`. -/
abbrev mbBlock : List Instr := [ldh .r17 hBytes, .lsl .r17 .r17 3, ldh .r18 hBits, .sub .r17 .r17 .r18, .li .r14 255]

/-- `maskByte`'s shift. -/
abbrev mbIte : Prog isa :=
  .ite (.zero .d .r17) (.block []) (.loop (.block [.lsr .d .r14 .r14 1, .subi .r17 .r17 1]) (.nonzero .d .r17))

theorem maskByte_eq : maskByte = .seq (.block mbBlock) mbIte := rfl

/-- `mbBlock`: the shift, from the header's bits and bytes. -/
theorem mb_ok {s : State} {B : Addr} {Z bits : Nat} (hs : Scr s B Z) (hZ : 24 ≤ Z) (h23 : s.gpr .r23 = B)
    (hbw : s.mem.readW (off B hBits) 64 = BitVec.ofNat 64 bits)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8)) (hb : bits < 2 ^ 32) :
    WP isa (.block mbBlock) s fun t => (t.gpr .r17 = BitVec.ofNat 64 (8 * ((bits + 7) / 8) - bits) ∧
      t.gpr .r14 = BitVec.ofNat 64 255 ∧ t.mem = s.mem) ∧ Keep [.r14, .r17, .r18] s t := by
  have l8 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 8) 8 := by rw [h23]; exact hs.ld (d := 8) (n := 8) (by omega)
  have l16 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 16) 8 := by
    rw [h23]; exact hs.ld (d := 16) (n := 8) (by omega)
  have v8 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 bits := by rw [h23]; exact hbw
  have v16 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [h23]; exact hyw
  refine WP.keep [.r14, .r17, .r18] ?_ (by decide)
  unfold mbBlock ldh
  prun [hBits, hBytes, l8, l16, v8, v16, ofNat_shl3 (show 8 * ((bits + 7) / 8) < 2 ^ 64 by omega),
    ofNat_sub' (show bits ≤ 8 * ((bits + 7) / 8) by omega) (show 8 * ((bits + 7) / 8) < 2 ^ 64 by omega)]

/-- `maskByte`: `r14 :=` the mask of the first octet's bits, from the header's
bits and bytes. -/
theorem maskByte_ok {s : State} {B : Addr} {Z bits : Nat} (hs : Scr s B Z) (hZ : 24 ≤ Z) (h23 : s.gpr .r23 = B)
    (hbw : s.mem.readW (off B hBits) 64 = BitVec.ofNat 64 bits)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8)) (hb : bits < 2 ^ 32) :
    WP isa maskByte s fun t => (t.gpr .r14 = (tbOf bits).setWidth 64 ∧ t.mem = s.mem) ∧ Keep [.r14, .r17, .r18] s t := by
  obtain ⟨d, hd⟩ : ∃ d, d = 8 * ((bits + 7) / 8) - bits := ⟨_, rfl⟩
  have hd8 : d < 8 := by omega
  have htb : (tbOf bits).setWidth 64 = BitVec.ofNat 64 (255 / 2 ^ d) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    unfold tbOf; rw [← hd, BitVec.toNat_ofNat]
    have : 255 / 2 ^ d < 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  rw [htb, maskByte_eq]
  refine WP.seq (WP.mono (mb_ok hs hZ h23 hbw hyw hb) fun s₁ ⟨⟨a17, a14, m1⟩, k1⟩ => ?_)
  rw [← hd] at a17
  refine WP.ite (decide (d = 0)) (eval_zero_ofNat _ _ (by omega) a17) (fun hc => ?_) (fun hc => ?_)
  · have hc' : d = 0 := by simpa using hc
    refine WP.mono (WP.keep [] (Q := fun t => t = s₁) (by prun) (by decide)) fun t ⟨ht, _⟩ => ?_
    subst ht
    exact ⟨⟨by rw [a14, hc', Nat.pow_zero, Nat.div_one], m1⟩, k1⟩
  · have hc' : d ≠ 0 := by simpa using hc
    refine WP.mono (shiftLoop14_ok (by decide) (by omega) (by omega) a14 a17) fun t ⟨⟨t14, tm⟩, kt⟩ =>
      ⟨⟨t14, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩

/-- `scalar`'s block: the cut's index, `rand`'s and x's addresses, the count and the index 0. -/
abbrev sbBlock : List Instr := [ldh .r22 hBytes, .sub .r22 .r28 .r22] ++ ptrs ++ cutSetup

theorem scalar_eq : scalar = .seq maskByte (.seq (.block sbBlock)
    (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r6 cutBody)) := rfl

/-- `sbBlock`, from the header's bytes and words 8 and 11. -/
theorem sb_ok {s : State} {B X R : Addr} {Z k bits : Nat} (hs : Scr s B Z) (hZ : 96 ≤ Z) (h23 : s.gpr .r23 = B)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : (bits + 7) / 8 ≤ k) (hk' : k < 2 ^ 64)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8))
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hR : s.mem.readW (off B 88) 64 = off R 0) :
    WP isa (.block sbBlock) s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (k - (bits + 7) / 8) ∧ t.gpr .r24 = off R 0 ∧ t.gpr .r25 = off X 0 ∧
        t.gpr .r6 = BitVec.ofNat 64 k ∧ t.gpr .r4 = BitVec.ofNat 64 0 ∧ t.gpr .r14 = s.gpr .r14 ∧ t.mem = s.mem) ∧
      Keep [.r4, .r6, .r22, .r24, .r25] s t := by
  have l16 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 16) 8 := by
    rw [h23]; exact hs.ld (d := 16) (n := 8) (by omega)
  have v16 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [h23]; exact hyw
  have l88 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 88) 8 := by
    rw [h23]; exact hs.ld (d := 88) (n := 8) (by omega)
  have l64 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 64) 8 := by
    rw [h23]; exact hs.ld (d := 64) (n := 8) (by omega)
  have v88 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 88) 64 = off R 0 := by rw [h23]; exact hR
  have v64 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 64) 64 = off X 0 := by rw [h23]; exact hX
  refine WP.keep [.r4, .r6, .r22, .r24, .r25] ?_ (by decide)
  unfold sbBlock ldh ptrs cutSetup
  prun [hBytes, l16, v16, l88, l64, v88, v64, h28, ofNat_sub' hk hk', BitVec.add_zero]

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
  have h28' : s₁.gpr .r28 = BitVec.ofNat 64 k := (k1.gpr .r28 (by decide)).trans h28
  refine WP.seq (WP.mono (sb_ok (bits := bits) (X := X) (R := R) (h.hs.congr k1.wr) (Nat.le_trans (by decide) hZ') g23 h28' (by omega) (by omega)
      (by rw [m1]; exact hyw) (by rw [m1]; exact hX) (by rw [m1]; exact hR))
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
    subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [slot]; omega, by simp only [slot]; omega⟩

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
    (by rw [hdr_of_comb o1 (by decide)]; exact hO) hsepO
    (by rw [p1]; omega) (by rw [z1, p1]; exact hzP) (by rw [p1]; exact hpk))
    fun s₂ ⟨⟨ob, o2, m, bm, om⟩, k2⟩ => ?_)
  rw [z1, p1] at ob o2
  refine WP.mono (VG.Proof.Ffdh.PPC64LE.Derive.status_ok s₂ (1 < z ∧ z < P - 1) o2) fun t ⟨⟨t3, tm⟩, kt⟩ =>
    ⟨⟨by rw [tm, ob], t3, m, (comb_att o1).trans (body_att bm), by rw [tm]; exact om⟩,
      ((k1.trans k2).trans kt).mono (by decide)⟩

/-! ## The body -/

/-- A change at x's `k` octets keeps the context, apart from them. -/
theorem ctx_of_x {C X : Addr} {n k : Nat} {m m' : Mem} (h : Outside X 0 k m m')
    (hsep : ∀ y, ofs C y < n → k ≤ ofs X y) : Outside C n (2 ^ 64) m m' := fun y hy => h y (Or.inr (by
  rcases hy with hy | hy
  · have := hsep y hy; omega
  · have := (y - C).isLt; simp only [ofs] at hy; omega))

/-- The registers the body writes. -/
def bodyRegs : List Reg :=
  scalarCRegs ++ VG.Proof.Ffdh.PPC64LE.Derive.xRangeRegs ++ goodRegs ++
    ([.r0, .r3, .r6, .r12, .r15, .r16, .r17, .r25, .r27] : List Reg)

/-- The cached body: x cut from `rand` to the context's width, then
`g^x mod p` by the context's comb or zeros at `O` and the status; zeros at x
but for the status 1. -/
theorem bodyC_ok {s : State} {B D X O R C : Addr} {Z w k L p bits : Nat} (h : Env s B Z w)
    (h23 : s.gpr .r23 = B) (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L = 2 * k ∨ L = 3 * k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 k)
    (hO : s.mem.readW (off B 80) 64 = off O 0) (hR : s.mem.readW (off B 88) 64 = off R 0)
    (hbw : s.mem.readW (off B hBits) 64 = BitVec.ofNat 64 bits)
    (hyw : s.mem.readW (off B hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8))
    (hRw : s.mem.readW (off B hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits))
    (hCw : s.mem.readW (off B hCtx) 64 = C) (hc : CtxRd s B Z C w) (hsepCX : ∀ y, ofs C y < 8 * ctxWords w → k ≤ ofs X y)
    (hents : ∀ a < 32, ent s.mem C w a =
      combM (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p w (Spec.Rsa.FixedBaseComb.exponent bits a))
    (hr2 : val32 s.mem C (rowOff w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % p)
    (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * k)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hx : Scr s X k) (hsepX : ∀ i < k, ∀ y, ofs B y < Z → off X i ≠ y) (hsepBX : ∀ y, ofs B y < Z → k ≤ ofs X y)
    (hsepRX : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) (hsepDX : ∀ i < L, ∀ y, ofs X y < k → off D i ≠ y)
    (hsepXO : ∀ i < k, ∀ y, ofs O y < k → off X i ≠ y) (hsepOX : ∀ i < k, ∀ y, ofs X y < k → off O i ≠ y)
    (ho : Scr s O k) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs B x) (hsepB : ∀ x, ofs B x < Z → k ≤ ofs O x)
    (hP : VG.Proof.MillerRabin.PPC64LE.arr s.mem B w 0 = p) (hp2 : 2 ≤ p) (hodd : p % 2 = 1) (hpk : p < 256 ^ k) :
    WP isa body s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
          (Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits)))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p)) ∧
        Spec.Rsa.bytesAt t.mem O k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
            (Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits)))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
          Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^
            Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits)) % p) k
          else List.replicate k 0) ∧
        Spec.Rsa.bytesAt t.mem X k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
            (Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits)))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
          cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits) else List.replicate k 0) ∧
        ∀ d, (d + 8 ≤ 32 ∨ 56 ≤ d) → d + 8 ≤ 256 → word t.mem B d = word s.mem B d) ∧ Keep bodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hw := h.hw; have hw' := h.hw'
  have hnw := hs.nowrap
  have e0 := VG.Proof.Ffdh.PPC64LE.Domain.slot_eq w 0; have e28 := VG.Proof.Ffdh.PPC64LE.Domain.slot_eq w 28
  unfold body
  -- x.
  refine WP.seq (WP.mono (scalarC_ok h h23 h28 (by omega) hk' hb1 hbk hbw hyw hX hR hrdR hx hsepRX)
    fun s₃ ⟨⟨xb, xout⟩, k3⟩ => ?_)
  generalize hxo : cut (Spec.Rsa.bytesAt s.mem R k) (k - (bits + 7) / 8) (tbOf bits) = xo at xb ⊢
  have hxv : Spec.Rsa.os2ip xo < 2 ^ bits := by
    rw [← hxo, scalarC_value (by simp [Spec.Rsa.bytesAt]) hb1 hbk]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have osc := GenerateKey.out_scr xout hsepBX
  have hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem B d = word s.mem B d := fun d hd =>
    Outside.word osc (Or.inl (by omega)) (by omega)
  have hp3 : VG.Proof.MillerRabin.PPC64LE.arr s₃.mem B w 0 = p := by
    rw [VG.Proof.MillerRabin.PPC64LE.arr, Outside.val32 osc (Or.inl (by omega)) (by omega)]; exact hP
  have hbD : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs X y < k → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
    VG.Proof.Ffdh.PPC64LE.Domain.outside_bytesAt xout (by omega) hq
  have sepG : ∀ i < k, ∀ y, ofs X y < k → off (off D k) i ≠ y := fun i hi => by
    rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hsepDX _ (by omega)
  have eb : Derive.bnd s₃.mem D k L p = Derive.bnd s.mem D k L p := by
    unfold Derive.bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, hbD _ _ fun i hi => by
        rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hsepDX _ (by omega)]
    · rw [ite_eq_right hq, ite_eq_right hq]
  have eg : Spec.Rsa.bytesAt s₃.mem (off D k) k = Spec.Rsa.bytesAt s.mem (off D k) k := hbD _ _ sepG
  have cx3 := ctx_of_x (n := 8 * ctxWords w) xout hsepCX
  have e3 := h.keep k3 (by decide)
  have g23 : s₃.gpr .r23 = B := (k3.gpr .r23 (by decide)).trans h23
  have g21 : s₃.gpr .r21 = D := (k3.gpr .r21 (by decide)).trans h21
  have g27 : s₃.gpr .r27 = BitVec.ofNat 64 L := (k3.gpr .r27 (by decide)).trans h27
  have g28 : s₃.gpr .r28 = BitVec.ofNat 64 k := (k3.gpr .r28 (by decide)).trans h28
  have rdQ : L = 3 * k → ∀ i < k, InRegions (s₃.rd ++ s₃.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off', k3.rd, k3.wr]; exact hrdD _ (by omega)
  have sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hsepD _ (by omega)
  -- x's range.
  refine WP.seq (WP.seq (WP.mono (Derive.xRange_ok (xl := k) e3 g23 g21 g27 g28 (by omega) (by omega) (by omega)
    (by omega) (by omega) (Nat.le_refl _)
    (by show word s₃.mem B 64 = _; rw [hw3 64 (by omega)]; exact hX)
    (by show word s₃.mem B 72 = _; rw [hw3 72 (by omega)]; exact hXL)
    (fun i hi => (hx.congr k3.wr).ld (d := i) (n := 1) (by omega)) hsepX rdQ sepQ (by omega))
    fun s₄ ⟨⟨a26, p4, b4, a10⟩, k4⟩ => ?_))
  rw [xb, hp3, eb] at a26
  rw [hp3] at p4
  have k34 := k3.trans k4
  have e4 : Env s₄ B Z w := ⟨hs.congr k34.wr, a10, (k34.gpr .r29 (by decide)).trans h.h29,
    (k34.gpr .r11 (by decide)).trans h.h11, (k34.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have hw4 : ∀ d, d + 8 ≤ 256 → word s₄.mem B d = word s.mem B d := fun d hd => by
    rw [Outside.word b4 (by omega) (by omega), hw3 d hd]
  have xb4 : Spec.Rsa.bytesAt s₄.mem X k = xo := by
    rw [VG.Proof.Ffdh.PPC64LE.Domain.Body.bytesAt b4 hZ hsepX, xb]
  have g23₄ : s₄.gpr .r23 = B := (k4.gpr .r23 (by decide)).trans g23
  have g28₄ : s₄.gpr .r28 = BitVec.ofNat 64 k := (k4.gpr .r28 (by decide)).trans g28
  -- The end: x masked by the status.
  have fin : ∀ u : State, ∀ st : Nat, Keep bodyRegs s u →
      u.gpr .r3 = BitVec.ofNat 64 st → 1 ≤ st → st < 4 →
      st = VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt (Spec.Rsa.os2ip xo)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) →
      Spec.Rsa.bytesAt u.mem O k = (if st = 1 then Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^
          Spec.Rsa.os2ip xo % p) k else List.replicate k 0) →
      Spec.Rsa.bytesAt u.mem X k = xo →
      (∀ d, (d + 8 ≤ 32 ∨ 56 ≤ d) → d + 8 ≤ 256 → word u.mem B d = word s.mem B d) →
      WP isa VG.Impl.Ffdh.PPC64LE.GenerateKey.maskX u fun t =>
        (t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt (Spec.Rsa.os2ip xo)
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p)) ∧
          Spec.Rsa.bytesAt t.mem O k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt (Spec.Rsa.os2ip xo)
              (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
            Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^ Spec.Rsa.os2ip xo % p) k
            else List.replicate k 0) ∧
          Spec.Rsa.bytesAt t.mem X k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt (Spec.Rsa.os2ip xo)
              (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
            xo else List.replicate k 0) ∧
          ∀ d, (d + 8 ≤ 32 ∨ 56 ≤ d) → d + 8 ≤ 256 → word t.mem B d = word s.mem B d) ∧ Keep bodyRegs s t := by
    intro u st ku u3 hs1 hs4 hst uO uX uw
    have hX4 : u.mem.readW (off B 64) 64 = off X 0 := by
      show word u.mem B 64 = _; rw [uw 64 (by omega) (by omega)]; exact hX
    refine WP.mono (GenerateKey.maskX_ok (hs.congr ku.wr) (by omega) ((ku.gpr .r23 (by decide)).trans h23)
      ((ku.gpr .r28 (by decide)).trans h28) hX4 (by omega) (by omega) (hx.congr ku.wr) u3 hs1 hs4)
      fun t ⟨⟨tz, tout⟩, kt⟩ => ⟨⟨?_, ?_, ?_, fun d hd hd' => ?_⟩, (ku.trans kt).mono (by decide)⟩
    · rw [kt.gpr .r3 (by decide), u3, hst]
    · rw [VG.Proof.Ffdh.PPC64LE.Domain.outside_bytesAt tout (by omega) hsepOX, uO, hst]
    · rw [tz, uX, hst]
    · refine (Outside.word_sep (d := d) tout hsepBX (by omega) (by omega) hnw).trans ?_
      exact uw d hd hd'
  have hBn : B.toNat + Z ≤ 2 ^ 64 := hnw
  refine WP.ite (s₄.gpr .r26 == 0) (eval_zero _ _) (fun hv => ?_) (fun hv => ?_)
  · -- Out of range.
    rw [a26, VG.Proof.Ffdh.PPC64LE.Domain.mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    unfold VG.Impl.Ffdh.PPC64LE.Derive.dpBad
    refine WP.seq (WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off O 0 ∧ t.mem = s₄.mem) (by
        prun [g23₄, (hs.congr k34.wr).ld (d := 80) (n := 8) (by omega),
          show s₄.mem.readW (off B 80) 64 = off O 0 from (hw4 80 (by omega)).trans hO])
      (by decide)) fun s₅ ⟨⟨a27, m5⟩, k5⟩ => ?_)
    have k45 := k34.trans k5
    refine WP.seq (WP.mono (Pub.output_ok (b := false) (hs.congr k45.wr) (ho.congr k45.wr)
      ((k5.gpr .r10 (by decide)).trans a10) ((k45.gpr .r29 (by decide)).trans h.h29)
      ((k5.gpr .r28 (by decide)).trans g28₄) a27 (by rw [k5.gpr .r26 (by decide), a26, decide_eq_false hv])
      (by omega) (by omega) (Nat.le_trans (by simp only [slot]; omega) hZ) hsepO) fun s₆ ⟨⟨ob, ot, _⟩, k6⟩ => ?_)
    refine WP.mono (VG.Proof.Ffdh.PPC64LE.Domain.li_ok s₆ 2 (by decide)) fun u ⟨⟨u3, um⟩, ku⟩ =>
      fin u 2 (((k45.trans k6).trans ku).mono (by decide)) u3 (by decide) (by decide) ?_ ?_ ?_ ?_
    · unfold VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt; rw [ite_eq_left hv]
    · rw [um, ite_eq_right (by decide)]
      exact Pub.zero_bytes fun i hi => by rw [ob i hi]; rfl
    · rw [um, VG.Proof.Ffdh.PPC64LE.Domain.outside_bytesAt ot (by omega) hsepXO, m5, xb4]
    · intro d hd hd'
      rw [um]
      refine (Pub.Outside.word_apart (d := d) ot hsepB (by omega) (by omega) hnw).trans ?_
      show Mont.word s₅.mem B _ = _
      rw [m5, hw4 _ hd']
  · -- In range.
    rw [a26, VG.Proof.Ffdh.PPC64LE.Domain.mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hv
    have cx4 : Outside C (8 * ctxWords w) (2 ^ 64) s.mem s₄.mem :=
      cx3.trans (outs_ctx (body_att b4) (attOut_fit e3) hc.sep)
    have hl4 : (Spec.Rsa.bytesAt s₄.mem X k).length = k := VG.Proof.Bignum.bytesAt_length _ _ _
    have ci : CombIn s₄ B C X Z w (Spec.Rsa.bytesAt s₄.mem X k) p
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) bits := by
      refine ⟨e4, g23₄, by rw [g28₄, hl4], by rw [show hCtx = 0 from rfl]; exact (hw4 0 (by omega)).trans hCw,
        hc.congr k34.rd k34.wr, fun a ha => ?_, ?_, p4, by rw [show hRows = 24 from rfl]; exact (hw4 24 (by omega)).trans hRw,
        by rw [show s₄.mem.readW (off B 64) 64 = word s₄.mem B 64 from rfl, hw4 64 (by omega)]
           exact hX.trans (BitVec.add_zero _),
        fun n hn => (hx.congr k34.wr).ld (d := n) (n := 1) (by omega), fun n hn => hsepX n (by omega),
        fun n hn => by simp [Spec.Rsa.bytesAt, off],
        ⟨hodd, by omega, (Rsa.FixedBaseComb.rows_small (show bits ≤ 8192 by omega)).1, by rw [hl4]; omega⟩, by omega⟩
      · rw [← hents a ha]
        exact Outside.val32 cx4 (Or.inl (by have := row_fits (w := w) ha; omega))
          (by have := row_fits (w := w) ha; have := hc.hn; omega)
      · rw [← hr2]
        exact Outside.val32 cx4 (Or.inl (by have := row1_fits w; omega)) (by have := row1_fits w; have := hc.hn; omega)
    refine WP.mono (goodC_ok ci (ho.congr k34.wr) (by omega) (by omega)
      (by rw [show s₄.mem.readW (off B 80) 64 = word s₄.mem B 80 from rfl, hw4 80 (by omega)]; exact hO) hsepO hpk hl4)
      fun u ⟨⟨uO, u3, m, mo, om⟩, ku⟩ => ?_
    rw [xb4, Rsa.FixedBaseComb.high_zero bits _ hxv, VG.Proof.Bignum.powMod_eq] at uO u3
    refine fin u _ ((k34.trans ku).mono (by decide)) u3 (by split <;> decide) (by split <;> decide) ?_ ?_ ?_ ?_
    · unfold VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
      have hn : ¬¬(0 < Spec.Rsa.os2ip xo ∧ Spec.Rsa.os2ip xo < Derive.bnd s.mem D k L p) := fun h' => h' hv
      simp only [hn, ↓reduceIte]
    · rw [uO]
      by_cases hc' : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^ Spec.Rsa.os2ip xo % p ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^ Spec.Rsa.os2ip xo % p < p - 1
      · rw [ite_eq_left hc', ite_eq_left hc', ite_eq_left rfl]
      · rw [ite_eq_right hc', ite_eq_right hc', ite_eq_right (by decide)]
    · rw [VG.Proof.Ffdh.PPC64LE.Domain.outside_bytesAt om (by omega) hsepXO, ← xb4]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi => byte_of_outs mo (attOut_fit e4)
        (hsepX i (by simpa using hi))
    · intro d hd hd'
      refine (Pub.Outside.word_apart (d := d) om hsepB (by omega) (by omega) hnw).trans ?_
      show Mont.word m B _ = _
      rw [show Mont.word m B d = m.readW (off B d) 64 from rfl, hdr_of_att mo hd hd']
      exact hw4 d hd'

end VG.Proof.Ffdh.PPC64LE.Cached
