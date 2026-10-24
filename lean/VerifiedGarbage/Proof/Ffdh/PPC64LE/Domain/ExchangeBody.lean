module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# FFDH's exchange on PPC64LE: the power and the output

In the working space of `Body.lean`, p in array 0: `zMask_ok`, the mask of
`z ∉ {0, 1, p − 1}` for z in array 4; `exPower_ok`, `z = y^x mod p` into
array 4; `exOut_ok`, z's octets to `out` masked by `1 < z < p − 1`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- The registers `zMask` writes. -/
def zRegs : List Reg := constsRegs ++ ([.r4, .r19, .r26] : List Reg)

/-- `zMask`: `r26 :=` the mask of `z ∉ {0, 1, p − 1}` for z in array 4. -/
theorem zMask_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (hp : 1 ≤ arr s.mem B w 0) :
    WP isa zMask s fun t =>
      (t.gpr .r26 = mask (decide (arr s.mem B w 4 ≠ 0 ∧ arr s.mem B w 4 ≠ 1 ∧
          arr s.mem B w 4 ≠ arr s.mem B w 0 - 1)) ∧
        arr t.mem B w 4 = arr s.mem B w 4 ∧ arr t.mem B w 0 = arr s.mem B w 0 ∧
        Outside B (slot w 5) (3 * (8 * (w + 2))) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep zRegs s t := by
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e4 := slot_eq w 4; have e5 := slot_eq w 5
  have e28 := slot_eq w 28
  generalize hy : arr s.mem B w 4 = y
  generalize hP : arr s.mem B w 0 = p at hp
  unfold zMask
  refine WP.seq (WP.mono (consts_ok h h23 (by rw [hP]; exact hp)) fun s₁ ⟨⟨v7, v6, v5, o1, a10⟩, k1⟩ => ?_)
  rw [hP] at v6
  have e1 : Env s₁ B Z w := ⟨h.hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have y1 : val32 s₁.mem B (slot w 4) (2 * w) = y := by rw [Outside.val32 o1 (by omega) (by omega)]; exact hy
  have p1 : val32 s₁.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o1 (by omega) (by omega)]; exact hP
  refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = mask true ∧ t.mem = s₁.mem)
    (by prun; rfl) (by decide)) fun s₂ ⟨⟨a26, m2⟩, k2⟩ => ?_)
  have e2 := e1.keep k2 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e2 .r19 (a := 4) (b := 5) (by decide) (by decide))
    fun s₃ ⟨⟨a19, m3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₃ ((k3.gpr .r26 (by decide)).trans a26) a19) fun s₄ ⟨⟨b26, m4⟩, k4⟩ => ?_)
  have e4' := (e2.keep k3 (by decide)).keep k4 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e4' .r19 (a := 4) (b := 7) (by decide) (by decide))
    fun s₅ ⟨⟨c19, m5⟩, k5⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₅ ((k5.gpr .r26 (by decide)).trans b26) c19) fun s₆ ⟨⟨c26, m6⟩, k6⟩ => ?_)
  have e6 := (e4'.keep k5 (by decide)).keep k6 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e6 .r19 (a := 4) (b := 6) (by decide) (by decide)) fun s₇ ⟨⟨d19, m7⟩, k7⟩ => ?_)
  refine WP.mono (clear19_ok s₇ ((k7.gpr .r26 (by decide)).trans c26) d19) fun t ⟨⟨d26, mt⟩, kt⟩ => ?_
  have hm6 : s₆.mem = s₁.mem := by rw [m6, m5, m4, m3, m2]
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  have hmt : t.mem = s₁.mem := by rw [mt, m7, hm6]
  have r5 : val32 s₁.mem B (slot w 5) (2 * w) = 0 := v5
  have r6 : val32 s₁.mem B (slot w 6) (2 * w) = p - 1 := v6
  have r7 : val32 s₁.mem B (slot w 7) (2 * w) = 1 := v7
  simp only [hm6, hm4, m2, y1, r5, r6, r7] at d26
  refine ⟨⟨?_, by rw [arr, hmt]; exact y1, by rw [arr, hmt]; exact p1, by rw [hmt]; exact o1, ?_⟩,
    ((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7 |>.trans kt).mono (by decide)⟩
  · rw [d26]
    congr 1
    simp only [Bool.true_and, Bool.and_assoc, Bool.decide_and, decide_not]
  · exact ((((((k2.trans k3).trans k4).trans k5).trans k6).trans k7).trans kt).gpr .r10 (by decide) |>.trans a10

/-- The registers `exPower` writes. -/
def exPowRegs : List Reg := ModExp.powSRegs ++ ([.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16,
  .r17, .r20, .r30, .r31] : List Reg)

/-- What `exPower` leaves from `s`: `y^x mod p` in array 4, p in array 0. -/
def exPowPost (B Y X : Addr) (w k xl : Nat) (s t : State) : Prop :=
  arr t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) %
      arr s.mem B w 0 ∧ arr t.mem B w 0 = arr s.mem B w 0 ∧ Body B w s.mem t.mem ∧
    t.gpr .r10 = off B (slot w 0)

/-- `exPre`, with the registers it leaves for the power, and then the power:
y's `k` octets (at `r9`) into array 4, then `y^x mod p` there, for x's `xl`
octets at `X`, whose address and length are in the header's words 8 and 9. -/
theorem exPower_split {s : State} {B Y X : Addr} {Z w k xl : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h9 : s.gpr .r9 = Y) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hxl : 1 ≤ xl) (hxl' : xl ≤ 1024)
    (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Y i) 1) (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Y i ≠ x)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1) :
    WP isa exPre s fun s₆ =>
      (s₆.gpr .r30 = off X 0 ∧ s₆.gpr .r31 = BitVec.ofNat 64 xl ∧ s₆.gpr .r10 = off B (slot w 0) ∧
        s₆.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ s₆.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ s₆.gpr .r23 = B ∧
        s₆.gpr .r28 = BitVec.ofNat 64 k) ∧
      WP isa ModExp.powSecret s₆ fun t => exPowPost B Y X w k xl s t ∧ Keep exPowRegs s t := by
  unfold exPowPost
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e1 := slot_eq w 1; have e4 := slot_eq w 4; have e8 := slot_eq w 8
  have e28 := slot_eq w 28
  generalize hP : arr s.mem B w 0 = p at hp2 hodd
  unfold exPre
  refine WP.seq (WP.mono (Pub.loadX_ok hs h23 h9 h28 h.h10 h.h29 h.h11 hk hkw (by omega) (by omega) hrdY hsepY)
    fun s₀ ⟨⟨y0, _, o0, a10⟩, k0⟩ => ?_)
  have e0' : Env s₀ B Z w := ⟨hs.congr k0.wr, a10, (k0.gpr .r29 (by decide)).trans h.h29,
    (k0.gpr .r11 (by decide)).trans h.h11, (k0.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  have p0 : val32 s₀.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o0 (by omega) (by omega)]; exact hP
  have b0 : Body B w s.mem s₀.mem := Body.of o0 (by omega) (by omega)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e0'.base (rd := .r5) (by decide) (by decide) 1) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  have e1' := e0'.keep k1 (by decide)
  refine WP.mono (e1'.base (rd := .r8) (by decide) (by decide) 2) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2' := e1'.keep k2 (by decide)
  refine WP.mono (e2'.base (rd := .r9) (by decide) (by decide) 3) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3' := e2'.keep k3 (by decide)
  have hm3 : s₃.mem = s₀.mem := by rw [m3, m2, m1]
  have p3 : val32 s₃.mem B (slot w 0) (2 * w) = p := by rw [hm3]; exact p0
  refine WP.seq (WP.mono (r2_ok e3'.hs ((k3.gpr .r8 (by decide)).trans a8) a9 e3'.h10
    ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5)) e3'.h11 (by omega) (by omega)
    (by omega) (by rw [p3]; exact hp2)) fun s₄ ⟨hr2, o4, k4⟩ => ?_)
  rw [p3] at hr2
  have e4' := e3'.keep k4 (by decide)
  have p4 : val32 s₄.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o4 (by omega) (by omega)]; exact p3
  have y4 : val32 s₄.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) := by
    rw [Outside.val32 o4 (by omega) (by omega), hm3]; exact y0
  have b4 : Body B w s.mem s₄.mem := Outside.trans b0 (by rw [← hm3]; exact Body.of o4 (by omega) (by omega))
  have hlow : (word s₄.mem B (slot w 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₄.mem B (slot w 0)
    have h2 : val32 s₄.mem B (slot w 0) (2 * w - 1 + 1) =
        w32 s₄.mem B (slot w 0) + 2 ^ 32 * val32 s₄.mem B (slot w 0 + 4) (2 * w - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * w), p4] at h2
    omega
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok e4'.hs e4'.h10 (by omega) hlow) fun s₅ ⟨⟨r12lt, r12inv, m5⟩, k5⟩ => ?_
  have hw64 : s₅.mem.readW (off B 64) 64 = off X 0 := by
    rw [m5, ← hX]; exact Outside.word b4 (Or.inl (by omega)) (by omega)
  have hw72 : s₅.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl := by
    rw [m5, ← hXL]; exact Outside.word b4 (Or.inl (by omega)) (by omega)
  have k15 := (((k0.trans k1).trans k2).trans k3).trans k4 |>.trans k5
  have hld : WP isa (.block [.load .d .r30 .r23 64, .load .d .r31 .r23 72]) s₅ fun t =>
      (t.gpr .r30 = off X 0 ∧ t.gpr .r31 = BitVec.ofNat 64 xl ∧ t.mem = s₅.mem) ∧ Keep [.r30, .r31] s₅ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k15.gpr .r23 (by decide)).trans h23, (hs.congr k15.wr).ld (d := 64) (n := 8) (by omega),
      (hs.congr k15.wr).ld (d := 72) (n := 8) (by omega), hw64, hw72]
  refine WP.mono hld fun s₆ ⟨⟨a30, a31, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have e5' := e4'.keep k5 (by decide)
  have g10 : s₆.gpr .r10 = off B (slot w 0) := (k6.gpr .r10 (by decide)).trans e5'.h10
  have g29 : s₆.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k6.gpr .r29 (by decide)).trans e5'.h29
  have g11 : s₆.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k6.gpr .r11 (by decide)).trans e5'.h11
  rw [← m5, ← m6] at hr2 p4 y4
  have b6 : Body B w s.mem s₆.mem := by rw [m6, m5]; exact b4
  refine ⟨⟨a30, a31, g10, g29, g11, (k16.gpr .r23 (by decide)).trans h23, (k16.gpr .r28 (by decide)).trans h28⟩, ?_⟩
  refine WP.mono (ModExp.powSecret_ok (D := X) (L := xl) (hs.congr k16.wr) (by omega)
    (by omega) (by omega) g10 g29 g11
    (by rw [(k6.gpr .r12 (by decide))]; exact r12lt)
    (by rw [(k6.gpr .r12 (by decide)), m6, m5]; exact r12inv) (by rw [p4]; exact hp2) (by rw [p4]; exact hodd)
    (by rw [hr2, p4]; exact Nat.mod_lt _ (by omega)) a30 a31 hxl (by omega)
    (fun i hi => by rw [k16.rd, k16.wr]; exact hrdX i hi) hsepX)
    fun t ⟨⟨hpow, o7⟩, k7⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, (k16.trans k7).mono (by decide)⟩
  · rw [b6.bytesAt hZ hsepX, p4, y4] at hpow
    exact hpow (by rw [hr2, two_pow_128])
  · rw [arr, Outs.val32 o7 (fun r hr => ?_) (by omega), p4]
    simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [slot_eq] <;> omega
  · exact Outside.trans b6 (Body.of_outs o7 fun r hr => by
      simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [slot_eq] <;> omega)
  · exact (k7.gpr .r10 (by decide)).trans g10

/-- `exPower`: y's `k` octets (at `r9`) into array 4, then `y^x mod p` there,
for x's `xl` octets at `X`, whose address and length are in the header's
words 8 and 9. -/
theorem exPower_ok {s : State} {B Y X : Addr} {Z w k xl : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h9 : s.gpr .r9 = Y) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hxl : 1 ≤ xl) (hxl' : xl ≤ 1024)
    (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Y i) 1) (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Y i ≠ x)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1) :
    WP isa exPower s fun t => exPowPost B Y X w k xl s t ∧ Keep exPowRegs s t :=
  WP.seq (WP.mono (exPower_split h h23 h9 h28 hk hkw hxl hxl' hrdY hsepY hrdX hsepX hX hXL hp2 hodd)
    fun _ h => h.2)

/-- The registers `exOut` writes. -/
def exOutRegs : List Reg := zRegs ++ ([.r0, .r3, .r15, .r16, .r17, .r27, .r31] : List Reg)

/-- What `exOut` leaves from `s`: z's octets or zeros at `O`, and the status. -/
def exOutPost (B O : Addr) (w k : Nat) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem O k = (if 1 < arr s.mem B w 4 ∧ arr s.mem B w 4 < arr s.mem B w 0 - 1 then
      Spec.Rsa.i2osp (arr s.mem B w 4) k else List.replicate k 0) ∧
    t.gpr .r3 = BitVec.ofNat 64 (if 1 < arr s.mem B w 4 ∧ arr s.mem B w 4 < arr s.mem B w 0 - 1 then 1 else 0) ∧
    ∃ m, Body B w s.mem m ∧ Outside O 0 k m t.mem

/-- `exOutPre`, with the registers it leaves for the output, and then the
output: z (array 4, below p) to the `k` octets at `O` (the header's word 10)
if `1 < z < p − 1`, else zeros; `r3 := 1` or 0. -/
theorem exOut_split {s : State} {B O : Addr} {Z w k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hO : s.mem.readW (off B 80) 64 = off O 0) (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x)
    (hp : 1 ≤ arr s.mem B w 0) (hzp : arr s.mem B w 4 < arr s.mem B w 0) (hpk : arr s.mem B w 0 < 256 ^ k) :
    WP isa exOutPre s fun s₃ =>
      (s₃.gpr .r27 = off O 0 ∧ s₃.gpr .r10 = off B (slot w 0) ∧ s₃.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        s₃.gpr .r28 = BitVec.ofNat 64 k ∧ s₃.gpr .r23 = B ∧ s₃.gpr .r11 = BitVec.ofNat 64 (2 * w)) ∧
      WP isa PublicChecked.output s₃ fun t => exOutPost B O w k s t ∧ Keep exOutRegs s t := by
  unfold exOutPost
  have hnw := hs.nowrap
  have e0 := slot_eq w 0; have e4 := slot_eq w 4; have e5 := slot_eq w 5; have e8 := slot_eq w 8
  have e28 := slot_eq w 28
  generalize hz : arr s.mem B w 4 = z at hzp
  generalize hP : arr s.mem B w 0 = p at hp hzp hpk
  unfold exOutPre
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s.mem) (by
      prun [h23, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a31, m1⟩, k1⟩ => ?_)
  have e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, (k1.gpr .r10 (by decide)).trans h10,
    (k1.gpr .r29 (by decide)).trans h29, (k1.gpr .r11 (by decide)).trans h11, a31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (zMask_ok e1 ((k1.gpr .r23 (by decide)).trans h23) (by rw [m1, hP]; exact hp))
    fun s₂ ⟨⟨a26, z2, p2, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hz, hP] at a26
  rw [m1, hz] at z2
  rw [m1, hP] at p2
  have k12 := k1.trans k2
  have hb : (decide (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1)) = decide (1 < z ∧ z < p - 1) := by
    apply decide_eq_decide.mpr; omega
  rw [hb] at a26
  have hw80 : s₂.mem.readW (off B 80) 64 = off O 0 := by
    show Mont.word s₂.mem B 80 = _
    rw [Outside.word o2 (Or.inl (by omega)) (by omega), m1]; exact hO
  refine WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off O 0 ∧ t.mem = s₂.mem) (by
      prun [(k12.gpr .r23 (by decide)).trans h23, (hs.congr k12.wr).ld (d := 80) (n := 8) (by omega), hw80])
    (by decide)) fun s₃ ⟨⟨a27, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine ⟨⟨a27, (k3.gpr .r10 (by decide)).trans a10, (k13.gpr .r29 (by decide)).trans h29,
    (k13.gpr .r28 (by decide)).trans h28, (k13.gpr .r23 (by decide)).trans h23,
    (k13.gpr .r11 (by decide)).trans h11⟩, ?_⟩
  refine WP.mono (Pub.output_ok (b := decide (1 < z ∧ z < p - 1)) (hs.congr k13.wr) (ho.congr k13.wr)
    ((k3.gpr .r10 (by decide)).trans a10) ((k13.gpr .r29 (by decide)).trans h29)
    ((k13.gpr .r28 (by decide)).trans h28) a27 ((k3.gpr .r26 (by decide)).trans a26) hk hkw (by omega) hsep)
    fun t ⟨⟨ob, ot, t3⟩, kt⟩ => ⟨⟨?_, ?_, s₂.mem, ?_, by rw [← m3]; exact ot⟩, (k13.trans kt).mono (by decide)⟩
  · by_cases hc : 1 < z ∧ z < p - 1
    · rw [ite_eq_left hc]
      exact Pub.out_bytes hkw (by rw [← m3] at z2; exact z2) (by omega) fun i hi => by
        rw [ob i hi, m3, ite_eq_left (decide_eq_true hc)]
    · rw [ite_eq_right hc]
      exact Pub.zero_bytes fun i hi => by rw [ob i hi, ite_eq_right (by simpa using hc)]
  · rw [t3]; simp only [decide_eq_true_eq]
  · rw [← m1]; exact Body.of o2 (by omega) (by omega)

/-- `exOut`: z (array 4, below p) to the `k` octets at `O` (the header's word
10) if `1 < z < p − 1`, else zeros; `r3 := 1` or 0. -/
theorem exOut_ok {s : State} {B O : Addr} {Z w k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hO : s.mem.readW (off B 80) 64 = off O 0) (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x)
    (hp : 1 ≤ arr s.mem B w 0) (hzp : arr s.mem B w 4 < arr s.mem B w 0) (hpk : arr s.mem B w 0 < 256 ^ k) :
    WP isa exOut s fun t => exOutPost B O w k s t ∧ Keep exOutRegs s t :=
  WP.seq (WP.mono (exOut_split hs ho h10 h29 h11 h23 h28 hw hw' hZ hk hkw hO hsep hp hzp hpk) fun _ h => h.2)

end VG.Proof.Ffdh.PPC64LE.Domain
