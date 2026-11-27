module

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Fast
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid

/-! ### `Ffdh.PPC64LE.Domain.ExchangeFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Domain.ExchangeBody`, which this module and modules that import it used -/

section

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
  obtain e0 := slot_eq w 0; have e4 := slot_eq w 4; have e5 := slot_eq w 5
  obtain e28 := slot_eq w 28
  generalize hy : arr s.mem B w 4 = y
  generalize hP : arr s.mem B w 0 = p at hp
  unfold zMask
  refine WP.seq (WP.mono (consts_ok h h23 (by rw [hP]; exact hp)) fun s₁ ⟨⟨v7, v6, v5, o1, a10⟩, k1⟩ => ?_)
  rw [hP] at v6
  obtain e1 : Env s₁ B Z w := ⟨h.hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  obtain y1 : val32 s₁.mem B (slot w 4) (2 * w) = y := by rw [Outside.val32 o1 (by omega_arith) (by omega_arith)]; exact hy
  obtain p1 : val32 s₁.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o1 (by omega_arith) (by omega_arith)]; exact hP
  refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = mask true ∧ t.mem = s₁.mem)
    (by prun; rfl) (by decide)) fun s₂ ⟨⟨a26, m2⟩, k2⟩ => ?_)
  obtain e2 := e1.keep k2 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e2 .r19 (a := 4) (b := 5) (by decide) (by decide))
    fun s₃ ⟨⟨a19, m3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₃ ((k3.gpr .r26 (by decide)).trans a26) a19) fun s₄ ⟨⟨b26, m4⟩, k4⟩ => ?_)
  obtain e4' := (e2.keep k3 (by decide)).keep k4 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e4' .r19 (a := 4) (b := 7) (by decide) (by decide))
    fun s₅ ⟨⟨c19, m5⟩, k5⟩ => ?_)
  refine WP.seq (WP.mono (clear19_ok s₅ ((k5.gpr .r26 (by decide)).trans b26) c19) fun s₆ ⟨⟨c26, m6⟩, k6⟩ => ?_)
  obtain e6 := (e4'.keep k5 (by decide)).keep k6 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e6 .r19 (a := 4) (b := 6) (by decide) (by decide)) fun s₇ ⟨⟨d19, m7⟩, k7⟩ => ?_)
  refine WP.mono (clear19_ok s₇ ((k7.gpr .r26 (by decide)).trans c26) d19) fun t ⟨⟨d26, mt⟩, kt⟩ => ?_
  obtain hm6 : s₆.mem = s₁.mem := by rw [m6, m5, m4, m3, m2]
  obtain hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  obtain hmt : t.mem = s₁.mem := by rw [mt, m7, hm6]
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
def exPowRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17,
  .r18, .r19, .r20, .r22, .r24, .r25, .r30, .r31]

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
    (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1)
    (hpt : 2 ^ (64 * (w - 1)) < arr s.mem B w 0) :
    WP isa exPre s fun s₆ =>
      (s₆.gpr .r30 = off X 0 ∧ s₆.gpr .r31 = BitVec.ofNat 64 xl ∧ s₆.gpr .r10 = off B (slot w 0) ∧
        s₆.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ s₆.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ s₆.gpr .r23 = B ∧
        s₆.gpr .r28 = BitVec.ofNat 64 k) ∧
      WP isa ModExp.powWinFn s₆ fun t => exPowPost B Y X w k xl s t ∧ Keep exPowRegs s t := by
  unfold exPowPost
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  obtain e0 := slot_eq w 0; have e1 := slot_eq w 1; have e4 := slot_eq w 4; have e8 := slot_eq w 8
  obtain e24 := slot_eq w 24; have e28 := slot_eq w 28
  generalize hP : arr s.mem B w 0 = p at hp2 hodd
  unfold exPre
  refine WP.seq (WP.mono (Pub.loadX_ok hs h23 h9 h28 h.h10 h.h29 h.h11 hk hkw (by omega_arith) (by omega_arith) hrdY hsepY)
    fun s₀ ⟨⟨y0, _, o0, a10⟩, k0⟩ => ?_)
  obtain e0' : Env s₀ B Z w := ⟨hs.congr k0.wr, a10, (k0.gpr .r29 (by decide)).trans h.h29,
    (k0.gpr .r11 (by decide)).trans h.h11, (k0.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  obtain p0 : val32 s₀.mem B (slot w 0) (2 * w) = p := by rw [Outside.val32 o0 (by omega_arith) (by omega_arith)]; exact hP
  obtain b0 : Body B w s.mem s₀.mem := Body.of o0 (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e0'.base (rd := .r5) (by decide) (by decide) 1) fun s₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  obtain e1' := e0'.keep k1 (by decide)
  refine WP.mono (e1'.base (rd := .r8) (by decide) (by decide) 2) fun s₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  obtain e2' := e1'.keep k2 (by decide)
  refine WP.mono (e2'.base (rd := .r9) (by decide) (by decide) 3) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  obtain e3' := e2'.keep k3 (by decide)
  obtain hm3 : s₃.mem = s₀.mem := by rw [m3, m2, m1]
  obtain p3 : val32 s₃.mem B (slot w 0) (2 * w) = p := by rw [hm3]; exact p0
  obtain hlow : (word s₃.mem B (slot w 0)).toNat % 2 = 1 := by
    obtain h1 := word_eq_w32 s₃.mem B (slot w 0)
    have h2 : val32 s₃.mem B (slot w 0) (2 * w - 1 + 1) =
        w32 s₃.mem B (slot w 0) + 2 ^ 32 * val32 s₃.mem B (slot w 0 + 4) (2 * w - 1) := rfl
    rw [Nat.sub_add_cancel (by omega_arith : 1 ≤ 2 * w), p3] at h2
    omega_arith
  refine WP.mono (Pub.minv_ok e3'.hs e3'.h10 (by omega_arith) hlow) fun s₄ ⟨⟨r12lt, r12inv, m4⟩, k4⟩ => ?_
  obtain e4' := e3'.keep k4 (by decide)
  obtain p4' : val32 s₄.mem B (slot w 0) (2 * w) = p := by rw [m4]; exact p3
  obtain k14 := (((k0.trans k1).trans k2).trans k3).trans k4
  refine WP.seq (WP.mono (Pre.r2Hi_ok (N := p) e4'.hs ((k4.gpr .r8 (by decide)).trans ((k3.gpr .r8 (by decide)).trans a8))
    ((k4.gpr .r9 (by decide)).trans a9) e4'.h10
    ((k4.gpr .r5 (by decide)).trans ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5))) e4'.h11
    (by omega_arith) (by omega_arith) (by omega_arith) r12lt (by rw [m4]; exact r12inv) p4'
    (by rw [← hP]; exact hpt) hodd) fun s₅ ⟨hr2, o5, k5⟩ => ?_)
  obtain e5' := e4'.keep k5 (by decide)
  obtain p5 : val32 s₅.mem B (slot w 0) (2 * w) = p := by
    rw [Outside.val32 o5 (by omega_arith) (by omega_arith)]; exact p4'
  obtain y5 : val32 s₅.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) := by
    rw [Outside.val32 o5 (by omega_arith) (by omega_arith), m4, hm3]; exact y0
  obtain b5 : Body B w s.mem s₅.mem :=
    Outside.trans b0 (by rw [← hm3, ← m4]; exact Body.of o5 (by omega_arith) (by omega_arith))
  obtain hw64 : s₅.mem.readW (off B 64) 64 = off X 0 := by
    rw [← hX]; exact Outside.word b5 (Or.inl (by omega_arith)) (by omega_arith)
  obtain hw72 : s₅.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl := by
    rw [← hXL]; exact Outside.word b5 (Or.inl (by omega_arith)) (by omega_arith)
  obtain k15 := k14.trans k5
  obtain hld : WP isa (.block [.load .d .r30 .r23 64, .load .d .r31 .r23 72]) s₅ fun t =>
      (t.gpr .r30 = off X 0 ∧ t.gpr .r31 = BitVec.ofNat 64 xl ∧ t.mem = s₅.mem) ∧ Keep [.r30, .r31] s₅ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k15.gpr .r23 (by decide)).trans h23, (hs.congr k15.wr).ld (d := 64) (n := 8) (by omega_arith),
      (hs.congr k15.wr).ld (d := 72) (n := 8) (by omega_arith), hw64, hw72]
  refine WP.mono hld fun s₆ ⟨⟨a30, a31, m6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  obtain g10 : s₆.gpr .r10 = off B (slot w 0) := (k6.gpr .r10 (by decide)).trans e5'.h10
  obtain g29 : s₆.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k6.gpr .r29 (by decide)).trans e5'.h29
  obtain g11 : s₆.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k6.gpr .r11 (by decide)).trans e5'.h11
  obtain p4 : val32 s₆.mem B (slot w 0) (2 * w) = p := by rw [m6]; exact p5
  obtain y4 : val32 s₆.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) := by
    rw [m6]; exact y5
  rw [← m6] at hr2
  obtain b6 : Body B w s.mem s₆.mem := by rw [m6]; exact b5
  refine ⟨⟨a30, a31, g10, g29, g11, (k16.gpr .r23 (by decide)).trans h23, (k16.gpr .r28 (by decide)).trans h28⟩, ?_⟩
  refine WP.mono (Win.powWinCall_ok (D := X) (L := xl) (hs.congr k16.wr) (by omega_arith)
    (by omega_arith) (by omega_arith) g10 g29 g11
    (Win.word_odd (by omega_arith) p4 hodd) (by rw [p4]; exact hp2) (by rw [p4]; exact hodd)
    (by rw [hr2, p4]; exact Nat.mod_lt _ (by omega_arith)) a30 a31 hxl (by omega_arith)
    (fun i hi => by rw [k16.rd, k16.wr]; exact hrdX i hi) hsepX)
    fun t ⟨⟨hpow, o7⟩, k7⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, (k16.trans k7).mono (by decide)⟩
  · rw [b6.bytesAt hZ hsepX, p4, y4] at hpow
    exact hpow (by rw [hr2, two_pow_128])
  · rw [arr, Outs.val32 o7 (fun r hr => ?_) (by omega_arith), p4]
    simp only [Win.win, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; dsimp only; simp only [slot_eq]; omega_arith
  · exact Outside.trans b6 (Body.of_outs o7 fun r hr => by
      simp only [Win.win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; dsimp only; simp only [slot_eq]; omega_arith)
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
    (hp2 : 2 ≤ arr s.mem B w 0) (hodd : arr s.mem B w 0 % 2 = 1)
    (hpt : 2 ^ (64 * (w - 1)) < arr s.mem B w 0) :
    WP isa exPower s fun t => exPowPost B Y X w k xl s t ∧ Keep exPowRegs s t :=
  WP.seq (WP.mono (exPower_split h h23 h9 h28 hk hkw hxl hxl' hrdY hsepY hrdX hsepX hX hXL hp2 hodd hpt)
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
  obtain e0 := slot_eq w 0; have e4 := slot_eq w 4; have e5 := slot_eq w 5; have e8 := slot_eq w 8
  obtain e28 := slot_eq w 28
  generalize hz : arr s.mem B w 4 = z at hzp
  generalize hP : arr s.mem B w 0 = p at hp hzp hpk
  unfold exOutPre
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s.mem) (by
      prun [h23, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a31, m1⟩, k1⟩ => ?_)
  obtain e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, (k1.gpr .r10 (by decide)).trans h10,
    (k1.gpr .r29 (by decide)).trans h29, (k1.gpr .r11 (by decide)).trans h11, a31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (zMask_ok e1 ((k1.gpr .r23 (by decide)).trans h23) (by rw [m1, hP]; exact hp))
    fun s₂ ⟨⟨a26, z2, p2, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hz, hP] at a26
  rw [m1, hz] at z2
  rw [m1, hP] at p2
  obtain k12 := k1.trans k2
  obtain hb : (decide (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1)) = decide (1 < z ∧ z < p - 1) := by
    apply decide_eq_decide.mpr; omega_arith
  rw [hb] at a26
  obtain hw80 : s₂.mem.readW (off B 80) 64 = off O 0 := by
    show Mont.word s₂.mem B 80 = _
    rw [Outside.word o2 (Or.inl (by omega_arith)) (by omega_arith), m1]; exact hO
  refine WP.mono (WP.keep [.r27] (Q := fun t => t.gpr .r27 = off O 0 ∧ t.mem = s₂.mem) (by
      prun [(k12.gpr .r23 (by decide)).trans h23, (hs.congr k12.wr).ld (d := 80) (n := 8) (by omega_arith), hw80])
    (by decide)) fun s₃ ⟨⟨a27, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine ⟨⟨a27, (k3.gpr .r10 (by decide)).trans a10, (k13.gpr .r29 (by decide)).trans h29,
    (k13.gpr .r28 (by decide)).trans h28, (k13.gpr .r23 (by decide)).trans h23,
    (k13.gpr .r11 (by decide)).trans h11⟩, ?_⟩
  refine WP.mono (Pub.output_ok (b := decide (1 < z ∧ z < p - 1)) (hs.congr k13.wr) (ho.congr k13.wr)
    ((k3.gpr .r10 (by decide)).trans a10) ((k13.gpr .r29 (by decide)).trans h29)
    ((k13.gpr .r28 (by decide)).trans h28) a27 ((k3.gpr .r26 (by decide)).trans a26) hk hkw (by omega_arith) hsep)
    fun t ⟨⟨ob, ot, t3⟩, kt⟩ => ⟨⟨?_, ?_, s₂.mem, ?_, by rw [← m3]; exact ot⟩, (k13.trans kt).mono (by decide)⟩
  · by_cases hc : 1 < z ∧ z < p - 1
    · rw [ite_eq_left hc]
      exact Pub.out_bytes hkw (by rw [← m3] at z2; exact z2) (by omega_arith) fun i hi => by
        rw [ob i hi, m3, ite_eq_left (decide_eq_true hc)]
    · rw [ite_eq_right hc]
      exact Pub.zero_bytes fun i hi => by rw [ob i hi, ite_eq_right (by simpa using hc)]
  · rw [t3]; simp only [decide_eq_true_eq]
  · rw [← m1]; exact Body.of o2 (by omega_arith) (by omega_arith)

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

end

end

/-!
# `vg_ffdh_exchange` on PPC64LE: the function

`vg_ffdh_exchange(out = r3, out_len = r4, domain = r5, domain_len = r6,
p_len = r7, x = r8, x_len = r9, peer = r10, peer_len, scratch, scratch_len)`,
the last three on the stack (`exContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- The arguments on the stack: `peer_len`, `scratch` and `scratch_len`. -/
abbrev exStack (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- What timing may depend on: the domain, the peer and the status. -/
def exLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
  let yB := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat
  dom.map (·.toNat) ++ yB.map (·.toNat) ++
    [if (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf (s.gpr .r7).toNat dom)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) (Spec.Rsa.os2ip yB)).isSome then 1 else 0]

/-- `vg_ffdh_exchange`, on the registers and the stack. -/
def exContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let dom : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let x : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let peer : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧ s.rd = [dom, x, peer, exStack s] ∧ s.wr = [out, scr] ∧
      out.Disjoint dom ∧ out.Disjoint x ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint (exStack s) ∧
      dom.Disjoint scr ∧ x.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint (exStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r7).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r7).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = (s.gpr .r7).toNat ∧ (stackArg s 0).toNat = (s.gpr .r7).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .r7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 2).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .r7).toNat dom
    let y := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
    Spec.Ffdh.domainValid (s.gpr .r7).toNat dom = true → Spec.Ffdh.publicValid ⟨a, y⟩ = true →
      Spec.Rsa.written t.mem (s.gpr .r3) (s.gpr .r4).toNat ((t.gpr .r3).setWidth 32)
        (Spec.Ffdh.exchangeOp a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) y)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2 ∧
      exLeak s₁ = exLeak s₂

end VG.Proof.Ffdh.PPC64LE.Domain

end

end

/-!
# `vg_ffdh_exchange` on PPC64LE: correctness

`exchange` loads the working space's address from the stack (`loadS1_ok`),
saves the nonvolatile registers in its header, stores x, `x_len` and `out`
in the header's words 8–10 (`hdr_ok`), sets up the registers, loads and
checks p (`loadP_ok`), computes z (`exPower_ok`), writes it or zeros
(`exOut_ok`) and restores the registers (`ex_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- The second argument on the stack, `scratch`, into `r11`. -/
theorem loadS1_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s fun t =>
      (t.gpr .r11 = stackArg s 1 ∧ t.mem = s.mem) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  obtain ea : exec (.addSp .r11 104) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 104)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- x, `x_len` and `out` into the header's words 8–10 at `S`, the peer into
`r9` and the domain's arguments into `r3`–`r5`. -/
theorem hdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r3 .r23 80, .addi .r9 .r10 0,
      .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r3 ∧
        t.gpr .r9 = s.gpr .r10 ∧ t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [.r3, .r4, .r5, .r9] s t := by
  refine WP.keep _ ?_ (by decide)
  obtain i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  obtain i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  obtain i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  obtain o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega_arith)
  obtain o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega_arith)
  obtain o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r3) (by omega_arith)
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))

/-- Bytes apart from the working space are kept by a change in it. -/
theorem outside_bytesAt {B Q : Addr} {o n Z k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off Q i ≠ x) : Spec.Rsa.bytesAt m' Q k = Spec.Rsa.bytesAt m Q k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have := hsep i (List.mem_range.mp hi) (off Q i)
  show o + n ≤ ofs B (off Q i)
  by_contra hc
  exact this (by omega_arith) rfl

theorem saved_ne11' : ∀ i < 18, Impl.Ffdh.PPC64LE.Domain.saved i ∉ ([.r11] : List Reg) := by decide

theorem ex_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r11] : List Reg) ++ ([.r23] : List Reg) ++ ([.r3, .r4, .r5, .r9] : List Reg) ++
      ([.r10, .r11, .r21, .r27, .r28, .r29, .r31] : List Reg) ++
      ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
        (exPowRegs ++ exOutRegs ++ ([.r3] : List Reg)) := by
  decide

theorem ret_bv (c : Prop) [Decidable c] :
    (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem ex_correct (s : State) (h : exContract.pre s) :
    ∃ tr t, Exec isa exchange s tr t ∧ abiPreserved s t ∧ exContract.post s t := by
  show WP isa exchange s fun t => abiPreserved s t ∧ exContract.post s t
  obtain ⟨hsp, hrd, hwr, dOD, dOX, dOP, dOS, dOA, dDS, dXS, dPS, dSA, nwO, nwD, nwX, nwP, nwS, ⟨hk, hk'⟩, hL,
    hol, hpl, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  obtain hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨exStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 104) 8
    rw [show s.sp + BitVec.ofNat 64 104 = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [Offset.add_add]]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [hol] at hwr dOD dOX dOP dOS dOA nwO
  rw [hpl] at hrd dOP dPS nwP
  generalize hOd : s.gpr .r3 = O at hwr dOD dOX dOP dOS dOA nwO
  generalize hDd : s.gpr .r5 = D at hrd dOD dDS nwD
  generalize hLd : (s.gpr .r6).toNat = L at hrd dOD dDS nwD hL
  generalize hkd : (s.gpr .r7).toNat = k at hk hk' hL hxk hsl hwr dOD dOX dOP dOS dOA nwO hrd dPS nwP
  generalize hXd : s.gpr .r8 = X at hrd dOX dXS nwX
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dOX dXS nwX hx1 hxk
  generalize hPd : s.gpr .r10 = P at hrd dOP dPS nwP
  generalize hSd : stackArg s 1 = S at hwr dOS dDS dXS dPS dSA nwS
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dOS dDS dXS dPS dSA nwS
  obtain hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  obtain hZ256 : 256 ≤ Z := by omega_arith
  generalize hwd : (k + 7) / 8 = w
  obtain hw4 : 4 ≤ w := by omega_arith
  obtain hw' : w ≤ 128 := by omega_arith
  obtain hZw : slot w 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  obtain e0 : slot w 0 = 256 := by rw [slot_eq]; omega_arith
  obtain hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  obtain hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  obtain hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  obtain sepD := sep_of_disjoint dDS (by omega_arith)
  obtain sepX := sep_of_disjoint dXS (by omega_arith)
  obtain sepP := sep_of_disjoint dPS (by omega_arith)
  obtain rdD := rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_arith)
  obtain rdX := rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega_arith)
  obtain rdP := rd_of_mem (s := s) (D := P) (L := k) (by rw [hrd]; simp) (by omega_arith)
  obtain sepO : ∀ x, ofs O x < k → Z ≤ ofs S x := Pub.sep_of_disjoint dOS
  obtain sepSO : ∀ x, ofs S x < Z → k ≤ ofs O x := Pub.sep_of_disjoint dOS.symm
  unfold exchange exFront
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s hA1) fun s₀ ⟨⟨a11, m0⟩, k0⟩ => ?_)
  obtain a11' : s₀.gpr .r11 = S := a11.trans hSd
  refine WP.block_append (WP.mono (save_ok (ws := .r11) (by decide) s₀ (by rw [a11', k0.wr]; exact hin))
    fun s₁ hS => ?_)
  obtain k1 := k0.trans hS.keep
  obtain h23₁ : s₁.gpr .r23 = S := hS.r23.trans a11'
  obtain hfr₁ : Frame [savR S] s.mem s₁.mem := by rw [← m0, ← a11']; exact hS.frame
  refine WP.block_append (WP.mono (hdr_ok h23₁ (by rw [k1.wr]; exact hinH))
    fun s₂ ⟨⟨w8, w9, w10, b9, b3, b4, b5, o2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1.gpr .r5 (by decide)).trans hDd))
    (by rw [b4, k1.gpr .r6 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1.gpr .r7 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m3⟩, k3⟩ => ?_
  rw [hwd] at a11 a29 a10
  obtain k123 := k12.trans k3
  obtain e3 : Env s₃ S Z w := ⟨hs.congr k123.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  obtain hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [m3, outside_bytesAt o2 (by omega_arith) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    obtain hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_arith)) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  obtain g23 : s₃.gpr .r23 = S := (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)
  refine WP.seq (WP.mono (loadP_ok e3 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k123.rd, k123.wr]; exact rdD i (by omega_arith)) (fun i hi => sepD i (by omega_arith)))
    fun s₄ ⟨⟨p4, c4, b4'⟩, k4⟩ => ?_)
  rw [hb3 D k fun i hi => sepD i (by omega_arith)] at p4 c4
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) = p at p4 c4
  obtain e4 : Env s₄ S Z w := e3.keep k4 (by decide)
  obtain k1234 := k123.trans k4
  obtain hpk : p < 256 ^ k := by
    rw [← hp]; have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem D k)
    rwa [bytesAt_length] at this
  -- The header's words.
  obtain hw4' : ∀ d, d + 8 ≤ 256 → word s₄.mem S d = word s₂.mem S d := fun d hd => by
    rw [Outside.word b4' (by omega_arith) (by omega_arith), m3]
  generalize hz : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) % p = z
  obtain hite : WP isa (.ite (.zero .d .r0) (.seq exPower exOut) (.block [.li .r3 0])) s₄ fun t =>
      (Spec.Rsa.modulusValid p k = true →
        Spec.Rsa.bytesAt t.mem O k = (if 1 < z ∧ z < p - 1 then Spec.Rsa.i2osp z k else List.replicate k 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if 1 < z ∧ z < p - 1 then 1 else 0)) ∧
      (∀ i < 18, word t.mem S (112 + 8 * i) = word s₄.mem S (112 + 8 * i)) ∧
      Keep (exPowRegs ++ exOutRegs ++ ([.r3] : List Reg)) s₄ t := by
    refine WP.ite (s₄.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · have hv := c4.mp (by simpa using hb)
      obtain hf := modulus_facts hv
      obtain hX₄ : s₄.mem.readW (off S 64) 64 = off X 0 := by
        show word s₄.mem S 64 = _
        rw [hw4' 64 (by omega_arith), w8, k1.gpr .r8 (by decide), hXd]; simp [off]
      obtain hXL₄ : s₄.mem.readW (off S 72) 64 = BitVec.ofNat 64 xl := by
        show word s₄.mem S 72 = _
        rw [hw4' 72 (by omega_arith), w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
      refine WP.seq (WP.mono (exPower_ok (Y := P) (X := X) (k := k) (xl := xl) e4
        ((k4.gpr .r23 (by decide)).trans g23)
        ((k4.gpr .r9 (by decide)).trans ((k3.gpr .r9 (by decide)).trans (b9.trans
          ((k1.gpr .r10 (by decide)).trans hPd))))
        ((k4.gpr .r28 (by decide)).trans a28) (by omega_arith) (by omega_arith) hx1 (by omega_arith)
        (fun i hi => by rw [k1234.rd, k1234.wr]; exact rdP i hi) sepP
        (fun i hi => by rw [k1234.rd, k1234.wr]; exact rdX i hi) sepX hX₄ hXL₄
        (by rw [p4]; exact hf.1) (by rw [p4]; exact hf.2)
        (by rw [p4]; exact top_of_valid hv (by omega_using [hwd]) (by omega_using [hw4]))) fun s₅ ⟨⟨z5, p5, b5', r10₅⟩, k5⟩ => ?_)
      rw [Body.bytesAt b4' hZw sepP, Body.bytesAt b4' hZw sepX, hb3 P k sepP, hb3 X xl sepX, p4, hz] at z5
      obtain hO5 : s₅.mem.readW (off S 80) 64 = off O 0 := by
        show word s₅.mem S 80 = _
        rw [Outside.word b5' (by omega_arith) (by omega_arith), hw4' 80 (by omega_arith), w10, k1.gpr .r3 (by decide), hOd]
        simp [off]
      obtain k45 := k1234.trans k5
      refine WP.mono (exOut_ok (O := O) (k := k) (e4.hs.congr k5.wr)
        (Scr.of_mem (by rw [k45.wr, hwr]; simp) nwO) r10₅
        ((k5.gpr .r29 (by decide)).trans e4.h29) ((k5.gpr .r11 (by decide)).trans e4.h11)
        ((k5.gpr .r23 (by decide)).trans ((k4.gpr .r23 (by decide)).trans g23))
        ((k5.gpr .r28 (by decide)).trans ((k4.gpr .r28 (by decide)).trans a28)) hw4 hw' hZw (by omega_arith) (by omega_arith)
        hO5 sepO (by rw [p5, p4]; omega_arith) (by rw [z5, p5, p4, ← hz]; exact Nat.mod_lt _ (by omega_arith))
        (by rw [p5, p4]; exact hpk)) fun t ⟨⟨tb, t3, m, bm, om⟩, kt⟩ => ⟨fun _ => ?_, fun i hi => ?_,
          (k5.trans kt).mono (by decide)⟩
      · rw [z5, p5, p4] at tb t3
        exact ⟨tb, t3⟩
      · refine (Pub.Outside.word_apart (d := 112 + 8 * i) om sepSO (by omega_arith) (by omega_arith) hs.nowrap).trans ?_
        show Mont.word m S (112 + 8 * i) = Mont.word s₄.mem S (112 + 8 * i)
        rw [Outside.word bm (by omega_arith) (by omega_arith), Outside.word b5' (by omega_arith) (by omega_arith)]
    · refine WP.mono (li_ok s₄ 0 (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ =>
        ⟨fun hv => absurd (c4.mpr hv) (by simpa using hb), fun i hi => by rw [tm], kt.mono (by decide)⟩
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  obtain kall := k1234.trans k5
  obtain hsav : ∀ i < 18, t₅.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    obtain ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← k0.gpr _ (saved_ne11' i hi), ← hS.saved i hi, a11', ea]
    show word t₅.mem S (112 + 8 * i) = word s₁.mem S (112 + 8 * i)
    rw [tw i hi, hw4' _ (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
  refine WP.mono (restore_ok t₅ ((k5.gpr .r23 (by decide)).trans ((k4.gpr .r23 (by decide)).trans g23))
    (by rw [kall.wr]; exact hin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (ex_pres_not_written r hr hn)]
  · dsimp only [exContract]
    intro hdv hpv
    rw [hDd, hLd, hkd] at hdv hpv
    rw [hpl, hkd, hPd] at hpv
    obtain hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp] at hmod
    obtain hlo : 256 ^ (k - 1) ≤ p := by
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hmod; exact hmod.2
    obtain hf := modulus_facts hmod
    rw [hDd, hLd, hkd, hpl, hkd, hPd, hXd, hxd, hOd, hol, hkd]
    rw [Proof.Ffdh.exchangeOp_eq (k := k) hpv (by rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp]; omega_arith)
      (by rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp]; exact Proof.Ffdh.octets_bitLength (by omega_arith) hlo hpk),
      Proof.Ffdh.domainOf_p _ _ hLk.1, hp, hz, um, uot .r3 (by decide)]
    obtain ⟨tb, t3⟩ := tpost hmod
    rw [t3, ret_bv]
    by_cases hc : 1 < z ∧ z < p - 1
    · simp only [hc, and_self, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hc, and_self, ↓reduceIte]
    · simp only [hc, ↓reduceIte, Spec.Rsa.written, true_and]
      rw [tb]; simp only [hc, ↓reduceIte]

end VG.Proof.Ffdh.PPC64LE.Domain
