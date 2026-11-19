module

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Power
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.Power
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `Ffdh.PPC64LE.CheckPrivate.Fn`, which only this module used -/

section

/-!
# `vg_ffdh_check_private` on PPC64LE: the function

`vg_ffdh_check_private(domain = r3, domain_len = r4, p_len = r5, y = r6,
y_len = r7, x = r8, x_len = r9, scratch = r10, scratch_len)`, the last on the
stack (`kpContract`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE

/-- The argument on the stack: `scratch_len`. -/
abbrev kpStack (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- What timing may depend on: the domain, y and the status. -/
def kpLeak (s : State) : List Nat :=
  let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
  let yB := Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
  dom.map (·.toNat) ++ yB.map (·.toNat) ++ [Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf (s.gpr .r5).toNat dom)
    (Spec.Rsa.os2ip yB) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))]

/-- `vg_ffdh_check_private`, on the registers and the stack. -/
def kpContract : Contract isa where
  pre s :=
    let dom : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let y : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let x : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, kpStack s] ∧ s.wr = [scr] ∧
      dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint (kpStack s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧
      (s.gpr .r7).toNat = (s.gpr .r5).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .r5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (stackArg s 0).toNat
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    Spec.Ffdh.domainValid (s.gpr .r5).toNat dom = true →
      ((t.gpr .r3).setWidth 32).toNat = Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf (s.gpr .r5).toNat dom)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat))
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ kpLeak s₁ = kpLeak s₂

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-! ### `Ffdh.PPC64LE.CheckPrivate.CT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.CheckPrivate.Front`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.CheckPrivate.Status`, which the modules that import this one used -/

section

/-! ### `Ffdh.PPC64LE.CheckPrivate.Body`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_check_private` on PPC64LE: after p's check

In the working space of `Domain/Body.lean`, p in array 0, x's address and
length and y's address in the header's words 8–10: `cpCmp_split`, z (array
4) compared with 2, `p − 2` and y; `cpBody_ok`, x's range (`xRange`), then
status 2, or `z = g^x mod p` and its comparison (`cpGood`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The registers `cpTail` writes. -/
def cpTailRegs : List Reg := zRegs ++ ([.r0, .r3, .r6, .r10, .r14, .r15, .r16, .r17, .r19, .r26, .r31] : List Reg)

/-- The condition for status 1: `z ∉ {0, 1, p − 1}` and `z = y`. -/
abbrev good (z p y : Nat) : Prop := (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1) ∧ z = y

/-- `cpTail`: with z in array 4, p in array 0 and y's `k` octets at `r12`,
`r3 :=` 1 if `good`, else 0. -/
theorem cpTail_ok {s : State} {B Yv : Addr} {Z w k : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (h12 : s.gpr .r12 = off Yv 0) (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * w) (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1)
    (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa cpTail s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if good (arr s.mem B w 4) (arr s.mem B w 0)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k)) then 1 else 0) ∧
        Body B w s.mem t.mem ∧ t.gpr .r23 = B) ∧ Keep cpTailRegs s t := by
  have hnw := hs.nowrap
  obtain e0 := Domain.slot_eq w 0; have e4 := Domain.slot_eq w 4; have e5 := Domain.slot_eq w 5
  obtain e8 := Domain.slot_eq w 8; have e9 := Domain.slot_eq w 9; have e28 := Domain.slot_eq w 28
  generalize hz : arr s.mem B w 4 = z
  generalize hP : arr s.mem B w 0 = p at hp
  generalize hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y
  unfold cpTail
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s.mem) (by
      prun [h23, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a31, m1⟩, k1⟩ => ?_)
  obtain e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, (k1.gpr .r10 (by decide)).trans h10,
    (k1.gpr .r29 (by decide)).trans h29, (k1.gpr .r11 (by decide)).trans h11, a31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (zMask_ok e1 ((k1.gpr .r23 (by decide)).trans h23) (by rw [m1, hP]; exact hp))
    fun s₂ ⟨⟨a26, z2, p2, o2, a10⟩, k2⟩ => ?_)
  rw [m1, hz, hP] at a26
  rw [m1, hz] at z2
  rw [m1, hP] at p2
  rw [m1] at o2
  obtain k12 := k1.trans k2
  obtain b2 : Body B w s.mem s₂.mem := Body.of o2 (by omega_using [e0, e5]) (by omega_using [e5, e28])
  unfold loadY
  refine WP.seq ?_
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain e2 : Env s₂ B Z w := ⟨hs.congr k12.wr, a10, (k12.gpr .r29 (by decide)).trans h29,
    (k12.gpr .r11 (by decide)).trans h11, (k2.gpr .r31 (by decide)).trans a31, hw, hw', hZ⟩
  refine WP.mono (e2.base (rd := .r10) (by decide) (by decide) 8) fun s₃ ⟨⟨a10₃, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r6] (Q := fun t => t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s₃.mem) (by
      prun [(k3.gpr .r28 (by decide)).trans ((k12.gpr .r28 (by decide)).trans h28), BitVec.add_zero])
    (by decide)) fun s₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  obtain k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 8) (hs.congr k14.wr) ((k4.gpr .r10 (by decide)).trans a10₃)
    ((k14.gpr .r12 (by decide)).trans h12) a6 ((k14.gpr .r11 (by decide)).trans h11) hk hkw (by omega_using [hw'])
    (by omega_using [e8]) (by omega_using [hZ, e8, e28]) (by rw [k14.rd, k14.wr]; exact hrdY) hsepY) fun s₅ ⟨v8, o5, k5⟩ => ?_)
  rw [m4, m3, b2.bytesAt hZ hsepY, hy] at v8
  obtain k15 := k14.trans k5
  have hh : hdrBytes = 256 := rfl
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₅.mem) (by
      prun [(k15.gpr .r23 (by decide)).trans h23, hh, BitVec.add_zero]
      simp [off, slot, hh]) (by decide)) fun s₆ ⟨⟨a10₆, m6⟩, k6⟩ => ?_
  obtain k16 := k15.trans k6
  obtain e6 : Env s₆ B Z w := ⟨hs.congr k16.wr, a10₆, (k16.gpr .r29 (by decide)).trans h29,
    (k16.gpr .r11 (by decide)).trans h11, ((k3.trans k4).trans (k5.trans k6)).gpr .r31 (by decide) |>.trans
      ((k2.gpr .r31 (by decide)).trans a31), hw, hw', hZ⟩
  refine WP.seq (WP.mono (eqMask_ok e6 .r19 (a := 4) (b := 8) (by decide) (by decide)) fun s₇ ⟨⟨a19, m7⟩, k7⟩ => ?_)
  obtain o5' : Outside B (slot w 8) (8 * w) s₂.mem s₆.mem := by rw [m6, ← m3, ← m4]; exact o5
  obtain z6 : val32 s₆.mem B (slot w 4) (2 * w) = z := by rw [Outside.val32 o5' (by omega_using [e4, e8]) (by omega_using [hw', e4])]; exact z2
  obtain y6 : val32 s₆.mem B (slot w 8) (2 * w) = y := by rw [m6]; exact v8
  rw [z6, y6] at a19
  obtain k17 := k16.trans k7
  refine WP.mono (WP.keep [.r26, .r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (if good z p y then 1 else 0) ∧
      t.mem = s₇.mem) (by
      unfold both
      prun [(k7.gpr .r26 (by decide)).trans ((((k3.trans k4).trans (k5.trans k6)).gpr .r26 (by decide)).trans a26),
        a19, mask_and']
      rw [BitVec.and_comm, mask_and_one]
      congr 1
      by_cases h1 : z ≠ 0 ∧ z ≠ 1 ∧ z ≠ p - 1 <;> by_cases h2 : z = y <;> simp [good, h1, h2]) (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_, (kt.gpr .r23 (by decide)).trans ((k17.gpr .r23 (by decide)).trans h23)⟩,
      (k17.trans kt).mono (by decide)⟩
  rw [mt, m7]
  exact Outside.trans b2 (Body.of o5' (by omega_using [e0, e8]) (by omega_using [e8, e28]))

/-- `cpCmp`, split after y's address is loaded from the header's word 10. -/
theorem cpCmp_split {s : State} {B Yv : Addr} {Z w k : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h23 : s.gpr .r23 = B) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hY : s.mem.readW (off B 80) 64 = off Yv 0) (hw : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * w) (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1)
    (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa (.block [.load .d .r12 .r23 80]) s fun s₁ =>
      (s₁.gpr .r12 = off Yv 0 ∧ s₁.gpr .r10 = off B (slot w 0) ∧ s₁.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        s₁.gpr .r23 = B ∧ s₁.gpr .r28 = BitVec.ofNat 64 k ∧ s₁.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) ∧
      WP isa cpTail s₁ fun t =>
        (t.gpr .r3 = BitVec.ofNat 64 (if good (arr s.mem B w 4) (arr s.mem B w 0)
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k)) then 1 else 0) ∧
          Body B w s.mem t.mem ∧ t.gpr .r23 = B) ∧ Keep (([.r12] : List Reg) ++ cpTailRegs) s t := by
  have hnw := hs.nowrap
  obtain e28 := Domain.slot_eq w 28
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = off Yv 0 ∧ t.mem = s.mem) (by
      prun [h23, hs.ld (d := 80) (n := 8) (by omega_using [hZ, e28]), hY]) (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ =>
    ⟨⟨a12, (k1.gpr .r10 (by decide)).trans h10, (k1.gpr .r11 (by decide)).trans h11,
      (k1.gpr .r23 (by decide)).trans h23, (k1.gpr .r28 (by decide)).trans h28,
      (k1.gpr .r29 (by decide)).trans h29⟩, ?_⟩
  refine WP.mono (cpTail_ok (Yv := Yv) (hs.congr k1.wr) ((k1.gpr .r10 (by decide)).trans h10)
    ((k1.gpr .r29 (by decide)).trans h29) ((k1.gpr .r11 (by decide)).trans h11) ((k1.gpr .r23 (by decide)).trans h23)
    ((k1.gpr .r28 (by decide)).trans h28) a12 hw hw' hZ hk hkw (by rw [k1.rd, k1.wr]; exact hrdY) hsepY
    (by rw [m1]; exact hp)) fun t ⟨⟨t3, tb, t23⟩, kt⟩ => ⟨⟨?_, by rw [← m1]; exact tb, t23⟩, k1.trans kt⟩
  rw [t3, m1]

/-- The registers `cpBody` writes. -/
def cpBodyRegs : List Reg :=
  xRangeRegs ++ exPowRegs ++ ([.r3, .r9, .r12] : List Reg) ++ cpTailRegs

/-- `cpBody`: 2 if x is out of range; else 1 if `z = g^x mod p` (g's `k`
octets at `D + k`) is `good` with y, else 0. -/
theorem cpBody_ok {s : State} {B D X Yv : Addr} {Z w k L xl p x g y b : Nat} (h : Env s B Z w)
    (h23 : s.gpr .r23 = B) (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L = 2 * k ∨ L = 3 * k) (hxl : 1 ≤ xl) (hxk : xl ≤ k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 xl)
    (hY : s.mem.readW (off B 80) 64 = off Yv 0)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hrdX : ∀ i < xl, InRegions (s.rd ++ s.wr) (off X i) 1) (hsepX : ∀ i < xl, ∀ x, ofs B x < Z → off X i ≠ x)
    (hrdY : ∀ i < k, InRegions (s.rd ++ s.wr) (off Yv i) 1) (hsepY : ∀ i < k, ∀ x, ofs B x < Z → off Yv i ≠ x)
    (hP : arr s.mem B w 0 = p) (hp2 : 2 ≤ p) (hodd : p % 2 = 1)
    (hpt : 2 ^ (64 * (w - 1)) < p)
    (hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X xl) = x) (hg : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = g)
    (hy : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yv k) = y) (hb : bnd s.mem D k L p = b) :
    WP isa cpBody s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < x ∧ x < b) then 2 else if good (g ^ x % p) p y then 1 else 0) ∧
        ∀ i < 18, word t.mem B (112 + 8 * i) = word s.mem B (112 + 8 * i)) ∧ Keep cpBodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  obtain e0 := Domain.slot_eq w 0; have e8 := Domain.slot_eq w 8; have e28 := Domain.slot_eq w 28
  obtain rdQ : L = 3 * k → ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1 := fun hq i hi => by
    rw [off_off']; exact hrdD _ (by omega_using [hq, hi])
  obtain sepQ : L = 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun hq i hi => by
    rw [off_off']; exact hsepD _ (by omega_using [hq, hi])
  obtain rdG : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1 := fun i hi => by
    rw [off_off']; exact hrdD _ (by omega_using [hL, hi])
  obtain sepG : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact hsepD _ (by omega_using [hL, hi])
  unfold cpBody
  refine WP.seq (WP.mono (xRange_ok h h23 h21 h27 h28 (by omega_using [hk]) (by omega_using [hwk]) (by omega_using [hk', hL]) (by omega_using [hk']) hxl hxk hX hXL
    hrdX hsepX rdQ sepQ (by omega_using [hP, hp2])) fun s₁ ⟨⟨a26, p1, b1, a10⟩, k1⟩ => ?_)
  rw [hx, hP, hb] at a26
  rw [hP] at p1
  obtain e1 : Env s₁ B Z w := ⟨hs.congr k1.wr, a10, (k1.gpr .r29 (by decide)).trans h.h29,
    (k1.gpr .r11 (by decide)).trans h.h11, (k1.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  obtain hw1 : ∀ d, d + 8 ≤ 256 → word s₁.mem B d = word s.mem B d := fun d hd => by
    rw [Outside.word b1 (by omega_using [e0, hd]) (by omega_using [hd])]
  obtain g23 : s₁.gpr .r23 = B := (k1.gpr .r23 (by decide)).trans h23
  obtain g28 : s₁.gpr .r28 = BitVec.ofNat 64 k := (k1.gpr .r28 (by decide)).trans h28
  refine WP.ite (s₁.gpr .r26 == 0) (eval_zero _ _) (fun hv => ?_) (fun hv => ?_)
  · -- Out of range.
    rw [a26, mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    refine WP.mono (li_ok s₁ 2 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, fun i hi => ?_⟩,
      (k1.trans kt).mono (by decide)⟩
    · rw [t3, ite_eq_left hv]
    · rw [tm, hw1 _ (by omega_using [hi])]
  · -- In range.
    rw [a26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hv
    unfold cpGood
    refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₁.mem) (by
        prun [(k1.gpr .r21 (by decide)).trans h21, g28]) (by decide)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)
    obtain k12 := k1.trans k2
    obtain e2 := e1.keep k2 (by decide)
    obtain b12 : Body B w s.mem s₂.mem := by rw [m2]; exact b1
    refine WP.seq (WP.mono (exPower_ok (Y := off D k) (X := X) (k := k) (xl := xl) e2
      ((k2.gpr .r23 (by decide)).trans g23) a9 ((k2.gpr .r28 (by decide)).trans g28) (by omega_using [hk]) (by omega_using [hwk]) hxl
      (by omega_using [hk', hxk]) (by rw [k12.rd, k12.wr]; exact rdG) sepG (by rw [k12.rd, k12.wr]; exact hrdX) hsepX
      (by rw [m2]; exact (hw1 64 (by omega_using [])).trans hX) (by rw [m2]; exact (hw1 72 (by omega_using [])).trans hXL)
      (by rw [m2, p1]; exact hp2) (by rw [m2, p1]; exact hodd)
      (by rw [m2, p1]; exact hpt)) fun s₃ ⟨⟨z3, p3, b3, r10₃⟩, k3⟩ => ?_)
    rw [b12.bytesAt hZ sepG, b12.bytesAt hZ hsepX, hg, hx, m2, p1] at z3
    rw [m2, p1] at p3
    obtain k13 := k12.trans k3
    obtain b13 : Body B w s.mem s₃.mem := Outside.trans b12 b3
    unfold cpCmp
    refine WP.seq (WP.mono (cpCmp_split (Yv := Yv) (hs.congr k13.wr) r10₃ ((k13.gpr .r29 (by decide)).trans h.h29)
      ((k13.gpr .r11 (by decide)).trans h.h11) ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans g23))
      ((k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans g28))
      (by show Mont.word s₃.mem B 80 = _; rw [Outside.word b13 (by omega_using [e0]) (by omega_using [])]; exact hY) hw hw' hZ
      (by omega_using [hk]) (by omega_using [hwk]) (by rw [k13.rd, k13.wr]; exact hrdY) hsepY (by rw [p3]; omega_using [hp2]))
      fun s₄ ⟨_, hw4⟩ => WP.mono hw4 fun t ⟨⟨t3, tb, _⟩, kt⟩ => ?_)
    rw [z3, p3, b13.bytesAt hZ hsepY, hy] at t3
    refine ⟨⟨?_, fun i hi => ?_⟩, (k13.trans kt).mono (by decide)⟩
    · rw [t3]; exact congrArg _ (ite_eq_right (fun h' => h' hv)).symm
    · rw [Outside.word tb (by omega_using [e0, hi]) (by omega_using [hi]), Outside.word b13 (by omega_using [e0, hi]) (by omega_using [hi])]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-!
# FFDH's key pairs on PPC64LE: the status

For a valid domain of `L` octets at `D`, `privateStatus` of y and x as the
code computes it: 2 unless `0 < x < bnd`, else 1 if `g^x mod p` is `good`
with y (not 0, 1 or `p − 1`, and y), else 0 (`privateStatus_dom`): with
`y = g^x mod p`, y is valid exactly when `g^x mod p` is in `2..p − 2`
(`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)
open VG.Proof.Mont (off)
open VG.Proof.Ffdh.PPC64LE.Derive (bnd)

/-- `privateStatus` for a valid domain of `L = 2 k` or `3 k` octets at `D`. -/
theorem privateStatus_dom {m : Mem} {D : Addr} {k L : Nat} (hk : 0 < k) (hL : L = 2 * k ∨ L = 3 * k)
    (hv : domainValid k (bytesAt m D L) = true) (y x : Nat) :
    privateStatus (domainOf k (bytesAt m D L)) y x =
      if ¬ (0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))) then 2 else
        if good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y then 1
        else 0 := by
  have hpv : parametersValid (domainOf k (bytesAt m D L)) = true := by
    unfold domainValid at hv
    simp only [Bool.and_eq_true] at hv
    exact hv.1
  have h2k : 2 * k ≤ L := by omega_using [hL]
  have hmod := Proof.Ffdh.domainValid_mod hv
  have hp2 : 2 ≤ (domainOf k (bytesAt m D L)).p := (Proof.Ffdh.PPC64LE.Domain.modulus_facts hmod).1
  rw [Proof.Ffdh.privateStatus_eq hpv, Proof.Ffdh.PPC64LE.Derive.privateValid_dom hk hL]
  by_cases h : 0 < x ∧ x < bnd m D k L (os2ip (bytesAt m D k))
  · simp only [h, and_self, decide_true, Bool.true_eq_false, ↓reduceIte, not_true_eq_false]
    have hc : (publicValid ⟨domainOf k (bytesAt m D L), y⟩ = true ∧
        (domainOf k (bytesAt m D L)).g ^ x % (domainOf k (bytesAt m D L)).p = y) ↔
        good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y := by
      rw [← Proof.Ffdh.domainOf_p m D h2k, show os2ip (bytesAt m (off D k) k) = (domainOf k (bytesAt m D L)).g by
        rw [Proof.Ffdh.domainOf_g m D h2k]]
      have hz := Nat.mod_lt ((domainOf k (bytesAt m D L)).g ^ x) (show 0 < (domainOf k (bytesAt m D L)).p by omega_using [hp2])
      constructor
      · rintro ⟨hy, rfl⟩
        have := (Proof.Ffdh.publicValid_power hpv x).mp hy
        exact ⟨by omega_using [this], rfl⟩
      · rintro ⟨hr, rfl⟩
        exact ⟨(Proof.Ffdh.publicValid_power hpv x).mpr (by omega_using [hz, hr]), rfl⟩
    by_cases hg : good (os2ip (bytesAt m (off D k) k) ^ x % os2ip (bytesAt m D k)) (os2ip (bytesAt m D k)) y
    · rw [ite_eq_left (hc.mpr hg), ite_eq_left hg]
    · rw [ite_eq_right (fun h' => hg (hc.mp h')), ite_eq_right hg]
  · simp [h]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on PPC64LE: the front

`cpFront` saves the nonvolatile registers in the working space's header,
stores x, `x_len` and y's address in its words 8–10 (`kpHdr_ok`), sets up
the registers and g's address in `r9`. It reaches `Base` for the domain of
`kdOf`, whose y is g, and `ExtK`: the header's words, x's and y's bytes,
readable and apart from the working space (`kp_front`), keeping the bytes
apart from the working space.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The public data of a run: the domain, g (as `CD`'s y) and the working
space; x's address and length, y's address, the bound on x and whether x is
within it. -/
structure KD where
  c : CD
  X : Addr
  xl : Nat
  Yv : Addr
  b : Nat
  v : Bool

/-- x's value in `s`. -/
abbrev xvalK (d : KD) (s : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.X d.xl)

def kdOf (s : State) : KD :=
  let c : CD := ⟨s.gpr .r3, off (s.gpr .r3) (s.gpr .r5).toNat, s.gpr .r10, (s.gpr .r5).toNat, (s.gpr .r4).toNat,
    (stackArg s 0).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat⟩
  let b := bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat c.p
  let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  ⟨c, s.gpr .r8, (s.gpr .r9).toNat, s.gpr .r6, b, decide (0 < x ∧ x < b)⟩

/-- What holds of x and y from the header's stores on. -/
structure ExtK (d : KD) (s : State) : Prop where
  wX : s.mem.readW (off d.c.S 64) 64 = off d.X 0
  wXL : s.mem.readW (off d.c.S 72) 64 = BitVec.ofNat 64 d.xl
  wY : s.mem.readW (off d.c.S 80) 64 = off d.Yv 0
  rdX : ∀ i < d.xl, InRegions (s.rd ++ s.wr) (off d.X i) 1
  sepX : ∀ i < d.xl, ∀ y, ofs d.c.S y < d.c.Z → off d.X i ≠ y
  rdY : ∀ i < d.c.k, InRegions (s.rd ++ s.wr) (off d.Yv i) 1
  sepY : ∀ i < d.c.k, ∀ y, ofs d.c.S y < d.c.Z → off d.Yv i ≠ y
  xl1 : 1 ≤ d.xl
  xlk : d.xl ≤ d.c.k

theorem ExtK.keep {d : KD} {s t : State} {rs : List Reg} (h : ExtK d s) (k : Keep rs s t)
    (hm : Body d.c.S d.c.w s.mem t.mem) : ExtK d t where
  wX := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 64 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wX
  wXL := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 72 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wXL
  wY := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 80 = _
    rw [Outside.word hm (Or.inl (by omega_using [this])) (by omega_using [])]; exact h.wY
  rdX := by rw [k.rd, k.wr]; exact h.rdX
  sepX := h.sepX
  rdY := by rw [k.rd, k.wr]; exact h.rdY
  sepY := h.sepY
  xl1 := h.xl1
  xlk := h.xlk

/-- The registers `cpFront` writes. -/
def kpFrontRegs : List Reg := ([.r23] : List Reg) ++ setup0Regs ++ ([.r9] : List Reg)

/-- x, `x_len` and y's address into the header's words 8–10 at `S`. -/
theorem kpHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r6 .r23 80] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r6 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [] s t := by
  refine WP.keep _ ?_ (by decide)
  obtain i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  obtain i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  obtain i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  obtain o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega_using [])
  obtain o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega_using [])
  obtain o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r6) (by omega_using [])
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega_using []) (by omega_using []), o1.word (by omega_using []) (by omega_using [])]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega_using []) (by omega_using [])]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega_using []) (by omega_using [])).trans (o1.mono (by omega_using []) (by omega_using []))).trans
      (o2.mono (by omega_using []) (by omega_using []))

/-- `cpFront`: `Base` and `ExtK` for `kdOf`, the saved registers in the
header, the bytes apart from the working space, and the registers it
writes. -/
theorem kp_front {s : State} (h : kpContract.pre s) :
    WP isa (.block cpFront) s fun t => Base (kdOf s).c t ∧ ExtK (kdOf s) t ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep kpFrontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL, hyl, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [kdOf]
  rw [hyl] at hrd dYS nwY
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hxk hsl hrd dYS nwY ⊢
  generalize hYd : s.gpr .r6 = Yv at hrd dYS nwY ⊢
  generalize hXd : s.gpr .r8 = X at hrd dXS nwX ⊢
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dXS nwX hx1 hxk ⊢
  generalize hSd : s.gpr .r10 = S at hwr dDS dYS dXS dSA nwS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dDS dYS dXS dSA nwS ⊢
  obtain hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_using [hL]
  obtain hZ256 : 256 ≤ Z := by omega_using [hsl, hZd]
  obtain hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  obtain hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  obtain hin : ∀ i < 18, InRegions s.wr (off (Domain.savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  obtain hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  unfold cpFront
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Domain.save_ok (ws := .r10) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  obtain h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  obtain hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := hSd ▸ hS.frame
  rw [WP.block_append_iff]
  refine WP.mono (kpHdr_ok h23₁ (by rw [k1.wr]; exact hinH)) fun s₂ ⟨⟨w8, w9, w10, o2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) ((k12.gpr .r3 (by decide)).trans hDd)
    (by rw [k12.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k12.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11', a29, a10, a31, m3⟩, k3⟩ => ?_
  obtain k123 := k12.trans k3
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₃.mem) (by prun [a21, a28])
    (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  obtain kall := k123.trans kt
  obtain hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [mt, m3, outside_bytesAt o2 (by omega_using [hZ256]) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    obtain hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_using [hZ256])) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  obtain sepD := sep_of_disjoint dDS (by omega_using [hLd])
  obtain rdD : ∀ i < L, InRegions (t.rd ++ t.wr) (off D i) 1 := fun i hi => by
    rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_using [hLd]) i hi
  obtain sepG : ∀ i < k, ∀ x, ofs S x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact sepD _ (by omega_using [hLk, hi])
  obtain hw3 : ∀ d, word t.mem S d = word s₂.mem S d := fun d => by rw [mt, m3]
  refine ⟨⟨⟨hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans a10, (kt.gpr .r29 (by decide)).trans a29,
    (kt.gpr .r11 (by decide)).trans a11', (kt.gpr .r31 (by decide)).trans a31, show 4 ≤ (k + 7) / 8 by omega_using [hk],
    show (k + 7) / 8 ≤ 128 by omega_using [hk'], hZw⟩, (kt.gpr .r21 (by decide)).trans a21,
    (kt.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)),
    (kt.gpr .r27 (by decide)).trans a27, (kt.gpr .r28 (by decide)).trans a28,
    hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega_using [hLk, hi]), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    ⟨?_, ?_, ?_,
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega_using [hxd]) i hi,
    sep_of_disjoint (L := xl) dXS (by omega_using [hxd]),
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := Yv) (L := k) (by rw [hrd]; simp) (by omega_using [hkd]) i hi,
    sep_of_disjoint (L := k) dYS (by omega_using [hkd]), hx1, hxk⟩, fun i hi => ?_, hb3, kall.mono (by decide)⟩
  · show word t.mem S 64 = _
    rw [hw3, w8, k1.gpr .r8 (by decide), hXd]; simp [off]
  · show word t.mem S 72 = _
    rw [hw3, w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
  · show word t.mem S 80 = _
    rw [hw3, w10, k1.gpr .r6 (by decide), hYd]; simp [off]
  · rw [hw3, o2.word (by omega_using []) (by omega_using [hi])]
    obtain ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, hSd, ea]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on PPC64LE: constant time

As `vg_ffdh_derive_public`'s (`Derive/CT.lean`), with the public data `KD`
(`kdOf`): the domain (g as `CD`'s y), x's address and length, y's address,
the bound on x and whether x is within it. p's load and check are the
domain check's pieces (`DA`, `DL`, `DC1`, `DC2`), each predicate stating that
the rest of the check reaches `K4` (`KB_loadP`); x's range as the
derivation's; the power and the comparison by `exPower_split` and
`cpCmp_split`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint two_taintR)

/-- g's address, the bound and x's range, as the data has them. -/
def InvK (d : KD) (s : State) : Prop :=
  d.c.Y = off d.c.D d.c.k ∧ bnd s.mem d.c.D d.c.k d.c.L d.c.p = d.b ∧
    (0 < xvalK d s ∧ xvalK d s < d.b ↔ d.v = true)

theorem InvK.keep {d : KD} {s t : State} (h : InvK d s) (hb : Base d.c s) (he : ExtK d s)
    (hm : Body d.c.S d.c.w s.mem t.mem) : InvK d t := by
  have hZ := hb.env.hZ
  refine ⟨h.1, (bnd_congr fun hq => hm.bytesAt hZ fun i hi => by
    rw [off_off']; exact hb.sepD _ (by omega_using [hq, hi])).trans h.2.1, ?_⟩
  have ex : xvalK d t = xvalK d s := by simp only [xvalK]; rw [hm.bytesAt hZ he.sepX]
  rw [ex]; exact h.2.2

/-! ## The predicates -/

def K0 (d : KD) (s : State) : Prop := kpContract.pre s ∧ kdOf s = d

/-- From `cpFront` on. -/
def KB (d : KD) (s : State) : Prop := Base d.c s ∧ ExtK d s ∧ InvK d s

/-- After p's check. -/
def K4 (d : KD) (s : State) : Prop := E4 d.c s ∧ ExtK d s ∧ InvK d s

/-- With `loadN`'s arguments, and p's load and check to come. -/
def K1a (d : KD) (s : State) : Prop :=
  E1a d.c s ∧ WP isa (.seq Precompute.loadN Precompute.check) s (K4 d)

/-- After `loadN`. -/
def K2 (d : KD) (s : State) : Prop := E2 d.c s ∧ WP isa Precompute.check s (K4 d)

/-- After `check1`. -/
def K3 (d : KD) (s : State) : Prop := E3 d.c s ∧ WP isa Precompute.check2 s (K4 d)

/-- After x's range: `r26` is zero exactly when x is out of range. -/
def KR2 (d : KD) (s : State) : Prop :=
  Base d.c s ∧ ExtK d s ∧ arr s.mem d.c.S d.c.w 0 = d.c.p ∧ Spec.Rsa.modulusValid d.c.p d.c.k = true ∧
    (s.gpr .r26 = 0 ↔ d.v = false) ∧ d.c.Y = off d.c.D d.c.k

/-- After x's address and length are loaded. -/
def KR1 (d : KD) (s : State) : Prop :=
  (s.gpr .r10 = off d.c.S (slot d.c.w 4) ∧ s.gpr .r12 = off d.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.xl ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧ s.gpr .r21 = d.c.D ∧ s.gpr .r23 = d.c.S ∧
    s.gpr .r27 = BitVec.ofNat 64 d.c.L ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧ s.gpr .r31 = d.c.S) ∧
  WP isa (.seq xLoadRest xMask) s (KR2 d)

/-- Before the power: g's address in `r9`, and p checked. -/
def KG2 (d : KD) (s : State) : Prop :=
  Base d.c s ∧ ExtK d s ∧ arr s.mem d.c.S d.c.w 0 = d.c.p ∧ Spec.Rsa.modulusValid d.c.p d.c.k = true ∧
    s.gpr .r9 = d.c.Y

/-- Before the comparison's rest: its registers, and that it ends with the
working space in `r23`. -/
def V7 (d : KD) (s : State) : Prop :=
  (s.gpr .r12 = off d.Yv 0 ∧ s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧
    s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2))) ∧
  WP isa cpTail s (CF d.c)

/-- After the power. -/
def V6 (d : KD) (s : State) : Prop :=
  (s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧ s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k) ∧
  WP isa (.block [.load .d .r12 .r23 80]) s (V7 d)

/-- After `exPre`. -/
def V5 (d : KD) (s : State) : Prop :=
  (s.gpr .r30 = off d.X 0 ∧ s.gpr .r31 = BitVec.ofNat 64 d.xl ∧ s.gpr .r10 = off d.c.S (slot d.c.w 0) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.c.w + 2)) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.c.w) ∧
    s.gpr .r23 = d.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 d.c.k) ∧
  WP isa ModExp.powWin s (V6 d)

/-! ## Pins -/

theorem pins_kbase {Φ : KD → State → Prop} (h : ∀ d s, Φ d s → Base d.c s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => (h _ _ h₁).pins (h _ _ h₂)

theorem pins_K0 : Pins K0 [.r10] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  have e₁ := congrArg (fun d => d.c.S) h₁
  have e₂ := congrArg (fun d => d.c.S) h₂
  simp only [kdOf] at e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact e₁.trans e₂.symm

theorem pins_K1a : Pins K1a (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E1a (Φ := E1a) (fun _ _ h => h) d.c s₁ s₂ h₁.1 h₂.1

theorem pins_K2 : Pins K2 (baseRegs ++ ([.r12, .r6] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E1a (Φ := E1a) (fun _ _ h => h) d.c s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_K3 : Pins K3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := fun d s₁ s₂ h₁ h₂ =>
  pins_E3 d.c s₁ s₂ h₁.1 h₂.1

theorem pins_KR1 : Pins KR1 [.r6, .r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29, .r31] := by
  rintro d s₁ s₂ ⟨⟨a10, a12, a6, a11, a21, a23, a27, a28, a29, a31⟩, -⟩
    ⟨⟨b10, b12, b6, b11, b21, b23, b27, b28, b29, b31⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a31, b31]

theorem pins_KG2 : Pins KG2 (baseRegs ++ ([.r9] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]

theorem pins_V5 : Pins V5 [.r10, .r11, .r23, .r28, .r29, .r30, .r31] := by
  rintro d s₁ s₂ ⟨⟨a30, a31, a10, a29, a11, a23, a28⟩, -⟩ ⟨⟨b30, b31, b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a30, b30]
  · rw [a31, b31]

theorem pins_V6 : Pins V6 [.r10, .r11, .r23, .r28, .r29] := by
  rintro d s₁ s₂ ⟨⟨a10, a29, a11, a23, a28⟩, -⟩ ⟨⟨b10, b29, b11, b23, b28⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_V7 : Pins V7 [.r10, .r11, .r12, .r23, .r28, .r29] := by
  rintro d s₁ s₂ ⟨⟨a12, a10, a11, a23, a28, a29⟩, -⟩ ⟨⟨b12, b10, b11, b23, b28, b29⟩, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a23, b23]
  · rw [a28, b28]
  · rw [a29, b29]

theorem pins_KCF : Pins (fun (d : KD) s => CF d.c s) [.r23] := by
  intro d s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; exact h₁.trans h₂.symm

/-! ## The front and p's check -/

theorem KF0 {d : KD} {s : State} (h : K0 d s) : WP isa (.block cpFront) s (KB d) := by
  obtain ⟨hpre, rfl⟩ := h
  refine WP.mono (kp_front hpre) fun t ⟨hb, he, _, hby, _⟩ => ⟨hb, he, rfl,
    bnd_congr fun hq => hby _ _ fun i hi => by
      rw [off_off']; exact hb.sepD _ (by simp only [kdOf] at hq hi ⊢; omega_using [hq, hi]), ?_⟩
  have ex : xvalK (kdOf s) t = xvalK (kdOf s) s := by simp only [xvalK]; rw [hby _ _ he.sepX]
  show 0 < xvalK (kdOf s) t ∧ xvalK (kdOf s) t < bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat
    (kdOf s).c.p ↔ decide _ = true
  rw [ex, decide_eq_true_iff]
  exact Iff.rfl

/-- p's load and check, from `KB`, by correctness. -/
theorem KB_loadP {d : KD} {s : State} (h : KB d s) : WP isa loadP s (K4 d) := by
  obtain ⟨hb, he, hi⟩ := h
  have hk := hb.k64
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hb.k1024 (fun i hi => hb.rdD i (by have := hb.kL; omega_using [hi, this]))
    (fun i hi => hb.sepD i (by have := hb.kL; omega_using [hi, this]))) fun t ⟨⟨pt, ct, bt⟩, kt⟩ => ?_
  have ep : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.c.D d.c.k) = d.c.p := by
    rw [← Proof.Ffdh.take_bytesAt _ _ hb.kL, hb.bD]
  rw [ep] at pt ct
  exact ⟨⟨hb.keep kt bt, pt, ct⟩, he.keep kt bt, hi.keep hb he bt⟩

theorem KF1 {d : KD} {s : State} (h : KB d s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (K1a d) :=
  wp_split (DA h.1) (KB_loadP h)

theorem KF2 {d : KD} {s : State} (h : K1a d s) : WP isa Precompute.loadN s (K2 d) :=
  wp_split (DL h.1) h.2

theorem KF3 {d : KD} {s : State} (h : K2 d s) : WP isa (.block Precompute.check1) s (K3 d) :=
  wp_split (DC1 h.1) h.2

theorem KF4 {d : KD} {s : State} (h : K3 d s) : WP isa Precompute.check2 s (K4 d) := h.2

theorem KLi {d : KD} {s : State} (h : Base d.c s) (v : Nat) (hv : v < 2 ^ 15) :
    WP isa (.block [.li .r3 v]) s (fun t => CF d.c t) :=
  WP.mono (li_ok s v hv) fun t ⟨_, kt⟩ => by show t.gpr .r23 = _; rw [kt.gpr .r23 (by decide)]; exact h.r23

/-! ## x's range -/

theorem KTR1 {d : KD} {s : State} (h : K4 d s ∧ s.gpr .r0 = 0) : WP isa (.block xLoadPre) s (KR1 d) := by
  obtain ⟨⟨⟨hb, hp, h0⟩, he, hi⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hZ := hb.env.hZ
  have hwd : d.c.w = (d.c.k + 7) / 8 := rfl
  have e28 := Domain.slot_eq d.c.w 28
  have rdQ : d.c.L = 3 * d.c.k → ∀ i < d.c.k, InRegions (s.rd ++ s.wr) (off (off d.c.D (2 * d.c.k)) i) 1 :=
    fun hq i hi => by rw [off_off']; exact hb.rdD _ (by omega_using [hq, hi])
  have sepQ : d.c.L = 3 * d.c.k → ∀ i < d.c.k, ∀ y, ofs d.c.S y < d.c.Z →
      off (off d.c.D (2 * d.c.k)) i ≠ y := fun hq i hi => by rw [off_off']; exact hb.sepD _ (by omega_using [hq, hi])
  have hrange := xRange_ok hb.env hb.r23 hb.r21 hb.r27 hb.r28 (by omega_using [hk]) (by omega_using [hwd])
    (by rcases hb.hL with h | h <;> omega_using [hk', h]) (by omega_using [hk']) he.xl1 he.xlk he.wX he.wXL he.rdX he.sepX rdQ sepQ
    (by rw [hp]; omega_using [hf])
  unfold xRange at hrange
  refine wp_split (WP.mono (xLoadPre_ok hb.env hb.r23 he.wX he.wXL) fun t ⟨⟨a10, a12, a6, _⟩, kt⟩ =>
    ⟨a10, a12, a6, (kt.gpr .r11 (by decide)).trans hb.env.h11, (kt.gpr .r21 (by decide)).trans hb.r21,
      (kt.gpr .r23 (by decide)).trans hb.r23, (kt.gpr .r27 (by decide)).trans hb.r27,
      (kt.gpr .r28 (by decide)).trans hb.r28, (kt.gpr .r29 (by decide)).trans hb.env.h29,
      (kt.gpr .r31 (by decide)).trans hb.env.h31⟩) (WP.mono hrange fun t ⟨⟨t26, tp, tb, t10⟩, kt⟩ => ?_)
  have hb' : Base d.c t := Base.of hb (fun r hr => by
      simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [t10, hb.env.h10]
      all_goals exact kt.gpr _ (by decide)) kt.rd kt.wr tb
  refine ⟨hb', he.keep kt tb, by rw [tp, hp], hv, ?_, hi.1⟩
  rw [t26, hp, hi.2.1, mask_eq_zero, decide_eq_false_iff_not]
  show ¬ (0 < xvalK d s ∧ xvalK d s < d.b) ↔ _
  rw [hi.2.2]
  cases d.v <;> simp

/-! ## In range -/

theorem KG1 {d : KD} {s : State} (h : KR2 d s ∧ s.gpr .r26 ≠ 0) :
    WP isa (.block [.add .r9 .r21 .r28]) s (KG2 d) := by
  obtain ⟨⟨hb, he, hp, hv, -, hY⟩, -⟩ := h
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off d.c.D d.c.k ∧ t.mem = s.mem)
    (by prun [hb.r21, hb.r28]) (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  have hm : Body d.c.S d.c.w s.mem t.mem := by rw [mt]; exact Outside.refl _ _ _ _
  exact ⟨hb.keep kt hm, he.keep kt hm, by rw [arr, mt]; exact hp, hv, a9.trans hY.symm⟩

theorem KG3 {d : KD} {s : State} (h : KG2 d s) : WP isa exPre s (V5 d) := by
  obtain ⟨hb, he, hp, hv, h9⟩ := h
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hxk := he.xlk
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have hwd : d.c.w = (d.c.k + 7) / 8 := rfl
  have e0 := Domain.slot_eq d.c.w 0
  have e28 := Domain.slot_eq d.c.w 28
  refine WP.mono (exPower_split hb.env hb.r23 h9 hb.r28 (by omega_using [hk]) (by omega_using [hwd]) he.xl1 (by omega_using [hk', hxk]) hb.rdY hb.sepY
    he.rdX he.sepX he.wX he.wXL (by rw [hp]; exact hf.1) (by rw [hp]; exact hf.2)
    (by rw [hp]; exact top_of_valid hv (by omega_using [hwd]) (by omega_using [hk, hwd])))
    fun s₆ ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, hw⟩ => ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, WP.mono hw
      fun t ⟨⟨_, p5, b5, r10₅⟩, k5⟩ => ?_⟩
  have k29 := (k5.gpr .r29 (by decide)).trans hb.env.h29
  have k11 := (k5.gpr .r11 (by decide)).trans hb.env.h11
  have k23 := (k5.gpr .r23 (by decide)).trans hb.r23
  have k28 := (k5.gpr .r28 (by decide)).trans hb.r28
  refine ⟨⟨r10₅, k29, k11, k23, k28⟩, WP.mono (cpCmp_split (Yv := d.Yv) (hb.env.hs.congr k5.wr) r10₅ k29 k11 k23
    k28 ?_ hb.env.hw hb.env.hw' hZ (by omega_using [hk]) (by omega_using [hwd]) (by rw [k5.rd, k5.wr]; exact he.rdY) he.sepY
    (by rw [p5, hp]; omega_using [hf])) fun s₁ ⟨regs, hw'⟩ => ⟨regs, WP.mono hw' fun u ⟨⟨_, _, u23⟩, _⟩ => u23⟩⟩
  show word t.mem d.c.S 80 = _
  rw [Outside.word b5 (Or.inl (by omega_using [e0])) (by omega_using [])]; exact he.wY

/-! ## Constant time -/

theorem kp_rel : RelCT isa (Two K0) checkPrivate fun _ _ => True := by
  unfold checkPrivate
  refine RelCT.seq (R := Two KB) (two_post (two_taint _ pins_K0 (by taint_decide)) fun _ _ h => KF0 h)
    (RelCT.seq (R := Two K4) ?_
      (RelCT.seq (R := Two fun (d : KD) s => CF d.c s) ?_ (two_taint _ pins_KCF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_kbase (Φ := KB) fun _ _ h => h.1) (by taint_decide))
        fun _ _ h => KF1 h)
      (RelCT.seq (two_post (two_taint _ pins_K1a (by taint_decide)) fun _ _ h => KF2 h)
        (RelCT.seq (two_post (two_taint _ pins_K2 (by taint_decide)) fun _ _ h => KF3 h)
          (two_post (two_taint _ pins_K3 (by taint_decide)) fun _ _ h => KF4 h)))
  · refine two_ite (Φ := K4) (fun d s₁ s₂ h₁ h₂ => h₁.1.2.2.trans h₂.1.2.2.symm) ?_
      (two_post (two_taint _ (pins_kbase (Φ := fun d s => K4 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KLi h.1.1.1 0 (by decide))
    unfold cpBody xRange
    refine RelCT.seq (R := Two KR2) (RelCT.seq
      (two_post (two_taint _ (pins_kbase (Φ := fun d s => K4 d s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => KTR1 h)
      (two_post (two_taint _ pins_KR1 (by taint_decide)) fun _ _ h => h.2)) ?_
    refine two_ite (Φ := KR2) (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm) ?_ ?_
    · exact two_post (two_taint _ (pins_kbase (Φ := fun d s => KR2 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1)
        (by taint_decide)) fun _ _ h => KLi h.1.1 2 (by decide)
    · unfold cpGood exPower cpCmp
      exact RelCT.seq (two_post (two_taint _ (pins_kbase (Φ := fun d s => KR2 d s ∧ s.gpr .r26 ≠ 0)
          fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => KG1 h)
        (RelCT.seq (RelCT.seq (two_post (two_taint _ pins_KG2 (by taint_decide)) fun _ _ h => KG3 h)
          (two_post (two_taintR _ pins_V5 (by taint_decide_rel)) fun _ _ h => h.2))
          (RelCT.seq (two_post (two_taint _ pins_V6 (by taint_decide)) fun _ _ h => h.2)
            (two_post (two_taint _ pins_V7 (by taint_decide)) fun _ _ h => h.2)))

/-- The status is 2 exactly when x is out of range. -/
theorem privateStatus_two (a : Spec.Ffdh.Parameters) (y x : Nat) :
    Spec.Ffdh.privateStatus a y x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateStatus
  cases Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp

/-- Runs with the same public arguments and leakage have the same public
data. -/
theorem kdOf_eq {s t : State} (hs : kpContract.pre s) (h3 : s.gpr .r3 = t.gpr .r3) (h4 : s.gpr .r4 = t.gpr .r4)
    (h5 : s.gpr .r5 = t.gpr .r5) (h6 : s.gpr .r6 = t.gpr .r6) (h7 : s.gpr .r7 = t.gpr .r7)
    (h8 : s.gpr .r8 = t.gpr .r8) (h9 : s.gpr .r9 = t.gpr .r9) (h10 : s.gpr .r10 = t.gpr .r10)
    (a0 : stackArg s 0 = stackArg t 0) (hl : kpLeak s = kpLeak t) : kdOf s = kdOf t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := hs
  simp only [Spec.Ffdh.domainLenValid] at hL
  simp only [kpLeak] at hl
  obtain ⟨e12, e3⟩ := List.append_inj hl (by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h4, h7])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h4])
  have ed : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat := by
    have := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
    rw [← h3, ← h4] at this; exact this
  have sl : ∀ o, o + (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat →
      Spec.Rsa.bytesAt s.mem (s.gpr .r3 + BitVec.ofNat 64 o) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 o) (s.gpr .r5).toNat := fun o ho => by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem _ ho, ← VG.Proof.Dsa.bytesAt_slice t.mem _ ho, ed]
  have hp : ∀ m : Mem, Spec.Rsa.os2ip ((Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r4).toNat).take (s.gpr .r5).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r5).toNat) := fun m => by
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega_using [hL])]
  have hpT : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r5).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat) := by rw [← hp, ← hp, ed]
  have hbT : ∀ P, bnd t.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat P =
      bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat P := fun P =>
    bnd_congr fun hq => (sl _ (by omega_using [hq])).symm
  have e4 := (privateStatus_two _ _ _).symm.trans
    ((iff_of_eq (congrArg (· = 2) (List.cons.inj e3).1)).trans (privateStatus_two _ _ _))
  rw [← h3, ← h4, ← h5, ← h8, ← h9] at e4
  rw [Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega_using [hk]) (by omega_using [hL]),
    Proof.Ffdh.PPC64LE.Derive.privateValid_dom (by omega_using [hk]) (by omega_using [hL]), hpT, hbT] at e4
  have hv := bool_eq_of_false_iff e4
  have ext : ∀ a b : KD, a.c = b.c → a.X = b.X → a.xl = b.xl → a.Yv = b.Yv → a.b = b.b → a.v = b.v → a = b := by
    rintro ⟨⟩ ⟨⟩; simp_all
  have hc : (kdOf s).c = (kdOf t).c := by
    simp only [kdOf]
    rw [← h3, ← h4, ← h5, ← h10, ← a0, ed]
    simp only [off]
    rw [sl _ (by omega_using [hL])]
  refine ext _ _ hc (by simp only [kdOf, h8]) (by simp only [kdOf, h9]) (by simp only [kdOf, h6]) ?_ ?_
  · show bnd s.mem _ _ _ (kdOf s).c.p = bnd t.mem _ _ _ (kdOf t).c.p
    rw [← hc, ← h3, ← h4, ← h5, hbT]
  · show decide _ = decide _
    rw [← h3, ← h4, ← h5, ← h8, ← h9]
    simp only [CD.p, hp, hpT, hbT]
    exact hv

theorem kp_ct : ConstantTime isa kpContract.pre kpContract.pub checkPrivate :=
  RelCT.constantTime (kp_rel.mono (fun s _ ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, h9, h10, a0, hl⟩ =>
    ⟨kdOf s, ⟨hs, rfl⟩, ⟨ht, (kdOf_eq hs h3 h4 h5 h6 h7 h8 h9 h10 a0 hl).symm⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-! ### `Ffdh.PPC64LE.CheckPrivate.Implies`, which only this module used -/

section

/-!
# `vg_ffdh_check_private` on PPC64LE: the shared contract

`kpContract` states the shared contract on the registers and the stack
(`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE

theorem kpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `kpContract.pre`: a 512-bit p without q, the domain at
`0x2000`, y at `0x1000`, x at `0x3000`, the working space at `0x4000`, and
the stack argument at `0x9060`. -/
def kpSatState : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 128 | .r5 => 64 | .r6 => 0x1000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 0x20 else bif Nat.beq a.toNat 0x9061 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x1000, 64⟩, ⟨0x3000, 1⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 8448⟩]

theorem kp_implies : kpContract.Implies (Spec.Ffdh.checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_simp [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | sig_disjoint_symm
      | omega
      | (sig_simp_only [Nat.mul_comm] at *
         first | with_reducible assumption | sig_disjoint_symm)
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_false, Bool.cond_true,
          Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [kpStack])
  post := by
    sig_implies_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, kpLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [kpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSatState

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end

/-! ### `Ffdh.PPC64LE.CheckPrivate.Correct`, which only this module used -/

section

/-!
# `vg_ffdh_check_private` on PPC64LE: correctness

`checkPrivate` saves the registers and sets up (`kp_front`), loads and
checks p (`loadP_ok`), checks x's range and compares `g^x mod p` with 2,
`p − 2` and y (`cpBody_ok`), and restores the registers (`kp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

private theorem kp_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ kpFrontRegs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (cpBodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem kp_correct (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa checkPrivate s tr t ∧ abiPreserved s t ∧ kpContract.post s t := by
  show WP isa checkPrivate s fun t => abiPreserved s t ∧ kpContract.post s t
  have hpre := h
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, nwS, -, hL, hyl, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW (s.gpr .r10)) (8 * i)) 8 := fun i hi =>
    ⟨⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩, by rw [hwr]; simp, by
      rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega_using [hsl, hi]) (by omega_using [hi])⟩
  unfold checkPrivate
  refine WP.seq (WP.mono (kp_front hpre) fun s₁ ⟨hb, he, hsav, hby, k1⟩ => ?_)
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have e0 := Domain.slot_eq (kdOf s).c.w 0
  have e28 := Domain.slot_eq (kdOf s).c.w 28
  refine WP.seq (WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hk' (fun i hi => hb.rdD i (by omega_using [hLk, hi]))
    (fun i hi => hb.sepD i (by omega_using [hLk, hi]))) fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_)
  have hb2 := hb.keep k2 b2
  have he2 := he.keep k2 b2
  have hDk : Spec.Rsa.bytesAt s₁.mem (s.gpr .r3) (s.gpr .r5).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat := by
    rw [← Proof.Ffdh.take_bytesAt _ _ (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by
      rcases hLk with h | h <;> simp only [kdOf] at h <;> omega_using [h]), ← Proof.Ffdh.take_bytesAt s.mem _
      (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by rcases hLk with h | h <;> simp only [kdOf] at h <;> omega_using [h])]
    exact congrArg _ hb.bD
  rw [show (kdOf s).c.D = s.gpr .r3 from rfl, show (kdOf s).c.k = (s.gpr .r5).toNat from rfl, hDk] at p2 c2
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat) = p at p2 c2
  generalize hxv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (s.gpr .r8) (s.gpr .r9).toNat) = xv
  generalize hgv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat) = g
  generalize hyv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (s.gpr .r6) (s.gpr .r5).toNat) = yv
  generalize hbv : bnd s₂.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p = b
  have k12 := k1.trans k2
  have hite : WP isa (.ite (.zero .d .r0) cpBody (.block [.li .r3 0])) s₂ fun t =>
      (Spec.Rsa.modulusValid p (s.gpr .r5).toNat = true →
        t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < xv ∧ xv < b) then 2 else if good (g ^ xv % p) p yv then 1 else 0)) ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = word s₂.mem (s.gpr .r10) (112 + 8 * i)) ∧
      Keep (cpBodyRegs ++ ([.r3] : List Reg)) s₂ t := by
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · have hv := c2.mp (by simpa using hz)
      have hf := modulus_facts hv
      refine WP.mono (cpBody_ok (Yv := s.gpr .r6) hb2.env hb2.r23 hb2.r21 hb2.r27 hb2.r28 rfl hk hk' hLk
        he2.xl1 he2.xlk he2.wX he2.wXL he2.wY hb2.rdD hb2.sepD he2.rdX he2.sepX he2.rdY he2.sepY p2 hf.1
        hf.2 (top_of_valid hv (by have : (kdOf s).c.k = (s.gpr .r5).toNat := rfl; simp only [CD.w]; omega_using [this])
          (by have : (kdOf s).c.k = (s.gpr .r5).toNat := rfl; simp only [CD.w]; omega_using [hk])) hxv hgv hyv hbv) fun t ⟨⟨t3, tw⟩, kt⟩ => ⟨fun _ => t3, tw, kt.mono (by decide)⟩
    · refine WP.mono (li_ok s₂ 0 (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ =>
        ⟨fun hv => absurd (c2.mpr hv) (by simpa using hz), fun i hi => by rw [tm], kt.mono (by decide)⟩
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  have kall := k12.trans k5
  have hsav' : ∀ i < 18, t₅.mem.readW (off (Domain.savW (s.gpr .r10)) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (Domain.savW (s.gpr .r10)) (8 * i) = off (s.gpr .r10) (112 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [ea]
    show word t₅.mem (s.gpr .r10) (112 + 8 * i) = _
    have b2' : Body (s.gpr .r10) (kdOf s).c.w s₁.mem s₂.mem := b2
    rw [tw i hi, Outside.word b2' (by omega_using [e0, hi]) (by omega_using [hi])]
    exact hsav i hi
  refine WP.mono (Domain.restore_ok t₅ ((k5.gpr .r23 (by decide)).trans hb2.r23) (by rw [kall.wr]; exact hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (kp_pres_not_written r hr hn)]
  · dsimp only [kpContract]
    intro hdv
    have hL' : (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat ∨ (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat := hLk
    have hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ (by omega_using [hL']), hp] at hmod
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
      rw [b2.bytesAt hZ hq]; exact hby Q n hq
    have ex : Spec.Rsa.bytesAt s₂.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat := hsep _ _ he.sepX
    have eg : Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat := hsep _ _ hb.sepY
    have ey : Spec.Rsa.bytesAt s₂.mem (s.gpr .r6) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r5).toNat := hsep _ _ he.sepY
    have eb : bnd s₂.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p =
        bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p :=
      bnd_congr fun hq => hsep _ _ fun i hi => by
        rw [off_off']; exact hb.sepD (2 * (s.gpr .r5).toNat + i) (by simp only [kdOf]; omega_using [hq, hi])
    rw [ex] at hxv
    rw [eg] at hgv
    rw [ey] at hyv
    rw [eb] at hbv
    have hk0 : 0 < (s.gpr .r5).toNat := by have := hb.k64; simp only [kdOf] at this; omega_using [this]
    rw [privateStatus_dom hk0 hL' hdv, hp, hyl, hyv, hxv, hgv, hbv, uot .r3 (by decide), tpost hmod,
      ret_status _ (by split <;> [decide; split <;> decide])]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate

end

end


/-!
# `vg_ffdh_check_private` on PPC64LE: verified against the shared contract

With correctness (`kp_correct`), constant time (`kp_ct`) and the shared
contract (`kp_implies`), `checkPrivate` is verified (`kp_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Impl.Ffdh.PPC64LE.CheckPrivate

/-- `vg_ffdh_check_private`. -/
theorem kp_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi) :=
  Verified.of_correct kp_correct kp_ct kp_implies

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
