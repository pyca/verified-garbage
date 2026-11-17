module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime

/-! ### `Bignum.PPC64LE.CrtMid2`, which this module and modules that import it used -/

section

/-! ### `Bignum.PPC64LE.CrtPhaseD`, which this module and modules that import it used -/

section

/-! ### `Bignum.PPC64LE.CrtRecP1`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: `h`, its operands

`recP1_ok`: in `p`'s working space, `-p⁻¹ mod 2³²` into `r12`, `R² mod p`
into array 7 and `m₂ mod p` into array 1 (`reduceIn`), from `m₂`'s words in
`X`'s array 6, with `m₁` kept in array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The registers `recombineP` writes. -/
def recRegs : List Reg := .r10 :: powerRegs

/-- Array `a` of a working space into its array `b`. -/
theorem arrCopy_ok {s : State} {B : Addr} {w a b : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s B (slot w 24)) (ha : a < 24) (hb : b < 24) (hab : a ≠ b) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hc : ∀ t, val32 t.mem B (slot w b) (2 * w) = val32 s.mem B (slot w a) (2 * w) →
      Mont.Outside B (slot w b) (8 * w) s.mem t.mem → Keep [.r0, .r14, .r15, .r17] s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.base .r14 b ++ PublicChecked.base .r15 a)) (.seq copyN c)) s Q := by
  have hn := hs.nowrap
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain hsl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ slot w 24 := fun j hj => by
    simp only [e]
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 24 by omega_arith)
    rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
  obtain hsep : slot w a + 8 * w ≤ slot w b ∨ slot w b + 8 * w ≤ slot w a := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · left; simp only [e]
      have := Nat.mul_le_mul_right (8 * (w + 2)) (show a + 1 ≤ b by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
    · right; simp only [e]
      have := Nat.mul_le_mul_right (8 * (w + 2)) (show b + 1 ≤ a by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
  obtain la := hsl a ha; have lb := hsl b hb
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 b) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) a) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) hw hw' (by omega_arith) (by omega_arith) hsep) fun t ⟨⟨hw8, out⟩, k3⟩ => ?_)
  obtain hm : s₂.mem = s.mem := by rw [m2, m1]
  rw [hm] at hw8 out
  refine hc t ?_ out (k12.trans k3).mono
  rw [Pre.val32_eq_wv, wv_congr2 (fun i hi => hw8 i hi), ← Pre.val32_eq_wv]

/-- `recombineP`'s first part, in `p`'s working space `off BX oA` (`P` in
array 0, `m₁` in array 4), `m₂` the first `w_P n` words of `X`'s array 6
(`n` chunks of `⌈k / 8⌉` words, `k` in `r25`). -/
theorem recP1'_ok {pc : Bool} {s : State} {BX : Addr} {Z oA wP wX k Pv m1 m2 : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wP 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h25 : s.gpr .r25 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wP * nChunks ((k + 7) / 8) wP ≤ wX)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1)
    (hm2 : wv s.mem BX (slot wX 6) (wP * nChunks ((k + 7) / 8) wP) = m2)
    (hR2 : pc = true → ∃ S pL b, R2C false s BX S Z wP Pv pL b ∧ s.gpr .r30 = S)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wP 0) (2 * wP) = Pv →
      val32 t.mem (off BX oA) (slot wP 1) (2 * wP) = m2 % Pv →
      val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = m1 →
      val32 t.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wP 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wP 24) s.mem t.mem → t.gpr .r10 = off (off BX oA) (slot wP 0) →
      Keep recRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
      PublicChecked.base .r9 3)) (.seq (r2Step pc)
      (.seq (.block (PublicChecked.base .r14 9 ++ PublicChecked.base .r15 4)) (.seq copyN (.seq reduceIn
      (.seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 1)) (.seq copyN
      (.seq (.block (PublicChecked.base .r14 1 ++ PublicChecked.base .r15 4)) (.seq copyN
      (.seq (.block (PublicChecked.base .r14 4 ++ PublicChecked.base .r15 9)) (.seq copyN c))))))))))) s Q := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wP 0; have eA1 := e wP 1; have eA2 := e wP 2; have eA4 := e wP 4; have eA7 := e wP 7
  obtain eA9 := e wP 9; have eA8 := e wP 24
  obtain eX6 := e wX 6; have eX8 := e wX 8
  obtain hsA := hs.sub hA
  have hnA := hsA.nowrap
  obtain hlow : (word s.mem (off BX oA) (slot wP 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wP by omega_arith), ← Pre.val32_eq_wv, hP, hPodd]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok hsA h10 (by omega_arith) hlow) fun s₁ ⟨⟨i12, iinv, m1'⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 1) fun s₂ ⟨⟨a5, m2'⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 2) fun s₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 3) fun s₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  obtain hm4 : s₄.mem = s.mem := by rw [m4, m3, m2', m1']
  obtain g12 : s₄.gpr .r12 = s₁.gpr .r12 := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide)]
  obtain hsepB : ∀ S : Addr, (∀ x, ofs S x < 8 * wP → Z ≤ ofs BX x) →
      ∀ x, ofs S x < 8 * wP → slot wP 24 ≤ ofs (off BX oA) x := fun S hS x hx => by
    have := hS x hx
    rcases ofs_rebase BX x (o := oA) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith
  refine WP.seq (WP.mono (r2Step_ok (hsA.congr k14.wr) hsepB
    ((k4.gpr _ (by decide)).trans a8) a9
    ((k14.gpr _ (by decide)).trans h10) ((k4.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans a5))
    ((k14.gpr _ (by decide)).trans h11) ((k14.gpr _ (by decide)).trans h29)
    hw2 hw' (by simp only [e]; omega_arith) (by rw [g12]; exact i12)
    (by rw [g12, hm4]; exact iinv) (by rw [hm4, hP]; exact hP2) (by rw [hm4, hP]; exact hPodd)
    (fun hp => let ⟨S, pL, b, C, a30⟩ := hR2 hp; ⟨S, pL, b, by
      rw [hm4, hP]; exact C.of_mem hm4 (by rw [k14.rd, k14.wr]) (k14.gpr _ (by decide)),
      (k14.gpr _ (by decide)).trans a30⟩))
    fun s₅ ⟨r1, out5, k5⟩ => ?_)
  obtain k15 := k14.trans k5
  rw [hm4, hP] at r1
  rw [hm4] at out5
  have o5 : Mont.Outside (off BX oA) (slot wP 1) (24 * (wP + 2)) s.mem s₅.mem := out5
  obtain v0₅ : val32 s₅.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o5.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  obtain v4₅ : val32 s₅.mem (off BX oA) (slot wP 4) (2 * wP) = m1 := by
    rw [o5.val32 (Or.inr (by omega_arith)) (by omega_arith), hm1]
  obtain w0₅ : w32 s₅.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) :=
    o5.w32 (Or.inl (by omega_arith)) (by omega_arith)
  obtain g12₅ : s₅.gpr .r12 = s₁.gpr .r12 := by rw [k5.gpr _ (by decide), g12]
  -- `m₁` into array 9.
  refine arrCopy_ok (a := 4) (b := 9) (hsA.congr k15.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k15.gpr _ (by decide)).trans h10) ((k15.gpr _ (by decide)).trans h29) ((k15.gpr _ (by decide)).trans h11)
    fun s₆ c9 o6 k6 => ?_
  obtain k16 := k15.trans k6
  obtain outB6 : Outside BX oA (slot wP 24) s.mem s₆.mem :=
    (out_sub (fun y hy => out5 y hy) (by omega_arith) (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => o6 y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  obtain g12₆ : s₆.gpr .r12 = s₁.gpr .r12 := by rw [k6.gpr _ (by decide), g12₅]
  -- `m₂ mod p` into array 4.
  refine WP.seq (WP.mono (reduceIn_ok' (k := k) (Cv := m2) (hs.congr k16.wr) hA hXA hw2 hw' hnw
    ((k16.gpr _ (by decide)).trans h10) ((k16.gpr _ (by decide)).trans h21) ((k16.gpr _ (by decide)).trans h29)
    ((k16.gpr _ (by decide)).trans h11) ((k16.gpr _ (by decide)).trans h27) ((k16.gpr _ (by decide)).trans h28)
    ((k16.gpr _ (by decide)).trans h25) hk hk'
    (by rw [g12₆]; exact i12)
    (by rw [g12₆, o6.w32 (Or.inl (by omega_arith)) (by omega_arith), w0₅]; exact iinv)
    (by rw [o6.val32 (Or.inl (by omega_arith)) (by omega_arith), v0₅]) hP2 hPodd
    (by rw [o6.val32 (Or.inl (by omega_arith)) (by omega_arith), r1])
    (by rw [outB6.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hm2))
    fun s₇ ⟨⟨r4, r0, r1', i12', iinv', out7, a10', wk7⟩, k7⟩ => ?_)
  obtain k17 := k16.trans k7
  obtain v9₇ : val32 s₇.mem (off BX oA) (slot wP 9) (2 * wP) = m1 := by
    rw [wk7.val32 (Or.inr (by omega_arith)) (by omega_arith), c9, v4₅]
  -- `R² mod p` into array 7, `m₂ mod p` into array 1, `m₁` into array 4.
  refine arrCopy_ok (a := 1) (b := 7) (hsA.congr k17.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    a10' ((k17.gpr _ (by decide)).trans h29) ((k17.gpr _ (by decide)).trans h11) fun s₈ c7 o8 k8 => ?_
  obtain k18 := k17.trans k8
  refine arrCopy_ok (a := 4) (b := 1) (hsA.congr k18.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k8.gpr _ (by decide)).trans a10') ((k18.gpr _ (by decide)).trans h29) ((k18.gpr _ (by decide)).trans h11)
    fun s₉ c1 o9 k9 => ?_
  obtain k19 := k18.trans k9
  refine arrCopy_ok (a := 9) (b := 4) (hsA.congr k19.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a10')) ((k19.gpr _ (by decide)).trans h29)
    ((k19.gpr _ (by decide)).trans h11) fun t c4 o10 k10 => ?_
  obtain k110 := k19.trans k10
  obtain g12t : t.gpr .r12 = s₇.gpr .r12 := by rw [k10.gpr _ (by decide), k9.gpr _ (by decide), k8.gpr _ (by decide)]
  obtain w0t : w32 t.mem (off BX oA) (slot wP 0) = w32 s₇.mem (off BX oA) (slot wP 0) := by
    rw [o10.w32 (Or.inl (by omega_arith)) (by omega_arith), o9.w32 (Or.inl (by omega_arith)) (by omega_arith),
      o8.w32 (Or.inl (by omega_arith)) (by omega_arith)]
  refine hc t ?_ ?_ ?_ ?_ (by rw [g12t]; exact i12') (by rw [g12t, w0t]; exact iinv') ?_
    ((k10.gpr _ (by decide)).trans ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a10')))
    k110.mono
  · rw [o10.val32 (Or.inl (by omega_arith)) (by omega_arith), o9.val32 (Or.inl (by omega_arith)) (by omega_arith),
      o8.val32 (Or.inl (by omega_arith)) (by omega_arith), r0]
  · rw [o10.val32 (Or.inl (by omega_arith)) (by omega_arith), c1, o8.val32 (Or.inl (by omega_arith)) (by omega_arith), r4]
  · rw [c4, o9.val32 (Or.inr (by omega_arith)) (by omega_arith), o8.val32 (Or.inr (by omega_arith)) (by omega_arith), v9₇]
  · rw [o10.val32 (Or.inr (by omega_arith)) (by omega_arith), o9.val32 (Or.inr (by omega_arith)) (by omega_arith), c7, r1',
      ← Nat.pow_add, show 64 * wP + 64 * wP = 128 * wP by omega_arith]
  · exact (outB6.trans out7).trans ((out_sub (fun y hy => o8 y hy) (by omega_arith) (by omega_arith) (by omega_arith)).trans
      ((out_sub (fun y hy => o9 y hy) (by omega_arith) (by omega_arith) (by omega_arith)).trans
        (out_sub (fun y hy => o10 y hy) (by omega_arith) (by omega_arith) (by omega_arith))))

/-- `recombineP`'s first part, `k` (in the header) first. -/
theorem recP1_ok {pc : Bool} {s : State} {BX : Addr} {Z oA wP wX k Pv m1 m2 : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wP 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wP * nChunks ((k + 7) / 8) wP ≤ wX)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1)
    (hm2 : wv s.mem BX (slot wX 6) (wP * nChunks ((k + 7) / 8) wP) = m2)
    (hR2 : pc = true → ∃ S pL b, R2C false s BX S Z wP Pv pL b)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wP 0) (2 * wP) = Pv →
      val32 t.mem (off BX oA) (slot wP 1) (2 * wP) = m2 % Pv →
      val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = m1 →
      val32 t.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wP 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wP 24) s.mem t.mem → t.gpr .r10 = off (off BX oA) (slot wP 0) →
      Keep recRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (([.load .d .r25 .r23 oNLen] : List Instr) ++ r2Ptr pc false)) (.seq (.block
      (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3))
      (.seq (r2Step pc)
      (.seq (.block (PublicChecked.base .r14 9 ++ PublicChecked.base .r15 4)) (.seq copyN (.seq reduceIn
      (.seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 1)) (.seq copyN
      (.seq (.block (PublicChecked.base .r14 1 ++ PublicChecked.base .r15 4)) (.seq copyN
      (.seq (.block (PublicChecked.base .r14 4 ++ PublicChecked.base .r15 9)) (.seq copyN c)))))))))))) s Q := by
  have hn := hs.nowrap
  have hK' : s.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := hK
  obtain hZ : 256 ≤ Z := by have := slot_le (w := wX) (j := 0) (by decide); unfold slot at *; omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r25] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 k ∧ t.mem = s.mem) (by
    prun [h23, oNLen, hs.ld (show 16 + 8 ≤ Z by omega_arith), hK']) (by decide)) fun s₁ ⟨⟨a25', m₁⟩, k₁⟩ => ?_
  refine WP.mono (r2Ptr_ok (hs.congr k₁.wr) hZ ((k₁.gpr _ (by decide)).trans h23) m₁ hR2)
    fun s' ⟨⟨p30, mp⟩, kp⟩ => ?_
  obtain m' : s'.mem = s.mem := mp.trans m₁
  obtain k' := k₁.trans kp
  obtain a25 : s'.gpr .r25 = BitVec.ofNat 64 k := (kp.gpr _ (by decide)).trans a25'
  rw [← m'] at hP hm1 hm2
  refine recP1'_ok (hs.congr k'.wr) hA hXA hw2 hw' ((k'.gpr _ (by decide)).trans h10)
    ((k'.gpr _ (by decide)).trans h21) ((k'.gpr _ (by decide)).trans h29)
    ((k'.gpr _ (by decide)).trans h11) ((k'.gpr _ (by decide)).trans h27)
    ((k'.gpr _ (by decide)).trans h28) a25 hk hk' hnw hP hP2 hPodd hm1 hm2
    (fun hp => let ⟨S, pL, b, C, a30⟩ := p30 hp
      ⟨S, pL, b, C.of_mem m' (by rw [k'.rd, k'.wr]) (k'.gpr _ (by decide)), a30⟩)
    fun t v0 v1 v4 v7 t12 tinv o t10 k => ?_
  rw [m'] at o
  exact hc t v0 v1 v4 v7 t12 tinv o t10 (k'.trans k).mono

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-! ### `Bignum.PPC64LE.CrtRecP`, which only this module used -/

section

/-! ### `Bignum.PPC64LE.CrtRecP3`, which only this module used -/

section

/-!
# The RSA private-key operation on PPC64LE: `h`

`recP3_ok`: in `p`'s working space, `a qInv mod p` into array 4, for `a` in
array 3, `R² mod p` in array 7 and `qInv` from `X`'s array 7, by two
Montgomery multiplications.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Two Montgomery multiplications, the second by `R² mod P`: the product. -/
theorem mont_chain {P R a q x5 x4 : Nat} (hR : Nat.Coprime R P) (h5 : x5 * R % P = a * q % P)
    (h4 : x4 * R % P = x5 * (R * R % P) % P) (h4P : x4 < P) : x4 = a * q % P := by
  obtain e : x4 * R % P = a * q * R % P := by
    rw [h4, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h5, Nat.mod_mul_mod]
  rw [← Nat.mod_eq_of_lt h4P]
  exact VG.Proof.Bignum.mont_cancel hR e

/-- `recombineP`'s end, in `p`'s working space `off BX oA` (`-p⁻¹ mod 2³²` in
`r12`): `qInv` (`w_P` words of `X`'s array 7) into array 6, then
`a qInv R⁻¹ mod p` into array 5 and `a qInv mod p` into array 4. -/
theorem recP3_ok {s : State} {BX : Addr} {Z oA wP wX Pv a QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot wP 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hPodd : Pv % 2 = 1)
    (ha : val32 s.mem (off BX oA) (slot wP 3) (2 * wP) = a)
    (hRR : val32 s.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv) :
    WP isa (.seq (.block (PublicChecked.base .r14 6 ++ xb .r15 7)) (.seq copyN
      (.seq (PublicChecked.montOp 5 3 6) (PublicChecked.montOp 4 5 7)))) s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = a * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep (.r14 :: .r15 :: Pub.montRegs) s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wP 0; have eA2 := e wP 2; have eA3 := e wP 3; have eA4 := e wP 4; have eA5 := e wP 5
  obtain eA6 := e wP 6; have eA7 := e wP 7; have eA8 := e wP 24
  obtain sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  obtain hsA := hs.sub hA
  have hnA := hsA.nowrap
  obtain hA' : oA + slot wP 24 ≤ 2 ^ 64 := by omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 6) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) 7) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (b := oA + slot wP 6) (hs.congr k12.wr) a15
    (by rw [k2.gpr _ (by decide), a14, off_off]) ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  obtain o3 : Mont.Outside (off BX oA) (slot wP 6) (8 * wP) s.mem s₃.mem :=
    fun x hx => out_super out3 (by omega_arith) x hx
  obtain v6 : val32 s₃.mem (off BX oA) (slot wP 6) (2 * wP) = QI := by
    rw [Pre.val32_eq_wv, wv_off, ← hQ]; exact wv_congr2 fun i hi => hw3 i hi
  obtain v0 : val32 s₃.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  obtain v3 : val32 s₃.mem (off BX oA) (slot wP 3) (2 * wP) = a := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), ha]
  obtain v7 : val32 s₃.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o3.val32 (Or.inr (by omega_arith)) (by omega_arith), hRR]
  obtain w0 : w32 s₃.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) :=
    o3.w32 (Or.inl (by omega_arith)) (by omega_arith)
  obtain g12 : s₃.gpr .r12 = s.gpr .r12 := k13.gpr _ (by decide)
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 3) (b := 6) (hsA.congr k13.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k13.gpr _ (by decide)).trans h10) ((k13.gpr _ (by decide)).trans h29)
    ((k13.gpr _ (by decide)).trans h11) (by rw [g12]; exact h12) (by rw [g12, w0]; exact hinv)
    (by rw [v6, v0]; exact hQP)) fun s₄ ⟨⟨l5, e5, o4⟩, k4⟩ => ?_)
  obtain k14 := k13.trans k4
  rw [v0, v3, v6] at e5
  rw [v0] at l5
  obtain hpr : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 5 → j < 8 →
      ∀ r ∈ [(slot wP 2, 8 * (wP + 2)), (slot wP 3, 8 * (wP + 2)), (slot wP 5, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h2 h3 h5 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain s2 := slot_sep (w := wP) h2; have s3 := slot_sep (w := wP) h3; have s5 := slot_sep (w := wP) h5
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  obtain v0' : val32 s₄.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o4.val32 (hpr 0 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v0]
  obtain v7' : val32 s₄.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o4.val32 (hpr 7 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v7]
  obtain w0' : w32 s₄.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) := by
    rw [← w0]
    refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => o4 _ fun r hr => ?_)
    have := hpr 0 (by decide) (by decide) (by decide) (by decide) r hr
    rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith
  obtain g12' : s₄.gpr .r12 = s.gpr .r12 := k14.gpr _ (by decide)
  refine WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hsA.congr k14.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k14.gpr _ (by decide)).trans h10) ((k14.gpr _ (by decide)).trans h29)
    ((k14.gpr _ (by decide)).trans h11) (by rw [g12']; exact h12) (by rw [g12', w0']; exact hinv)
    (by rw [v7', v0']; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨⟨l4, e4, o5⟩, k5⟩ => ⟨⟨?_, ?_⟩, (k14.trans k5).mono⟩
  · rw [v0', v7'] at e4
    rw [v0'] at l4
    exact mont_chain (VG.Proof.Bignum.coprime_pow2 hPodd _) e5 e4 l4
  · have f4 := outs_sub o4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    obtain f5 := outs_sub o5 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    exact ((out3.mono (by omega_arith) (by omega_arith)).trans f4).trans f5

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: `h` in `p`'s working space

`recombineP_ok`: `h = (m₁ + p - m₂ mod p) mod p · qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `recombineP`, in `p`'s working space `off BX oA` (`P` in array 0, `m₁` in
array 4), for `m₂` the first `w_P n` words of `X`'s array 6 (`n` chunks of
`⌈k / 8⌉` words) and `qInv` in its array 7. -/
theorem recombineP_ok {pc : Bool} {s : State} {BX : Addr} {Z oA wP wX k Pv m1 m2 QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (hwx : wP ≤ wX) (hwX : wX < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wP 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wP * nChunks ((k + 7) / 8) wP ≤ wX)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1) (hm1P : m1 < Pv)
    (hm2 : wv s.mem BX (slot wX 6) (wP * nChunks ((k + 7) / 8) wP) = m2)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv)
    (hR2 : pc = true → ∃ S pL b, R2C false s BX S Z wP Pv pL b) :
    WP isa (recombinePG pc) s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = (m1 + Pv - m2 % Pv) % Pv * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep recRegs s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wP 0; have eA3 := e wP 3; have eA4 := e wP 4; have eA7 := e wP 7; have eA8 := e wP 24
  obtain sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  unfold recombinePG
  refine recP1_ok hs hA hXA hw2 hw' h10 h21 h29 h11 h23 h27 h28 hK hk hk' hnw hP hP2 hPodd hm1 hm2 hR2
    fun t₁ v0 v1 v4 v7 i12 iinv out1 t10 k1 => ?_
  obtain hsA := (hs.congr k1.wr).sub hA
  refine recP2a_ok (bj := 1) hsA (by unfold slot; omega_arith) (by decide) (by decide) (by decide) hw2 hw' t10
    ((k1.gpr _ (by decide)).trans h21) ((k1.gpr _ (by decide)).trans h29)
    ((k1.gpr _ (by decide)).trans h11) v0 v1 v4 (Nat.mod_lt _ (by omega_arith)) hm1P
    fun t₂ v3 out2 a10 k2 => ?_
  obtain hr2 : ∀ j, j ≠ 3 → j ≠ 4 → j < 8 →
      ∀ r ∈ [(slot wP 3, 8 * (wP + 2)), (slot wP 4, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h3 h4 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain s3 := slot_sep (w := wP) h3; have s4 := slot_sep (w := wP) h4
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  obtain out2' := outs_sub (S := slot wP 24) out2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith) (by omega_arith)
  obtain o12 := out1.trans out2'
  refine WP.mono (recP3_ok (hs.congr (k1.trans k2).wr) hA hXA hw2 hw' a10
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h29))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h11))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h27))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h28))
    (by rw [k2.gpr _ (by decide)]; exact i12)
    (by
      rw [k2.gpr _ (by decide)]
      refine Eq.trans ?_ iinv
      refine congrArg (fun v => (v * (t₁.gpr .r12).toNat + 1) % 2 ^ 32) ?_
      refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => out2 _ fun r hr => ?_)
      have := hr2 0 (by decide) (by decide) (by decide) r hr
      rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith)
    (by rw [out2.val32 (hr2 0 (by decide) (by decide) (by decide)) (by omega_arith), v0]) hPodd v3
    (by rw [out2.val32 (hr2 7 (by decide) (by decide) (by decide)) (by omega_arith), v7])
    (by rw [o12.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hQ) hQP)
    fun t ⟨⟨v4', out3⟩, k3⟩ => ⟨⟨v4', o12.trans out3⟩, ((k1.trans k2).trans k3).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: `h`

`phaseD_ok`: `m₂` into `X`'s array 6 (`exportM2`), then, in `p`'s working
space, `h = (m₁ - m₂ mod p) qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem Scr.le {s : State} {B : Addr} {Z n : Nat} (hs : Scr s B Z) (h : n ≤ Z) : Scr s B n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩, by have := hs.nowrap; omega_arith⟩

/-- `exportM2`, `setupP oBP oPLen` and `recombineP`: with `q`'s working space
at `off BX oQ` (`m₂` below `256^qL` in array 4, `qL ≤ k`) and `p`'s at
`off BX oP` (`P` in array 0, `m₁ < P` in array 4), `qInv < P` in `X`'s array
7: `h` into `p`'s array 4. -/
theorem phaseD_ok {pc : Bool} {s : State} {BX : Addr} {Z oP oQ wX pL qL k Pv m1 M2 QI : Nat}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 24 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 24 ≤ Z) (hXQ : slot wX 8 ≤ oQ) (_hPQ : oP + slot (wsWords pL) 24 ≤ oQ)
    (hwP : wsWords pL ≤ wX) (hwQ : wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL)
    (hq' : qL < 2 ^ 60) (hqk : qL ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wsWords pL * nChunks ((k + 7) / 8) (wsWords pL) ≤ wX)
    (hP0 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 0) (2 * wsWords pL) = Pv) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) (hm1 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = m1)
    (hm1P : m1 < Pv) (hm2 : Mont.val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2)
    (hm2b : M2 < 256 ^ qL) (hQI : Mont.val32 s.mem BX (slot wX 7) (2 * wX) = QI)
    (hQIb : QI < 2 ^ (64 * wsWords pL)) (hQP : QI < Pv)
    (hR2 : pc = true → ∃ S pL' b, R2C false s BX S Z (wsWords pL) Pv pL' b) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (recombinePG pc))) s fun t =>
      (Mont.val32 t.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) =
          (m1 + Pv - M2 % Pv) % Pv * QI % Pv ∧
        Mont.Outs BX [(slot wX 6, 8 * wX), (oP, slot (wsWords pL) 24)] s.mem t.mem) ∧
      Keep (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs) s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eX6 := e wX 6; have eX7 := e wX 7; have eX8 := e wX 8
  obtain eP0 := e (wsWords pL) 0; have eP4 := e (wsWords pL) 4; have eP8 := e (wsWords pL) 24
  obtain eQ8 := e (wsWords qL) 24
  obtain hw2 : 2 ≤ wsWords pL := by unfold wsWords; omega_arith
  refine WP.seq (WP.mono (exportM2_ok hs hQZ hXQ hwQ hwX h23 h27 h28 hBQ hQL hq1 hq')
    fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  -- `m₂`, below `2^(64 w_P n)`, in the words `reduceIn` reads.
  obtain hKn := le_nChunks_mul (K := (k + 7) / 8) (show 1 ≤ wsWords pL by omega_arith)
  obtain hM2n : M2 < 2 ^ (64 * (wsWords pL * nChunks ((k + 7) / 8) (wsWords pL))) := by
    refine Nat.lt_of_lt_of_le hm2b ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm (wsWords pL)]; omega_arith)
  obtain hbytes : wv s₁.mem BX (slot wX 6) (wsWords pL * nChunks ((k + 7) / 8) (wsWords pL)) = M2 :=
    wv_low (by rw [← Pre.val32_eq_wv, v6, hm2]) hM2n hnw
  obtain hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd =>
    o1.word (Or.inl (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (setupP_ok (oA := oP) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) (by decide)
    (by decide) (by omega_arith) (by rw [hd _ (by decide)]; exact hBP) (by rw [hd _ (by decide)]; exact hPL) hp1 hp')
    fun s₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  refine WP.mono (recombineP_ok (QI := QI) (k := k) (hs.congr k12.wr) hPZ hXP hw2 (by omega_arith) hwP hwX a10 a21
    a29 a11 ((k12.gpr _ (by decide)).trans h23) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) (by rw [m2, hd _ (by decide)]; exact hK) (by omega_arith) hk' hnw
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega_arith)) (by omega_arith), hP0]) hP2 hPodd
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega_arith)) (by omega_arith), hm1]) hm1P (by rw [m2]; exact hbytes)
    (by rw [m2, o1.wv (Or.inr (by omega_arith)) (by omega_arith)]
        exact wv_low (by rw [← Pre.val32_eq_wv]; exact hQI) hQIb hwP) hQP
    (fun hp => let ⟨S, pL', b, C⟩ := hR2 hp
      ⟨S, pL', b, (C.mono (oA := slot wX 6) (n := 8 * wX) o1 (by omega_arith) (by omega_arith)
        (by rw [k1.rd, k1.wr]) (k1.gpr _ (by decide))).of_mem m2 (by rw [k2.rd, k2.wr]) (k2.gpr _ (by decide))⟩))
    fun t ⟨⟨v4, o2⟩, k3⟩ => ⟨⟨v4, fun x hx => ?_⟩, (k12.trans k3).mono⟩
  obtain h1 := hx _ (List.mem_cons_self ..)
  obtain h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h1 h2
  have h1' : ofs BX x < slot wX 6 ∨ slot wX 6 + 8 * wX ≤ ofs BX x := h1
  have h2' : ofs BX x < oP ∨ oP + slot (wsWords pL) 24 ≤ ofs BX x := h2
  rw [m2] at o2
  rw [o2 x h2', o1 x h1']

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-! ### `Bignum.PPC64LE.CrtMid1`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: the powers

`mid1_ok`: after the front, `X` loaded and checked (`phaseA_ok`), then
`m₁ = c^dP mod p` and `m₂ = c^dQ mod q` (`phaseP_ok`), with `p`, `q` and
`qInv` masked.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

variable {pc : Bool}

/-- The numbers of the entry state `s₀`. -/
abbrev vN (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀))
abbrev vC (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (ck s₀))
abbrev vP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r9) (cpL s₀))
abbrev vQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀))
abbrev vDP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 2) (cpL s₀))
abbrev vDQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 4) (cqL s₀))
abbrev vQI (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 6) (cpL s₀))
/-- The checks' mask. -/
abbrev cb (s₀ : State) : Bool := crtMask (vN s₀) (ck s₀) (vC s₀) (vP s₀) (vQ s₀) (vQI s₀)
/-- `wP`, `wQ`, and the offsets of `P` and `Q`. -/
abbrev cwP (s₀ : State) : Nat := wsWords (cpL s₀)
abbrev cwQ (s₀ : State) : Nat := wsWords (cqL s₀)
abbrev oPa (s₀ : State) : Nat := slot (cwX s₀) 8
abbrev oQa (s₀ : State) : Nat := slot (cwX s₀) 8 + slot (cwP s₀) 24
/-- The masked `p`, `q` and `qInv`. -/
abbrev mP (s₀ : State) : Nat := if cb s₀ then vP s₀ else 3
abbrev mQ (s₀ : State) : Nat := if cb s₀ then vQ s₀ else 3
abbrev mQI (s₀ : State) : Nat := if cb s₀ then vQI s₀ else 0

/-- What the masked numbers satisfy. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    1 < mP s₀ ∧ mP s₀ % 2 = 1 ∧ 1 < mQ s₀ ∧ mQ s₀ % 2 = 1 ∧ mP s₀ < 2 ^ (64 * cwP s₀) ∧
      mQ s₀ < 2 ^ (64 * cwQ s₀) ∧ mQ s₀ ≤ 256 ^ cqL s₀ ∧ mQI s₀ < mP s₀ ∧ mQI s₀ < 2 ^ (64 * cwP s₀) := by
  obtain hpw : cpL s₀ ≤ 8 * cwP s₀ := by unfold cwP wsWords; omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
  obtain h3p : 3 < 2 ^ (64 * cwP s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwP s₀ by unfold cwP wsWords; omega_arith))
  obtain h3q : 3 < 2 ^ (64 * cwQ s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwQ s₀ by unfold cwQ wsWords; omega_arith))
  obtain h3 : 3 ≤ 256 ^ cqL s₀ := Nat.le_trans (by decide) (Nat.pow_le_pow_right (n := 256) (by decide) hP.q1)
  unfold mP mQ mQI
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide, by decide, h3p, h3q, h3, by decide, by omega_arith⟩
  · simp only [↓reduceIte]
    obtain ⟨_, _, hi, _, hp1, hpo, hq1, hqo⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
      hb
    exact ⟨hp1, hpo, hq1, hqo, Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw),
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hqw),
      Nat.le_of_lt (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)), hi,
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw)⟩

/-- With `pc`, the cached `R² mod p` and `R² mod q` at the entry's `r12`:
readable, apart from the working space, and the primes' under the mask. -/
structure R2F (s₀ : State) : Prop where
  hS : (s₀.gpr .r31).toNat + 8 * (cwP s₀ + cwQ s₀) ≤ 2 ^ 64
  rd : ∀ i < cwP s₀ + cwQ s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r31) (8 * i)) 8
  sep : ∀ x, ofs (s₀.gpr .r31) x < 8 * (cwP s₀ + cwQ s₀) → cZ s₀ ≤ ofs (cS s₀) x
  val : cb s₀ = true → wv s₀.mem (s₀.gpr .r31) 0 (cwP s₀) = 2 ^ (128 * cwP s₀) % vP s₀ ∧
    wv s₀.mem (s₀.gpr .r31) (8 * cwP s₀) (cwQ s₀) = 2 ^ (128 * cwQ s₀) % vQ s₀

/-- Memory apart from the working space, as at entry. -/
theorem wv_entry {s₀ s t : State} (hF : Front s₀ s) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hZ : 256 ≤ cZ s₀) {S : Addr} {n d : Nat} (hS : S.toNat + (d + 8 * n) ≤ 2 ^ 64)
    (hsep : ∀ x, ofs S x < d + 8 * n → cZ s₀ ≤ ofs (cS s₀) x) : wv t.mem S d n = wv s₀.mem S d n := by
  obtain O : Outside (cS s₀) 0 (cZ s₀) s₀.mem t.mem :=
    (hF.mem.mono (by omega_arith) (by omega_arith)).trans (ho.mono (by omega_arith) (by omega_arith))
  exact wv_congr2 fun i hi => Pub.Outside.word_apart O hsep (by omega_arith) (by omega_arith) hS

/-- Where `r2Copy` copies `R² mod p` from, from `R2F`, under the mask of `b`. -/
theorem R2F.pS {s₀ s t : State} {b : Bool} (F : R2F s₀) (hP : PF s₀)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r31) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask b) :
    R2S false t (cS s₀) (s₀.gpr .r31) (cZ s₀) (cwP s₀) (cpL s₀) b where
  src := by
    rw [ho.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith), hhd]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
  pl := nofun
  pl1 := hP.p1
  pl2 := by have := hP.pk; have := hP.k1024; omega_arith
  hS := by have := F.hS; omega_arith
  rd i hi := by rw [hrw]; exact F.rd i (by omega_arith)
  sep x hx := F.sep x (by omega_arith)
  r26 := h26

/-- Where `r2Copy` copies `R² mod q` from, from `R2F`: after `p`'s words. -/
theorem R2F.qS {s₀ s t : State} {b : Bool} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r31) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask b) :
    R2S true t (cS s₀) (off (s₀.gpr .r31) (8 * cwP s₀)) (cZ s₀) (cwQ s₀) (cpL s₀) b where
  src := by
    rw [ho.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith), hhd]
    simp only [↓reduceIte]
  pl _ := by rw [ho.word (Or.inl (by unfold oPLen; omega_arith)) (by unfold oPLen; omega_arith)]; exact hF.hPL
  pl1 := hP.p1
  pl2 := by have := hP.pk; have := hP.k1024; omega_arith
  hS := by have := F.hS; have := toNat_off_le (s₀.gpr .r31) (8 * cwP s₀); omega_arith
  rd i hi := by rw [hrw, off_off, ← Nat.mul_add]; exact F.rd (cwP s₀ + i) (by omega_arith)
  sep x hx := F.sep x (by
    rcases ofs_rebase (s₀.gpr .r31) x (o := 8 * cwP s₀) (by have := F.hS; omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · change ofs (off (s₀.gpr .r31) (8 * cwP s₀)) x < _ at hx; omega_arith
    · omega_arith)
  r26 := h26

/-- `R2C` for `p`: under the mask, the cached value is `R² mod p`. -/
theorem R2F.p {s₀ s t : State} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r31) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask (cb s₀)) :
    R2C false t (cS s₀) (s₀.gpr .r31) (cZ s₀) (cwP s₀) (mP s₀) (cpL s₀) (cb s₀) where
  toR2S := F.pS hP hhd ho hrw h26
  val hb := by
    rw [wv_entry hF ho (by have := hP.room; unfold slot hdrBytes at this; omega_arith)
      (by have := F.hS; omega_arith) fun x hx => F.sep x (by omega_arith)]
    simp only [mP, hb, ↓reduceIte]; exact (F.val hb).1
  three hb := by simp [mP, hb]

/-- `R2C` for `q`. -/
theorem R2F.q {s₀ s t : State} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r31) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask (cb s₀)) :
    R2C true t (cS s₀) (off (s₀.gpr .r31) (8 * cwP s₀)) (cZ s₀) (cwQ s₀) (mQ s₀) (cpL s₀) (cb s₀) where
  toR2S := F.qS hP hF hhd ho hrw h26
  val hb := by
    rw [wv_off, Nat.add_zero, wv_entry hF ho (by have := hP.room; unfold slot hdrBytes at this; omega_arith)
      (by have := F.hS; omega_arith) fun x hx => F.sep x (by omega_arith)]
    simp only [mQ, hb, ↓reduceIte]; exact (F.val hb).2
  three hb := by simp [mQ, hb]

theorem xval {m m' : Mem} {B : Addr} {a n d w : Nat} (h : Outside B a n m m') (hd : d + 8 * w ≤ a ∨ a + n ≤ d)
    (hd' : d + 8 * w ≤ 2 ^ 64) : Mont.val32 m' B d (2 * w) = Mont.val32 m B d (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, h.wv hd hd']

/-- The registers of `mid1`. -/
def mid1Regs : List Reg := loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg) ++
  ([.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] : List Reg) ++
  (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs) ++
  (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs)

/-- What `X` holds after `loadX` and `checks`. -/
structure XA (s₀ s t : State) : Prop where
  r26 : t.gpr .r26 = bmask (cb s₀)
  v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64
  v4 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = mP s₀
  v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀
  v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem

/-- `loadX` and `checks`, after the front. -/
theorem mid1A_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hc : ∀ t, XA s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks c)) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  obtain eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  obtain eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  obtain fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  obtain hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  have k0 := hF.keep
  obtain rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  obtain hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  refine wp_reassoc2 (WP.seq (WP.mono (phaseA_ok hF.scr (by omega_arith) k64 k1024 hF.r23 hF.r10 hF.r21 hF.r29 hF.r11
    hF.hN hF.hNL hF.hP hF.hPL hF.hQ hF.hQL hF.hIn hF.hQI p1 pk q1 qk (by rw [rd0]; exact hP.rN) hP.sN
    (by rw [rd0]; exact hP.rP) hP.sP (by rw [rd0]; exact hP.rQ) hP.sQ (by rw [rd0]; exact hP.rI) hP.sI
    (by rw [rd0]; exact hP.rQI) hP.sQI) fun t₁ ⟨⟨t26, v0, w0, v4, v5, v7, O1, a10⟩, k1⟩ => ?_))
  rw [hb0 hP.sN, hb0 hP.sI, hb0 hP.sP, hb0 hP.sQ, hb0 hP.sQI] at t26 v4 v5 v7
  exact hc t₁ ⟨t26, v0, w0, v4, v5, v7, O1.mono (by omega_arith) (by omega_arith)⟩ a10 k1

/-- What `X` holds after `loadIn`: the input again in array 6. -/
structure XL (s₀ s t : State) extends XA s₀ s t where
  v6 : wv t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀

/-- `loadIn`, after `X`'s checks. -/
theorem mid1L_ok {s₀ s t₁ : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (X : XA s₀ s t₁) (h10 : t₁.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)) {rs : List Reg} (k1 : Keep rs s t₁)
    (h21 : Reg.r21 ∉ rs) (h23 : Reg.r23 ∉ rs) (h29 : Reg.r29 ∉ rs) (h11 : Reg.r11 ∉ rs)
    (hc : ∀ t, XL s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      Keep (rs ++ ([.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] : List Reg)) s t → WP isa c t Q) :
    WP isa (.seq loadIn c) t₁ Q := by
  have hn := hP.nw
  have room := hP.room
  obtain k64 := hP.k64; have k1024 := hP.k1024
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5; have eX6 := e (cwX s₀) 6
  obtain eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  obtain hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
  have k0 := hF.keep
  obtain rd1 : t₁.rd ++ t₁.wr = s₀.rd ++ s₀.wr := by rw [k1.rd, k1.wr, k0.rd, k0.wr]
  obtain hd1 : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega_arith)
  unfold loadIn
  refine WP.seq (WP.mono (loadOne_ok (j := 6) (A := s₀.gpr .r7) (L := ck s₀) (hF.scr.congr k1.wr) (by omega_arith)
    (by decide) hwX ((k1.gpr _ h23).trans hF.r23) h10 ((k1.gpr _ h21).trans hF.r21) ((k1.gpr _ h29).trans hF.r29)
    ((k1.gpr _ h11).trans hF.r11) (by decide) (by decide) (by rw [hd1 _ (by decide)]; exact hF.hIn)
    (by rw [hd1 _ (by decide)]; exact hF.hNL) (by omega_arith) (by omega_arith) (by rw [rd1]; exact hP.rI) hP.sI)
    fun t ⟨⟨v6, _, O, t10⟩, k2⟩ => ?_)
  obtain hb : Spec.Rsa.bytesAt t₁.mem (s₀.gpr .r7) (ck s₀) = Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (ck s₀) := by
    rw [bytesAt_out X.out (by omega_arith) hP.sI, bytesAt_out hF.mem (by omega_arith) hP.sI]
  refine hc t ⟨⟨(k2.gpr _ (by decide)).trans X.r26,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v0,
    by rw [O.word (Or.inl (by omega_arith)) (by omega_arith)]; exact X.w0,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v4,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v5,
    by rw [xval O (Or.inr (by omega_arith)) (by omega_arith)]; exact X.v7,
    X.out.trans (O.mono (by omega_arith) (by omega_arith))⟩, by rw [← Pre.val32_eq_wv, v6, hb]⟩ t10 (k1.trans k2)

/-- What `p`'s working space holds after its power. -/
structure XP (s₀ s t : State) extends XL s₀ s t where
  p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀
  p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP s₀

/-- `m₁`, after `X`'s checks. -/
theorem mid1B_ok {pc : Bool} {s₀ s t₁ : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀)
    (hF : Front s₀ s) (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31)
    (X : XL s₀ s t₁) {rs : List Reg} (k1 : Keep rs s t₁) (h23 : Reg.r23 ∉ rs) (h27 : Reg.r27 ∉ rs)
    (h28 : Reg.r28 ∉ rs)
    (hc : ∀ t, XP s₀ s t → Keep (rs ++ (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs)) s t →
      WP isa c t Q) :
    WP isa (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen) c)) t₁ Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  obtain eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  obtain eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  obtain fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  obtain hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  have k0 := hF.keep
  obtain rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  obtain hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  obtain eX4 := e (cwX s₀) 4; have eX6 := e (cwX s₀) 6
  obtain hd1 : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega_arith)
  obtain hb1 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₁.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out X.out (by omega_arith) hs']; exact hb0 hs'
  obtain rd1 : t₁.rd ++ t₁.wr = s₀.rd ++ s₀.wr := by rw [k1.rd, k1.wr, rd0]
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 4) (oA := oPa s₀) (L := cpL s₀) (k := ck s₀)
    (D := stackArg s₀ 2) (Pv := mP s₀) (Cv := vC s₀) (hF.scr.congr k1.wr) (by omega_arith) (Nat.le_refl _)
    rfl (by unfold wsWords; omega_arith) hwX (by decide) ((k1.gpr _ h23).trans hF.r23) ((k1.gpr _ h27).trans hF.r27)
    ((k1.gpr _ h28).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd1 _ (by decide)]; exact hF.hBP) (by rw [hd1 _ (by decide)]; exact hF.hPL)
    (by rw [hd1 _ (by decide)]; exact hF.hNL)
    (by rw [hd1 _ (by decide)]; exact hF.hDP) p1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [rd1]; exact hP.rDP) hP.sDP
    X.v4 mPb (by omega_arith) mPo X.v6 (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _))
    (fun hp => by subst hp; exact ⟨_, _, _, (hR2 rfl).1.p hP hF (hR2 rfl).2 X.out rd1 X.r26⟩))
    fun t₂ ⟨⟨p0, p4, O2, _, _, _, _⟩, k2⟩ => ?_))
  rw [hb1 hP.sDP] at p4
  exact hc t₂ ⟨⟨⟨(k2.gpr _ (by decide)).trans X.r26,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v0,
    by rw [O2.word (Or.inl (by omega_arith)) (by omega_arith)]; exact X.w0,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v4,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v5,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v7,
    X.out.trans (O2.mono (by omega_arith) (by omega_arith))⟩,
    by rw [O2.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v6⟩, p0, p4⟩ (k1.trans k2)

theorem mid1_ok {pc : Bool} {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31)
    (hc : ∀ t, t.gpr .r26 = bmask (cb s₀) →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1 →
      word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64 →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀ →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP s₀ →
      Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vC s₀ ^ vDQ s₀ % mQ s₀ →
      t.gpr .r10 = off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0) →
      t.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2)) →
      Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem →
      Keep mid1Regs s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks (.seq loadIn (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen)
      (.seq (.block (setupP oBQ oQLen)) (.seq (powerG pc true 5 oDQ oQLen) c))))))) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  obtain eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  obtain eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  obtain fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  obtain hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
  have k0 := hF.keep
  obtain rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  obtain hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  refine mid1A_ok hP hF fun t₀ X₀ a10 k0' => ?_
  refine mid1L_ok hP hF X₀ a10 k0' (by decide) (by decide) (by decide) (by decide) fun t₁ X _ k1 => ?_
  refine mid1B_ok hP hF hR2 X k1 (by decide) (by decide) (by decide) fun t₂ Y k12 => ?_
  obtain hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    Y.out.word (Or.inl hd) (by omega_arith)
  obtain hb2 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₂.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out Y.out (by omega_arith) hs']; exact hb0 hs'
  -- `m₂`.
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 5) (oA := oQa s₀) (L := cqL s₀) (k := ck s₀)
    (D := stackArg s₀ 4) (Pv := mQ s₀) (Cv := vC s₀) (hF.scr.congr k12.wr) (by omega_arith) (by omega_arith)
    rfl (by unfold wsWords; omega_arith) hwX (by decide) ((k12.gpr _ (by decide)).trans hF.r23)
    ((k12.gpr _ (by decide)).trans hF.r27)
    ((k12.gpr _ (by decide)).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd2 _ (by decide)]; exact hF.hBQ) (by rw [hd2 _ (by decide)]; exact hF.hQL)
    (by rw [hd2 _ (by decide)]; exact hF.hNL)
    (by rw [hd2 _ (by decide)]; exact hF.hDQ) q1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [k12.rd, k12.wr, rd0]; exact hP.rDQ) hP.sDQ
    Y.v5 mQb (by omega_arith) mQo Y.v6 (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _))
    (fun hp => by subst hp; exact ⟨_, _, _, (hR2 rfl).1.q hP hF (hR2 rfl).2 Y.out (by rw [k12.rd, k12.wr, rd0]) Y.r26⟩))
    fun t₃ ⟨⟨_, q4, O3, c10, _, c29, _⟩, k3⟩ => ?_))
  rw [hb2 hP.sDQ] at q4
  obtain k13 := k12.trans k3
  refine hc t₃ ((k3.gpr _ (by decide)).trans Y.r26)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v0)
    (by rw [O3.word (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.w0)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v5)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v7)
    (by rw [val32_off_eq O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.p0)
    (by rw [val32_off_eq O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.p4) q4 c10 c29
    (Y.out.trans (O3.mono (by omega_arith) (by omega_arith))) k13

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-! ### `Bignum.PPC64LE.CrtPhaseE`, which only this module used -/

section

/-!
# The RSA private-key operation on PPC64LE: the result

`phaseE_ok`: `recombineX`, then `out` and `k` from the header, and
`output`: `out` holds `q h + m₂` (or zeros) and `r3` the mask's bit.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `recombineX`, then the output, under the mask of `b` in `r26`. -/
theorem phaseE_ok {s : State} {BX O : Addr} {Z oP oQ pL qL wX k Qv H M2 : Nat} {b : Bool}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 24 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 24 ≤ Z) (hXQ : slot wX 8 ≤ oQ)
    (hpq : wsWords pL + wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL) (hq' : qL < 2 ^ 60)
    (hM : Mont.val32 s.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1)
    (hM0 : word s.mem BX (slot wX 0) = BitVec.allOnes 64)
    (hq : Mont.val32 s.mem BX (slot wX 5) (2 * wX) = Qv) (hqb : Qv < 2 ^ (64 * wsWords qL))
    (hH : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = H)
    (hm2 : Mont.val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2)
    (hO : word s.mem BX oOut = off O 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * wX) (ho : Scr s O k) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs BX x)
    (h26 : s.gpr .r26 = bmask b) (hv : b = true → Qv * H + M2 < 256 ^ k) :
    WP isa (.seq recombineX (.seq (.block [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut,
      .load .d .r28 .r23 oNLen]) PublicChecked.output)) s fun t =>
      (Spec.Rsa.bytesAt t.mem O k = Spec.Rsa.i2osp (if b then Qv * H + M2 else 0) k ∧
        t.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0) ∧
        Frame [⟨off BX 256, Z - 256⟩, ⟨O, k⟩] s.mem t.mem) ∧
      Keep (recXRegs ++ ([.r0, .r3, .r15, .r16, .r17, .r27, .r28] : List Reg)) s t := by
  have hn := hs.nowrap
  have hno := ho.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eX0 := e wX 0; have eX2 := e wX 2; have eX8 := e wX 8
  refine WP.seq (WP.mono (recombineX_ok hs hPZ hXP hQZ hXQ hpq hwX h23 h27 h28 hBP hPL hBQ hQL hp1 hp' hq1 hq'
    hM hM0 hq hqb hH hm2) fun s₁ ⟨⟨v4, o1⟩, k1⟩ => ?_)
  obtain O1 : Outside BX (slot wX 2) (6 * (8 * (wX + 2))) s.mem s₁.mem := by
    intro x hx
    refine o1 x fun r hr => ?_
    change ofs BX x < r.1 ∨ r.1 + r.2 ≤ ofs BX x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    change ofs BX x < slot wX 2 ∨ slot wX 2 + 6 * (8 * (wX + 2)) ≤ ofs BX x at hx
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp only [e] at hx ⊢ <;> omega_arith
  obtain hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd => O1.word (Or.inl (by omega_arith)) (by omega_arith)
  obtain e0 : off BX 0 = BX := BitVec.add_zero BX
  obtain hO' : s₁.mem.readW BX 64 = off O 0 := by
    obtain h0 : word s₁.mem BX 0 = off O 0 := (hd 0 (by decide)).trans hO
    rw [← e0]; exact h0
  obtain ld0 : InRegions (s₁.rd ++ s₁.wr) BX 8 := by
    obtain e0' : Mont.off BX 0 = BX := BitVec.add_zero BX
    have := (hs.congr k1.wr).ld (show 0 + 8 ≤ Z by omega_arith); rwa [e0'] at this
  obtain hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by
    show word s₁.mem BX 16 = _; rw [hd 16 (by decide)]; exact hK
  refine WP.seq (WP.mono (WP.keep [.r10, .r29, .r27, .r28] (Q := fun t =>
    t.gpr .r10 = off BX (slot wX 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ t.gpr .r27 = off O 0 ∧
      t.gpr .r28 = BitVec.ofNat 64 k ∧ t.mem = s₁.mem) (by
    prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28,
      (k1.gpr .r23 (by decide)).trans h23, oOut, oNLen, ld0,
      (hs.congr k1.wr).ld (show 16 + 8 ≤ Z by omega_arith), hO', hK', BitVec.add_zero]) (by decide))
    fun s₂ ⟨⟨a10, a29, a27, a28, m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  refine WP.mono (Pub.output_ok (b := b) (hs.congr k12.wr) (ho.congr k12.wr) a10 a29 a28 a27
    (by rw [k12.gpr _ (by decide), h26]) hk hkw (by omega_arith) hsepO)
    fun t ⟨⟨hb, oo, t3⟩, k3⟩ => ⟨⟨?_, t3, ?_⟩, (k12.trans k3).mono⟩
  · cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      rw [Pub.zero_bytes hb, VG.Proof.Bignum.i2osp_zero']
    · simp only [↓reduceIte] at hb ⊢
      rw [m2] at hb
      exact Pub.out_bytes hkw v4 (hv rfl) hb
  · refine Pub.frame_two (m₁ := s₂.mem) ?_ oo (by omega_arith)
    rw [m2]
    exact O1.mono (by omega_arith) (by have := slot_le (w := wX) (j := 7) (by decide); simp only [e] at this ⊢; omega_arith)

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: the recombination

`mid2_ok`: from the powers, `h` (`phaseD_ok`), then `q h + m₂` written to
`out` under the mask (`phaseE_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

variable {pc : Bool}

/-- `m₁`, `m₂`, `h` and the result. -/
abbrev vm1 (s₀ : State) : Nat := vC s₀ ^ vDP s₀ % mP s₀
abbrev vm2 (s₀ : State) : Nat := vC s₀ ^ vDQ s₀ % mQ s₀
abbrev vh (s₀ : State) : Nat := (vm1 s₀ + mP s₀ - vm2 s₀ % mP s₀) % mP s₀ * mQI s₀ % mP s₀
abbrev vr (s₀ : State) : Nat := if cb s₀ then mQ s₀ * vh s₀ + vm2 s₀ else 0

theorem frame_of_out {m m' : Mem} {B : Addr} {o n : Nat} (h : Outside B o n m m') (hn : o + n ≤ 2 ^ 64)
    (hn0 : 0 < n) :
    Frame [⟨off B o, n⟩] m m' := by
  intro x hx
  refine h x ?_
  obtain hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  obtain e := ofs_rebase B x (o := o) (by omega_arith)
  change ¬ ofs (off B o) x + 1 ≤ n at hc
  change ofs B x < o ∨ o + n ≤ ofs B x
  rcases e with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith

/-- The registers of `mid2`. -/
def mid2Regs : List Reg := [.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] ++ recRegs ++
  (recXRegs ++ [.r0, .r3, .r15, .r16, .r17, .r27, .r28])

/-- What the working spaces hold after `h`. -/
structure XR (s₀ s u : State) : Prop where
  r26 : u.gpr .r26 = bmask (cb s₀)
  v0 : Mont.val32 u.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  w0 : word u.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64
  v5 : Mont.val32 u.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀
  h4 : Mont.val32 u.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vh s₀
  q4 : Mont.val32 u.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem u.mem

/-- `exportM2`, `setupP` and `recombineP`: `h`. -/
theorem mid2A_ok {pc : Bool} {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀)
    (hF : Front s₀ s) (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31)
    (t26 : t.gpr .r26 = bmask (cb s₀))
    (v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1)
    (w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64)
    (v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀)
    (v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀)
    (p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀)
    (p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vm1 s₀)
    (q4 : Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀)
    (O1 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem) (k1 : Keep mid1Regs s t)
    (hc : ∀ u, XR s₀ s u →
      Keep (mid1Regs ++ (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs)) s u → WP isa c u Q) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq (recombinePG pc) c))) t Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX2 := e (cwX s₀) 2; have eX5 := e (cwX s₀) 5
  obtain eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7
  obtain eX8 := e (cwX s₀) 8
  obtain eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  obtain eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  obtain hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQle, mQIP, mQIb⟩ := masked_facts hP
  obtain hdt : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega_arith)
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) mQle
  obtain hnw : cwP s₀ * nChunks ((ck s₀ + 7) / 8) (cwP s₀) ≤ cwX s₀ := by
    rw [dX]; exact chunks_le (by rw [dP]; unfold wsWords; omega_arith) (by
      rw [dP]; exact Nat.max_le.mpr ⟨by omega_arith, Nat.div_le_div_right (by omega_arith)⟩)
  -- `h`.
  refine wp_reassoc3 (WP.seq (WP.mono (phaseD_ok (oP := oPa s₀) (oQ := oQa s₀) (wX := cwX s₀) (pL := cpL s₀)
    (qL := cqL s₀) (Pv := mP s₀) (m1 := vm1 s₀) (M2 := vm2 s₀) (QI := mQI s₀) (hF.scr.congr k1.wr) (by omega_arith)
    (Nat.le_refl _) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hwX
    ((k1.gpr _ (by decide)).trans hF.r23) ((k1.gpr _ (by decide)).trans hF.r27)
    ((k1.gpr _ (by decide)).trans hF.r28) (by rw [hdt _ (by decide)]; exact hF.hBP)
    (by rw [hdt _ (by decide)]; exact hF.hPL) (by rw [hdt _ (by decide)]; exact hF.hBQ)
    (by rw [hdt _ (by decide)]; exact hF.hQL) (by rw [hdt _ (by decide)]; exact hF.hNL) p1 (by omega_arith) q1
    (by omega_arith) (Nat.le_of_lt qk) (by omega_arith) hnw p0 (by omega_arith) mPo p4 (Nat.mod_lt _ (by omega_arith)) q4 hm2b v7 mQIb mQIP
    (fun hp => by subst hp; exact ⟨_, _, _, (hR2 rfl).1.p hP hF (hR2 rfl).2 O1 (by rw [k1.rd, k1.wr, hF.keep.rd, hF.keep.wr]) t26⟩))
    fun t₂ ⟨⟨h4, OD⟩, k2⟩ => ?_))
  obtain k12 := k1.trans k2
  obtain FD : Frm (cS s₀) [(slot (cwX s₀) 6, 8 * cwX s₀), (oPa s₀, slot (cwP s₀) 24)] t.mem t₂.mem :=
    fun x hx => OD x hx
  obtain fr : ∀ {d n : Nat}, d + n ≤ slot (cwX s₀) 6 ∨ (slot (cwX s₀) 7 ≤ d ∧ d + n ≤ oPa s₀) ∨ oQa s₀ ≤ d →
      ∀ r ∈ [(slot (cwX s₀) 6, 8 * cwX s₀), (oPa s₀, slot (cwP s₀) 24)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d n hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  obtain hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd => by
    rw [FD.word_eq (fr (Or.inl (by omega_arith))) (by omega_arith)]; exact hdt d hd
  obtain xv : ∀ {d : Nat}, d + 8 * cwX s₀ ≤ slot (cwX s₀) 6 ∨ (slot (cwX s₀) 7 ≤ d ∧ d + 8 * cwX s₀ ≤ oPa s₀) →
      Mont.val32 t₂.mem (cS s₀) d (2 * cwX s₀) = Mont.val32 t.mem (cS s₀) d (2 * cwX s₀) := fun hd => by
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv, FD.wv_eq (fr (by omega_arith)) (by omega_arith)]
  obtain hq4 : Mont.val32 t₂.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀ := by
    rw [Pre.val32_eq_wv, wv_off, FD.wv_eq (fr (Or.inr (Or.inr (by omega_arith)))) (by omega_arith), ← wv_off,
      ← Pre.val32_eq_wv]; exact q4
  obtain OT : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t₂.mem := by
    refine O1.trans fun x hx => FD x fun r hr => ?_
    change ofs (cS s₀) x < 256 ∨ 256 + (cZ s₀ - 256) ≤ ofs (cS s₀) x at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  exact hc t₂ ⟨(k2.gpr _ (by decide)).trans t26, by rw [xv (Or.inl (by omega_arith))]; exact v0,
    by rw [FD.word_eq (fr (Or.inl (by omega_arith))) (by omega_arith)]; exact w0,
    by rw [xv (Or.inl (by omega_arith))]; exact v5, h4, hq4, OT⟩ k12

theorem mid2_ok {pc : Bool} {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀)
    (hF : Front s₀ s) (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31)
    (t26 : t.gpr .r26 = bmask (cb s₀))
    (v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1)
    (w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64)
    (v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀)
    (v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀)
    (p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀)
    (p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vm1 s₀)
    (q4 : Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀)
    (O1 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem) (k1 : Keep mid1Regs s t)
    (hc : ∀ u, Spec.Rsa.bytesAt u.mem (s₀.gpr .r3) (ck s₀) = Spec.Rsa.i2osp (vr s₀) (ck s₀) →
      u.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) →
      Frame [⟨off (cS s₀) 256, cZ s₀ - 256⟩, ⟨s₀.gpr .r3, ck s₀⟩] s.mem u.mem →
      Keep (mid1Regs ++ mid2Regs) s u → WP isa c u Q) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq (recombinePG pc) (.seq recombineX
      (.seq (.block [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen])
      (.seq PublicChecked.output c)))))) t Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  obtain eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX2 := e (cwX s₀) 2; have eX5 := e (cwX s₀) 5
  obtain eX8 := e (cwX s₀) 8
  obtain eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  obtain eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  obtain hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  obtain hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQle, mQIP, mQIb⟩ := masked_facts hP
  obtain hdt : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega_arith)
  obtain hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) mQle
  refine mid2A_ok hP hF hR2 t26 v0 w0 v5 v7 p0 p4 q4 O1 k1 fun t₂ R k12 => ?_
  obtain hdR : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    R.out.word (Or.inl hd) (by omega_arith)
  obtain hv : cb s₀ = true → mQ s₀ * vh s₀ + vm2 s₀ < 256 ^ ck s₀ := fun hb => by
    obtain ⟨_, _, _, hpq', hp1', _, hq1', _⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
    obtain hN := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
    unfold vh vm1 vm2 mQ mP mQI
    simp only [hb, ↓reduceIte]
    have := VG.Proof.Bignum.crt_recombine_bound (p := vP s₀) (q := vQ s₀) (mp := vC s₀ ^ vDP s₀ % vP s₀)
      (mq := vC s₀ ^ vDQ s₀ % vQ s₀) (qi := vQI s₀) (Nat.lt_trans Nat.zero_lt_one hp1')
      (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hq1'))
    rw [hpq'] at this
    omega_arith
  -- `q h + m₂`, written out.
  refine wp_reassoc3 (WP.seq (WP.mono (phaseE_ok (O := s₀.gpr .r3) (k := ck s₀) (b := cb s₀) (Qv := mQ s₀)
    (H := vh s₀) (M2 := vm2 s₀) (oP := oPa s₀) (oQ := oQa s₀) (hF.scr.congr k12.wr) (by omega_arith) (Nat.le_refl _)
    (by omega_arith) (by omega_arith) pq hwX ((k12.gpr _ (by decide)).trans hF.r23) ((k12.gpr _ (by decide)).trans hF.r27)
    ((k12.gpr _ (by decide)).trans hF.r28) (by rw [hdR _ (by decide)]; exact hF.hBP)
    (by rw [hdR _ (by decide)]; exact hF.hPL) (by rw [hdR _ (by decide)]; exact hF.hBQ)
    (by rw [hdR _ (by decide)]; exact hF.hQL) p1 (by omega_arith) q1 (by omega_arith)
    R.v0 R.w0 R.v5 mQb R.h4 R.q4
    (by rw [hdR _ (by decide)]; exact hF.hOut) (by rw [hdR _ (by decide)]; exact hF.hNL) (by omega_arith) (by omega_arith)
    (hP.out.congr ((hF.keep.trans k12).wr)) hP.sepO R.r26 hv)
    fun u ⟨⟨ub, u3, uF⟩, k3⟩ => ?_))
  refine hc u ub u3 ?_ (by have := k12.trans k3; rwa [List.append_assoc] at this)
  exact ((frame_of_out R.out (by omega_arith) (by omega_arith)).mono (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp)).trans uF

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: correctness

`crt` saves the nonvolatile registers, stores its arguments and sets up `X`
(`front_ok`), computes the result (`mid1_ok`, `mid2_ok`) and restores the
registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem pres_cases : ∀ r ∈ preserved, (∀ i < 18, r ≠ Crt.saved i) →
    r ∉ frontRegs ∧ r ∉ mid1Regs ++ mid2Regs := by
  decide

theorem toNat_flag (b : Bool) : BitVec.ofNat 64 (if b then 1 else 0) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

/-- `crtG pc`: with `pc`, given the cached values (`R2F`). -/
theorem crt_wp (pc : Bool) (s : State) {X : List Region} (h : preCore (baseRd s ++ X) s)
    (hR : pc = true → R2F s) :
    WP isa (crtG pc) s fun t => abiPreserved s t ∧ postCore s t := by
  have hP := pre_factsG h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  unfold crtG
  refine WP.seq (WP.mono (front_okG pc s h) fun s₁ ⟨hF, hhd⟩ => ?_)
  have hR2 : pc = true → R2F s ∧ word s₁.mem (cS s) oR2 = s.gpr .r31 := fun hp => ⟨hR hp, hhd hp⟩
  refine mid1_ok hP hF hR2 fun t t26 v0 w0 v5 v7 p0 p4 q4 _ _ O1 k1 => ?_
  refine mid2_ok hP hF hR2 t26 v0 w0 v5 v7 p0 p4 q4 O1 k1 fun u ub u3 uF ku => ?_
  have kfu := hF.keep.trans ku
  have hS : (⟨cS s, cZ s⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hin : ∀ i < 18, InRegions u.wr (off (savW (cS s)) (8 * i)) 8 := fun i hi => by
    rw [kfu.wr]
    show InRegions _ (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, hS, Offset.contains_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 18, u.mem.readW (off (savW (cS s)) (8 * i)) 64 = s.gpr (Crt.saved i) := fun i hi => by
    rw [uF.readW (r := ⟨off (savW (cS s)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
    · exact hF.sav i hi
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · show Region.Disjoint ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩
          ⟨cS s + BitVec.ofNat 64 256, _⟩
        rw [Offset.add_add]
        exact Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by show _ ≤ 2 ^ 64; omega_arith)
      · have sub : Region.Sub ⟨off (savW (cS s)) (8 * i), 8⟩ ⟨cS s, cZ s⟩ := by
          show Region.Sub ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩ _
          rw [Offset.add_add]; exact Offset.sub_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith)
        have dOS' : (⟨s.gpr .r3, ck s⟩ : Region).Disjoint ⟨cS s, cZ s⟩ := by
          show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region).Disjoint _
          rw [← hOL]; exact dOS
        exact dOS'.symm.sub_left sub
  refine WP.mono (restore_ok u (S := cS s) (v := fun i => s.gpr (Crt.saved i))
    (by rw [ku.gpr .r23 (by decide)]; exact hF.r23) hin hsav)
    fun w ⟨wrs, wot, wm, _, _, wsp, wlr⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Crt.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact wrs i hi
    · have hn : ∀ i < 18, r ≠ Crt.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_cases r hr hn
      rw [wot r hn, ku.gpr r h2, hF.keep.gpr r h1]
  · rw [wsp, kfu.sp]
  · rw [wlr, kfu.lr]
  · show Spec.Rsa.written w.mem (s.gpr .r3) (ck s) ((w.gpr .r3).setWidth 32) _
    rw [wm, wot .r3 (by decide), u3]
    refine VG.Proof.Bignum.crtWritten_of (VG.Proof.Bignum.bytesAt_length _ _ _) ub (toNat_flag _)
      (fun hv => ?_) (fun hv => ?_)
    · have hcb : cb s = (decide (vC s < vN s) && decide (vQI s < vP s) && decide (vP s * vQ s = vN s)) := by
        simp only [cb, crtMask, hv, Bool.true_and]
      refine ⟨?_, ?_⟩
      · rw [hcb]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
      · unfold vr
        cases hb : cb s
        · rfl
        · obtain ⟨_, _, _, _, hp1', _, _, _⟩ := mask_true hP.k64
            (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
            hb
          simp only [↓reduceIte, VG.Proof.Bignum.crtResult]
          rw [VG.Proof.Bignum.crt_coefficient_natural (Nat.lt_trans Nat.zero_lt_one hp1')]
          unfold vh vm1 vm2 mQ mP mQI
          simp only [hb, ↓reduceIte]
          exact Nat.add_comm _ _
    · have hcb : cb s = false := by simp only [cb, crtMask, hv, Bool.false_and]
      exact ⟨hcb, by unfold vr; rw [hcb]; rfl⟩

/-- A cache of two numbers of `a` and `b` words, as their words. -/
theorem cache_words {m : Mem} {P : Addr} {a b X Y : Nat}
    (h : Spec.Rsa.wordsAt m P (a + b) = Spec.Rsa.toWords X a ++ Spec.Rsa.toWords Y b)
    (hX : X < 2 ^ (64 * a)) (hY : Y < 2 ^ (64 * b)) : wv m P 0 a = X ∧ wv m P (8 * a) b = Y := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, List.range_add, List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hX]
    refine wv_of_words fun i hi => ?_
    show (m.readW (P + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hY]
    refine wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (P + BitVec.ofNat 64 (8 * a + 8 * i)) 64).toNat = _
    rw [show 8 * a + 8 * i = 8 * (a + i) by omega_arith, this, BitVec.toNat_ofNat]

/-- `R2F` from `fnContractP`'s precondition. -/
theorem r2F_of {s : State} (h : fnContractP.pre s) : R2F s where
  hS := h.2.2.2.1
  rd i hi := by
    have hi' : i < wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat := hi
    have := h.2.2.2.1; simp only [r2R] at this
    exact ⟨r2R s, List.mem_append_left _ (by rw [h.1.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)),
      Offset.contains_base _ (show 8 * i + 8 ≤ 8 * (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat) by
        omega_arith) (by omega_arith)⟩
  sep x hx := Pub.sep_of_disjoint h.2.2.1 x hx
  val hb := by
    have hw := h.2.2.2.2
    have ew : ∀ n, Spec.Rsa.primeWords n = wsWords n := fun _ => rfl
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length, ew] at hw
    obtain ⟨mP1, _, mQ1, _, mPb, mQb, _, _, _⟩ := masked_facts (pre_factsG h.1)
    have eP : mP s = vP s := by simp only [mP, hb, ↓reduceIte]
    have eQ : mQ s = vQ s := by simp only [mQ, hb, ↓reduceIte]
    rw [eP] at mP1 mPb; rw [eQ] at mQ1 mQb
    exact cache_words hw (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mP1)) mPb)
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mQ1)) mQb)

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t :=
  crt_wp false s (preCore_nil h) nofun

theorem fn_correctP (s : State) (h : fnContractP.pre s) :
    ∃ tr t, Exec isa crtP s tr t ∧ abiPreserved s t ∧ fnContractP.post s t :=
  crt_wp true s h.1 fun _ => r2F_of h

end VG.Proof.Bignum.PPC64LE.Crt
