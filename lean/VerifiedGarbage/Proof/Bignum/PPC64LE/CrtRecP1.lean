module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtR2
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

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
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  have hsl : ∀ j, j < 24 → slot w j + 8 * (w + 2) ≤ slot w 24 := fun j hj => by
    simp only [e]
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 24 by omega_arith)
    rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
  have hsep : slot w a + 8 * w ≤ slot w b ∨ slot w b + 8 * w ≤ slot w a := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · left; simp only [e]
      have := Nat.mul_le_mul_right (8 * (w + 2)) (show a + 1 ≤ b by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
    · right; simp only [e]
      have := Nat.mul_le_mul_right (8 * (w + 2)) (show b + 1 ≤ a by omega_arith)
      rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
  have la := hsl a ha; have lb := hsl b hb
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 b) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) a) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) hw hw' (by omega_arith) (by omega_arith) hsep) fun t ⟨⟨hw8, out⟩, k3⟩ => ?_)
  have hm : s₂.mem = s.mem := by rw [m2, m1]
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
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wP 0; have eA1 := e wP 1; have eA2 := e wP 2; have eA4 := e wP 4; have eA7 := e wP 7
  have eA9 := e wP 9; have eA8 := e wP 24
  have eX6 := e wX 6; have eX8 := e wX 8
  have hsA := hs.sub hA
  have hnA := hsA.nowrap
  have hlow : (word s.mem (off BX oA) (slot wP 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wP by omega_arith), ← Pre.val32_eq_wv, hP, hPodd]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok hsA h10 (by omega_arith) hlow) fun s₁ ⟨⟨i12, iinv, m1'⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 1) fun s₂ ⟨⟨a5, m2'⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 2) fun s₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 3) fun s₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm4 : s₄.mem = s.mem := by rw [m4, m3, m2', m1']
  have g12 : s₄.gpr .r12 = s₁.gpr .r12 := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide)]
  have hsepB : ∀ S : Addr, (∀ x, ofs S x < 8 * wP → Z ≤ ofs BX x) →
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
  have k15 := k14.trans k5
  rw [hm4, hP] at r1
  rw [hm4] at out5
  have o5 : Mont.Outside (off BX oA) (slot wP 1) (24 * (wP + 2)) s.mem s₅.mem := out5
  have v0₅ : val32 s₅.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o5.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have v4₅ : val32 s₅.mem (off BX oA) (slot wP 4) (2 * wP) = m1 := by
    rw [o5.val32 (Or.inr (by omega_arith)) (by omega_arith), hm1]
  have w0₅ : w32 s₅.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) :=
    o5.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have g12₅ : s₅.gpr .r12 = s₁.gpr .r12 := by rw [k5.gpr _ (by decide), g12]
  -- `m₁` into array 9.
  refine arrCopy_ok (a := 4) (b := 9) (hsA.congr k15.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k15.gpr _ (by decide)).trans h10) ((k15.gpr _ (by decide)).trans h29) ((k15.gpr _ (by decide)).trans h11)
    fun s₆ c9 o6 k6 => ?_
  have k16 := k15.trans k6
  have outB6 : Outside BX oA (slot wP 24) s.mem s₆.mem :=
    (out_sub (fun y hy => out5 y hy) (by omega_arith) (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => o6 y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  have g12₆ : s₆.gpr .r12 = s₁.gpr .r12 := by rw [k6.gpr _ (by decide), g12₅]
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
  have k17 := k16.trans k7
  have v9₇ : val32 s₇.mem (off BX oA) (slot wP 9) (2 * wP) = m1 := by
    rw [wk7.val32 (Or.inr (by omega_arith)) (by omega_arith), c9, v4₅]
  -- `R² mod p` into array 7, `m₂ mod p` into array 1, `m₁` into array 4.
  refine arrCopy_ok (a := 1) (b := 7) (hsA.congr k17.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    a10' ((k17.gpr _ (by decide)).trans h29) ((k17.gpr _ (by decide)).trans h11) fun s₈ c7 o8 k8 => ?_
  have k18 := k17.trans k8
  refine arrCopy_ok (a := 4) (b := 1) (hsA.congr k18.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k8.gpr _ (by decide)).trans a10') ((k18.gpr _ (by decide)).trans h29) ((k18.gpr _ (by decide)).trans h11)
    fun s₉ c1 o9 k9 => ?_
  have k19 := k18.trans k9
  refine arrCopy_ok (a := 9) (b := 4) (hsA.congr k19.wr) (by decide) (by decide) (by decide) (by omega_arith) hw'
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a10')) ((k19.gpr _ (by decide)).trans h29)
    ((k19.gpr _ (by decide)).trans h11) fun t c4 o10 k10 => ?_
  have k110 := k19.trans k10
  have g12t : t.gpr .r12 = s₇.gpr .r12 := by rw [k10.gpr _ (by decide), k9.gpr _ (by decide), k8.gpr _ (by decide)]
  have w0t : w32 t.mem (off BX oA) (slot wP 0) = w32 s₇.mem (off BX oA) (slot wP 0) := by
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
  have hZ : 256 ≤ Z := by have := slot_le (w := wX) (j := 0) (by decide); unfold slot at *; omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r25] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 k ∧ t.mem = s.mem) (by
    prun [h23, oNLen, hs.ld (show 16 + 8 ≤ Z by omega_arith), hK']) (by decide)) fun s₁ ⟨⟨a25', m₁⟩, k₁⟩ => ?_
  refine WP.mono (r2Ptr_ok (hs.congr k₁.wr) hZ ((k₁.gpr _ (by decide)).trans h23) m₁ hR2)
    fun s' ⟨⟨p30, mp⟩, kp⟩ => ?_
  have m' : s'.mem = s.mem := mp.trans m₁
  have k' := k₁.trans kp
  have a25 : s'.gpr .r25 = BitVec.ofNat 64 k := (kp.gpr _ (by decide)).trans a25'
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
