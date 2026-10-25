module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.WinPow

/-!
# The RSA private-key operation on PPC64LE: a prime's power, the exponent

`powerB_ok`: `c mod p` into array 4, `R² mod p` into array 1 and
`-p⁻¹ mod 2³²` into `r12`, then `(c mod p)^d mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `power`'s second part, in the working space `off BX oA` with the prime
`P` in array 0 and `x < P` in array 1, for the `L` bytes at `D` (from the
header's words `oD` and `oLen`): `x^d mod P` into array 4. -/
theorem powerB_ok {s : State} {BX D : Addr} {Z oA wA L Pv x : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA))
    (h18 : s.gpr .r18 = off D 0) (h19 : s.gpr .r19 = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hL' : L < 2 ^ 63) (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : val32 s.mem (off BX oA) (slot wA 0) (2 * wA) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hx : val32 s.mem (off BX oA) (slot wA 1) (2 * wA) = x) :
    WP isa (.seq (.block (PublicChecked.base .r14 4 ++ PublicChecked.base .r15 1)) (.seq copyN
      (.seq (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3))
      (.seq Precompute.r2 (.seq (.block (PublicChecked.minv ++ ([.addi .r30 .r18 0, .addi .r31 .r19 0] : List Instr)))
        ModExp.powWin))))) s fun t =>
      (val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv ∧
        val32 t.mem (off BX oA) (slot wA 4) (2 * wA) = x ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot wA 24) s.mem t.mem) ∧ Keep powerRegs s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 24
  have hsA := hs.sub hA
  have hnA := hsA.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 1) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hsA.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have v4 : val32 s₃.mem (off BX oA) (slot wA 4) (2 * wA) = x := by
    rw [Pre.val32_eq_wv, ← hx, Pre.val32_eq_wv]; exact wv_congr2 fun i hi => hw3 i hi
  have out3' : Mont.Outside (off BX oA) (slot wA 4) (8 * wA) s.mem s₃.mem := fun y hy => out3 y hy
  have v0 : val32 s₃.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [out3'.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 1) fun s₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 2) fun s₅ ⟨⟨a8, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 3) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have hm6 : s₆.mem = s₃.mem := by rw [m6, m5, m4]
  refine WP.seq (WP.mono (r2_ok (hsA.congr k16.wr) ((k6.gpr _ (by decide)).trans a8) a9
    ((k16.gpr _ (by decide)).trans h10) ((k6.gpr _ (by decide)).trans ((k5.gpr _ (by decide)).trans a5))
    ((k16.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by rw [hm6, v0]; exact hP2))
    fun s₇ ⟨h1, out7, k7⟩ => ?_)
  have k17 := k16.trans k7
  rw [hm6, v0] at h1
  rw [hm6] at out7
  have v0' : val32 s₇.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [out7.val32 (Or.inl (by omega_arith)) (by omega_arith), v0]
  have v4' : val32 s₇.mem (off BX oA) (slot wA 4) (2 * wA) = x := by
    rw [out7.val32 (Or.inr (by omega_arith)) (by omega_arith), v4]
  have hlow : (word s₇.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wA by omega_arith), ← Pre.val32_eq_wv, v0', hPodd]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hsA.congr k17.wr) ((k17.gpr _ (by decide)).trans h10) (by omega_arith) hlow)
    fun s₈ ⟨⟨i12, iinv, m8⟩, k8⟩ => ?_
  have k18 := k17.trans k8
  have outH : Outside BX oA (slot wA 24) s.mem s₈.mem := by
    rw [m8]
    exact (out_sub out3 (by omega_arith) (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => out7 y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off D 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 L ∧ t.mem = s₈.mem) (by
      prun [(k18.gpr .r18 (by decide)).trans h18, (k18.gpr .r19 (by decide)).trans h19, BitVec.add_zero])
    (by decide)) fun s₉ ⟨⟨a30, a31, m9⟩, k9⟩ => ?_
  have k19 := k18.trans k9
  have hm9 : s₉.mem = s₇.mem := by rw [m9, m8]
  have hb : Spec.Rsa.bytesAt s₉.mem D L = Spec.Rsa.bytesAt s.mem D L := by
    rw [m9]; exact bytesAt_out outH hA hsepD
  rw [← hm9] at v0' v4' h1 iinv
  refine WP.mono (Win.powWin_ok (hsA.congr k19.wr) hw2 hw' (Nat.le_refl _)
    ((k19.gpr _ (by decide)).trans h10) ((k19.gpr _ (by decide)).trans h29)
    ((k19.gpr _ (by decide)).trans h11) (by rw [k9.gpr _ (by decide)]; exact i12)
    (by rw [k9.gpr _ (by decide)]; exact iinv) (by rw [v0']; exact hP2) (by rw [v0']; exact hPodd)
    (by rw [h1, v0']; exact Nat.mod_lt _ (by omega_arith)) a30 a31 hL hL'
    (fun i hi => by rw [k19.rd, k19.wr]; exact hrdD i hi)
    (fun i hi y hy => hsepD i hi y (by rw [ofs_sub hy (by omega_arith)]; omega_arith))) fun t ⟨⟨hpow, out10⟩, k10⟩ => ?_
  have hpr : ∀ r ∈ Win.win wA, slot wA 0 + 4 * (2 * wA) ≤ r.1 ∨ r.1 + r.2 ≤ slot wA 0 := by
    intro r hr
    rw [Win.win, List.mem_singleton] at hr
    subst hr
    left; simp only [e]; omega_arith
  refine ⟨⟨?_, ?_, ?_⟩, (k19.trans k10).mono⟩
  · rw [out10.val32 hpr (by omega_arith), v0']
  · rw [hpow (by rw [h1, v0', ← Nat.pow_add, ← Nat.two_mul, ← Nat.mul_assoc]), v4', v0', hb]
  · refine outH.trans ?_
    rw [← m9]
    refine outs_sub out10 (fun r hr => ?_) (by omega_arith) (by omega_arith)
    rw [Win.win, List.mem_singleton] at hr
    subst hr
    simp only [e]; omega_arith

/-- `power xj oD oLen`, in the working space `off BX oA` of `w_A` words: for
the prime `P` (`w_A` words of `X`'s array `xj`) and the input (`k` bytes at
`I`), array 4 holds `c^d mod P` for the exponent `d` (`L` bytes at `D`), with
the input, `D` and `L` from the header. -/
theorem power_ok {s : State} {BX I D : Addr} {Z oA wA wX xj k L Pv oD oLen : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hI : word s.mem BX oIn = off I 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k)
    (hk' : k < 2 ^ 63) (hrdI : ∀ i < k, InRegions (s.rd ++ s.wr) (off I i) 1)
    (hsepI : ∀ i < k, ∀ x, ofs BX x < Z → off I i ≠ x)
    (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hDp : word s.mem BX oD = off D 0) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hL' : L < 2 ^ 63) (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1) :
    WP isa (power xj oD oLen) s fun t =>
      (val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv ∧
        val32 t.mem (off BX oA) (slot wA 4) (2 * wA) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem I k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot wA 24) s.mem t.mem) ∧ Keep powerRegs s t := by
  have eX8 : slot wX 8 = hdrBytes + 8 * (8 * (wX + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  unfold power
  have hA8 : oA + slot wA 8 ≤ Z := Nat.le_trans (by unfold slot; omega_arith) hA
  refine powerA_ok hs hA8 hXA hw2 hw' hwx hxj h10 h29 h11 h23 h27 h28 hoD hoL hI hK hDp hLw hk hk' hrdI hsepI hP
    (by omega_arith) fun t v0 v1 out t18 t19 k => ?_
  have hb : Spec.Rsa.bytesAt t.mem D L = Spec.Rsa.bytesAt s.mem D L := bytesAt_out out hA8 hsepD
  refine WP.mono (powerB_ok (hs.congr k.wr) hA hw2 hw' ((k.gpr _ (by decide)).trans h10)
    ((k.gpr _ (by decide)).trans h29) ((k.gpr _ (by decide)).trans h11) t18 t19 hL hL'
    (fun i hi => by rw [k.rd, k.wr]; exact hrdD i hi) hsepD v0 hP2 hPodd v1)
    fun u ⟨⟨u0, u4, uo⟩, ku⟩ => ⟨⟨u0, ?_, (out.mono (Nat.le_refl _) (by unfold slot; omega_arith)).trans uo⟩,
      (k.trans ku).mono⟩
  rw [u4, hb, ← Nat.pow_mod]

end VG.Proof.Bignum.PPC64LE.Crt
