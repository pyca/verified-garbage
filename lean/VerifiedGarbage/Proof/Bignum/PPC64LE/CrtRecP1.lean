module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
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
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `h`, its operands

`recP1_ok`: in `p`'s working space, `-p⁻¹ mod 2³²` into `r12`, `R² mod p`
into array 7 and `m₂ mod p` into array 1, from `m₂`'s bytes in `X`'s array 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The registers `recombineP` writes. -/
def recRegs : List Reg := .r10 :: powerRegs

/-- The bytes of a buffer within the working space, below a change. -/
theorem bytesAt_below {B : Addr} {o n d k : Nat} {m m' : Mem} (h : Outside B o n m m') (hd : d + k ≤ o)
    (hd' : o < 2 ^ 64) : Spec.Rsa.bytesAt m' (off B d) k = Spec.Rsa.bytesAt m (off B d) k := by
  rw [bytesAt_eq, bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ (Or.inl ?_)
  have hi := List.mem_range.mp hi
  rw [ofs_off B (by omega_arith)]; omega_arith

/-- `recombineP`'s first part, in `p`'s working space `off BX oA` (`P` in
array 0, `m₁` in array 4), `m₂` the `qL` bytes of `X`'s array 1 (`qL` in the
header). -/
theorem recP1'_ok {s : State} {BX : Addr} {Z oA wP wX qL Pv m1 m2 : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h31 : s.gpr .r31 = BitVec.ofNat 64 qL) (hq1 : 1 ≤ qL) (hqx : qL ≤ 8 * (wX + 2)) (hwX : wX < 2 ^ 31)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1)
    (hm2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off BX (slot wX 1)) qL) = m2)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wP 0) (2 * wP) = Pv →
      val32 t.mem (off BX oA) (slot wP 1) (2 * wP) = m2 % Pv →
      val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = m1 →
      val32 t.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wP 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wP 24) s.mem t.mem → Keep powerRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
      PublicChecked.base .r9 3)) (.seq Precompute.r2Prime
      (.seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 1)) (.seq copyN
      (.seq (.block (xb .r30 1)) (.seq ModArith.reduce64 c)))))) s Q := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wP 0; have eA1 := e wP 1; have eA4 := e wP 4; have eA7 := e wP 7; have eA8 := e wP 24
  have eX1 := e wX 1; have eX8 := e wX 8
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
  refine WP.seq (WP.mono (Pre.r2Prime_ok (hsA.congr k14.wr) ((k4.gpr _ (by decide)).trans a8) a9
    ((k14.gpr _ (by decide)).trans h10) ((k4.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans a5))
    ((k14.gpr _ (by decide)).trans h11) hw2 hw' (by simp only [e]; omega_arith) (by rw [g12]; exact i12)
    (by rw [g12, hm4]; exact iinv) (by rw [hm4, hP]; exact hP2) (by rw [hm4, hP]; exact hPodd))
    fun s₅ ⟨r1, out5, k5⟩ => ?_)
  have k15 := k14.trans k5
  rw [hm4, hP] at r1
  rw [hm4] at out5
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 7) fun s₆ ⟨⟨a14, m6⟩, k6⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) (((k15.trans k6).gpr _ (by decide)).trans h10)
    (((k15.trans k6).gpr _ (by decide)).trans h29) 1) fun s₇ ⟨⟨a15, m7⟩, k7⟩ => ?_
  have k17 := (k15.trans k6).trans k7
  refine WP.seq (WP.mono (copySub_ok (hsA.congr k17.wr) a15 ((k7.gpr _ (by decide)).trans a14)
    ((k17.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₈ ⟨⟨hw8, out8⟩, k8⟩ => ?_)
  have k18 := k17.trans k8
  rw [m7, m6] at hw8 out8
  have outB : Outside BX oA (slot wP 24) s.mem s₈.mem :=
    (out_sub (fun y hy => out5 y hy) (by omega_arith) (by omega_arith) (by omega_arith)).trans (out_sub out8 (by omega_arith) (by omega_arith) (by omega_arith))
  refine WP.seq (WP.mono (xb_ok (rd := .r30) (by decide) (by decide) ((k18.gpr _ (by decide)).trans h27)
    ((k18.gpr _ (by decide)).trans h28) 1) fun s₁₀ ⟨⟨a30, m10⟩, k10⟩ => ?_)
  have k110 := k18.trans k10
  have hm10 : s₁₀.mem = s₈.mem := m10
  have a31 : s₁₀.gpr .r31 = BitVec.ofNat 64 qL := (k110.gpr _ (by decide)).trans h31
  have o5 : Mont.Outside (off BX oA) (slot wP 1) (24 * (wP + 2)) s.mem s₅.mem := out5
  have o8 : Mont.Outside (off BX oA) (slot wP 7) (8 * wP) s₅.mem s₈.mem := fun y hy => out8 y hy
  have v0 : val32 s₁₀.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [hm10, o8.val32 (Or.inl (by omega_arith)) (by omega_arith), o5.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have v4 : val32 s₁₀.mem (off BX oA) (slot wP 4) (2 * wP) = m1 := by
    rw [hm10, o8.val32 (Or.inl (by omega_arith)) (by omega_arith), o5.val32 (Or.inr (by omega_arith)) (by omega_arith), hm1]
  have v7 : val32 s₁₀.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [hm10, Pre.val32_eq_wv, wv_congr2 (fun i hi => hw8 i hi), ← Pre.val32_eq_wv, r1, ← Nat.pow_add,
      ← Nat.two_mul, ← Nat.mul_assoc]
  have w0 : w32 s₁₀.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) := by
    rw [hm10, o8.w32 (Or.inl (by omega_arith)) (by omega_arith), o5.w32 (Or.inl (by omega_arith)) (by omega_arith)]
  have hb : Spec.Rsa.bytesAt s₁₀.mem (off BX (slot wX 1)) qL =
      Spec.Rsa.bytesAt s.mem (off BX (slot wX 1)) qL := by
    rw [hm10]; exact bytesAt_below outB (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (ModArith.reduce64_ok (D := off BX (slot wX 1)) (hsA.congr k110.wr) (by omega_arith) hw' (by omega_arith)
    ((k110.gpr _ (by decide)).trans h10) ((k110.gpr _ (by decide)).trans h29)
    ((k110.gpr _ (by decide)).trans h11) (by rw [v0]; omega_arith)
    (by rw [a30, off_off, Nat.add_zero]) a31 hq1 (by omega_arith)
    (fun i hi => by rw [off_off]; exact (hs.congr k110.wr).ld (by omega_arith))
    (fun i hi y hy he => by
      have := ofs_sub hy (by omega_arith)
      rw [← he] at this; simp only [off_off] at this; rw [show ofs BX (off BX (slot wX 1 + i)) = slot wX 1 + i from Mem.sub_ofNat_toNat BX (by omega_arith)] at this
      omega_arith)) fun t ⟨⟨r1', outR⟩, kR⟩ => ?_)
  have gr12 : t.gpr .r12 = s₁.gpr .r12 := by
    rw [kR.gpr _ (by decide), k10.gpr _ (by decide), k8.gpr _ (by decide),
      k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), g12]
  refine hc t (by rw [outR.val32 (Or.inl (by omega_arith)) (by omega_arith), v0])
    (by rw [r1', hb, hm2, v0]) (by rw [outR.val32 (Or.inr (by omega_arith)) (by omega_arith), v4])
    (by rw [outR.val32 (Or.inr (by omega_arith)) (by omega_arith), v7]) (by rw [gr12]; exact i12)
    (by rw [gr12, outR.w32 (Or.inl (by omega_arith)) (by omega_arith), w0]; exact iinv) ?_ (k110.trans kR).mono
  rw [hm10] at outR
  exact outB.trans (out_sub (fun y hy => outR y hy) (by omega_arith) (by omega_arith) (by omega_arith))

/-- `recombineP`'s first part, `q_len` (`qL`, in the header) first. -/
theorem recP1_ok {s : State} {BX : Addr} {Z oA wP wX qL Pv m1 m2 : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL) (hq1 : 1 ≤ qL) (hqx : qL ≤ 8 * (wX + 2)) (hwX : wX < 2 ^ 31)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1)
    (hm2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off BX (slot wX 1)) qL) = m2)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wP 0) (2 * wP) = Pv →
      val32 t.mem (off BX oA) (slot wP 1) (2 * wP) = m2 % Pv →
      val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = m1 →
      val32 t.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wP 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wP 24) s.mem t.mem → Keep powerRegs s t → WP isa c t Q) :
    WP isa (.seq (.block [.load .d .r31 .r23 oQLen]) (.seq (.block (PublicChecked.minv ++
      PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3)) (.seq Precompute.r2Prime
      (.seq (.block (PublicChecked.base .r14 7 ++ PublicChecked.base .r15 1)) (.seq copyN
      (.seq (.block (xb .r30 1)) (.seq ModArith.reduce64 c))))))) s Q := by
  have hn := hs.nowrap
  have hQL' : s.mem.readW (off BX 56) 64 = BitVec.ofNat 64 qL := hQL
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = BitVec.ofNat 64 qL ∧ t.mem = s.mem) (by
    prun [h23, oQLen, hs.ld (show 56 + 8 ≤ Z by have := slot_le (w := wX) (j := 0) (by decide); unfold slot at *; omega_arith),
      hQL']) (by decide)) fun s' ⟨⟨a31, m'⟩, k'⟩ => ?_)
  rw [← m'] at hP hm1 hm2
  refine recP1'_ok (hs.congr k'.wr) hA hXA hw2 hw' ((k'.gpr _ (by decide)).trans h10) ((k'.gpr _ (by decide)).trans h29)
    ((k'.gpr _ (by decide)).trans h11) ((k'.gpr _ (by decide)).trans h27)
    ((k'.gpr _ (by decide)).trans h28) a31 hq1 hqx hwX hP hP2 hPodd hm1 hm2 fun t v0 v1 v4 v7 t12 tinv o k => ?_
  rw [m'] at o
  exact hc t v0 v1 v4 v7 t12 tinv o (k'.trans k).mono

end VG.Proof.Bignum.PPC64LE.Crt
