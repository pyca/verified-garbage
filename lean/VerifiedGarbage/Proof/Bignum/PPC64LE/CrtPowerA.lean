module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: a prime's power, the input

`powerA_ok`: the prime from `X`'s array `xj` into the working space's array
0, and the input modulo the prime into its array 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The registers `power` writes. -/
def powerRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r30, .r31]

/-- The bytes of a buffer apart from the working space, after a change
within it. -/
theorem bytesAt_out {B I : Addr} {Z o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off I i ≠ x) :
    Spec.Rsa.bytesAt m' I k = Spec.Rsa.bytesAt m I k := by
  rw [bytesAt_eq, bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (I + BitVec.ofNat 64 i) (by omega) rfl

theorem wv_low_mod2 (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 = (word m p d).toNat % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega⟩
  rw [wv_add]
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `power`'s first part: the prime (`wv` of `X`'s array `xj`, `w_A` words)
into array 0 of the working space `off BX oA`, and the input (`k` bytes at
`I`, from the header) modulo it into array 1. -/
theorem powerA_ok {s : State} {BX I : Addr} {Z oA wA wX xj k Pv : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wA 8 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hI : word s.mem BX oIn = off I 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k)
    (hk' : k < 2 ^ 63) (hrdI : ∀ i < k, InRegions (s.rd ++ s.wr) (off I i) 1)
    (hsepI : ∀ i < k, ∀ x, ofs BX x < Z → off I i ≠ x)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP0 : 0 < Pv)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv →
      val32 t.mem (off BX oA) (slot wA 1) (2 * wA) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem I k) % Pv →
      Outside BX oA (slot wA 8) s.mem t.mem → Keep powerRegs s t → WP isa c t Q) :
    WP isa (.seq (.block ([.addi .r14 .r10 0] ++ xb .r15 xj)) (.seq copyN
      (.seq (.block [.load .d .r30 .r23 oIn, .load .d .r31 .r23 oNLen]) (.seq ModArith.reduce c)))) s Q := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 8
  have eX0 := e wX 0; have sXj := slot_le (w := wX) hxj
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem)
    (by prun [h10, BitVec.add_zero, off_off]) (by decide)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega) hw' (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have hI' : s₃.mem.readW (off BX 24) 64 = off I 0 := (out3.word (Or.inl (by omega)) (by omega)).trans hI
  have hK' : s₃.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k :=
    (out3.word (Or.inl (by omega)) (by omega)).trans hK
  refine WP.seq (WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off I 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 k ∧ t.mem = s₃.mem) (by
      prun [(k13.gpr .r23 (by decide)).trans h23, oIn, oNLen, (hs.congr k13.wr).ld (show 24 + 8 ≤ Z by omega),
        (hs.congr k13.wr).ld (show 16 + 8 ≤ Z by omega), hI', hK']) (by decide))
    fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have hsA := (hs.congr k14.wr).sub hA
  have hv0 : val32 s₄.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [m4, Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  refine WP.seq (WP.mono (ModArith.reduce_ok hsA (by omega) hw' (by omega) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) ((k14.gpr _ (by decide)).trans h11) (by omega) a30 a31 hk hk'
    (fun i hi => by rw [k14.rd, k14.wr]; exact hrdI i hi)
    (fun i hi x hx => hsepI i hi x (by rw [ofs_sub hx (by omega)]; omega))) fun t ⟨⟨h1, out5⟩, k5⟩ => ?_)
  have out5' : Outside (off BX oA) (slot wA 1) (24 * (wA + 2)) s₄.mem t.mem := fun x hx => out5 x hx
  have hb : Spec.Rsa.bytesAt s₄.mem I k = Spec.Rsa.bytesAt s.mem I k := by
    rw [m4]; exact bytesAt_out out3 (by omega) hsepI
  refine hc t ?_ ?_ ?_ (k14.trans k5).mono
  · rw [Pre.val32_eq_wv, out5'.wv (Or.inl (by omega)) (by omega), ← Pre.val32_eq_wv, hv0]
  · rw [h1, hb, hv0]
  · rw [m4] at out5'
    exact (out3.mono (by omega) (by omega)).trans (out_sub out5' (by omega) (by omega) (by omega))
