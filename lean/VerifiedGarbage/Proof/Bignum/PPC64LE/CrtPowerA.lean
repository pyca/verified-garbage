module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

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
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega_arith⟩
  rw [wv_add]
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `power`'s first part: the header's words (the input `I` of `k` bytes, the
exponent `D` of `L`), then the prime (`wv` of `X`'s array `xj`, `w_A` words)
into array 0 of the working space `off BX oA`, and the input modulo it into
array 1. -/
theorem powerA_ok {s : State} {BX I D : Addr} {Z oA wA wX xj k L Pv oD oLen : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wA 8 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hI : word s.mem BX oIn = off I 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hDp : word s.mem BX oD = off D 0) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L) (hk : 1 ≤ k)
    (hk' : k < 2 ^ 63) (hrdI : ∀ i < k, InRegions (s.rd ++ s.wr) (off I i) 1)
    (hsepI : ∀ i < k, ∀ x, ofs BX x < Z → off I i ≠ x)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP0 : 0 < Pv)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv →
      val32 t.mem (off BX oA) (slot wA 1) (2 * wA) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem I k) % Pv →
      Outside BX oA (slot wA 8) s.mem t.mem → t.gpr .r18 = off D 0 → t.gpr .r19 = BitVec.ofNat 64 L →
      Keep powerRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (([.load .d .r30 .r23 oIn, .load .d .r31 .r23 oNLen, .load .d .r18 .r23 oD,
      .load .d .r19 .r23 oLen, .addi .r14 .r10 0] : List Instr) ++ xb .r15 xj)) (.seq copyN (.seq ModArith.reduce c))) s Q := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 8
  have eX0 := e wX 0; have sXj := slot_le (w := wX) hxj
  have hI' : s.mem.readW (off BX 24) 64 = off I 0 := hI
  have hK' : s.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := hK
  have hD' : s.mem.readW (off BX oD) 64 = off D 0 := hDp
  have hL' : s.mem.readW (off BX oLen) 64 = BitVec.ofNat 64 L := hLw
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r30, .r31, .r18, .r19, .r14] (Q := fun t => t.gpr .r30 = off I 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 k ∧ t.gpr .r18 = off D 0 ∧ t.gpr .r19 = BitVec.ofNat 64 L ∧
    t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem) (by
      prun [h23, h10, oIn, oNLen, hs.ld (show 24 + 8 ≤ Z by omega_arith), hs.ld (show 16 + 8 ≤ Z by omega_arith),
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oD < 2 ^ 15 by omega_arith, show oD % 4 = 0 by omega_arith⟩,
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oLen < 2 ^ 15 by omega_arith, show oLen % 4 = 0 by omega_arith⟩,
        hs.ld (show oD + 8 ≤ Z by omega_arith), hs.ld (show oLen + 8 ≤ Z by omega_arith), hI', hK', hD', hL',
        BitVec.add_zero, off_off]) rfl) fun s₁ ⟨⟨a30, a31, a18, a19, a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₄ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k14 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have hsA := (hs.congr k14.wr).sub hA
  have hv0 : val32 s₄.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  refine WP.seq (WP.mono (ModArith.reduce_ok hsA (by omega_arith) hw' (by omega_arith) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) ((k14.gpr _ (by decide)).trans h11) (by omega_arith)
    ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a30))
    ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a31)) hk hk'
    (fun i hi => by rw [k14.rd, k14.wr]; exact hrdI i hi)
    (fun i hi x hx => hsepI i hi x (by rw [ofs_sub hx (by omega_arith)]; omega_arith))) fun t ⟨⟨h1, out5⟩, k5⟩ => ?_)
  have out5' : Outside (off BX oA) (slot wA 1) (24 * (wA + 2)) s₄.mem t.mem := fun x hx => out5 x hx
  have hb : Spec.Rsa.bytesAt s₄.mem I k = Spec.Rsa.bytesAt s.mem I k := bytesAt_out out3 (by omega_arith) hsepI
  refine hc t ?_ ?_ ?_ ((k5.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a18)))
    ((k5.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a19)))
    (k14.trans k5).mono
  · rw [Pre.val32_eq_wv, out5'.wv (Or.inl (by omega_arith)) (by omega_arith), ← Pre.val32_eq_wv, hv0]
  · rw [h1, hb, hv0]
  · exact (out3.mono (by omega_arith) (by omega_arith)).trans (out_sub out5' (by omega_arith) (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.Crt
