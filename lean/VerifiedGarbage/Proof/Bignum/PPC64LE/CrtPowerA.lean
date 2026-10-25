module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Prime
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
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
0, `-p⁻¹ mod 2³²`, `R² mod p` into array 1, and the input modulo the prime
into array 4.
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

/-- `power`'s first part: `k` (the header's word) into `r25`, the prime (`wv`
of `X`'s array `xj`, `w_A` words) into array 0 of the working space
`off BX oA`, `-p⁻¹ mod 2³²` into `r12`, `R² mod p` into array 1
(`r2Prime`), and `c mod p` into array 4 (`reduceIn`), for `c` the first
`w_A n` words of `X`'s array 6. -/
theorem powerA_ok {s : State} {BX : Addr} {Z oA wA wX xj k Pv Cv : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hn : wA * nChunks ((k + 7) / 8) wA ≤ wX)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hC : wv s.mem BX (slot wX 6) (wA * nChunks ((k + 7) / 8) wA) = Cv)
    (hc : ∀ t, val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv →
      val32 t.mem (off BX oA) (slot wA 1) (2 * wA) = 2 ^ (128 * wA) % Pv →
      val32 t.mem (off BX oA) (slot wA 4) (2 * wA) = Cv % Pv →
      (t.gpr .r12).toNat < 2 ^ 32 → (w32 t.mem (off BX oA) (slot wA 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 →
      Outside BX oA (slot wA 24) s.mem t.mem → t.gpr .r10 = off (off BX oA) (slot wA 0) →
      Keep (.r10 :: powerRegs) s t → WP isa c t Q) :
    WP isa (.seq (.block (([.load .d .r25 .r23 oNLen, .addi .r14 .r10 0] : List Instr) ++ xb .r15 xj)) (.seq copyN
      (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
        PublicChecked.base .r9 3)) (.seq Precompute.r2Prime (.seq reduceIn c))))) s Q := by
  have hn' := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 8; have eA24 := e wA 24
  have eX0 := e wX 0; have eX6 := e wX 6; have eX8 := e wX 8; have sXj := slot_le (w := wX) hxj
  have hK' : s.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := hK
  have hsA := hs.sub hA
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 k ∧
    t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem) (by
      prun [h23, h10, oNLen, hs.ld (show 16 + 8 ≤ Z by omega_arith), hK', BitVec.add_zero, off_off]) rfl)
    fun s₁ ⟨⟨a25, a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  -- The prime.
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have v0 : val32 s₃.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  have hlow : (word s₃.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wA by omega_arith), ← Pre.val32_eq_wv, v0, hPodd]
  -- `-p⁻¹ mod 2³²` and the bases.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hsA.congr k13.wr) ((k13.gpr _ (by decide)).trans h10) (by omega_arith) hlow)
    fun s₄ ⟨⟨i12, iinv, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 1) fun s₅ ⟨⟨a5, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 2) fun s₆ ⟨⟨a8, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h10)
    ((k16.gpr _ (by decide)).trans h29) 3) fun s₇ ⟨⟨a9, m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  have hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  have g12 : s₇.gpr .r12 = s₄.gpr .r12 := by
    rw [k7.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide)]
  -- `R² mod p`.
  refine WP.seq (WP.mono (Pre.r2Prime_ok (hsA.congr k17.wr) ((k7.gpr _ (by decide)).trans a8) a9
    ((k17.gpr _ (by decide)).trans h10) ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans a5))
    ((k17.gpr _ (by decide)).trans h11) hw2 hw' (by simp only [e]; omega_arith) (by rw [g12]; exact i12)
    (by rw [g12, hm7]; exact iinv) (by rw [hm7, v0]; exact hP2) (by rw [hm7, v0]; exact hPodd))
    fun s₈ ⟨h1, out8, k8⟩ => ?_)
  have k18 := k17.trans k8
  rw [hm7, v0] at h1
  rw [hm7] at out8
  have v0' : val32 s₈.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [out8.val32 (Or.inl (by omega_arith)) (by omega_arith), v0]
  have w8 : w32 s₈.mem (off BX oA) (slot wA 0) = w32 s₃.mem (off BX oA) (slot wA 0) := by
    have := out8.val32 (d := slot wA 0) (k := 1) (Or.inl (by omega_arith)) (by omega_arith)
    simpa [val32] using this
  have out38 : Outside BX oA (slot wA 24) s.mem s₈.mem :=
    (out3.mono (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => out8 y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  have g12' : s₈.gpr .r12 = s₄.gpr .r12 := (k8.gpr .r12 (by decide)).trans g12
  have hc6 : wA * nChunks ((k + 7) / 8) wA ≤ wX + 2 := by omega_arith
  -- `c mod p`.
  refine WP.seq (WP.mono (reduceIn_ok (Cv := Cv) (hs.congr k18.wr) hA hXA hw2 hw' hn ((k18.gpr _ (by decide)).trans h10)
    ((k18.gpr _ (by decide)).trans h21) ((k18.gpr _ (by decide)).trans h29) ((k18.gpr _ (by decide)).trans h11)
    ((k18.gpr _ (by decide)).trans h27) ((k18.gpr _ (by decide)).trans h28)
    (by rw [k8.gpr .r25 (by decide), k7.gpr .r25 (by decide), k6.gpr .r25 (by decide), k5.gpr .r25 (by decide),
      k4.gpr .r25 (by decide), k3.gpr .r25 (by decide), k2.gpr .r25 (by decide), a25]) hk hk'
    (by rw [g12']; exact i12) (by rw [g12', w8]; exact iinv) v0' hP2 hPodd h1
    ((out38.wv (Or.inl (by omega_arith)) (by omega_arith)).trans hC))
    fun t ⟨⟨t4, t0, t1, t12, tinv, tout, t10⟩, kt⟩ => ?_)
  exact hc t t0 t1 t4 t12 tinv (out38.trans tout) t10 ((k18.trans kt).mono (by decide +kernel))

end VG.Proof.Bignum.PPC64LE.Crt
