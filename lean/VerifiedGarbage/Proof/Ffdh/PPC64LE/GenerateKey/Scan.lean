module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.GenerateKey
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-!
# `vg_ffdh_generate_key` on PPC64LE: the scan of the bound's octets

`scanBody`, without a branch, keeps the first nonzero octet of the bound and
its index: after `j` of the `k` octets at `P`, `r9`, `r14` and the mask in
`r15` hold `scanAt` of them (`scan_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (mask)

/-! ## Masks -/

theorem nz_mask_nat : ∀ n < 256, BitVec.ofNat 64 0 - ((BitVec.ofNat 64 0 - BitVec.ofNat 64 n ||| BitVec.ofNat 64 n) >>> 63) =
    mask (n != 0) := by decide +kernel

/-- The mask of an octet being nonzero. -/
theorem nz_mask (b : Byte) : 0#64 - ((0#64 - b.setWidth 64 ||| b.setWidth 64) >>> 63) =
    mask (b != 0) := by
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have e2 : (b != 0) = (b.toNat != 0) := by
    cases h : (b != 0) <;> simp_all [BitVec.toNat_eq]
  rw [e, nz_mask_nat _ b.isLt, e2]

theorem mask_or_xor (a f : Bool) : (mask a ||| mask f) ^^^ mask f = mask (a && !f) := by
  cases a <;> cases f <;> rfl

theorem mask_or' (a f : Bool) : mask f ||| mask a = mask (f || a) := by cases a <;> cases f <;> rfl

/-- A choice by a mask. -/
theorem sel (x y : BitVec 64) (c : Bool) : x ^^^ ((x ^^^ y) &&& mask c) = if c then y else x := by
  cases c
  · show x ^^^ ((x ^^^ y) &&& 0) = x
    simp
  · show x ^^^ ((x ^^^ y) &&& BitVec.allOnes 64) = y
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem getD_bytesAt (m : Mem) (P : Addr) {n j : Nat} (hj : j < n) :
    (Spec.Rsa.bytesAt m P n).getD j 0 = m (off P j) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hj, off]

/-! ## The loop -/

/-- The registers the scan writes. -/
def scanRegs : List Reg := [.r0, .r4, .r6, .r9, .r12, .r14, .r15, .r16, .r17, .r18]

/-- What the scan holds after `j` octets. -/
def ScanInv (s : State) (P : Addr) (k j : Nat) (t : State) : Prop :=
  t.gpr .r12 = off P j ∧ t.gpr .r4 = BitVec.ofNat 64 j ∧
    t.gpr .r9 = BitVec.ofNat 64 (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.1 ∧
    t.gpr .r14 = (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.2.setWidth 64 ∧
    t.gpr .r15 = mask (scanAt (Spec.Rsa.bytesAt s.mem P k) j).1 ∧ t.mem = s.mem ∧ Keep scanRegs s t

theorem scanBody_ok {s t : State} {P : Addr} {k j : Nat} (hj : j < k)
    (hrd : InRegions (t.rd ++ t.wr) (off P j) 1) (h : ScanInv s P k j t) :
    WP isa (.block (scanBody ++ ([.subi .r6 .r6 1] : List Instr))) t fun u =>
      ScanInv s P k (j + 1) u ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 := by
  obtain ⟨t12, t4, t9, t14, t15, tm, tk⟩ := h
  have hb : t.mem (off P j) = (Spec.Rsa.bytesAt s.mem P k).getD j 0 := by rw [getD_bytesAt _ _ hj, tm]
  unfold ScanInv
  rw [scanAt_succ]
  rcases hr : scanAt (Spec.Rsa.bytesAt s.mem P k) j with ⟨f, i, o⟩
  rw [hr] at t9 t14 t15
  generalize (Spec.Rsa.bytesAt s.mem P k).getD j 0 = b at hb ⊢
  simp only
  unfold scanBody
  have hst : WP isa (.block ([.lbz .r16 .r12 0, .li .r0 0, .sub .r17 .r0 .r16, .logic .or .r17 .r17 .r16,
      .lsr .d .r17 .r17 63, .sub .r17 .r0 .r17, .logic .or .r17 .r17 .r15, .logic .xor .r17 .r17 .r15,
      .logic .xor .r18 .r9 .r4, .logic .and .r18 .r18 .r17, .logic .xor .r9 .r9 .r18,
      .logic .xor .r18 .r14 .r16, .logic .and .r18 .r18 .r17, .logic .xor .r14 .r14 .r18,
      .logic .or .r15 .r15 .r17, .addi .r12 .r12 1, .addi .r4 .r4 1] ++ ([.subi .r6 .r6 1] : List Instr))) t
      fun u => (u.gpr .r12 = off P (j + 1) ∧ u.gpr .r4 = BitVec.ofNat 64 (j + 1) ∧
        u.gpr .r9 = (BitVec.ofNat 64 i ^^^ ((BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 j) &&& mask (b != 0 && !f))) ∧
        u.gpr .r14 = (o.setWidth 64 ^^^ ((o.setWidth 64 ^^^ b.setWidth 64) &&& mask (b != 0 && !f))) ∧
        u.gpr .r15 = (mask f ||| mask (b != 0 && !f)) ∧ u.mem = t.mem ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ∧ Keep scanRegs t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t12, t4, t9, t14, t15, exec_lbz' (show Reg.r12 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
      BitVec.add_zero, Pub.read1_setWidth, hb]
    rw [nz_mask, mask_or_xor]
    exact ⟨by rw [BitVec.ofNat_add], rfl, rfl, rfl⟩
  refine WP.mono hst fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ => ⟨⟨u12, u4, ?_, ?_, ?_, um.trans tm, (tk.trans ku).mono (by decide)⟩, u6⟩
  · rw [u9, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u14, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u15, mask_or']
    cases f <;> cases hc : (b != 0) <;> simp_all

theorem sub1_ofNat {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel, BitVec.add_sub_cancel]

/-- `scanSetup` and the scan of the `k` octets at `P` (`r12`): `r9` and `r14`
are `lead` of them and its octet. -/
theorem scan_ok {s : State} {P : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off P i) 1) (h12 : s.gpr .r12 = off P 0)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) :
    WP isa (.block scanSetup) s fun u => WP isa (countLoop .r6 scanBody) u fun t =>
      (t.gpr .r9 = BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt s.mem P k)) ∧
        t.gpr .r14 = ((Spec.Rsa.bytesAt s.mem P k).getD (lead (Spec.Rsa.bytesAt s.mem P k)) 0).setWidth 64 ∧
        t.mem = s.mem) ∧ Keep scanRegs s t := by
  have hlen : (Spec.Rsa.bytesAt s.mem P k).length = k := by simp [Spec.Rsa.bytesAt]
  have hne : Spec.Rsa.bytesAt s.mem P k ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
  refine (WP.mono (WP.keep scanRegs (Q := fun u => u.gpr .r12 = off P 0 ∧ u.gpr .r4 = BitVec.ofNat 64 0 ∧
      u.gpr .r9 = BitVec.ofNat 64 (k - 1) ∧ u.gpr .r14 = BitVec.ofNat 64 0 ∧ u.gpr .r15 = BitVec.ofNat 64 0 ∧
      u.mem = s.mem ∧ u.gpr .r6 = BitVec.ofNat 64 k) ?_ (by decide)) fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ => ?_)
  · unfold scanSetup
    prun [h12, h28, sub1_ofNat hk1, BitVec.add_zero]
  have h0 : ScanInv s P k 0 u := by
    refine ⟨u12, u4, ?_, ?_, ?_, um, ku⟩ <;> rw [scanAt.eq_1]
    · rw [u9, hlen]
    · rw [u14]; rfl
    · rw [u15]; exact (show mask false = 0#64 by decide).symm
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega) (by omega) (ScanInv s P k)
    (fun j hj t ht _ => scanBody_ok hj (by rw [ht.2.2.2.2.2.2.rd, ht.2.2.2.2.2.2.wr]; exact hrd j hj) ht) h0 u6)
    fun t ⟨_, _, t9, t14, _, tm, kt⟩ => ?_
  have e := scanAt_length hne
  rw [hlen] at e
  rw [e] at t9 t14
  exact ⟨⟨t9, t14, tm⟩, kt⟩

end VG.Proof.Ffdh.PPC64LE.GenerateKey
