module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA public-key operation on PPC64LE: the function

`vg_rsa_public_precomputed_checked(out = r3, out_len = r4, pre = r5,
pre_len = r6, e = r7, e_len = r8, input = r9, input_len = r10, scratch,
scratch_len)`, the last two on the stack (`fnContract`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_rsa_public_precomputed_checked`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let pre : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 8⟩
    let e : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let inp : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ s.rd = [pre, e, inp, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r4).toNat ∧ (s.gpr .r6).toNat = Spec.Rsa.precomputedWords (s.gpr .r4).toNat ∧
      (s.gpr .r10).toNat = (s.gpr .r4).toNat ∧ 1 ≤ (s.gpr .r8).toNat ∧
      (s.gpr .r8).toNat ≤ (s.gpr .r4).toNat ∧ Spec.Rsa.publicScratchWords (s.gpr .r4).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .r4).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r4).toNat ((s'.gpr .r3).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r4).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      (Spec.Rsa.wordsAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat).map (·.toNat) =
        (Spec.Rsa.wordsAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat).map (·.toNat)

theorem ofNat_add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_shl3 (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_shl1 (a : Nat) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `setup`, `out` and `k` in `r3` and `r4` and the working space at `r23`. -/
theorem setup_ok {s : State} {S : Addr} {k : Nat} (h4 : s.gpr .r4 = BitVec.ofNat 64 k)
    (h23 : s.gpr .r23 = S) (hk : k ≤ 1024) :
    WP isa (.block setup) s fun t =>
      (t.gpr .r27 = s.gpr .r3 ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.mem = s.mem) ∧
      Keep [.r10, .r11, .r27, .r28, .r29] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h4, h23, BitVec.add_zero, ofNat_add7_shr3 k (by omega), ofNat_shl3, ofNat_shl1, hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

end VG.Proof.Bignum.PPC64LE.Pub
