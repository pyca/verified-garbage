module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute

/-!
# The RSA private-key operation on PPC64LE: the function

`vg_rsa_private_crt(out = r3, out_len = r4, n = r5, n_len = r6, input = r7,
input_len = r8, p = r9, p_len = r10, q, q_len, dp, dp_len, dq, dq_len,
qinv, qinv_len, scratch, scratch_len)`, the last ten on the stack
(`fnContract`); `vg_rsa_private_crt_precomputed`, which also takes the
primes' cached `R² mod p` and `R² mod q` in `r12` (`fnContractP`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE

/-- The regions `vg_rsa_private_crt` reads. -/
def baseRd (s : State) : List Region :=
  [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, ⟨s.gpr .r7, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (s.gpr .r10).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArgAddr s 0, 80⟩]

/-- `vg_rsa_private_crt`'s precondition, with the regions it reads `rd`. -/
def preCore (rd : List Region) (s : State) : Prop :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let n : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let inp : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let p : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64 ∧
      s.rd = rd ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r6).toNat ∧ (s.gpr .r4).toNat = (s.gpr .r6).toNat ∧
      (s.gpr .r8).toNat = (s.gpr .r6).toNat ∧ 1 ≤ (s.gpr .r10).toNat ∧
      (s.gpr .r10).toNat < (s.gpr .r6).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .r6).toNat ∧ (stackArg s 3).toNat = (s.gpr .r10).toNat ∧
      (stackArg s 7).toNat = (s.gpr .r10).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 9).toNat

/-- `vg_rsa_private_crt`'s result. -/
def postCore (s s' : State) : Prop :=
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r10).toNat))

/-- `vg_rsa_private_crt`'s public data. -/
def pubCore (s₁ s₂ : State) : Prop :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat

/-- `vg_rsa_private_crt`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s := preCore (baseRd s) s
  post := postCore
  pub := pubCore

/-- `fnContract.pre` as `preCore` with no regions but `baseRd`'s. -/
theorem preCore_nil {s : State} (h : fnContract.pre s) : preCore (baseRd s ++ []) s := by
  rw [List.append_nil]; exact h

/-- The cached `R² mod p` and `R² mod q` of `vg_rsa_private_crt_precomputed`,
at `r12`: `max(2, ⌈len / 8⌉)` words each. -/
def r2R (s : State) : Region :=
  ⟨s.gpr .r12, 8 * (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat)⟩

/-- `vg_rsa_private_crt_precomputed`, which takes in `r12` the address of
the primes' `R² mod p` and `R² mod q` (`Spec.Rsa.primeR2`), and computes
what `vg_rsa_private_crt` does. -/
def fnContractP : Contract isa where
  pre s := preCore (baseRd s ++ [r2R s]) s ∧ (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint (r2R s) ∧
    (r2R s).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩ ∧ (s.gpr .r12).toNat + (r2R s).len ≤ 2 ^ 64 ∧
    Spec.Rsa.wordsAt s.mem (s.gpr .r12) (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat) =
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) ++
        Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  post := postCore
  pub s₁ s₂ := pubCore s₁ s₂ ∧ s₁.gpr .r12 = s₂.gpr .r12

end VG.Proof.Bignum.PPC64LE.Crt
