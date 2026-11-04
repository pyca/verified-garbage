module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's check of an encoding on x86-64: the contract on the registers

`chkK T Hs Gs` is the contract of `checkEncoding` (an internal function of
verification): EMSA-PSS-VERIFY with the hash function `Hs` and MGF1's `Gs`,
those of the tables `hash` and `mgf1` it takes (`TabsAt`), with the stack
the frame and the calls use, `chkStack`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

/-- The stack below the stack pointer: the frame, the return address of
its calls, and that of the calls of MGF1's streaming functions. -/
def chkStack : Nat := 392 + 16

variable (T : Tabs) (Hs Gs : Spec.Mgf1.Hash)

/-- `check_encoding(digest = rdi, em = rsi, em_len = rdx, em_bits = rcx,
salt_len = r8, any_salt_len = r9d, scratch = [rsp + 8], scratch_len,
hash, mgf1 = [rsp + 32])`. -/
def chkK : Contract isa where
  pre s :=
    let dg : Region := ⟨s.gpr .rdi, T.H.D⟩
    let em : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let tH : Region := ⟨stackArg s 2, 40⟩
    let tG : Region := ⟨stackArg s 3, 40⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩
    chkStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [dg, em, tH, tG, args] ∧ s.wr = [scr] ∧
      dg.Disjoint scr ∧ em.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint dg ∧ ret.Disjoint em ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint dg ∧ stk.Disjoint em ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + T.H.D ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ Proof.RsaPss.maxEmBits ∧
      (s.gpr .rdx).toNat = Spec.RsaPss.emLength (s.gpr .rcx).toNat ∧
      Proof.RsaPss.encodingScratchWords ≤ (stackArg s 1).toNat ∧
      scr.Disjoint tH ∧ scr.Disjoint tG ∧ ret.Disjoint tH ∧ ret.Disjoint tG ∧ stk.Disjoint tH ∧ stk.Disjoint tG ∧
      (stackArg s 2).toNat + 40 ≤ 2 ^ 64 ∧ (stackArg s 3).toNat + 40 ≤ 2 ^ 64 ∧
      TabsAt T.H T.dn T.f T.G T.g (stackArg s 2) (stackArg s 3) s
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPss.verifyEncoding Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) T.H.D)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (s.gpr .rcx).toNat
        (Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32)) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32 ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      tabWords s₁.mem (stackArg s₁ 2) (stackArg s₁ 3) = tabWords s₂.mem (stackArg s₂ 2) (stackArg s₂ 3)

end VG.Proof.RsaPss.X86_64
