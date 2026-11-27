module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Spec.RsaPss

/-! ### `RsaPss.X86_64.EncCtx`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's encoding on x86-64: the contract on the registers

`encK T Hs Gs` is the contract of `encode` (an internal function of
signing): EMSA-PSS-ENCODE with the hash function `Hs` and MGF1's `Gs`, those
of the tables `hash` and `mgf1` it takes (`TabsAt`: the table of `MdHash` of
`T.H` and the table of `MdHash` of `T.G`), with the stack the frame and the
calls use, `encStack`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

/-- The stack below the stack pointer: the frame, the return address of
its calls, and that of the calls of MGF1's streaming functions. -/
def encStack : Nat := 392 + 16

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

variable (T : Tabs) (Hs Gs : Spec.Mgf1.Hash)

/-- `encode(em = rdi, em_len = rsi, digest = rdx, salt = rcx, salt_len = r8,
em_bits = r9, scratch = [rsp + 8], scratch_len, hash, mgf1 = [rsp + 32])`. -/
def encK : Contract isa where
  pre s :=
    let em : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let dg : Region := ⟨s.gpr .rdx, T.H.D⟩
    let sa : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let tH : Region := ⟨stackArg s 2, 56⟩
    let tG : Region := ⟨stackArg s 3, 56⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩
    encStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [dg, sa, tH, tG, args] ∧ s.wr = [em, scr] ∧
      em.Disjoint dg ∧ em.Disjoint sa ∧ em.Disjoint scr ∧ em.Disjoint args ∧
      dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint em ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint em ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + T.H.D ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ Proof.RsaPss.maxEmBits ∧
      (s.gpr .rsi).toNat = Spec.RsaPss.emLength (s.gpr .r9).toNat ∧
      Proof.RsaPss.encodingScratchWords ≤ (stackArg s 1).toNat ∧
      em.Disjoint tH ∧ em.Disjoint tG ∧ scr.Disjoint tH ∧ scr.Disjoint tG ∧ ret.Disjoint tH ∧ ret.Disjoint tG ∧
      stk.Disjoint tH ∧ stk.Disjoint tG ∧ (stackArg s 2).toNat + 56 ≤ 2 ^ 64 ∧ (stackArg s 3).toNat + 56 ≤ 2 ^ 64 ∧
      TabsAt T.H T.dn T.f T.G T.g (stackArg s 2) (stackArg s 3) s
  post s s' :=
    match Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) T.H.D)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (s.gpr .r9).toNat with
    | some e => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.bytesAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = e
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      tabWords s₁.mem (stackArg s₁ 2) (stackArg s₁ 3) = tabWords s₂.mem (stackArg s₂ 2) (stackArg s₂ 3)

end VG.Proof.RsaPss.X86_64

end

end

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
    let tH : Region := ⟨stackArg s 2, 56⟩
    let tG : Region := ⟨stackArg s 3, 56⟩
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
      (stackArg s 2).toNat + 56 ≤ 2 ^ 64 ∧ (stackArg s 3).toNat + 56 ≤ 2 ^ 64 ∧
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
