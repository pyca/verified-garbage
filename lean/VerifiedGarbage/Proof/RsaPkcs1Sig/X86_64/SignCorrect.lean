module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Sign
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! ### `RsaPkcs1Sig.X86_64.SignCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86_64.SignEntry`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86_64.SignBlocks`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86_64.SignCtx`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the contract on the registers

`sigContract` states the shared contract (with the stack the frame and the
call of `vg_rsa_private_checked` use, `sigStack`) on the registers and the
stack (`sign_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_sign` uses: its frame of
1192 bytes, the return address of its call, and the 3256 bytes its callee
`vg_rsa_private_checked` uses. -/
def sigStack : Nat := 4456

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- `vg_rsa_pkcs1_sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), digest = [rsp + 16],
digest_len = [rsp + 24], p = [rsp + 32], p_len = [rsp + 40], q = [rsp + 48],
q_len = [rsp + 56], dp = [rsp + 64], dp_len = [rsp + 72], dq = [rsp + 80],
dq_len = [rsp + 88], qinv = [rsp + 96], qinv_len = [rsp + 104],
scratch = [rsp + 112], scratch_len = [rsp + 120])`, using `sigStack` bytes of
stack. -/
def sigContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let dig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let p : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
    let q : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
    let dp : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
    let dq : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
    let qi : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
    let scr : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩
    sigStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint dig ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧ (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64 ∧
      (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64 ∧ (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 4).toNat ∧ (stackArg s 4).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 6).toNat ∧
      (stackArg s 6).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 8).toNat = (stackArg s 4).toNat ∧
      (stackArg s 12).toNat = (stackArg s 4).toNat ∧ (stackArg s 10).toNat = (stackArg s 6).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 14).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
        ((stackArg s 0).setWidth 32).toNat
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      (List.range 14).map (fun i => stackArg s₁ (i + 1)) = (List.range 14).map (fun i => stackArg s₂ (i + 1)) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

end VG.Proof.RsaPkcs1Sig.X86_64

end

end

/-! ### `RsaPkcs1Sig.X86_64.SignFrame`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, below which the
call of `vg_rsa_private_checked` uses 3264 bytes; its slots, and the
function's stack arguments, at `S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []

/-! ## The precondition, by name -/

/-- `sigContract.pre`, by name. -/
structure PreS (s : State) : Prop where
  sp1 : sigStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64
  hrd : ∀ r ∈ ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩] : List Region), r ∈ s.rd
  /-- The stack arguments, in a readable region of at least 120 bytes. -/
  hra : ∃ A, 120 ≤ A ∧ A < 2 ^ 32 ∧ (⟨stackArgAddr s 0, A⟩ : Region) ∈ s.rd
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dds : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dps : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqs : (⟨stackArg s 5, (stackArg s 6).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddps : (⟨stackArg s 7, (stackArg s 8).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddqs : (⟨stackArg s 9, (stackArg s 10).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqis : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dsa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wD : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wP : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wQ : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wDp : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wDq : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wQi : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wS : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 4).toNat
  pl2 : (stackArg s 4).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 6).toNat
  ql2 : (stackArg s 6).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 8).toNat = (stackArg s 4).toNat
  hqil : (stackArg s 12).toNat = (stackArg s 4).toNat
  hdql : (stackArg s 10).toNat = (stackArg s 6).toNat
  hsl : 16 * (s.gpr .rcx).toNat + 32 ≤ (stackArg s 14).toNat

/-! ## The frame -/

abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 sigStack

def stkR (s : State) : Region := ⟨kb s, sigStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The frame's base, from the stack's: `frameBytes` above it, below which
the call uses `sigStack - frameBytes` bytes. -/
theorem fb_eq (s : State) : fb s = off (kb s) (sigStack - frameBytes) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem kb_toNat {s : State} (hp : PreS s) : (kb s).toNat + sigStack + 128 ≤ 2 ^ 64 ∧
    (kb s).toNat + sigStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold sigStack at *; omega_arith

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]

theorem fb_toNat {s : State} (hp : PreS s) : (fb s).toNat + frameBytes + 8 + 120 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + (sigStack - frameBytes) := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold sigStack frameBytes at *; omega_using [h1])]
  unfold frameBytes sigStack at *; omega_using [h1]

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold sigStack frameBytes; omega_using [h])

theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega_using [hlt]
  have := frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sOl : word t.mem (fb s) oOl = s.gpr .rsi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

/-- `Env` but for the slots of `out` and `out_len`, which the call of
`vg_rsa_private_checked_precomputed` takes for its stack arguments; nothing
reads them after it. -/
structure EnvC (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.core {s t : State} (h : Env s t) : EnvC s t :=
  ⟨h.rsp, h.rd, h.wr, h.mem, h.sN, h.sK, h.sE, h.sEl⟩

theorem EnvC.scr {s t : State} (h : EnvC s t) (hp : PreS s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

theorem Env.scr {s t : State} (h : Env s t) (hp : PreS s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

theorem arg_outside {s : State} (hp : PreS s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 15) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

theorem Env.arg {s t : State} (h : Env s t) (hp : PreS s) {j : Nat} (hj : j < 15) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem arg_in {s t : State} (hp : PreS s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  obtain ⟨A, hA, hA', hm⟩ := hp.hra
  exact ⟨⟨stackArgAddr s 0, A⟩, List.mem_append_left _ (by rw [hrd]; exact hm),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj, hA]) (by omega_using [hj])⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = fb s) (j : Nat) : t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega_using [hd])).word (by omega_using [h]) (by omega_using [hd'])

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

end

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the blocks around the encoding and the call

The frame's push, the slots and the arguments of `encode` (`head_ok`, and
`encPre`, what `encode` needs), the zeros to `out` if it fails
(`zeroSlots_ok`), the arguments of `vg_rsa_private_checked` (`callArgs_ok`),
and the zeros to `EM` after the call (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame outside its slots or in `out`. -/
theorem Env.of {s t u : State} (he : Env s t) (hp : PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ (d + n ≤ oOut ∨ oEM ≤ d) ∧ d + n ≤ frameBytes) ∨
      r = outR s) : Env s u := by
  have hsl : ∀ {d}, oOut ≤ d → d + 8 ≤ oEM → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold oOut oEM at *; omega_arith) (by unfold frameBytes oEM at *; omega_arith)
          (by unfold frameBytes at *; omega_arith)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM frameBytes at *; omega_arith)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

/-- `EnvC` past changes of the registers but `rsp`, and of memory in the
frame outside its slots from `n`'s or in `out`. -/
theorem EnvC.of {s t u : State} (he : EnvC s t) (hp : PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ (d + n ≤ oN ∨ oEM ≤ d) ∧ d + n ≤ frameBytes) ∨
      r = outR s) : EnvC s u := by
  have hsl : ∀ {d}, oN ≤ d → d + 8 ≤ oEM → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold oN oEM at *; omega_arith) (by unfold frameBytes oEM at *; omega_arith)
          (by unfold frameBytes at *; omega_arith)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM frameBytes at *; omega_arith)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `EnvC` past changes of the registers but `rsp`. -/
theorem EnvC.regs {s t u : State} (he : EnvC s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : EnvC s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE,
    hm ▸ he.sEl⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : PreS s) (h : d + n ≤ frameBytes) :
    ∀ i < n, InRegions (⟨fb s, frameBytes⟩ :: s.wr) (off (fb s) d + BitVec.ofNat 64 i) 1 := by
  have := fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show off (fb s) d + BitVec.ofNat 64 i = off (fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega_arith) (by unfold frameBytes at *; omega_arith)

/-! ## The head -/

/-- The frame's push, the slots and the arguments of `encode`. -/
theorem head_ok {s : State} (hp : PreS s) :
    WP isa (.block (slotStores ++ encArgs)) (allocState frameBytes s) fun t => Env s t ∧
      t.gpr .r8 = off (fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2 ∧ (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := fb_toNat hp
  let A := allocState frameBytes s
  try rewrite [show allocState frameBytes s = A from rfl] at *
  have hA : A = allocState frameBytes s := rfl
  have hsp : A.gpr .rsp = fb s := rfl
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oOl) (s.gpr .rsi)).writeW
        (off (fb s) oN) (s.gpr .rdx)).writeW (off (fb s) oK) (s.gpr .rcx)).writeW (off (fb s) oE)
        (s.gpr .r8)).writeW (off (fb s) oEl) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := oN) (by decide), hs.st (d := oK) (by decide), hs.st (d := oE) (by decide),
      hs.st (d := oEl) (by decide)]
    rfl) rfl) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega_arith
    unfold frameBytes at hx hx'
    simp only [oOut, oOl, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
  have hslots : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oOl = s.gpr .rsi ∧
      word t₁.mem (fb s) oN = s.gpr .rdx ∧ word t₁.mem (fb s) oK = s.gpr .rcx ∧
      word t₁.mem (fb s) oE = s.gpr .r8 ∧ word t₁.mem (fb s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oOl, oN, oK, oE, oEl, and_self]
  have hsp₁ : t₁.gpr .rsp = fb s := (k₁.gpr (by decide)).trans hsp
  have hrd : t₁.rd = s.rd := k₁.2.1
  have g : ∀ r, r ≠ .rsp → t₁.gpr r = s.gpr r := fun r h => by
    rw [k₁.gpr (by simp)]; simp [hA, allocState_gpr, h]
  refine WP.mono (WP.keep [.r8, .rdx, .rsi, .r9] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r8 = off (fb s) oEM ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2) (by
    xrun [encArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp₁,
      sx_ofNat (show oEM < 2 ^ 31 by decide), arg_in hp hrd (show 0 < 15 by decide),
      arg_in hp hrd (show 1 < 15 by decide), arg_in hp hrd (show 2 < 15 by decide),
      arg_outside hp ho₁ (show 0 < 15 by decide), arg_outside hp ho₁ (show 1 < 15 by decide),
      arg_outside hp ho₁ (show 2 < 15 by decide)]) rfl) fun t ⟨⟨hm, h8, hdx, hsi, h9⟩, k⟩ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hslots
  refine ⟨⟨(k.gpr (by decide)).trans hsp₁, k.2.1.trans hrd, k.2.2.trans k₁.2.2, frame_of_outside (hm ▸ ho₁),
    hm ▸ h1, hm ▸ h2, hm ▸ h3, hm ▸ h4, hm ▸ h5, hm ▸ h6⟩, h8, by rw [k.gpr (by decide), g _ (by decide)],
    hdx, hsi, h9, fun r hr hr' => ?_⟩
  rw [k.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all),
    g r hr']

/-- What `encode` needs, from the head. -/
theorem encPre {s t : State} (hp : PreS s) (he : Env s t) (h8 : t.gpr .r8 = off (fb s) oEM)
    (hcx : t.gpr .rcx = s.gpr .rcx) (hdx : t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (hsi : t.gpr .rsi = stackArg s 1) (h9 : t.gpr .r9 = stackArg s 2) :
    EPre t ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk2 := hp.k2
  have hdl := hp.wD
  have sEM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) :=
    frame_sub s (by unfold oEM frameBytes; omega_arith)
  exact {
    rdx := by rw [hdx]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx]
    kle := hk2
    buf := fun i hi => by rw [h8, he.wr]; exact frame_bytes hp (by unfold oEM frameBytes; omega_arith) i hi
    rd := fun j hj => by
      rw [hsi, he.rd, he.wr]
      rw [h9] at hj
      exact ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (hp.hrd _ (by simp)),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    sep := fun j hj i hi => by
      rw [hsi, h8]
      rw [h9] at hj
      exact ne_of_disjoint (hp.dKd.sub_left sEM).symm (by omega_arith) (by omega_arith) hj hi }

/-! ## Zeros to `out` -/

/-- The address and length of `out`, from their slots. -/
theorem zeroHead_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) t
      fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

theorem zeroSlots_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa zeroSlots t fun u => Env s u ∧ (u.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsiK := hp.hsi
  unfold zeroSlots
  refine WP.seq (WP.mono (zeroHead_ok hp he) fun t₁ ⟨k₁, hm₁, hdi, hsi⟩ => ?_)
  have hwr : outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [outR]
  refine WP.mono (Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega_arith) (by omega_arith)
    (by rw [hsi, Rec.ofNat_toNat64]) (by
      rw [hdi]; intro i hi; exact ⟨_, hwr, Offset.contains_base _ (by have := hp.wO; omega_arith) (by omega_arith)⟩))
    fun u ⟨hK, hm, hax⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hm, hdi, ← hsiK]
    have := bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega_arith)
    rwa [List.length_replicate] at this

/-! ## The arguments of the call -/

/-- The call's stack argument `i`: `EM`, `n_len`, then the function's stack
arguments from `p` on. -/
def callArg (s : State) : Nat → BitVec 64
  | 0 => off (fb s) oEM
  | 1 => s.gpr .rcx
  | i + 2 => stackArg s (i + 3)

/-- Stack argument `j + 3` to the frame's word `j + 2`. -/
theorem copyArg_ok {s t : State} (hp : PreS s) (he : Env s t) {j : Nat} (hj : j < 12) :
    WP isa (.block (copyArg j)) t fun t' => Env s t' ∧
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3)) ∧ Keep [.rax] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax] (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3))) (by
    xrun [copyArg, @arg_ea s, ea_sp, he.rsp, arg_in hp he.rd (show j + 3 < 15 by omega_arith),
      he.arg hp (show j + 3 < 15 by omega_arith), hs.st (d := 8 * (j + 2)) (by unfold frameBytes; omega_arith)]) rfl)
    fun t' ⟨hm, k⟩ => ⟨Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 (hm ▸ (Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
      ⟨8 * (j + 2), 8, List.mem_singleton.mp hr, .inl (by unfold oOut; omega_arith), by unfold frameBytes; omega_arith⟩, hm, k⟩

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : PreS s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), Env s t →
    WP isa (.block ((List.range n).flatMap copyArg)) t fun t' => Env s t' ∧
      (∀ i < n, word t'.mem (fb s) (8 * (i + 2)) = stackArg s (i + 3)) ∧
      (∀ d, d + 8 ≤ 16 ∨ 16 + 8 * n ≤ d → d + 8 ≤ frameBytes → word t'.mem (fb s) d = word t.mem (fb s) d) ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax] t t'
  | 0, _, t, he => WP.block_nil ⟨he, fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Frame.refl _ _,
      Keep.refl _ _⟩
  | n + 1, hn, t, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copies_ok hp n (by omega_arith) t he) fun t₁ ⟨he₁, hw₁, hk₁, hf₁, k₁⟩ => ?_
    refine WP.mono (copyArg_ok hp he₁ (show n < 12 by omega_arith)) fun t' ⟨he', hm, k'⟩ =>
      ⟨he', fun i hi => ?_, fun d hd hd' => ?_, hf₁.trans (hm ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * (n + 2)) (n := 8) (k := 112)
          (by omega_arith) (by omega_arith))), (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [word_wo _ _ _ (.inr (by omega_arith)) (by unfold frameBytes at *; omega_arith) (by unfold frameBytes at *; omega_arith)]
        exact hw₁ i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm, word_wo _ _ _ (by omega_arith) (by unfold frameBytes at *; omega_arith) (by unfold frameBytes at *; omega_arith)]
      exact hk₁ d (by omega_arith) hd'

theorem callArgs_eq : callArgs =
    (([.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl)), .mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)),
      .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] : List Instr) ++ lea .rax oEM ++
      ([.store (sp 0) .rax, .store (sp 8) .rcx] : List Instr)) ++ (List.range 12).flatMap copyArg := by
  simp only [callArgs, List.append_assoc]

/-- The arguments of `vg_rsa_private_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block callArgs) t fun t' => Env s t' ∧ (∀ i < 14, word t'.mem (fb s) (8 * i) = callArg s i) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hs := he.scr hp
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  rw [callArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.mem = (t.mem.writeW (fb s) (off (fb s) oEM)).writeW (off (fb s) 8) (s.gpr .rcx) ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
      u.gpr .rcx = s.gpr .rcx ∧ u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = s.gpr .r9) (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, h0, h8, hs.st (d := 8) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), hs.ld (d := oN) (by decide),
      hs.ld (d := oK) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      he.sOut, he.sOl, he.sN, he.sK, he.sE, he.sEl, sx_ofNat (show oEM < 2 ^ 31 by decide)]) rfl) fun u ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have f : Frame [⟨fb s, 64 / 8⟩, ⟨off (fb s) 8, 64 / 8⟩] t.mem u.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have f' : Frame [⟨fb s, 112⟩] t.mem u.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base (fb s) (d := 8) (n := 8) (k := 112) (by decide)⟩
  have heu : Env s u := by
    refine Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 f fun r hr => .inl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 8, by simp [off], .inl (by decide), by decide⟩
    · exact ⟨8, 8, rfl, .inl (by decide), by decide⟩
  refine WP.mono (copies_ok hp 12 (Nat.le_refl _) u heu) fun t' ⟨he', hw, hk, hf', k'⟩ =>
    ⟨he', fun i hi => ?_, by rw [k'.gpr (by decide), hdi], by rw [k'.gpr (by decide), hsi],
      by rw [k'.gpr (by decide), hdx], by rw [k'.gpr (by decide), hcx], by rw [k'.gpr (by decide), h8],
      by rw [k'.gpr (by decide), h9], f'.trans hf', (k.trans k').mono (by decide)⟩
  match i, hi with
  | 0, _ =>
    rw [hk 0 (.inl (by decide)) (by decide), hm]
    have := word_wo (t.mem.writeW (fb s) (off (fb s) oEM)) (fb s) (d := 8) (d' := 0) (s.gpr .rcx)
      (.inr (by decide)) (by decide) (by decide)
    rw [this]; exact Ver.word_self0 _ _ _
  | 1, _ =>
    rw [hk 8 (.inl (by decide)) (by decide), hm]; exact word_writeW_self _ _ _ _
  | i + 2, hi => exact hw i (by omega_arith)

/-- The count and address of `EM`'s bytes, and the zero byte. -/
theorem wipeHead_ok {s t : State} (hp : PreS s) (he : EnvC s t) :
    WP isa (.block (([.mov .r11 (.mem (sp oK)), .mov32 .rdx (.imm 0)] : List Instr) ++ lea .r10 oEM)) t fun u =>
      Keep [.r11, .rdx, .r10] t u ∧ u.mem = t.mem ∧ u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧
      u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r11, .rdx, .r10] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM) (by
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, hs.ld (d := oK) (by decide), he.sK,
      sx_ofNat (show oEM < 2 ^ 31 by decide), Rec.ofNat_toNat64]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

/-- `EM` overwritten with zeros, keeping `rax`. -/
theorem wipe_ok {s t : State} (hp : PreS s) (he : EnvC s t) :
    WP isa wipe t fun u => EnvC s u ∧ u.gpr .rax = t.gpr .rax ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat := by
  have hs := he.scr hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  unfold wipe
  refine WP.seq (WP.mono (wipeHead_ok hp he) fun t₁ ⟨k₁, hm₁, h11, hdx, h10⟩ => ?_)
  have he₁ : EnvC s t₁ := he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2
  refine wp_countdown (cnt := .r11) (N := (s.gpr .rcx).toNat) (by omega_arith) (by omega_arith)
    (fun i u => EnvC s u ∧ Keep [.r11, .rdx, .r10] t₁ u ∧ u.gpr .rdx = 0 ∧
      u.gpr .r10 = off (fb s) (oEM + i) ∧
      u.mem = writeBytes t₁.mem (off (fb s) oEM) (List.replicate i 0)) ?_ (fun u ⟨heu, ku, _, _, hmu⟩ => ?_)
    ⟨he₁, Keep.refl _ _, hdx, by rw [h10]; rfl, by simp only [List.replicate_zero, writeBytes_nil]⟩ h11
  · intro i hi u ⟨heu, ku, hdxu, h10u, hmu⟩ _
    have hA : InRegions u.wr (u.gpr .r10) 1 := by
      rw [h10u, heu.wr]
      obtain ⟨r, h, c⟩ := frame_bytes hp (d := oEM + i) (n := 1) (by unfold oEM frameBytes; omega_arith) 0 (by decide)
      exact ⟨r, h, by simpa only [BitVec.add_zero, off] using c⟩
    refine WP.mono (WP.keep [.r10, .r11] (Q := fun u' => u'.mem = u.mem.writeW (u.gpr .r10) (0 : Byte) ∧
        u'.gpr .r10 = u.gpr .r10 + 1 ∧ u'.gpr .r11 = u.gpr .r11 - 1 ∧ u'.zf = some (u.gpr .r11 - 1 == 0)) (by
      xrun [ea0, hA, hdxu]; rfl) rfl) fun u' ⟨⟨hm', h10', h11', hz⟩, k'⟩ => ⟨⟨?_, (ku.trans k').mono (by simp),
        by rw [k'.gpr (by decide), hdxu], ?_, ?_⟩, h11', hz⟩
    · refine EnvC.of heu hp (k'.gpr (by decide)) k'.2.1 k'.2.2 (hm' ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
        ⟨oEM + i, 1, by rw [List.mem_singleton.mp hr, h10u], .inr (by unfold oEM; omega_arith),
          by unfold oEM frameBytes; omega_arith⟩
    · rw [h10', h10u]; exact off_off _ _ _
    · rw [hm', hmu, h10u, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega_arith), List.length_replicate,
        show off (fb s) oEM + BitVec.ofNat 64 i = off (fb s) (oEM + i) from off_off _ _ _]
  · refine ⟨heu, ku.gpr (by decide) |>.trans (k₁.gpr (by decide)), ?_⟩
    rw [hmu, hm₁]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (frame_writeBytes t.mem _ _).bytes (R := ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by dsimp only; omega_arith) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, List.length_replicate]
    have h := hp.dKo.sub_left (frame_sub s (d := oEM) (n := (s.gpr .rcx).toNat)
      (by unfold oEM frameBytes; omega_arith))
    rw [hp.hsi] at h
    exact h.symm

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

end

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the entry of `vg_rsa_private_checked`

Everything the call uses is in the function's stack, at offsets of its
base `kb`: the callee's stack (`stackBytes` bytes at `kb`), the return
address (at `kb + stackBytes`), and the frame above (at
`kb + stackBytes + 8`), which holds the call's stack arguments and `EM`. Its
precondition at the call (`priv_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (chkContract stackBytes)

theorem fb_kb (s : State) : fb s = off (kb s) 3264 := fb_eq s

/-- The callee's stack pointer. -/
theorem fb_sub8 (s : State) : fb s - 8 = off (kb s) 3256 := by
  rw [fb_kb, off, off, show (3264 : Nat) = 3256 + 8 from rfl, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem ksub (s : State) {d n : Nat} (h : d + n ≤ sigStack) : Region.Sub ⟨off (kb s) d, n⟩ (stkR s) :=
  Offset.sub_base _ h

theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 100) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 3256 + 8 * (i + 1)) (n := 8) (e := 3256) (k := 8) (by omega_using []) (by omega_using [hi])
    (by omega_using [])
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [off, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_kb, off_off, show 3256 + 8 * (i + 1) = 3264 + 8 * i by omega_using []]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_kb, off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `EM`, as the call's input. -/
def emR (s : State) : Region := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩

/-- What the call reads: `n`, `e`, `EM`, the key's parts and its stack
arguments. -/
def privRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, emR s,
    ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat⟩,
    ⟨stackArg s 7, (stackArg s 8).toNat⟩, ⟨stackArg s 9, (stackArg s 10).toNat⟩,
    ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out` and the working space. -/
def privWr (s : State) : List Region := [outR s, scrR s]

theorem priv_pre {s t : State} (hp : PreS s) (hsp : t.gpr .rsp = fb s)
    (hw : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContract.pre (t.callEntry.withRegions (privRd s) (privWr s)) := by
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = callArg s i :=
    fun i hi => (stackArg_entry hsp _ _ (by omega_using [hi])).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega_using [hj])
  simp only [chkContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), callArg,
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 5 (by decide) : stackArg _ 7 = _),
    (hE2 6 (by decide) : stackArg _ 8 = _), (hE2 7 (by decide) : stackArg _ 9 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _), (hE2 9 (by decide) : stackArg _ 11 = _),
    (hE2 10 (by decide) : stackArg _ 12 = _), (hE2 11 (by decide) : stackArg _ 13 = _), fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have e1 : sigStack = 4456 := rfl
  have e2 : oEM = 160 := rfl
  have e3 : stackBytes = 3256 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hfb : fb s = off (kb s) 3264 := fb_kb s
  have hem : off (fb s) oEM = off (kb s) 3424 := by rw [hfb, off_off]; rfl
  have sM : Region.Sub (emR s) (stkR s) := by simp only [emR]; rw [hem]; exact ksub s (by omega_using [e1, hk2])
  have sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by rw [hfb]; exact ksub s (by decide)
  have sR : Region.Sub ⟨off (kb s) 3256, 8⟩ (stkR s) := ksub s (by decide)
  have sK : Region.Sub ⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ (stkR s) := by
    rw [show off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s from BitVec.add_sub_cancel _ _]
    exact Region.sub_prefix (by decide)
  have hkk : off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s := BitVec.add_sub_cancel _ _
  have dMA : (emR s).Disjoint ⟨fb s, 112⟩ := by
    simp only [emR]; rw [hem, hfb]; exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hk2]) (by omega_using [])
  have dRM : (⟨off (kb s) 3256, 8⟩ : Region).Disjoint (emR s) := by
    simp only [emR]; rw [hem]; exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using []) (by omega_using [hk2])
  have dRA : (⟨off (kb s) 3256, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using []) (by omega_using [])
  have dKM : (⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ : Region).Disjoint (emR s) := by
    simp only [emR]; rw [hkk, hem]; exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hk2])
  have dKA : (⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hkk, hfb]; exact Offset.base_disjoint _ (by omega_using []) (by omega_using [])
  have wM : (off (fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hem, toNat_off (by omega_using [hK1, e1])]; omega_using [hK1, e1, hk2]
  have hR : (off (kb s) 3256).toNat = (kb s).toNat + 3256 := toNat_off (by omega_using [hK1, e1])
  have dK := hp.dKo; have dKn := hp.dKn; have dKe := hp.dKe; have dKp := hp.dKp; have dKq := hp.dKq
  have dKdp := hp.dKdp; have dKdq := hp.dKdq; have dKqi := hp.dKqi; have dKs := hp.dKs
  refine ⟨by omega_using [e3, hR], by omega_using [hK1, e1, hR], rfl, rfl, hp.dOn, hp.dOe, (dK.sub_left sM).symm, hp.dOp, hp.dOq, hp.dOdp, hp.dOdq,
    hp.dOqi, hp.dOs, (dK.sub_left sA).symm,
    hp.dns, hp.des, dKs.sub_left sM, hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, (dKs.sub_left sA).symm,
    dK.sub_left sR, dKn.sub_left sR, dKe.sub_left sR, dRM, dKp.sub_left sR, dKq.sub_left sR, dKdp.sub_left sR,
    dKdq.sub_left sR, dKqi.sub_left sR, dKs.sub_left sR, dRA,
    dK.sub_left sK, dKn.sub_left sK, dKe.sub_left sK, dKM, dKp.sub_left sK, dKq.sub_left sK, dKdp.sub_left sK,
    dKdq.sub_left sK, dKqi.sub_left sK, dKs.sub_left sK, dKA,
    hp.wO, hp.wN, hp.wE, wM, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, hp.hsi, trivial, hp.L1,
    hp.L2, hp.pl1, hp.pl2, hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by simp only [Spec.Rsa.scratchWords]; exact hp.hsl⟩

/-! ## Memory across the call -/

/-- The callee's stack and the return address, below the frame. -/
theorem below_kb (s : State) : below (fb s) (3256 + 8) = ⟨kb s, 3264⟩ := by
  simp only [below]; rw [fb_kb]; exact congrArg (Region.mk · 3264) (BitVec.add_sub_cancel _ _)

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

/-- What the call writes is apart from the frame. -/
theorem frame_apart {s : State} (hp : PreS s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ privWr s ++ [below (fb s) (3256 + 8)], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.dKo.sub_left (frame_sub s hd))
  · exact (hp.dKs.sub_left (frame_sub s hd))
  · rw [below_kb, fb_kb, off_off]
    exact (Offset.base_disjoint (kb s) (e := 3264 + d) (n := n) (k := 3264) (by omega_using [])
      (by have := (kb_toNat hp).1; unfold frameBytes at hd; unfold sigStack at this; omega_using [hd])).symm

theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) :
    Frame [below (fb s) (3256 + 8)] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {p : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off p d, 8⟩ : Region).Disjoint r) : word m' p d = word m p d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

end

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the call of `vg_rsa_private_checked`

The private operation, for an implementation `v` of the CRT (`CrtImpl`), is
`vg_rsa_private_checked`'s code (`privCode v`), which has a frame of its own:
it uses 3256 bytes of stack (`privCode_depth`). Its arguments
(`callArgs_ok`) and the call (`priv_call`), which signs `EM` into `out`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract)

/-! ## The private operation -/

def pdName (v : CrtImpl) : String := v.pubOp.name

/-- What a call of the private operation on `EM` gives, from `t`: `out`
holds the signature of `EM`, or zeros; the frame is kept. -/
def PrivPost (s t t' : State) : Prop :=
  EnvC s t' ∧
    Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)) ∧
    (∀ d n, d + n ≤ frameBytes → ∀ i < n,
      t'.mem (off (fb s) d + BitVec.ofNat 64 i) = t.mem (off (fb s) d + BitVec.ofNat 64 i)) ∧
    (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10

/-- A call of code that does what `vg_rsa_private_checked` does (`k`, with
its postcondition), given what it reads (`rds`, `privRd` and more). -/
theorem privWith_call {name : String} {code : Prog isa} {k : Contract isa}
    (hcorr : ∀ s, k.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hk : ∀ a b, k.post a b → chkContract.post a b) (hsp : code.all (fun i => !isa.writesSp i) = true)
    (hd : code.x86_64Depth = 3256) {s t : State} (hp : PreS s) (he : EnvC s t) {rds : List Region}
    (hw : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9)
    (hpre : k.pre (t.callEntry.withRegions rds (privWr s)))
    (hc : Covers (rds ++ privWr s) (t.rd ++ t.wr)) (hcw : Covers (privWr s) t.wr) :
    WP isa (.call name code) t (PrivPost s t) := by
  refine WP.call_sp_mx (k := k) hcorr (SpSafe.of_all hsp) (by rw [hd]; decide) hpre hc hcw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  replace hpost := hk _ _ hpost
  rw [hd, he.rsp] at hf
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions rds (privWr s)) i = callArg s i :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_using [hi])).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions rds (privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega_using [hj])
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr, below_kb]; exact .inl (Region.sub_prefix (by decide))
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  have hEM : Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) oEM) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (callEntry_frame he.rsp).bytes
      (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩) (fun r hr => ?_) (by dsimp only; omega_using []) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, below_kb, fb_kb, off_off]
    exact (Offset.base_disjoint (kb s) (e := 3264 + oEM) (n := (s.gpr .rcx).toNat) (k := 3264) (by omega_using [])
      (by have := (kb_toNat hp).1; unfold oEM; unfold sigStack at this; omega_using [hk2])).symm
  simp only [chkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE 0 (by decide), callArg, hm₂, hg₂ .rax (by decide),
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 6 (by decide) : stackArg _ 8 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_using []), b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []),
    hEM, b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega_using []), b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega_using []),
    ← hp.hdpl, b hp.dKdp hp.dOdp hp.ddps.symm (by have := hp.wDp; omega_using []), hp.hdpl,
    ← hp.hdql, b hp.dKdq hp.dOdq hp.ddqs.symm (by have := hp.wDq; omega_using []), hp.hdql,
    ← hp.hqil, b hp.dKqi hp.dOqi hp.dqis.symm (by have := hp.wQi; omega_using []), hp.hqil] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_⟩, hpost, fun d n hd i hi => ?_, hcs, hmx⟩
  · simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (Ver.sub_refl _))
    · exact .inr (.inr (Ver.sub_refl _))
    · rw [below_kb]; exact .inl (Region.sub_prefix (by decide))
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sN
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sK
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sE
  · rw [slot_keep hf (frame_apart hp (by decide))]; exact he.sEl
  · have := (fb_toNat hp).1
    exact hf.bytes (R := ⟨off (fb s) d, n⟩) (frame_apart hp hd) (by dsimp only; unfold frameBytes at hd; omega_using [hd]) hi

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

end

/-!
# `vg_rsa_pkcs1_sign` on x86-64: correctness

The encoding into `EM`, then zeros to `out` if it fails, or the private
operation on `EM` and zeros to `EM` (`afterEnc_ok`); the whole function
(`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (test0_ok freed)

theorem writtenOutcome_of {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out n = Spec.Rsa.bytesAt m out n) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  cases o <;> exact ⟨h.1, hb.trans h.2⟩

/-- The result of the private operation on the encoding `o`, or `invalid`. -/
def privOut (s : State) : Option (List Byte) → Spec.Rsa.Outcome
  | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
  | none => .invalid

/-- What the call of the private operation on `EM` (`em`, in `t`) gives:
`out` holds its result. -/
def CallOut (s t : State) (em : List Byte) (u : State) : Prop :=
  EnvC s u ∧
    Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32) (privOut s (some em)) ∧
    (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10

/-- After the encoding, whose result is `o`, with the arguments `args` of
the call `call` (`hcall`). -/
theorem afterEncWith_ok {args : List Instr} {privName : String} {priv : Prog isa} {s t₁ t₂ : State} (hp : PreS s)
    (he₁ : Env s t₁) (h8₁ : t₁.gpr .r8 = off (fb s) oEM) (hK₂ : Keep clob t₁ t₂) {o : Option (List Byte)}
    (hlen : ∀ em, o = some em → em.length = (s.gpr .rcx).toNat) (hpost : EOut t₁ t₂ o)
    (hcall : ∀ t em, Env s t → Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em →
      WP isa (.block args) t fun u => WP isa (.call privName priv) u (CallOut s t em)) :
    WP isa (afterEncWith args privName priv) t₂ fun u => EnvC s u ∧
      Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32)
        (privOut s o) ∧
      (∀ r ∈ calleeSaved, u.gpr r = t₂.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t₂.mxcsr.extractLsb' 6 10 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  unfold afterEncWith
  refine WP.seq (WP.mono_mx (by decide) (test0_ok t₂) fun t₃ ⟨hs₃, hz₃⟩ hmx₃ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₂⟩ := hpost
    have he₃ : Env s t₃ := he₁.regs (by rw [hs₃.1, hK₂.gpr (by decide)]) (hs₃.2.1.trans hm₂)
      (hs₃.2.2.1.trans hK₂.2.1) (hs₃.2.2.2.trans hK₂.2.2)
    refine WP.ite true (by simp [eval, hz₃, hax]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (WP.keep [.rdi, .rsi, .r8, .r10, .rax] (zeroSlots_ok hp he₃) (by decide))
      fun u ⟨⟨heu, hax', hout⟩, ku⟩ hmx => ⟨heu.core, ⟨hax', hout⟩, fun r hr => ?_, by rw [hmx, hmx₃]⟩
    rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
      hs₃.1]
  | some em =>
    obtain ⟨hax, hm₂⟩ := hpost
    have hl : em.length = (s.gpr .rcx).toNat := hlen em rfl
    have he₂ : Env s t₂ := Env.of he₁ hp (hK₂.gpr (by decide)) hK₂.2.1 hK₂.2.2 (hm₂ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₁, hl], .inr (Nat.le_refl _),
        by unfold oEM frameBytes; omega_using [hk2]⟩
    have he₃ : Env s t₃ := he₂.regs (by rw [hs₃.1]) hs₃.2.1 hs₃.2.2.1 hs₃.2.2.2
    have hEM : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em := by
      have h₂ := bytesAt_writeBytes t₁.mem (off (fb s) oEM) em (by omega_using [hl])
      rw [hl] at h₂
      rw [hs₃.2.1, hm₂, h8₁, h₂]
    refine WP.ite false (by simp [eval, hz₃, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (hcall t₃ em he₃ hEM) fun t₄ h₄ => WP.seq (WP.mono h₄
      fun t₅ ⟨he₅, hout₅, hcs₅, hmx₅⟩ => ?_))
    refine WP.mono_mx (by decide) (WP.keep [.r11, .rdx, .r10] (wipe_ok hp he₅) (by decide))
      fun u ⟨⟨heu, haxu, hbytes⟩, ku⟩ hmxu => ⟨heu, ?_, fun r hr => ?_, ?_⟩
    · rw [haxu]; exact writtenOutcome_of hbytes hout₅
    · rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        hcs₅ r hr, hs₃.1]
    · rw [hmxu, hmx₅, hmx₃]

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them; the frame's bytes
then hold whatever they hold once released (`alloc_frame_ok`). -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ ∀ m u, Frame [⟨fb s, frameBytes⟩] s₂.mem m →
        Q { freed frameBytes s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q :=
  alloc_frame_ok (by decide) hsp hb

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreS s) {m : Mem} (h : Frame [stkR s, outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := sigStack) (d := 0) (k := 8)
      (by unfold sigStack; omega_using [])
    simpa only [stkR, kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem signId_eq (nB eB pB qB dPB dQB qInvB : List Byte) (x : BitVec 32) (H : List Byte) :
    Spec.RsaPkcs1Sig.signId nB eB pB qB dPB dQB qInvB x.toNat H =
      match encodeId x H nB.length with
      | some em => Spec.Rsa.privateChecked nB eB em pB qB dPB dQB qInvB
      | none => .invalid := by
  unfold Spec.RsaPkcs1Sig.signId encodeId Spec.RsaPkcs1Sig.sign
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat <;> rfl

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em : List Byte}
    (h : encodeId x H k = some em) : em.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- The function, with the code `ae` after the encoding, which does what
`afterEnc_ok` says (`hae`). -/
theorem codeWith_ok {ae : Prog isa} {s : State} (hp : PreS s)
    (hae : ∀ {t₁ t₂ : State}, Env s t₁ → t₁.gpr .r8 = off (fb s) oEM → Keep clob t₁ t₂ → ∀ {o : Option (List Byte)},
      (∀ em, o = some em → em.length = (s.gpr .rcx).toNat) → EOut t₁ t₂ o →
      WP isa ae t₂ fun u => EnvC s u ∧
        Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32) (privOut s o) ∧
        (∀ r ∈ calleeSaved, u.gpr r = t₂.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t₂.mxcsr.extractLsb' 6 10) :
    WP isa (.frame (.alloc frameBytes) (.seq (.block (slotStores ++ encArgs)) (.seq encode ae)) (.free frameBytes)) s
      fun s' => abiPreserved s s' ∧ sigContract.post s s' := by
  have hk2 := hp.k2
  refine wp_alloc (by have := hp.sp1; unfold sigStack at this; unfold frameBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono_mx (by decide) (head_ok hp) fun t₁ ⟨he₁, h8₁, hcx₁, hdx₁, hsi₁, h9₁, hcs₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (encode_ok (encPre hp he₁ h8₁ hcx₁ hdx₁ hsi₁ h9₁))
    fun t₂ ⟨hK₂, hout₂⟩ hmx₂ => ?_)
  refine WP.mono (hae he₁ h8₁ hK₂ (fun em h' => encodeId_length h') hout₂)
    fun u ⟨heu, hwu, hcsu, hmxu⟩ => ⟨heu.rsp, by rw [heu.wr]; rfl, fun m uu fm => ?_⟩
  have hs := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  simp only [off, BitVec.add_zero] at hs
  refine ⟨⟨fun r hr => ?_, ret_frame hp (heu.mem.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show u.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [heu.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else u.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcsu r hr, hK₂.gpr (by simp [calleeSaved, clob] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all),
        hcs₁ r hr hr']
  · show u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmxu, hmx₂, hmx₁]; rfl
  · show Spec.Rsa.writtenOutcome m _ _ _ _
    have hH : Spec.Rsa.bytesAt t₁.mem (t₁.gpr .rsi) (t₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat := by
      rw [hsi₁, h9₁]
      exact bytes_of_frame he₁.mem hp.dKd hp.dOd hp.dds.symm (by have := hp.wD; omega_using [])
    rw [signId_eq, bytesAt_length, ← hH]
    have hsi := hp.hsi
    exact Proof.Rsa.writtenOutcome_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.dKo.sub_left hs).symm
      rwa [hsi] at this) hwu

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
