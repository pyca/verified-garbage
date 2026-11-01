module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-SHA-224 on RISC-V: the whole derivation

`pbkdf2` over SHA-224's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 240 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha224I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha224

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
  hiN := Spec.Hmac.sha224I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha224I.finalizeApi.name
  itN := "vg_pbkdf2_hmac_sha224_iterate"
  itC := Pbkdf2.RISCV64.Sha224.code
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha256Family.ok224
  hiCt := Proof.Hmac.Stream.RISCV64.Sha224.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha224.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha224.hashOkW 240 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha224.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha224.ctW 240
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha256.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha224I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha256Family.hash224, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha224
