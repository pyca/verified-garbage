module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Md5
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-MD5 on RISC-V: the whole derivation

`pbkdf2` over MD5's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 224 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.md5I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Md5

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Md5.hash
  hiN := Spec.Hmac.md5I.initAnyKeyApi.name
  hfN := Spec.Hmac.md5I.finalizeApi.name
  itN := "vg_pbkdf2_hmac_md5_iterate"
  itC := Pbkdf2.RISCV64.Md5.code
  itW := 224

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Md5.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Md5.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Md5.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Md5.hashOkW 224 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Md5.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Md5.ctW 224
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Md5.RISCV64.Stream.callee.noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.md5I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Md5.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Md5
