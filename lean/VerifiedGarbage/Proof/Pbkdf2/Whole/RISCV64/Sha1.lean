module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Verified
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: the whole derivation

`pbkdf2` over SHA-1's streaming functions, HMAC's `init` and `finalize` and
SHA-1's own PBKDF2 `iterate` (`F`, with 240 bytes of working space for
`iterate`, `Proof/Pbkdf2/Sha1/RISCV64/`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha1I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha1

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha1.hash
  hiN := Spec.Hmac.sha1I.initAnyKeyApi.name
  hfN := Spec.Hmac.sha1I.finalizeApi.name
  itN := "vg_pbkdf2_hmac_sha1_iterate"
  itC := Impl.Pbkdf2.Sha1.RISCV64.iterate
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha1.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha1.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha1.fin_ct
  itOk := Pbkdf2.Sha1.RISCV64.verifiedW 240 (by decide) (by decide)
  itCt := Pbkdf2.Sha1.RISCV64.ct fun _ _ h => h
  itNf := Pbkdf2.Sha1.RISCV64.noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha1.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha1
