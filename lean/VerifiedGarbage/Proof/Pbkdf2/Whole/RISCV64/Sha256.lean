module

import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha256Out
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.RISCV64
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha256Out
meta import VerifiedGarbage.Impl.Sha256.RISCV64
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Pbkdf2.RISCV64.Sha256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-256 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-256's sizes, compression function and digest code (`it`): what its
proof needs of SHA-256 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha256

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-256's parameters of the iteration. -/
def it : It where
  N := 32
  B := 64
  D := 32
  CW := 80
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.RISCV64.compress
  out := (List.range 8).flatMap Impl.Sha256.RISCV64.Stream.outW
  pad := padBE 64 32 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha256.md 80 Impl.Sha256.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha256.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha256.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-256, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 239 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha256S Proof.Sha256.md Spec.Sha256.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  out := Sha256Out.out_ok 8 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha256S Wi).pre (iterK Spec.Hmac.sha256S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha256

end

end

/-!
# PBKDF2-HMAC-SHA-256 on RISC-V: the whole derivation

`pbkdf2` over SHA-256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 240 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha256I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha256

open VG.RISCV64
open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash256 ok256)

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := hash256
  hiN := Spec.Hmac.sha256I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha256I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha256_iterate"
  itC := Pbkdf2.RISCV64.Sha256.code
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := ok256
  hiCt := Proof.Hmac.Stream.RISCV64.Sha256.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha256.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha256.hashOkW 240 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha256.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha256.ctW 240
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha256.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, hash256, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha256
