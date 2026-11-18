module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Impl.Sha512.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha512Out
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Sha512.RISCV64
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha512Out
meta import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Md5.RISCV64.Compress
meta import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Impl.Md5.RISCV64
public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
meta import VerifiedGarbage.Impl.Md5.RISCV64
meta import VerifiedGarbage.Impl.Md5.RISCV64.Stream
meta import VerifiedGarbage.Proof.Md5.Md
meta import VerifiedGarbage.Proof.Md5.RISCV64.Stream
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha256Out
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Impl.Sha256.RISCV64
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha256Out
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224

/-! ### `Pbkdf2.Whole.RISCV64.Sha512_224`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512_224`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512/224 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512/224's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512/224 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512_224

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512/224's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 28
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 3).flatMap Impl.Sha512.RISCV64.Stream.outW ++ Impl.Sha512.RISCV64.Stream.outHi 3
  pad := padBE 128 28 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512/224, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512_224S Proof.Sha512.md Spec.Sha512.H0_512_224 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out224_ok
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512_224S Wi).pre (iterK Spec.Hmac.sha512_224S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512_224

end

end

/-!
# PBKDF2-HMAC-SHA-512/224 on RISC-V: the whole derivation

`pbkdf2` over SHA-512/224's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512_224I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_224

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512_224.hash
  hiN := Spec.Hmac.sha512_224I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512_224I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_224_iterate"
  itC := Pbkdf2.RISCV64.Sha512_224.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512_224.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512_224.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512_224.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512_224.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512_224.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512_224.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512_224.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_224

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha384`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha384`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-384 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-384's sizes, compression function and digest code (`it`): what its
proof needs of SHA-384 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha384

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-384's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 48
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 6).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 48 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-384, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha384S Proof.Sha512.md Spec.Sha512.H0_384 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 6 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha384S Wi).pre (iterK Spec.Hmac.sha384S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha384

end

end

/-!
# PBKDF2-HMAC-SHA-384 on RISC-V: the whole derivation

`pbkdf2` over SHA-384's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha384I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha384

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha384.hash
  hiN := Spec.Hmac.sha384I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha384I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha384_iterate"
  itC := Pbkdf2.RISCV64.Sha384.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha384.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha384.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha384.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha384.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha384.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha384.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha384.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha384

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha224`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha224`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-224 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-224's sizes, compression function and digest code (`it`): what its
proof needs of SHA-224 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha224

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-224's parameters of the iteration. -/
def it : It where
  N := 32
  B := 64
  D := 28
  CW := 80
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.RISCV64.compress
  out := (List.range 7).flatMap Impl.Sha256.RISCV64.Stream.outW
  pad := padBE 64 28 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha256.md 80 Impl.Sha256.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha256.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha256.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-224, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 239 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha224S Proof.Sha256.md Spec.Sha256.H0_224 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  out := Sha256Out.out_ok 7 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha224S Wi).pre (iterK Spec.Hmac.sha224S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha224

end

end

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
  hiN := Spec.Hmac.sha224I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha224I.finalizeApi.name ++ "_core"
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
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
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

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha512`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 64
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 8).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 64 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512S Proof.Sha512.md Spec.Sha512.H0_512 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 8 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m =>
    (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512S Wi).pre (iterK Spec.Hmac.sha512S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512

end

end

/-!
# PBKDF2-HMAC-SHA-512 on RISC-V: the whole derivation

`pbkdf2` over SHA-512's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512.hash
  hiN := Spec.Hmac.sha512I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_iterate"
  itC := Pbkdf2.RISCV64.Sha512.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Md5`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Md5`, which only this module used -/

section

/-!
# PBKDF2-HMAC-MD5 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for MD5's sizes, compression function and digest code (`it`): what its
proof needs of MD5 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Md5

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padLE)

/-- MD5's parameters of the iteration. -/
def it : It where
  N := 16
  B := 64
  D := 16
  CW := 80
  cmpN := "vg_md5_compress"
  cmpC := Impl.Md5.RISCV64.compress
  out := Impl.Md5.RISCV64.Stream.params.out
  pad := padLE 64 16 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Md5.md 80 Impl.Md5.RISCV64.compress :=
  ⟨Proof.Md5.RISCV64.Stream.callee.verified, Proof.Md5.RISCV64.Stream.callee.noFrames⟩

/-- What the proof needs of MD5, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 223 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.md5S Proof.Md5.md Spec.Md5.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega_using [hj])
  out := fun s h₁ h₂ h₃ => (Proof.Md5.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Md5.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.md5S Wi).pre (iterK Spec.Hmac.md5S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Md5

end

end

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
  hiN := Spec.Hmac.md5I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.md5I.finalizeApi.name ++ "_core"
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
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Md5.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
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

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha512_256`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512_256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512/256 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512/256's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512/256 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512_256

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512/256's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 32
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 4).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 32 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512/256, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512_256S Proof.Sha512.md Spec.Sha512.H0_512_256 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 4 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512_256S Wi).pre (iterK Spec.Hmac.sha512_256S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512_256

end

end

/-!
# PBKDF2-HMAC-SHA-512/256 on RISC-V: the whole derivation

`pbkdf2` over SHA-512/256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512_256I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_256

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512_256.hash
  hiN := Spec.Hmac.sha512_256I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512_256I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_256_iterate"
  itC := Pbkdf2.RISCV64.Sha512_256.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512_256.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512_256.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512_256.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512_256.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512_256.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512_256.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512_256.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_256

end

end

/-!
# PBKDF2 on RISC-V, without secret residue

Each hash's PBKDF2, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`). Its postcondition reads the memory on return
only within `out`, as on x86-64 (`Proof/Pbkdf2/Md/X86_64/ScrubAll.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega_using [hi])]
    exact h

/-- `Spec.Hmac.md5I.pbkdf2Api`. -/
def md5Pbkdf2Reg : Registration Spec.Hmac.md5I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Md5.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Md5.pbkdf2 }
    (pbkdf2Out Spec.Hmac.md5I _)

/-- `Spec.Hmac.sha1I.pbkdf2Api`. -/
def sha1Pbkdf2Reg : Registration Spec.Hmac.sha1I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha1.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha1.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha1I _)

/-- `Spec.Hmac.sha224I.pbkdf2Api`. -/
def sha224Pbkdf2Reg : Registration Spec.Hmac.sha224I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha224.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha224.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha224I _)

/-- `Spec.Hmac.sha256I.pbkdf2Api`. -/
def sha256Pbkdf2Reg : Registration Spec.Hmac.sha256I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha256.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha256I _)

/-- `Spec.Hmac.sha384I.pbkdf2Api`. -/
def sha384Pbkdf2Reg : Registration Spec.Hmac.sha384I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha384.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha384.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha384I _)

/-- `Spec.Hmac.sha512I.pbkdf2Api`. -/
def sha512Pbkdf2Reg : Registration Spec.Hmac.sha512I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512I _)

/-- `Spec.Hmac.sha512_224I.pbkdf2Api`. -/
def sha512_224Pbkdf2Reg : Registration Spec.Hmac.sha512_224I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512_224.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512_224.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512_224I _)

/-- `Spec.Hmac.sha512_256I.pbkdf2Api`. -/
def sha512_256Pbkdf2Reg : Registration Spec.Hmac.sha512_256I.pbkdf2Api RISCV64.target :=
  withScrub { code := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.F.pbkdf2, verified := Proof.Pbkdf2.Whole.RISCV64.Sha512_256.pbkdf2 }
    (pbkdf2Out Spec.Hmac.sha512_256I _)

end VG.Proof.Pbkdf2.Whole.RISCV64.Scrub
