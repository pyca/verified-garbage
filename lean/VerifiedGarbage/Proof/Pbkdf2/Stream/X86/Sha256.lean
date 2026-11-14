module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.Sha256.X86.Stream
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! ### `Sha256.X86.Variants.Code`, which only this module used -/

section

/-!
# SHA-256 backends on x86: the code built on them

SHA-256 has backends on x86 (`Interface.lean`): implementations of its
compression function, each with the streaming `update` and `finalize` made
with it. HMAC and PBKDF2 are the code of every other hash function, at SHA-256
made with a backend: its streaming functions as the code calls them
(`hmacHash`), SHA-256 as a Merkle–Damgård hash function for HMAC's `init` and
`finalize` and PBKDF2's iteration, which call the compression function
(`mdHash`, `Impl/Pbkdf2/Md/X86.lean`), and the functions the whole of PBKDF2
calls (`fns`, `Impl/Pbkdf2/Whole/X86.lean`), by the names the generic
registration files give them (with the backend's suffix).

SHA-224 is SHA-256 from another initial hash value, so HMAC-SHA-224 and
PBKDF2-HMAC-SHA-224 are the same code at SHA-224 made with a backend
(`hmacHash224`, `mdHash224`, `fns224`): SHA-224's `init`, the backend's
SHA-256 `update`, `finalize` and compression function, and a 28-byte digest
of the 32 bytes `finalize` writes.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86.Variants

open VG.X86

/-- SHA-256's streaming functions, with a backend's `update` and `finalize`
(`updC`, `finC`), which take their working space as an argument, named
`update_scratch` and `finalize_scratch` with its suffix: a 96-byte state, 20 words of working
space and a 32-byte digest. -/
def hmacHash (suffix : String) (updC finC : Prog isa) : Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨64, 96, 32, 32, 20, Spec.Sha256.initApi.name, Impl.Sha256.X86.Stream.init,
    "vg_sha256_update_scratch" ++ suffix, updC, "vg_sha256_finalize_scratch" ++ suffix,
    finC⟩

/-- SHA-256 as a Merkle–Damgård hash function, with a backend's compression
function `cmpN`/`cmpC` and the streaming functions calling it: a 32-byte hash
value, a big-endian 8-byte length field, and 112 bytes of scratch space for
the compression function. -/
def mdHash (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨hmacHash suffix updC finC, 32, 8, true, 112, cmpN, cmpC, Impl.Sha256.X86.Stream.params.out⟩

/-- The functions the whole of PBKDF2 calls for SHA-256 with a backend. -/
def fns (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns where
  H := hmacHash suffix updC finC
  W := Spec.Hmac.sha256I.scratch
  hiN := "vg_hmac_sha256_init_scratch" ++ suffix
  hiC := (mdHash suffix cmpN cmpC updC finC).hmacInit
  hfN := "vg_hmac_sha256_finalize_scratch" ++ suffix
  hfC := (mdHash suffix cmpN cmpC updC finC).hmacFin
  itN := "vg_pbkdf2_hmac_sha256_iterate" ++ suffix
  itC := (mdHash suffix cmpN cmpC updC finC).iterate

/-- SHA-224's streaming functions: SHA-224's `init`, and a backend's SHA-256
`update` and `finalize` (`updC`, `finC`), named with its suffix: SHA-256's
96-byte state and 20 words of working space, and a 28-byte digest of the
32 bytes `finalize` writes. -/
def hmacHash224 (suffix : String) (updC finC : Prog isa) : Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨64, 96, 28, 32, 20, Spec.Sha256.init224Api.name, Impl.Sha256.X86.Stream.init224,
    "vg_sha256_update_scratch" ++ suffix, updC, "vg_sha256_finalize_scratch" ++ suffix,
    finC⟩

/-- SHA-224 as a Merkle–Damgård hash function, with a backend's SHA-256
compression function `cmpN`/`cmpC` and the streaming functions calling it:
SHA-256's 32-byte hash value, big-endian 8-byte length field and 112 bytes of
scratch space for the compression function. -/
def mdHash224 (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨hmacHash224 suffix updC finC, 32, 8, true, 112, cmpN, cmpC, Impl.Sha256.X86.Stream.params.out⟩

/-- The functions the whole of PBKDF2 calls for SHA-224 with a backend. -/
def fns224 (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns where
  H := hmacHash224 suffix updC finC
  W := Spec.Hmac.sha224I.scratch
  hiN := "vg_hmac_sha224_init_scratch" ++ suffix
  hiC := (mdHash224 suffix cmpN cmpC updC finC).hmacInit
  hfN := "vg_hmac_sha224_finalize_scratch" ++ suffix
  hfC := (mdHash224 suffix cmpN cmpC updC finC).hmacFin
  itN := "vg_pbkdf2_hmac_sha224_iterate" ++ suffix
  itC := (mdHash224 suffix cmpN cmpC updC finC).iterate

end VG.Proof.Sha256.X86.Variants

end

end


/-!
# SHA-256's streaming functions on x86 (32-bit), for every backend

SHA-256 has an implementation of its compression function for each variant
of its interface on x86 (`Variants/Sha256/X86/`), and its streaming `update`
and `finalize` made with each (`Sha256Stream`, verified for any initial hash
value): `sha256OK` is `HashOK` for any of them, with `vg_sha256_init`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash)

/-- SHA-256's streaming `update` and `finalize` made with one implementation
of its compression function, named with its suffix (e.g. `_shani`; nothing
for the baseline implementation), verified against their per-target
contracts, which hold from any initial hash value; they keep `esp` and use
at most 20 bytes of stack. -/
structure Sha256Stream where
  suffix : String
  upd : Prog isa
  fin : Prog isa
  updOK : Verified X86.target upd Proof.Sha256.updateX86
  finOK : Verified X86.target fin Proof.Sha256.finalizeX86
  updSp : NoSp upd
  finSp : NoSp fin
  updSU : stackUse upd ≤ 20
  finSU : stackUse fin ≤ 20

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha256H (v : Sha256Stream) : Hash := hmacHash v.suffix v.upd v.fin

theorem sha256_initSp : NoSp Impl.Sha256.X86.Stream.init := nosp_of (by lit_decide)
theorem sha256_initSU : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha256OK (v : Sha256Stream) : HashOK (sha256H v) where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 32 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 32 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.X86.Stream.init_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := sha256_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := sha256_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86
