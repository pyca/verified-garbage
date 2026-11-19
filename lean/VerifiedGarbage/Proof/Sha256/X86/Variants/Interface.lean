module

public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
import VerifiedGarbage.Proof.Sha256.PostOut
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.Sha256.X86.Stream
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
meta import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.Impl.Pbkdf2.Md.X86
meta import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
meta import VerifiedGarbage.Impl.Sha256.X86.Stream
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash

/-! ### `Pbkdf2.Stream.X86.Sha256`, which only this module used -/

section

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
  ⟨64, 96, 32, 32, 20, (Spec.Sha256.initApi.name ++ "_core"), Impl.Sha256.X86.Stream.init,
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
  ⟨64, 96, 28, 32, 20, (Spec.Sha256.init224Api.name ++ "_core"), Impl.Sha256.X86.Stream.init224,
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

end

end

/-! ### `Pbkdf2.Md.X86.Sha256`, which this module and modules that import it used -/

section

/-!
# HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 over the compression function on x86 (32-bit), for every backend

SHA-256 as a `Hash` of `Impl/Pbkdf2/Md/X86.lean` with a backend's
compression function and streaming functions
(`Proof.Sha256.X86.Variants.mdHash`), what the proofs know of it (`sha256Ok`):
SHA-256's `Md` (`Proof/Sha256/Md.lean`) from `H0`, the digest its streaming
code writes (`Proof.Sha256.X86.Stream.shape`), and the backend's verified
compression function, whose contract is `cmpK`; and the generic proofs of
HMAC's `finalize` and PBKDF2's iteration (`HmacFinCT.lean`, `IterateCT.lean`)
at it, moved to the shared contracts of `Spec.Hmac.sha256I`. Their taint
checks depend only on the sizes, so they are evaluated once, for every
backend (`sha256Shape`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream sha256OK)
open VG.Proof.Sha256.X86.Variants (mdHash)

/-- SHA-256 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha256M (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  mdHash v.suffix cmpN cmpC v.upd v.fin

/-- `MdOk` for SHA-256, for any backend: its streaming functions `v` and its
verified compression function `cmpC`. -/
def sha256Ok (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa} (hc : CompOk Proof.Sha256.md 112 cmpC) :
    MdOk (sha256M v cmpN cmpC) where
  hH := sha256OK v
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    show 32 ≤ 32 by decide, show 32 + 8 < 64 by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  tail := sha256_tail
  out := outOk_of_shape Proof.Sha256.X86.Stream.shape
  comp := hc
  sizes := sha256_sizes
where
  sha256_tail : Proof.Sha256.md.tailPad 32 = (sha256M v cmpN cmpC).tailB := by
    show Proof.Sha256.md.tailPad 32 = Impl.Pbkdf2.Md.X86.tail 64 32 8 true
    decide
  sha256_sizes : Sizes (sha256M v cmpN cmpC) :=
    ⟨show 64 = 64 ∨ 64 = 128 by decide, show 0 < 32 ∧ 32 ≤ 64 ∧ 32 % 4 = 0 by decide,
      show 0 < 32 ∧ 32 ≤ 32 ∧ 32 % 4 = 0 by decide, show 32 + 8 + 4 ≤ 64 by decide,
      show 96 = 32 + 64 from rfl, show 112 ≤ 8 * 20 by decide, show 20 ≤ 64 by decide,
      show 32 ≤ 32 ∧ 32 ≤ 64 by decide⟩

/-- SHA-256's sizes and digest code, without the functions: `shapeOf` of
every backend's `sha256M`, written out, so that the kernel reduces each side
to it field by field rather than comparing the backends' functions. -/
def sha256Shape : Hash :=
  ⟨⟨64, 96, 32, 32, 20, "", .block [], "", .block [], "", .block []⟩, 32, 8, true, 112, "", .block [],
    Impl.Sha256.X86.Stream.params.out⟩

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream initW initG finW finG iterW iterG countF)

theorem sha256Shape_iterChecks : Iterate.Checks sha256Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha256Shape_initChecks : HmacInit.Checks sha256Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha256Shape_finChecks : HmacFin.Checks sha256Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha256_iterChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    Iterate.Checks (sha256M v cmpN cmpC) :=
  iterChecks_of_shape (H := sha256M v cmpN cmpC) sha256Shape_iterChecks

theorem sha256_initChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacInit.Checks (sha256M v cmpN cmpC) :=
  initChecks_of_shape (H := sha256M v cmpN cmpC) sha256Shape_initChecks

theorem sha256_finChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacFin.Checks (sha256M v cmpN cmpC) :=
  finChecks_of_shape (H := sha256M v cmpN cmpC) sha256Shape_finChecks

theorem sha256_iterImp : (iterW Spec.Hmac.sha256S 104).Implies (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha256I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 96 32 104
  sig_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 96 32 104

theorem sha256_initImp : (initW Spec.Hmac.sha256S 104).Implies (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha256I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 104
  sig_implies [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 104

theorem sha256_finImp : (finW Spec.Hmac.sha256S 104).Implies (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha256I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 96 32 104
  sig_implies [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 96 32 104

/-- PBKDF2's iteration for SHA-256 with any backend. -/
theorem sha256_iterate (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha256I X86.abi 48) :=
  (Iterate.verifiedW (sha256Ok v cmpN hc) (sha256_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 + 64 ≤ 8 * 104 by decide) sha256_iterImp.sat_left).of_implies sha256_iterImp

/-- HMAC's `finalize` for SHA-256 with any backend. -/
theorem sha256_finalize (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha256I X86.abi 48) :=
  (HmacFin.verifiedW (sha256Ok v cmpN hc) (sha256_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 ≤ 8 * 104 by decide) sha256_finImp.sat_left).of_implies sha256_finImp

end VG.Proof.Pbkdf2.Md.X86.Instances

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream)

/-- HMAC's `init` for SHA-256 with any backend. -/
theorem sha256_init (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha256I X86.abi 48) :=
  (HmacInit.verifiedW (sha256Ok v cmpN hc) (sha256_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 104 by decide) sha256_initImp.sat_left).of_implies sha256_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances

end

end

/-! ### `Pbkdf2.Md.X86.Sha224`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Stream.X86.Sha224`, which this module and modules that import it used -/

section

/-!
# SHA-224's streaming functions on x86 (32-bit), for every backend

`HashOK` for SHA-224 (`sha224OK`), for any of SHA-256's backends on x86
(`Sha256Stream`): SHA-256's streaming functions from SHA-224's initial hash
value (`vg_sha224_init`, then the backend's `update` and `finalize`, whose
contracts hold from any initial hash value), with the digest the first 28
bytes of the final hash value.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash224)
open VG.Proof.Hmac.Generic.Common (readW_reloc bytesAt_reloc)

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha224H (v : Sha256Stream) : Hash := hmacHash224 v.suffix v.upd v.fin

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_using [hj])
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega_using [])

theorem sha224_initSp : NoSp Impl.Sha256.X86.Stream.init224 := nosp_of (by lit_decide)
theorem sha224_initSU : stackUse Impl.Sha256.X86.Stream.init224 ≤ 20 := by lit_decide

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha224OK (v : Sha256Stream) : HashOK (sha224H v) where
  SH := Spec.Hmac.sha224S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 28 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 28 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := sha224_repr
  init := Proof.Sha256.X86.Stream.init224_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := sha224_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := sha224_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86

end

end

/-!
# HMAC-SHA-224 and PBKDF2-HMAC-SHA-224 over the compression function on x86 (32-bit), for every backend

SHA-224 as a `Hash` of `Impl/Pbkdf2/Md/X86.lean` with a backend's SHA-256
compression function and streaming functions
(`Proof.Sha256.X86.Variants.mdHash224`), what the proofs know of it
(`sha224Ok`): SHA-256's `Md` (`Proof/Sha256/Md.lean`) from `H0_224`, with the
digest the first 28 bytes of the final hash value, the digest SHA-256's
streaming code writes (`Proof.Sha256.X86.Stream.shape`), and the backend's
verified compression function, whose contract is `cmpK`; and the generic
proofs of HMAC's `init` and `finalize` and PBKDF2's iteration at it, moved to
the shared contracts of `Spec.Hmac.sha224I`, as for SHA-256 (`Sha256.lean`).
Their taint checks depend only on the sizes, so they are evaluated once, for
every backend (`sha224Shape`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream sha224OK)
open VG.Proof.Sha256.X86.Variants (mdHash224)

/-- SHA-224 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha224M (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  mdHash224 v.suffix cmpN cmpC v.upd v.fin

/-- `MdOk` for SHA-224, for any backend: its streaming functions `v` and its
verified compression function `cmpC`. -/
def sha224Ok (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa} (hc : CompOk Proof.Sha256.md 112 cmpC) :
    MdOk (sha224M v cmpN cmpC) where
  hH := sha224OK v
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, show 28 ≤ 32 by decide, show 28 + 8 < 64 by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  tail := sha224_tail
  out := outOk_of_shape Proof.Sha256.X86.Stream.shape
  comp := hc
  sizes := sha224_sizes
where
  sha224_tail : Proof.Sha256.md.tailPad 28 = (sha224M v cmpN cmpC).tailB := by
    show Proof.Sha256.md.tailPad 28 = Impl.Pbkdf2.Md.X86.tail 64 28 8 true
    decide
  sha224_sizes : Sizes (sha224M v cmpN cmpC) :=
    ⟨show 64 = 64 ∨ 64 = 128 by decide, show 0 < 32 ∧ 32 ≤ 64 ∧ 32 % 4 = 0 by decide,
      show 0 < 28 ∧ 28 ≤ 32 ∧ 28 % 4 = 0 by decide, show 28 + 8 + 4 ≤ 64 by decide,
      show 96 = 32 + 64 from rfl, show 112 ≤ 8 * 20 by decide, show 20 ≤ 64 by decide,
      show 28 ≤ 32 ∧ 32 ≤ 64 by decide⟩

/-- SHA-224's sizes and digest code, without the functions: `shapeOf` of
every backend's `sha224M`, written out, so that the kernel reduces each side
to it field by field rather than comparing the backends' functions. -/
def sha224Shape : Hash :=
  ⟨⟨64, 96, 28, 32, 20, "", .block [], "", .block [], "", .block []⟩, 32, 8, true, 112, "", .block [],
    Impl.Sha256.X86.Stream.params.out⟩

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream initW initG finW finG iterW iterG countF)

theorem sha224Shape_iterChecks : Iterate.Checks sha224Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    load := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha224Shape_initChecks : HmacInit.Checks sha224Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    blocks := ⟨?_, ?_⟩
    toOuter := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha224Shape_finChecks : HmacFin.Checks sha224Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    fin1 := ⟨?_, ?_⟩
    mid := ⟨?_, ?_⟩
    out := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha224_iterChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    Iterate.Checks (sha224M v cmpN cmpC) :=
  iterChecks_of_shape (H := sha224M v cmpN cmpC) sha224Shape_iterChecks

theorem sha224_initChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacInit.Checks (sha224M v cmpN cmpC) :=
  initChecks_of_shape (H := sha224M v cmpN cmpC) sha224Shape_initChecks

theorem sha224_finChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacFin.Checks (sha224M v cmpN cmpC) :=
  finChecks_of_shape (H := sha224M v cmpN cmpC) sha224Shape_finChecks

theorem sha224_iterImp : (iterW Spec.Hmac.sha224S 104).Implies (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha224I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 96 28 104
  sig_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 96 28 104

theorem sha224_initImp : (initW Spec.Hmac.sha224S 104).Implies (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 104
  sig_implies [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 104

theorem sha224_finImp : (finW Spec.Hmac.sha224S 104).Implies (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 96 28 104
  sig_implies [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 96 28 104

/-- PBKDF2's iteration for SHA-224 with any backend. -/
theorem sha224_iterate (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha224I X86.abi 48) :=
  (Iterate.verifiedW (sha224Ok v cmpN hc) (sha224_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 + 64 ≤ 8 * 104 by decide) sha224_iterImp.sat_left).of_implies sha224_iterImp

/-- HMAC's `finalize` for SHA-224 with any backend. -/
theorem sha224_finalize (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I X86.abi 48) :=
  (HmacFin.verifiedW (sha224Ok v cmpN hc) (sha224_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 ≤ 8 * 104 by decide) sha224_finImp.sat_left).of_implies sha224_finImp

/-- HMAC's `init` for SHA-224 with any backend. -/
theorem sha224_init (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I X86.abi 48) :=
  (HmacInit.verifiedW (sha224Ok v cmpN hc) (sha224_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 104 by decide) sha224_initImp.sat_left).of_implies sha224_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances

end

end

/-!
# SHA-256 backends on x86

A backend is one implementation of SHA-256's compression function on x86: a
variant of the interface `Sha256` on x86 (`Variants/Sha256/X86/`). Each
function built on it (in `Generic/Sha256/X86/`) is emitted once for each
backend, named with its suffix (see `TCB/Emit.lean`): its own functions, the
streaming ones made with it (`functions`; its compression function and the
streaming functions with their working space passed in `scratch` are
internal functions, emitted from their callers' code), and
HMAC's `init` and `finalize`, PBKDF2's `iterate` and the whole of PBKDF2,
the implementations for every hash function (`Impl/Pbkdf2/Md/X86.lean`,
`Impl/Pbkdf2/Whole/X86.lean`) at SHA-256 made with the backend
(`Code.lean`). HMAC's `init` calls SHA-256's streaming `init` and the
backend's compression function; HMAC's `finalize` the backend's streaming
`finalize` (`stream`) and its compression function; PBKDF2's iteration its
compression function. They are proven once for every backend, against the
contracts of `Spec.Hmac.sha256I` (`Proof/Sha256/X86/Variants/Interface.lean`,
`Proof/Pbkdf2/Whole/X86/Sha256.lean`), from what the backend proves of its
compression function and streaming functions. The same functions at SHA-224
(`Impl.Pbkdf2.Md.X86`'s code at `mdHash224`, `fns224`), which call SHA-224's
`init` and the backend's SHA-256 functions, are proven once for every backend
too, against the contracts of `Spec.Hmac.sha224I`
(`Proof/Sha256/X86/Variants/Interface.lean`, `Proof/Pbkdf2/Whole/X86/Sha224.lean`).
So adding an implementation of the compression function also emits the
SHA-256, HMAC and PBKDF2 functions that call it. What the kernel checks of each backend's code (that it keeps
`esp`, and the stack it uses) is evaluated on its literals.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86.Variants

open VG.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream)
open VG.Proof.Pbkdf2.Md.X86 (sha256M sha224M)

structure StreamFn where
  api : Api
  code : Prog isa
  contract : Contract isa
  stack : Nat := 0
  verified : Verified X86.target code contract
  ofSig : ∃ pre post leak,
    contract = api.sig.contract (X86.abi) pre post api.writeArgs stack leak
  ofApi : contract = api.contract X86.abi stack
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- Its postcondition reads the memory on return only within the buffers. -/
  post : X86.Scrub.PostOut contract (api.sig.retBits 32)
  /-- What `X86.Scrub.scrubFOf` needs of its code over its stack: from the
  variant's facts of the code it wraps (`update_scrub`, …), not evaluated
  again. -/
  scrub : X86.Scrub.scrubFSide code [] stack = true

/-- `f` as a registration of its `Api` (`Api.artifact`), followed by the
zeroing of its stack and the clearing of the registers a callee may change
(`X86.Scrub.scrubFOf`): it returns without secret residue. -/
def StreamFn.reg (f : StreamFn) : Registration f.api X86.target :=
  X86.Scrub.scrubFOf {
      consts := []
      tables := []
      code := f.code
      contract := f.contract
      stack := f.stack
      verified := f.verified
      ofApi := f.ofApi
      ofSig := f.ofSig
      spSafe := f.spSafe }
    f.post f.stack f.scrub

/-! ## What the cleanup of the streaming functions needs

Their postconditions read the memory on return only within the buffers
(`updateOut`, …). `update` and `finalize` are the code of the variant's
streaming functions in a frame of working space: what `scrubFOf` needs of
them (`update_scrub`, …) follows from that frame with an empty body,
evaluated once here, and the variant's `calleeOk` and stack of the code
(`Fill`, `Proof/Framework/X86/ScrubCall.lean`). -/

theorem updateOut (stack : Nat) :
    X86.Scrub.PostOut (Spec.Sha256.updateContract X86.abi stack) (Spec.Sha256.updateSig.retBits 32) :=
  X86.Scrub.postOut_of_local X86.Scrub.ScrubAbi.plain (Proof.Sha256.updatePost_out 32)

theorem finalizeOut (stack : Nat) :
    X86.Scrub.PostOut (Spec.Sha256.finalizeContract X86.abi stack) (Spec.Sha256.finalizeSig.retBits 32) :=
  X86.Scrub.postOut_of_local X86.Scrub.ScrubAbi.plain (Proof.Sha256.finalizePost_out 32)

theorem finalize224Out (stack : Nat) :
    X86.Scrub.PostOut (Spec.Sha256.finalize224Contract X86.abi stack) (Spec.Sha256.finalize224Sig.retBits 32) :=
  X86.Scrub.postOut_of_local X86.Scrub.ScrubAbi.plain (Proof.Sha256.finalize224Post_out 32)

theorem update_side :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 636 5 (.block [])) [] 636 = true := by
  lit_decide

/-- What `scrubFOf` needs of `update`'s code with the streaming `update` `c`, in its
frame of 636 bytes, from `c`'s `calleeOk` and stack. -/
theorem update_scrub (c : Prog isa) (hc : calleeOk c = true) (hs : stackUse c ≤ 20) :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 636 5 c) [] (20 + 636) = true := by
  have h := X86.Scrub.calleeSide_of_le (n := 20) hs hc
  exact X86.Scrub.scrubFSide_of_fill (n := 20) (by fill_calls) update_side

theorem finalize_side :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 632 4 (.block [])) [] 632 = true := by
  lit_decide

/-- What `scrubFOf` needs of `finalize`'s code with the streaming `finalize` `c`, in its
frame of 632 bytes, from `c`'s `calleeOk` and stack. -/
theorem finalize_scrub (c : Prog isa) (hc : calleeOk c = true) (hs : stackUse c ≤ 20) :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 632 4 c) [] (20 + 632) = true := by
  have h := X86.Scrub.calleeSide_of_le (n := 20) hs hc
  exact X86.Scrub.scrubFSide_of_fill (n := 20) (by fill_calls) finalize_side

theorem finalize224_side :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 632 4 (Impl.Sha256.X86.Stream.finalize224 "" (.block [])))
      [] (20 + 632) = true := by
  lit_decide

/-- What `scrubFOf` needs of SHA-224's `finalize` with the compression function
`cmpN`/`cmpC`, from `cmpC`'s `calleeOk` and stack. -/
theorem finalize224_scrub (cmpN : String) (cmpC : Prog isa) (hc : calleeOk cmpC = true) (hs : stackUse cmpC = 0) :
    X86.Scrub.scrubFSide (Impl.StackScratch.X86.withStackScratch 632 4 (Impl.Sha256.X86.Stream.finalize224 cmpN cmpC))
      [] (20 + 632) = true := by
  have h := X86.Scrub.calleeSide_of_eq (n := 0) hs hc
  exact X86.Scrub.scrubFSide_of_fill (n := 0) (by fill_calls) finalize224_side

/-- The functions the whole of PBKDF2 calls, with the compression function
`cmpN`/`cmpC` and the streaming functions `s`. -/
abbrev pbkdf2Fns (s : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns :=
  fns s.suffix cmpN cmpC s.upd s.fin

/-- The functions the whole of PBKDF2-HMAC-SHA-224 calls, with the
compression function `cmpN`/`cmpC` and the streaming functions `s`. -/
abbrev pbkdf2Fns224 (s : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns :=
  fns224 s.suffix cmpN cmpC s.upd s.fin

structure Backend where
  /-- The compression function, verified: it keeps `esp`, and calls nothing
  that uses the stack. -/
  cmpN : String
  cmpC : Prog isa
  cmp : Verified X86.target cmpC Proof.Sha256.compressX86
  cmpSp : NoSp cmpC
  cmpStack : stackUse cmpC = 0
  /-- SHA-256's streaming `update` and `finalize` made with it, verified, and
  the suffix of the names of the functions emitted for it (e.g. `_shani`;
  nothing for the baseline implementation). -/
  stream : Sha256Stream
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- Its own functions: the streaming functions made with it (SHA-224's
  `finalize` among them). -/
  functions : List StreamFn
  /-- The compression function and the streaming functions it makes, the
  code the functions built on it call, have no MMX instruction and make no
  indirect call (`calleeOk`): what the cleanup of every function that calls
  them needs of them, with their stack (`X86.Scrub.calleeSide`), so that each
  proves only its own code, whatever the implementation
  (`Proof/Framework/X86/ScrubCall.lean`). -/
  cmpScrub : calleeOk cmpC = true
  updScrub : calleeOk stream.upd = true
  finScrub : calleeOk stream.fin = true
  /-- No instruction of the functions built on it writes `esp` (the
  artifacts' `spSafe`). -/
  initSp : (sha256M stream cmpN cmpC).hmacInit.all (fun i => !isa.writesSp i) = true
  finSp : (sha256M stream cmpN cmpC).hmacFin.all (fun i => !isa.writesSp i) = true
  iterSp : (sha256M stream cmpN cmpC).iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : (pbkdf2Fns stream cmpN cmpC).pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- What the whole of PBKDF2 needs of the functions it calls: they keep
  `esp`, and use at most 48 bytes of stack. -/
  initNoSp : NoSp (sha256M stream cmpN cmpC).hmacInit
  initStack : stackUse (sha256M stream cmpN cmpC).hmacInit ≤ 48
  finalizeNoSp : NoSp (sha256M stream cmpN cmpC).hmacFin
  finalizeStack : stackUse (sha256M stream cmpN cmpC).hmacFin ≤ 48
  iterNoSp : NoSp (sha256M stream cmpN cmpC).iterate
  iterStack : stackUse (sha256M stream cmpN cmpC).iterate ≤ 48
  /-- The same of the functions at SHA-224. -/
  init224Sp : (sha224M stream cmpN cmpC).hmacInit.all (fun i => !isa.writesSp i) = true
  fin224Sp : (sha224M stream cmpN cmpC).hmacFin.all (fun i => !isa.writesSp i) = true
  iter224Sp : (sha224M stream cmpN cmpC).iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2_224Sp : (pbkdf2Fns224 stream cmpN cmpC).pbkdf2.all (fun i => !isa.writesSp i) = true
  init224NoSp : NoSp (sha224M stream cmpN cmpC).hmacInit
  init224Stack : stackUse (sha224M stream cmpN cmpC).hmacInit ≤ 48
  finalize224NoSp : NoSp (sha224M stream cmpN cmpC).hmacFin
  finalize224Stack : stackUse (sha224M stream cmpN cmpC).hmacFin ≤ 48
  iter224NoSp : NoSp (sha224M stream cmpN cmpC).iterate
  iter224Stack : stackUse (sha224M stream cmpN cmpC).iterate ≤ 48

namespace Backend

variable (v : Backend)

/-- What the names of the functions emitted for it end with. -/
abbrev suffix : String := v.stream.suffix

/-- SHA-256 as a Merkle–Damgård hash function, as HMAC's `finalize` and
PBKDF2's iteration call it. -/
abbrev M : Impl.Pbkdf2.Md.X86.Hash := sha256M v.stream v.cmpN v.cmpC

/-- The functions the whole of PBKDF2 calls. -/
abbrev F : Impl.Pbkdf2.Whole.X86.Fns := pbkdf2Fns v.stream v.cmpN v.cmpC

/-- The compression function, as HMAC's `finalize` and PBKDF2's iteration
call it. -/
theorem comp : Proof.Pbkdf2.Md.X86.CompOk Proof.Sha256.md 112 v.cmpC := ⟨v.cmp, v.cmpSp, v.cmpStack⟩

theorem hmacInit : Verified X86.target v.M.hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha256I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha256_init v.stream v.cmpN v.comp

theorem hmacFin : Verified X86.target v.M.hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha256I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha256_finalize v.stream v.cmpN v.comp

theorem iterate : Verified X86.target v.M.iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha256I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha256_iterate v.stream v.cmpN v.comp

/-- SHA-224 as a Merkle–Damgård hash function, with the backend's SHA-256
compression function and streaming functions. -/
abbrev M224 : Impl.Pbkdf2.Md.X86.Hash := sha224M v.stream v.cmpN v.cmpC

/-- The functions the whole of PBKDF2-HMAC-SHA-224 calls. -/
abbrev F224 : Impl.Pbkdf2.Whole.X86.Fns := pbkdf2Fns224 v.stream v.cmpN v.cmpC

theorem hmacInit224 : Verified X86.target v.M224.hmacInit (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha224_init v.stream v.cmpN v.comp

theorem hmacFin224 : Verified X86.target v.M224.hmacFin (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha224_finalize v.stream v.cmpN v.comp

theorem iterate224 : Verified X86.target v.M224.iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha224I X86.abi 48) :=
  Proof.Pbkdf2.Md.X86.Instances.sha224_iterate v.stream v.cmpN v.comp

end Backend

end VG.Proof.Sha256.X86.Variants
