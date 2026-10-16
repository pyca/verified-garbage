module

public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Sha512.AArch64.Compress
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SHA-512 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC, PBKDF2 and Ed25519 consume the resulting streaming functions.
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64
open VG.Impl.Sha512.AArch64.Stream (compressName updateWith finalizeWith finalizeDigestWith params384 params512_256
  params512_224)

/-- What a backend's `finalizeDigestWith` with the digest code `o` (SHA-384's,
SHA-512/256's or SHA-512/224's `finalize`, writing a `D`-byte digest) needs
checked for its code, as `finalizeCT`, `finalizeKeeps` and `finalizeDepth`
for `finalize`. -/
structure DigestOk (o : List Instr) (D : Nat) (suffix : String) (code : Prog isa) : Prop where
  ct : ConstantTime isa (finKD (P := { Stream.params with out := o }) md D).pre
    (finKD (P := { Stream.params with out := o }) md D).pub
    (finalizeDigestWith { Stream.params with out := o } suffix code)
  keeps : ((instrs (finalizeMain { Stream.params with out := o } (compressName suffix) code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  depth : (finalizeMain { Stream.params with out := o } (compressName suffix) code).aarch64Depth = 0

/-- The one-shot digest with the digest code `o`, from the initial hash value
`iv`, calling the compression function `code` with the suffix `suffix`. -/
def oneShotWith (o : List Instr) (iv : Spec.Sha512.HashValue) (suffix : String) (code : Prog isa) :
    Prog isa :=
  Impl.MdStream.AArch64.OneShot.digest Stream.params { Stream.params with out := o }
    (Impl.Sha512.AArch64.Stream.init iv) (compressName suffix) code

/-- The one-shot digest is constant time. -/
abbrev OneShotCT (o : List Instr) (D : Nat) (iv : Spec.Sha512.HashValue) (suffix : String)
    (code : Prog isa) : Prop :=
  ConstantTime isa (MdStream.AArch64.OneShot.oneK (P := Stream.params) md iv D).pre
    (MdStream.AArch64.OneShot.oneK (P := Stream.params) md iv D).pub
    (oneShotWith o iv suffix code)

structure Compress where
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha512.compressAArch64
  noFrames : code.noFrames = true
  /-- Current streaming wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre
    (updK (P := Stream.params) md).pub (updateWith suffix code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre
    (finK (P := Stream.params) md).pub (finalizeWith suffix code)
  updateKeeps : ((instrs (updateMain Stream.params (compressName suffix) code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  finalizeKeeps : ((instrs (finalizeMain Stream.params (compressName suffix) code)).all fun i =>
    untouched.all fun r => !clobbers i r) = true
  updateDepth : (updateMain Stream.params (compressName suffix) code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params (compressName suffix) code).aarch64Depth = 0
  /-- SHA-384's, SHA-512/256's and SHA-512/224's `finalize`. -/
  digest384 : DigestOk (out64 6) 48 suffix code
  digest512_256 : DigestOk (out64 4) 32 suffix code
  digest512_224 : DigestOk (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 suffix code
  /-- The one-shot digests of SHA-512, SHA-384, SHA-512/256 and SHA-512/224. -/
  oneShot512 : OneShotCT (out64 8) 64 Spec.Sha512.H0_512 suffix code
  oneShot384 : OneShotCT (out64 6) 48 Spec.Sha512.H0_384 suffix code
  oneShot512_256 : OneShotCT (out64 4) 32 Spec.Sha512.H0_512_256 suffix code
  oneShot512_224 : OneShotCT (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 Spec.Sha512.H0_512_224
    suffix code

namespace Compress

variable (v : Compress)

/-- The symbol of the compression function. -/
def name : String := compressName v.suffix

def update : Prog isa := updateWith v.suffix v.code
def finalize : Prog isa := finalizeWith v.suffix v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha512.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT v.updateKeeps
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha512.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    v.finalizeKeeps (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc => h iv m hr hl hc,
    fun _ _ _ _ h => h, h.2.2⟩

/-- `finalizeDigestWith` writing a `D`-byte digest, with the digest code `o`. -/
theorem finalizeDigest_verified {o : List Instr} {D : Nat}
    (hs : ShapeD (P := { Stream.params with out := o }) md D)
    (dk : DigestOk o D v.suffix v.code) :
    Verified AArch64.target (finalizeDigestWith { Stream.params with out := o } v.suffix v.code)
      (finKD (P := { Stream.params with out := o }) md D) :=
  MdStream.AArch64.Finalize.verifiedD (P := { Stream.params with out := o })
    ⟨Stream.dims.1, Stream.dims.2, Stream.dims.3, Stream.dims.4⟩ hs
    (v.callee.withOut o) dk.ct dk.keeps (by rw [dk.depth]; decide)

theorem finalizeDigest_keepsV {o : List Instr} {D : Nat}
    (hs : ShapeD (P := { Stream.params with out := o }) md D) :
    (finalizeDigestWith { Stream.params with out := o } v.suffix v.code).allInstrs VG.AArch64.keepsV = true :=
  MdStream.AArch64.finalize_keepsVD hs v.keepsV

theorem update_keepsV : v.update.allInstrs VG.AArch64.keepsV = true := MdStream.AArch64.update_keepsV v.keepsV

theorem finalize_keepsV : v.finalize.allInstrs VG.AArch64.keepsV = true :=
  MdStream.AArch64.finalize_keepsV Stream.shape v.keepsV

theorem update_depth : v.update.aarch64Depth = 1 := by
  simp only [update, updateWith, Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]
  rfl

theorem finalize_depth : v.finalize.aarch64Depth = 1 := by
  simp only [finalize, finalizeWith, Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]
  rfl

end Compress
end VG.Proof.Sha512.AArch64
