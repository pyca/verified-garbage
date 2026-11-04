module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
public import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
meta import VerifiedGarbage.Proof.MdHashTable.PPC64LE
meta import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# The Merkle–Damgård families of the tables of `MdHash` on PPC64LE

Untrusted: everything here is checked by Lean. For each family of streaming
code (MD5, SHA-1, SHA-256 and SHA-224, the SHA-512 family), with the
parameters `shapeOf` gives its indices (`Impl/RsaPss/PPC64LE.lean`): what
`ctHash` needs of its code (`CtOK`), the taint checks of its blocks
(`CtTaint`), and the constant time of its compression function, from its
artifact's proof, and of the digest of its hash value
(`Impl/MdHashTable/PPC64LE.lean`), by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Impl.MdHashTable.PPC64LE (digest)
open VG.Proof.RsaPss.PPC64LE (CtOK CtTaint)

/-- A family of streaming code: its parameters, its `Md`, its compression
function and what the proofs need of them. -/
structure Fam where
  P : Params
  md : Md P.B P.N P.L
  cn : String
  cc : Prog isa
  ok : CtOK P md cc (digest P)
  ct : CtTaint P
  hcc : ConstantTime isa (compressK md).pre (compressK md).pub cc
  hdc : ConstantTime isa (digestK md).pre (digestK md).pub (digest P)

def md5F : Fam where
  P := Impl.Md5.PPC64LE.Stream.params
  md := Proof.Md5.md
  cn := "vg_md5_compress"
  cc := Impl.Md5.PPC64LE.compress
  ok := ⟨Proof.Md5.PPC64LE.Stream.dims, Proof.Md5.PPC64LE.Stream.shape, by decide, Proof.Md5.PPC64LE.Stream.callee,
    digest_correct Proof.Md5.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := Proof.Md5.PPC64LE.compress_verified.2.1
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha1F : Fam where
  P := Impl.Sha1.PPC64LE.Stream.params
  md := Proof.Sha1.md
  cn := "vg_sha1_compress"
  cc := Impl.Sha1.PPC64LE.compress
  ok := ⟨Proof.Sha1.PPC64LE.Stream.dims, Proof.Sha1.PPC64LE.Stream.shape, by decide, Proof.Sha1.PPC64LE.Stream.callee,
    digest_correct Proof.Sha1.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := Proof.Sha1.PPC64LE.compress_verified.2.1
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha256F : Fam where
  P := Impl.Sha256.PPC64LE.mdParams
  md := Proof.Sha256.md
  cn := "vg_sha256_compress"
  cc := Impl.Sha256.PPC64LE.compress
  ok := ⟨Proof.Sha256.PPC64LE.Md.dims, Proof.Sha256.PPC64LE.Md.shape, by decide, Proof.Sha256.PPC64LE.Md.callee,
    digest_correct Proof.Sha256.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := Proof.Sha256.PPC64LE.compress_verified.2.1
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha512F : Fam where
  P := Impl.Sha512.PPC64LE.mdParams
  md := Proof.Sha512.md
  cn := "vg_sha512_compress"
  cc := Impl.Sha512.PPC64LE.compress
  ok := ⟨Proof.Sha512.PPC64LE.Md.dims, Proof.Sha512.PPC64LE.Md.shape, by decide, Proof.Sha512.PPC64LE.Md.callee,
    digest_correct Proof.Sha512.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega),
    fun n hn => show n < 2 ^ 64 by omega⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := Proof.Sha512.PPC64LE.compress_verified.2.1
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

end VG.Proof.MdHashTable.PPC64LE
