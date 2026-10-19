module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Impl.Ecdh.P256.X86_64
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Check
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Bswap
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Ops
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# ECDSA verification over P-256 on x86-64: the checked code without its displacements

From a taint that knows no region bases, the analysis does not read
displacements and immediates (`Proof/Framework/X86_64/TaintErase.lean`), so
the constant-time checks of the code before and after the comb, and of the
comb's tail, analyse it with them erased. Its field arithmetic is then the
same few blocks again and again: with each a constant (`materialize_shared`),
the kernel analyses each once from the same taint.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

/-- P-256's comb table. -/
def p256Table : CombData := ⟨7,Impl.P256.p256Comb7,Impl.P256.p256Comb7Start,"VG_P256_COMB",true⟩

/-- The code before the comb, without its displacements. -/
def beforeErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifyPrefix p256)

/-- The code after the comb, without its displacements. -/
def afterErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifySuffix p256).inline

/-- The comb's tail, without its displacements. -/
def tailErased : Prog VG.X86_64.isa :=
  VG.X86_64.Code.erase (Code.seq (.block (publicLoads (p256.combCfg p256Table)))
    (publicRest (p256.combCfg p256Table))).inline

materialize_shared beforeErased
materialize_shared afterErased
materialize_shared tailErased

end VG.Proof.Ecdsa.Verify.X86_64
