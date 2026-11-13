module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT

/-!
# The callee of decryption

For each implementation `c` of `vg_rsa_private_crt` (a variant of
`RsaPrivateCrt`), `vg_rsa_private_checked` calling it, the internal
function the padding functions call, is a `PrivImpl`
(`privOf`): `privK` is its contract, and it uses its frame and two return
addresses of stack, since its callees' callees use none. So is
`vg_rsa_private_checked_precomputed` (`privNameP`, `privCodeP`), under
`chkContractP`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Rsa.X86_64

/-- `vg_rsa_private_checked_precomputed` calling `c`: its name and code. -/
def privNameP (c : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ c.suffix
def privCodeP (c : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.codeP c.nameP c.codeP c.pubOp.name c.pubOp.code

theorem privCodeP_depth (c : CrtImpl) : (privCodeP c).x86_64Depth ≤ privStack := by
  simp only [privCodeP, Impl.Rsa.X86_64.PrivChecked.codeP, Impl.Rsa.X86_64.PrivChecked.bodyP,
    Impl.Rsa.X86_64.PrivChecked.checkP, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp c.nospP, c.depthP,
    x86_64Depth_noSp c.pubOp.nosp, c.pubOp.depth]
  decide

theorem privCodeP_ok (c : CrtImpl) (s : State) (h : chkContractP.pre s) :
    ∃ t s', Exec isa (privCodeP c) s t s' ∧ abiPreserved s s' ∧ chkContractP.post s s' :=
  codeP_correct c _ s h

theorem privCodeP_ct (c : CrtImpl) : ConstantTime isa chkContractP.pre chkContractP.pub (privCodeP c) :=
  codeP_constantTime c _

theorem privCodeP_spSafe (c : CrtImpl) : (privCodeP c).all (fun i => !isa.writesSp i) = true :=
  codeP_spSafe c _

end VG.Proof.RsaPkcs1Enc.X86_64
