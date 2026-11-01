module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCt

/-!
# EMSA-PSS's encoding and its check on x86-64, as callees

For each hash function `v` (a variant of `MdHash`), `encode` and
`checkEncoding` as `Generic/MdHash/X86_64/RsaPss.lean` emits them, with the
facts their callers, signing and verification
(`Generic/MdHash/RsaPrivateCrt/X86_64/RsaPss.lean`,
`Generic/MdHash/RsaPublicPrecomputed/X86_64/RsaPss.lean`), need: their
contracts on the registers, constant time, the stack pointer and the stack
they use (`encOf`, `chkOf`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64

/-- A function meeting `encK G`. -/
structure EncImpl (G : Spec.Mgf1.Hash) where
  name : String
  code : Prog isa
  ok : ∀ s, (encK G).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (encK G).post s s'
  ct : ConstantTime isa (encK G).pre (encK G).pub code
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  depth : code.x86_64Depth ≤ encStack

/-- A function meeting `chkK G`. -/
structure ChkImpl (G : Spec.Mgf1.Hash) where
  name : String
  code : Prog isa
  ok : ∀ s, (chkK G).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (chkK G).post s s'
  ct : ConstantTime isa (chkK G).pre (chkK G).pub code
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  depth : code.x86_64Depth ≤ chkStack

/-- `encode` made with `v`'s compression function. -/
def encOf (v : Pbkdf2.Md.X86_64.MdHash) : EncImpl v.mgf.G where
  name := s!"vg_rsa_pss_{v.mgf.G.rust}_mgf1_{v.mgf.G.rust}_encode" ++ v.suffix
  code := Impl.RsaPss.X86_64.encode v.H
  ok := Enc.enc_correct v.ok v.K v.mgf
  ct := Enc.enc_ct v.ok v.K v.mgf v.pss
  spSafe := Enc.enc_spAll v.ok v.K
  depth := Enc.enc_xd v.K

/-- `checkEncoding` made with `v`'s compression function. -/
def chkOf (v : Pbkdf2.Md.X86_64.MdHash) : ChkImpl v.mgf.G where
  name := s!"vg_rsa_pss_{v.mgf.G.rust}_mgf1_{v.mgf.G.rust}_check_encoding" ++ v.suffix
  code := Impl.RsaPss.X86_64.checkEncoding v.H
  ok := Chk.chk_correct v.ok v.K v.mgf
  ct := Chk.chk_ct v.ok v.K v.mgf v.pss
  spSafe := Chk.chk_spAll v.ok v.K
  depth := Chk.chk_xd v.K

end VG.Proof.RsaPss.X86_64
