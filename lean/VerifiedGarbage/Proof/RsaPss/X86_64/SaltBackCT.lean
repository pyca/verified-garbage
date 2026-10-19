module
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBack

import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT
import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.DirectLen
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirectCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
meta import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
meta import VerifiedGarbage.Proof.RsaPss.Encoding
meta import VerifiedGarbage.Proof.RsaPss.MgfBytes
meta import VerifiedGarbage.Proof.RsaPss.SignCases
meta import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
meta import VerifiedGarbage.Proof.RsaPss.X86_64.DirectLen
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirectCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.Sha256.StateMem

/-! Constant-time public dispatch for PSS salt verification. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {extra : State → State → Prop}

/-- Testing the public salt mode preserves the verification state. -/
theorem saltAny_ct : RelCT isa (Two (VAt (extra := extra) G (JM H (X7 H))))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt (extra := extra) G (JM H (X7 H)) a t ∧
      isa.eval .e t = some (decide (vw H a 35 = 0))) := by
  refine two_post (vtwo (G := G) (H := H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- The bound on the requested length is public too. -/
theorem saltLen_ct : RelCT isa (Two (VAt (extra := extra) G (JM H (X7 H))))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt (extra := extra) G (JM H (X7 H)) a t ∧
      isa.eval .b t = some (decide ((stackArg a 1).toNat < vdb H.D a))) := by
  refine two_post (vtwo (G := G) (H := H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) (by taint_decide))
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((stackArg s 1).toNat < vdb H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb H.D s < 2 ^ 64 by unfold vdb veml; omega)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp), ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.arg1, S.vdb]

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH K in
theorem genericSaltBack_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JM H (X7 H)))) (genericSaltBack H)
      (Two (VAt (extra := extra) lk.G (JR H))) :=
  RelCT.assoc ((cyd_ct hH lk hc.verify).seq ((copyDb_ct hH hc.verify).seq
    ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
      ((mhash_ct hH K hc.hash1).seq (cmpH_ct hH hc.verify))))))

include hH K in
theorem saltBack_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JM H (X7 H)))) (saltBack H)
      (Two (VAt (extra := extra) lk.G (JR H))) := by
  have generic := genericSaltBack_ct (extra := extra) hH K lk hc
  have fixed := fixedSaltBack_ct (extra := extra) hH K lk hc
  unfold saltBack
  refine saltAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (saltLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine fixed.mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (stackArg a 1).toNat < vdb H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.arg1, S.vdb]⟩

end VG.Proof.RsaPss.X86_64
