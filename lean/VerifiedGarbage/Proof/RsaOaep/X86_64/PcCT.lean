module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcContract
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.PcContract
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
meta import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
meta import VerifiedGarbage.Proof.RsaOaep.Decode
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: constant time

The pieces of `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` (`EncCT`), for entry states
related to the anchor by `contract` too (`PP`: the precondition, `pre` and
its words), and the call of the precomputed public operation, constant time
for its contract, which makes `pre`'s words public. Nothing follows the
call.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

/-- What `contract` adds to `encK`'s precondition and public data. -/
def PP (H : Spec.Mgf1.Hash) (a s : State) : Prop :=
  PPre H s ∧ stackArg a 7 = stackArg s 7 ∧ stackArg a 8 = stackArg s 8 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 7) (stackArg s 8).toNat

/-- Before the call, with its arguments. -/
structure EWPP (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 5)
  w : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = pw s i
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rcx
  rdx : t.gpr .rdx = stackArg s 7
  rcx : t.gpr .rcx = stackArg s 8
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9

variable {H G : Spec.Mgf1.Hash}

theorem ew_pubArgs' {s t : State} (hp : PPre H s) (h : EW s t) :
    WP isa (.block Impl.RsaOaep.X86_64.Precomputed.pubArgs) t (EWPP s) := by
  rw [Impl.RsaOaep.X86_64.Precomputed.pubArgs, WP.block_append_iff]
  refine WP.mono (ew_pubArgs h) fun t₁ e => ?_
  refine WP.mono (wp_good (block_good _ rfl) (load_pre hp e.he.rsp e.he.rd e.he.fr))
    fun u ⟨⟨k, hm, hdx, hcx⟩, sp', mx', f'⟩ => ?_
  exact ⟨e.he.step k.2.1 k.2.2 sp' (keep_cs3 k (by decide)) mx' f', e.L.congr (k.gpr (by decide)) k.2.2
    (by rw [hm]), fun i hi => by rw [hm]; exact e.w i hi, (k.gpr (by decide)).trans e.rdi,
    (k.gpr (by decide)).trans e.rsi, hdx, hcx, (k.gpr (by decide)).trans e.r8, (k.gpr (by decide)).trans e.r9⟩

/-- What the precomputed public operation's contract makes public, from the anchor. -/
theorem pub_view {a s t : State} (S : ESib H G (PP H) a s) (h : EWPP s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 7, stackArg a 8, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    (∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = pw a i) ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  have hp := S.2.2.1
  have hF := fb_toNat hp.toEPre
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [e_entry_regs, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rcx) (by decide), S.2.2.2.1, S.2.2.2.2.1, S.gpr (r := .r8) (by decide),
      S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega), h.w i hi, pw_sib S]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h.rdx, h.rcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2.2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.r8, h.r9]
    rw [entryBytes h.he _ _ hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega)]
    exact S.2.1.2.2.2.symm

theorem call_ct (v : PublicImpl) : RelCT isa (Two (EAt H G (PP H) EWPP)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := S₁.2.2.1
  have hp₂ := S₂.2.2.1
  obtain ⟨r₁, g₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers hp₁ j₁.he.rd j₁.he.wr
  obtain ⟨c₂, w₂⟩ := call_covers hp₂ j₂.he.rd j₂.he.wr
  have p₁ := call_pre hp₁ j₁.he.rsp (j₁.w 0 (by decide)) (j₁.w 1 (by decide)) (j₁.w 2 (by decide))
    (j₁.w 3 (by decide)) j₁.rdi j₁.rsi j₁.rdx j₁.rcx j₁.r8 j₁.r9
  have p₂ := call_pre hp₂ j₂.he.rsp (j₂.w 0 (by decide)) (j₂.w 1 (by decide)) (j₂.w 2 (by decide))
    (j₂.w 3 (by decide)) j₂.rdi j₂.rsi j₂.rdx j₂.rcx j₂.r8 j₂.r9
  refine ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, ⟨List.map_inj_left.mp (r₁.trans r₂.symm),
    (g₁ 0 (by decide)).trans (g₂ 0 (by decide)).symm, (g₁ 1 (by decide)).trans (g₂ 1 (by decide)).symm,
    (g₁ 2 (by decide)).trans (g₂ 2 (by decide)).symm, (g₁ 3 (by decide)).trans (g₂ 3 (by decide)).symm,
    n₁.trans n₂.symm, e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

section
variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

include hH KH hG KG mH mG in
theorem encMain_ct (v : PublicImpl) : RelCT isa (Two (EAt mH.G mG.G (PP mH.G) (EK Hl.D)))
    (Impl.RsaOaep.X86_64.Precomputed.encMain Hl.stream Gm.stream v.name v.code) fun _ _ => True := by
  unfold Impl.RsaOaep.X86_64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  refine encMask_ct hH KH hG KG mH mG ?_
  refine RelCT.seq (two_post (Ψ := EAt mH.G mG.G (PP mH.G) EWPP) (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ t ⟨s, S, h⟩ => WP.mono (ew_pubArgs' S.2.2.1 h.1) fun _ e => ⟨s, S, e⟩) ?_
  exact call_ct v

include hH KH hG KG mH mG in
theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa (contract mH.G mG.G).pre (contract mH.G mG.G).pub
      (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream Gm.stream v.name v.code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (relCT_alloc ((encBodyWith_ct (P := PP mH.G) (hH := hH)
    (hG := hG) (mH := mH) (mG := mG) (hmain := encMain_ct hH KH hG KG mH mG v)).mono ?_ fun _ _ h => h))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, rfl, rfl⟩
  have p₁ := pre_of (G := mG.G) h₁
  have p₂ := pre_of (G := mG.G) h₂
  exact ⟨s₁, ⟨s₁, ⟨p₁.toEPre, encPub_refl _ _ s₁, p₁, rfl, rfl, rfl⟩, rfl⟩,
    ⟨s₂, ⟨p₂.toEPre, hpub.1, p₂, hpub.2⟩, rfl⟩⟩

include hH KH hG KG mH mG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, calling the
implementation `v` of `vg_rsa_public_precomputed_checked`, meets the shared
contract. -/
theorem code_verified (v : PublicImpl)
    (hsat : ∃ s, (Spec.RsaOaep.encryptPrecomputedContract mH.G mG.G abi encStack).pre s) :
    Verified target (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream Gm.stream v.name v.code)
      (Spec.RsaOaep.encryptPrecomputedContract mH.G mG.G abi encStack) :=
  Verified.of_correct (k := contract mH.G mG.G) (code_correct hH KH hG KG mH mG v)
    (code_constantTime hH KH hG KG mH mG v) (implies mH.G mG.G hsat)

end

end VG.Proof.RsaOaep.X86_64.Pc
