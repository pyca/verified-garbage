module

public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCT
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCT
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIOCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def publicData (q : DPub × BitVec 64) : PublicData := ⟨DPub.L q,q.1.N⟩

theorem db_pre {q : DPub × BitVec 64} {s : State} (h : DB q s) : Pre (publicData q) s := by
  obtain ⟨X,x,hc,hf,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
  exact ⟨X,x,hc,⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2⟩

/-- `DB` after `is65537`, which writes registers only. -/
theorem db_is65537 {q : DPub × BitVec 64} {s t : State} (h : DB q s) (hm : t.mem = s.mem)
    (k : Keep [.rax, .r8, .r9, .r10, .r11] s t) : DB q t := by
  obtain ⟨xb,σ,g,hg,hn,hinv,hlt,hone⟩ := h
  exact ⟨xb,σ,g.step (by rw [hm]; exact Frm.refl _ _ _) (k.mono (by decide)) (by rw [hm]),
    ⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,by rw [hm]; exact hg.hdr⟩,
    by rw [hm]; exact hn,by rw [hm]; exact hinv,by rw [hm]; exact hlt,by rw [hm]; exact hone⟩

/-- The exponentiation leaks the same in runs that agree on `e`: whether
`e` is 65537 is public. -/
theorem exp_ct (M : Mont) : RelCT isa (Two DB) (Folded.exp M.mm) (Two DC) := by
  unfold Folded.exp Folded.is65537
  refine RelCT.seq (RelCT.seq (two_piece (Ψ := fun q t => DB q t ∧ t.gpr .r8 = q.1.ep ∧
      t.gpr .r9 = BitVec.ofNat 64 q.1.len)
    [.rdi] (fun _ _ _ ⟨_,_,_,h₁,_⟩ ⟨_,_,_,h₂,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi,h₂.rdi]) (by taint_decide) ?_)
    (two_piece (Ψ := fun q t => DB q t ∧ t.zf = some (decide (Spec.Rsa.os2ip q.1.eb = 65537)))
    [.r8, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.1,h₂.2.1]
      · rw [h₁.2.2,h₂.2.2]) (by taint_decide) ?_)) ?_
  · rintro q s h
    obtain ⟨X,x,hc,hf,he,hlen,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    exact WP.mono (is65537Load_ok hc.good hf.1 he hlen) fun a ⟨h8,h9,ma,ka⟩ =>
      ⟨db_is65537 h ma (ka.mono (by decide)),h8,h9⟩
  · rintro q s ⟨h,h8,h9⟩
    obtain ⟨_,_,_,_,_,_,hL1,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    have h' := h
    obtain ⟨xb,σ,g,_⟩ := h'
    have hs := g.1.e.congrK g.inScr g.2.2.1
    exact WP.mono (is65537Check_ok h8 h9 hs g.1.el hL1
      (by have := g.1.L2; have := g.1.k2; show q.1.len < 2^31; omega)) fun a ⟨za,ma,ka⟩ =>
        ⟨db_is65537 h ma (ka.mono (by decide)),za⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval,h₁.2,h₂.2]) ?_ ?_
  · refine two_post ((two_map publicData (fun _ _ h => db_pre h.1.1) (exp65536_ct M)).mono
      (fun _ _ h => h) fun _ _ _ => trivial) ?_
    rintro q s ⟨⟨h,hz⟩,hb⟩
    have h65 : Spec.Rsa.os2ip q.1.eb = 65537 := by simpa [eval,hz] using hb
    obtain ⟨X,x,hc,hf,_⟩ := VG.Proof.Bignum.X86_64.db_pre h
    obtain ⟨xb,σ,g,_⟩ := h
    have hE := os2ip_evenLast g.1.eodd
    refine WP.mono (exp65536_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2)
      fun t ⟨ct,lt,vt,ft,kt⟩ => ⟨xb,σ,X,x,g.step (ft.mono (pExpRanges_pdAll _)) kt
        (ft.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
          (by unfold sMask sFn; omega)),ct,lt,?_⟩
    rw [← show Spec.Rsa.os2ip (evenLast q.1.eb) = 65536 by omega] at vt; exact vt
  · exact two_map id (fun _ _ h => h.1.1) pdExp_ct

/-- The computation leaks the same in runs with the same public data, given
that the last multiplication does (`hfinal`). -/
theorem rest_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp [wordIn]) (by simp [phases]) (RelCT.seq wordSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [wordOutStepsArr])
    (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (RelCT.seq (exp_ct M) (pdFinal_ct hfinal))
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub))
      (fun _ _ h => dd_wordOPre h) wordOut_ct

end VG.Proof.Bignum.X86_64.FoldedPublic
