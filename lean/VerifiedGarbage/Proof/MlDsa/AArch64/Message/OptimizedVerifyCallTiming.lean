import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootPairRegions rootsAt rootsAt_syms)
variable {p : Params}
/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, VPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ vlay p σ = L ∧ σ.mem = m

theorem VOk.facts {L : Lay} {m : Mem} (h : VOk p L m) : VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm.sub_left (vlay_X p σ).sub, hσ.stkSig, hσ.nSig, by simp [vlay, hσ.rd],
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [vlay, hσ.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [vlay, hσ.wr], mu_withinV p σ⟩⟩

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr (tab : Addr × Addr) {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) (callA n c verifyArgs)
      fun _ _ => True := by
  refine Message.Optimized.call_tr (by decide) hV.ver.1 hV.ver.2.1
    (fun L => [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]++rootPairRegions tab) (fun L => [⟨L.scr, sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ,hσ,h8,rfl,_⟩,_,hr,htab⟩ := hφ
    have H := verifyK_pre hp hσ h8 hc hm.1 hm.2 hr
    have etab : rootRegions t1=rootPairRegions tab := by
      change rootPairRegions (rootsAt t1)=rootPairRegions tab
      rw [rootsAt_syms hm.2,htab]
    simpa only [etab,verifyRd,verifyWr,vlay] using H
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3⟩ := verifyRegs_of c₁ f₁.1.1
    obtain ⟨y0, y1, y2, y3⟩ := verifyRegs_of c₂ f₂.1.1
    have ek : ∀ {g v m₀} {a a1 : State}, Ctx (vlay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.pkLen = bytesAt m₀ (σ.gpr .x0) p.pkLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (vlay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [vlay] at this ⊢; omega)
    have es : ∀ {g v m₀} {a a1 : State}, Ctx (vlay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) p.sigLen = bytesAt m₀ (σ.gpr .x5) p.sigLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (vlay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
    have eμ : ∀ {a a1 : State}, Moved verifyArgs a a1 →
        bytesAt a1.mem (vlay p σ).MU 64 = bytesAt a.mem (vlay p σ).MU 64 := fun f => by rw [f.2.mem]
    obtain ⟨ik, im, ic, is⟩ := verifyI_eq hi
    sig_pub [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, y0, y1, y2, y3, and_true]
    refine ⟨by rw [f₁.1.2.sp, f₂.1.2.sp, c₁.sp, c₂.sp], ?_⟩
    have etab : rootsAt a1=rootsAt b1 := by
      rw [rootsAt_syms f₁.2,rootsAt_syms f₂.2,φ₁.2.2.2,φ₂.2.2.2]
    refine ⟨congrArg Prod.fst etab,congrArg Prod.snd etab,?_⟩
    rw [ek c₁ f₁.1,ek c₂ f₂.1,es c₁ f₁.1,es c₂ f₂.1,eμ f₁.1,eμ f₂.1,φ₁.2.1,φ₂.2.1]
    have ik' : bytesAt m₁ (σ.gpr .x0) p.pkLen = bytesAt m₂ (σ.gpr .x0) p.pkLen := ik
    have is' : bytesAt m₁ (σ.gpr .x5) p.sigLen = bytesAt m₂ (σ.gpr .x5) p.sigLen := is
    rw [ik, im, ic, ik', is']
  · have F := hφ.1.facts
    have hw : Covers [⟨L.scr,sScr p⟩] L.wr := by
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_singleton] at hr
      subst r; exact F.inScr
    refine ⟨Covers.append_left ?_ hw.right,hw⟩
    apply Covers.append_left
    · refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,List.mem_append_left _ (F.key ▸ hL.inKey),within_self _⟩
      · obtain ⟨R,hR,hw⟩ := F.inMu; exact ⟨R,by simp [hR],hw⟩
      · exact ⟨_,List.mem_append_left _ F.inSig,within_self _⟩
    · have ht := Covers.pair hφ.2.2.1.forward.readable hφ.2.2.1.inverse.readable
      change Covers (rootPairRegions (rootsAt t)) (t.rd++t.wr) at ht
      simpa only [hφ.2.2.2,hc.rd,hc.wr] using ht

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
