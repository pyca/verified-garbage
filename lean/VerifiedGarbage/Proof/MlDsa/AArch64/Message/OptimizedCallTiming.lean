import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)

abbrev rootsAt (s : State) : Addr × Addr :=
  (s.syms "VG_MLDSA_NTT_EXPANDED",s.syms "VG_MLDSA_INV_FOLDED")
abbrev rootPairRegions (tab : Addr × Addr) : List Region := [⟨tab.1,3904⟩,⟨tab.2,3904⟩]
theorem rootsAt_syms {s t : State} (h : t.syms=s.syms) : rootsAt t=rootsAt s := by simp only [rootsAt,h]

def SOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃σ,SPre p σ ∧ (σ.gpr .x4).toNat<256 ∧ slay p σ=L ∧ σ.mem=m

variable {p : Params}
theorem SOk.facts {L : Lay} {m : Mem} (h : SOk p L m) : SFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.rndScr.symm.sub_left (slay_X p σ).sub, hσ.stkRnd, by simp [slay, hσ.rd],
    by simp [slay, hσ.wr], ⟨⟨σ.gpr .x7, mScrLen p⟩, by simp [slay, hσ.wr],
      within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x7, mScrLen p⟩, by simp [slay, hσ.wr], mu_within p σ⟩⟩

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr (tab : Addr × Addr) {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m t => SOk p L m ∧ MuOk L m t ∧ StaticRoots 16 t ∧ rootsAt t=tab) (callA n c signArgs) fun _ _ => True := by
  refine call_tr (by decide) hS.ver.1 hS.ver.2.1
    (fun L => [⟨L.key, p.skLen⟩, ⟨L.MU, 64⟩, ⟨L.rnd, 32⟩]++rootPairRegions tab) (fun L => [⟨L.sig, p.sigLen⟩, ⟨L.scr, sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ,hσ,h8,rfl,_⟩,_,hr,htab⟩ := hφ
    have H := signK_pre hp hσ h8 hc hm.1 hm.2 hr
    have etab : rootRegions t1=rootPairRegions tab := by
      change rootPairRegions (rootsAt t1)=rootPairRegions tab
      rw [rootsAt_syms hm.2,htab]
    simpa only [etab,signRd,signWr,slay] using H
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3, x4⟩ := signRegs_of c₁ f₁.1.1
    obtain ⟨y0, y1, y2, y3, y4⟩ := signRegs_of c₂ f₂.1.1
    have hk := hL.hKey
    have ek : ∀ {g v m₀} {a a1 : State}, Ctx (slay p σ) g v m₀ a → Moved signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.skLen = bytesAt m₀ (σ.gpr .x0) p.skLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (slay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [slay] at this ⊢; omega)
    have er : ∀ {g v m₀} {a a1 : State}, Ctx (slay p σ) g v m₀ a → Moved signArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) 32 = bytesAt m₀ (σ.gpr .x5) 32 := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (slay p σ).rnd) F.xRnd F.kRnd (by decide)
    have eμ : ∀ {a a1 : State}, Moved signArgs a a1 →
        bytesAt a1.mem (slay p σ).MU 64 = bytesAt a.mem (slay p σ).MU 64 := fun f => by rw [f.2.mem]
    sig_pub [signContract,signSig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,List.range,List.range.loop]
    simp only [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, and_true]
    refine ⟨by rw [f₁.1.2.sp, f₂.1.2.sp, c₁.sp, c₂.sp], ?_⟩
    have etab : rootsAt a1=rootsAt b1 := by
      rw [rootsAt_syms f₁.2,rootsAt_syms f₂.2,φ₁.2.2.2,φ₂.2.2.2]
    refine ⟨congrArg Prod.fst etab,congrArg Prod.snd etab,?_⟩
    rw [ek c₁ f₁.1, ek c₂ f₂.1, er c₁ f₁.1, er c₂ f₂.1, eμ f₁.1, eμ f₂.1, φ₁.2.1, φ₂.2.1]
    have := hi
    unfold signI at this
    rw [leak_eq hL F.key, leak_eq hL F.key] at this
    exact this
  · have F := hφ.1.facts
    have hw : Covers [⟨L.sig,p.sigLen⟩,⟨L.scr,sScr p⟩] L.wr := by
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact ⟨_,F.inSig,within_self _⟩
      · exact F.inScr
    refine ⟨Covers.append_left ?_ hw.right,hw⟩
    apply Covers.append_left
    · refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,List.mem_append_left _ (F.key ▸ hL.inKey),within_self _⟩
      · obtain ⟨R,hR,hw⟩ := F.inMu; exact ⟨R,by simp [hR],hw⟩
      · exact ⟨_,List.mem_append_left _ F.inRnd,within_self _⟩
    · have ht := Covers.pair hφ.2.2.1.forward.readable hφ.2.2.1.inverse.readable
      change Covers (rootPairRegions (rootsAt t)) (t.rd++t.wr) at ht
      simpa only [hφ.2.2.2,hc.rd,hc.wr] using ht

end VG.Proof.MlDsa.AArch64.Message.Optimized
