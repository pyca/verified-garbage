import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
variable {p : Params}

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) : Prop :=
  ∃ σ, CachedPre p σ ∧ (σ.gpr .x4).toNat < 256 ∧ cachedLay p σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  key : L.keyLen = p.pkLen
  xSig : L.XS.Disjoint ⟨L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 64
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.rd
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

theorem VOk.facts {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m : Mem} (h : VOk p L m) : VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.sigScr.symm.sub_left (cachedLay_X p σ).sub, hσ.stkSig, hσ.nSig, by simp [cachedLay, hσ.rd],
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [cachedLay, hσ.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩,
    ⟨⟨σ.gpr .x6, mScrLen p⟩, by simp [cachedLay, hσ.wr], mu_withinV p σ⟩⟩

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t) (callA n c verifyArgs)
      fun _ _ => True := by
  refine call_tr (by decide) hV.ver.1 hV.ver.2.1
    (fun L => [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]) (fun L => [⟨L.scr, sScr p⟩])
    (fun L g v m₀ t t1 hL hc hφ hm => ?_) (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g v m₀ t hL hc hφ => ?_)
  · obtain ⟨⟨σ, hσ, h8, rfl, -⟩, -⟩ := hφ
    exact verifyK_pre hp hσ h8 hc hm.1 (hm.2.sp.trans hc.sp)
  · obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁.1
    have F := φ₁.1.facts
    obtain ⟨x0, x1, x2, x3⟩ := verifyRegs_of c₁ f₁.1
    obtain ⟨y0, y1, y2, y3⟩ := verifyRegs_of c₂ f₂.1
    have ek : ∀ {g v m₀} {a a1 : State}, Ctx (cachedLay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x0) p.pkLen = bytesAt m₀ (σ.gpr .x0) p.pkLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (cachedLay p σ).key) hL.xKey hL.kKey (by have := hL.nKey; simp only [cachedLay] at this ⊢; omega)
    have es : ∀ {g v m₀} {a a1 : State}, Ctx (cachedLay p σ) g v m₀ a → Moved verifyArgs a a1 →
        bytesAt a1.mem (σ.gpr .x5) p.sigLen = bytesAt m₀ (σ.gpr .x5) p.sigLen := fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq (p := (cachedLay p σ).sig) F.xSig F.kSig (by have := F.nSig; omega)
    have eμ : ∀ {a a1 : State}, Moved verifyArgs a a1 →
        bytesAt a1.mem (cachedLay p σ).MU 64 = bytesAt a.mem (cachedLay p σ).MU 64 := fun f => by rw [f.2.mem]
    obtain ⟨ik, im, ic, is⟩ := verifyI_eq hi
    sig_pub [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    simp only [x0, x1, x2, x3, y0, y1, y2, y3, and_true]
    refine ⟨by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp], ?_⟩
    rw [ek c₁ f₁, ek c₂ f₂, es c₁ f₁, es c₂ f₂, eμ f₁, eμ f₂, φ₁.2, φ₂.2]
    have ik' : bytesAt m₁ (σ.gpr .x0) p.pkLen = bytesAt m₂ (σ.gpr .x0) p.pkLen := ik
    have is' : bytesAt m₁ (σ.gpr .x5) p.sigLen = bytesAt m₂ (σ.gpr .x5) p.sigLen := is
    rw [ik, im, ic, ik', is']
  · have F := hφ.1.facts
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (F.key ▸ hL.inKey), within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact F.inScr

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .x0) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat ++
      bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat ++ bytesAt s₁.mem (s₁.gpr .x5) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .x0) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat ++
      bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat ++ bytesAt s₂.mem (s₂.gpr .x5) p.sigLen)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6
  x7 : s₁.gpr .x7 = s₂.gpr .x7

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageCachedContract p AArch64.abi 16).pub s₁ s₂) : VPub p s₁ s₂ := by
  sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem cachedLay_eq {s₁ s₂ : State} (h₁ : CachedPre p s₁) (h₂ : CachedPre p s₂) (h : VPub p s₁ s₂) : cachedLay p s₁ = cachedLay p s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [rKey, rMsg, rCtx, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x7]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [h.x6]
  simp only [cachedLay, h.sp, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, e1, e2]


end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
