import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT

/-! ## From `CachedVerifyRel.lean` -/

section

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

end

/-! ## From `CachedVerifyHash.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
variable {p : Params}

/-- The cached digest is readable and survives the hashing workspace. -/
structure TrSide (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  read : ∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R
  x : L.XS.Disjoint ⟨L.rnd, 64⟩
  stack : L.STK.Disjoint ⟨L.rnd, 64⟩

theorem VOk.trSide {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m : Mem} (h : VOk p L m) : TrSide L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨⟨⟨σ.gpr .x7, 64⟩, by simp [cachedLay, hσ.rd], within_self _⟩,
    hσ.trScr.symm.sub_left (cachedLay_X p σ).sub, hσ.stkTr⟩

theorem TrSide.parts {L : VG.Proof.MlDsa.AArch64.Message.Lay} (h : TrSide L) :
    (∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R) ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.ST, 200⟩ ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.KS, 640⟩ ∧ L.STK.Disjoint ⟨L.rnd, 64⟩ :=
  ⟨h.read, h.x.symm.sub_right (Region.sub_prefix (by decide)),
    h.x.symm.sub_right (within_off L.X (d := 200) (n := 640) (k := 1024) (by omega)).sub, h.stack⟩

theorem cachedTr_val {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m} {t : State} (h : Ctx L g vv m t) :
    (VG.Impl.MlDsa.AArch64.Message.Arg.slot fRnd).val t = L.rnd := by
  rw [h.slotV (f := fRnd) (j := 5) rfl (by omega)]
  rfl

theorem VOk.digest {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m} {t : State}
    (h : VOk p L m) (hc : Ctx L g vv m t) : bytesAt t.mem L.rnd 64 = H (bytesAt m L.key p.pkLen) 64 := by
  rw [hc.bytesAt_eq h.trSide.x h.trSide.stack (by decide)]
  obtain ⟨σ, hσ, _, rfl, rfl⟩ := h
  exact hσ.digest

/-- Reusing the digest retains the public-input-only leakage contract. -/
theorem cachedMu_tr (v : Proof.Sha3.AArch64.Permutation) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p L m) (muHash v.callee (.slot fRnd))
      (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t) := by
  have mh := muHash_tr_of v (I := verifyI p) (Φ := fun L m _ => VOk p L m) (G := TrSide)
    (tr := .slot fRnd) (by decide) rfl (fun L => L.rnd)
    (fun _ _ _ _ _ hc => cachedTr_val hc) (fun _ _ h => h.parts)
  have mh' : RelCT isa (Two (verifyI p) fun L m _ => VOk p L m) (muHash v.callee (.slot fRnd))
      (fun _ _ => True) := RelCT.mono mh (fun _ _ h => by
        obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := h
        exact ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁.trSide, φ₁⟩, ⟨φ₂.trSide, φ₂⟩⟩)
        (fun _ _ _ => trivial)
  exact two_wp mh' fun L g vv m t hL hc hφ => by
    obtain ⟨a, b, c, d⟩ := hφ.trSide.parts
    refine WP.mono (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
      (fun _ hc' => cachedTr_val hc') a b c d) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
    unfold VMuOk
    rw [hμ, hφ.digest hc]

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify

end

/-! ## From `CachedVerifyCT.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
variable {p : Params}

/-- Hashing the cached digest and verifying preserve the common layout. -/
theorem verifyBody_tr (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p L m)
      (.seq (muHash v.callee (.slot fRnd)) (callA n c verifyArgs))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    ((cachedMu_tr v).seq (verifyCall_tr hV hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m₀} {t : State},
        L.Ok → Ctx L g vv m₀ t → VOk p L m₀ →
        WP isa (.seq (muHash v.callee (.slot fRnd)) (callA n c verifyArgs)) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc hφ => by
      obtain ⟨a, b, c, d⟩ := hφ.trSide.parts
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      refine WP.seq (WP.mono (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
        (fun _ hc' => cachedTr_val hc') a b c d) fun t₂ ⟨hc₂, _⟩ => ?_)
      exact WP.mono (verifyCall_ok hV hp hσ h8 hc₂) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageCachedContract p AArch64.abi 16).pre x ∧ (verifyMessageCachedContract p AArch64.abi 16).pre y ∧
    (verifyMessageCachedContract p AArch64.abi 16).pub x y

theorem enterV_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x6]) (.block (enter .x6 p cachedVerifySaves)) (.block [])).isSome = true := by
  rfl

theorem verifyMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    ConstantTime isa (verifyMessageCachedContract p AArch64.abi 16).pre (verifyMessageCachedContract p AArch64.abi 16).pub
      (verifyMessageCached v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageCachedContract p AArch64.abi 16).pre s₁ ∧
      (verifyMessageCachedContract p AArch64.abi 16).pre s₂ ∧ (verifyMessageCachedContract p AArch64.abi 16).pub s₁ s₂) =
      Ghost (VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessageCached top
  have hlsr := ghost_step (P := VP2 p) (A := fun x a => a = x) (B := ALsr) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(vPub_of hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨lsr_ok _, lsr_ok _⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, (vPub_of hxy.2.2).x4]) ?_ ?_)
  · exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.sp, f₂.1.sp]; exact (vPub_of hxy.2.2).sp, by simp⟩) movz2_taint
  · let A : State → State → Prop := fun x a => ALsr x a ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (cachedLay p x) a.gpr a.v a.mem t
    have hent := ghost_step (P := VP2 p) (A := A) (B := B) (c := .block (enter .x6 p cachedVerifySaves))
      (AArch64.taintRel [.x6] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (vPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.get .x6, f₂.1.1.get .x6]; exact (vPub_of hxy.2.2).x6⟩) (enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageCachedContract p AArch64.abi 16).pre x' → A x' a' →
            WP isa (.block (enter .x6 p cachedVerifySaves)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := cachedLay_ok hp (cachedPre_of hx) h8
          exact WP.mono (enter_ok hL rfl (by decide) rfl (o.get .x6) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (cachedSaves_vals o) (by decide)) fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← (vPub_of hxy.2.2).x4, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq
      (RelCT.mono (verifyBody_tr v hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩, ⟨h8y, b', mb, cb⟩⟩ => ?_)
        fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := cachedPre_of hxy.1
    have hy := cachedPre_of hxy.2.1
    have hpub := vPub_of hxy.2.2
    have e := cachedLay_eq hx hy hpub
    refine ⟨cachedLay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, cachedLay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify

end
