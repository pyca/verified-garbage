import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyHash

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
