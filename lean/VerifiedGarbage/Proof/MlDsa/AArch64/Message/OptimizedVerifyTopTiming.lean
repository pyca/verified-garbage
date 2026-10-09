import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyBodyTiming

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootsAt rootsAt_syms)
variable {p : Params}

structure VPub (p : Params) (s t : State) extends Message.VPub p s t where
  roots : rootsAt s=rootsAt t

theorem vPub_of {s t : State}
    (h : (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub s t) : VPub p s t := by
  sig_pub [verifyMessageContract,verifyMessageSig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,
    List.range,List.range.loop] at h
  obtain ⟨sp,hf,hi,leak,x0,x1,x2,x3,x4,x5,x6⟩ := h
  exact ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6⟩,Prod.ext hf hi⟩

theorem vlay_eq {s t : State} (hs : VPre p s) (ht : VPre p t) (h : VPub p s t) : vlay p s=vlay p t := by
  have hf := congrArg Prod.fst h.roots
  have hi := congrArg Prod.snd h.roots
  have er : s.rd=t.rd := by
    rw [hs.rd,ht.rd]
    simp only [rKey,rMsg,rCtx,rootRegions,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5] at hf hi ⊢
    rw [hf,hi]
  have ew : s.wr=t.wr := by rw [hs.wr,ht.wr,h.x6]
  simp only [vlay,h.sp,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5,h.x6,er,ew]

abbrev VP2 (p : Params) (x y : State) : Prop :=
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre x ∧
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre y ∧
  (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub x y

theorem verifyMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) :
    ConstantTime isa (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub
      (verifyMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s₁ ∧
      (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre s₂ ∧ (verifyMessageContract p (abi.withConsts signRootConsts) 16).pub s₁ s₂) =
      Ghost (VP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := VP2 p) (A := fun x a => a = x) (B := fun x a => ALsr x a ∧ a.syms=x.syms) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(vPub_of hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩), WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩)⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.1.2, f₂.1.2, (vPub_of hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (vPub_of hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => (ALsr x a ∧ a.syms=x.syms) ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (vlay p x) a.gpr a.v a.mem t ∧ t.syms=x.syms
    have hent := ghost_step (P := VP2 p) (A := A) (B := B) (c := .block (enter .x6 p verifySaves))
      (AArch64.taintRel [.x6] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.1.sp, f₂.1.1.1.sp]; exact (vPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.1.get .x6, f₂.1.1.1.get .x6]; exact (vPub_of hxy.2.2).x6⟩) (enterV_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (verifyMessageContract p (abi.withConsts signRootConsts) 16).pre x' → A x' a' →
            WP isa (.block (enter .x6 p verifySaves)) a' (B x') := fun x' a' hx ⟨⟨⟨o, e⟩, hy⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := vlay_ok hp (vPre_of hx) h8
          exact WP.mono_syms (enter_ok hL rfl (by decide) rfl (o.get .x6) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (verifySaves_vals o) (by decide)) fun t hc hyt => ⟨h8, a', o.mem, hc, hyt.trans hy⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.1.2, ← (vPub_of hxy.2.2).x4, ← f₁.1.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (RelCT.exists_ fun tab => verifyBody_tr tab v hV hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca, sya⟩,
      ⟨h8y, b', mb, cb, syb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := vPre_of hxy.1
    have hy := vPre_of hxy.2.1
    have hpub := vPub_of hxy.2.2
    have e := vlay_eq hx hy hpub
    refine ⟨rootsAt x, vlay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨⟨x, hx, h8x, rfl, ma.symm⟩, roots_ctx hx (by simpa only [ma] using ca) sya, rootsAt_syms sya⟩,
      ⟨⟨y, hy, h8y, e.symm, mb.symm⟩, roots_ctx hy (by simpa only [mb] using cb) syb,
        (rootsAt_syms syb).trans hpub.roots.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk


end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
