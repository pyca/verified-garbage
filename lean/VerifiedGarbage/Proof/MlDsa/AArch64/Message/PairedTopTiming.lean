import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedBodyTiming

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots pairedSignRootConsts)
variable {p : Params}

structure SPub (p : Params) (s t : State) extends Message.SPub p s t where
  roots : rootsAt s=rootsAt t

theorem sPub_of {s t : State}
    (h : (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pub s t) : SPub p s t := by
  sig_pub [signMessageContract,signMessageSig,abi,argRegs,Abi.withConsts,Sign.pairedSignRootConsts_eq,
    List.range,List.range.loop] at h
  obtain ⟨sp,hf,hi,hp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩ := h
  exact ⟨⟨sp,leak,x0,x1,x2,x3,x4,x5,x6,x7⟩,Prod.ext hf (Prod.ext hi hp)⟩

theorem slay_eq {s t : State} (hs : SPre p s) (ht : SPre p t) (h : SPub p s t) : slay p s=slay p t := by
  have hf := congrArg Prod.fst h.roots
  have hi := congrArg (fun t=>t.2.1) h.roots
  have hp := congrArg (fun t=>t.2.2) h.roots
  have er : s.rd=t.rd := by
    rw [hs.rd,ht.rd]
    simp only [rKey,rMsg,rCtx,rootRegions,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5] at hf hi hp ⊢
    rw [hf,hi,hp]
  have ew : s.wr=t.wr := by rw [hs.wr,ht.wr,h.x6,h.x7]
  simp only [slay,h.sp,h.x0,h.x1,h.x2,h.x3,h.x4,h.x5,h.x6,h.x7,er,ew]

abbrev SP2 (p : Params) (x y : State) : Prop :=
  (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre x ∧
  (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre y ∧
  (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pub x y

theorem signMessage_ct (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) :
    ConstantTime isa (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pub
      (signMessage v.callee n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre s₁ ∧
      (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre s₂ ∧ (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pub s₁ s₂) =
      Ghost (SP2 p) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `x9 ← ctx_len >> 8`.
  have hlsr := ghost_step (P := SP2 p) (A := fun x a => a = x) (B := fun x a => ALsr x a ∧ a.syms=x.syms) (c := .block [.lsr .x .x9 .x4 8])
    (AArch64.taintRel [] (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨(sPub_of hxy.2.2).sp, by simp⟩) lsr_taint)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩), WP.mono_syms (lsr_ok _) (fun _ h hy=>⟨h,hy⟩)⟩
  refine RelCT.seq hlsr (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.1.2, f₂.1.2, (sPub_of hxy.2.2).x4]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact AArch64.taintRel [] (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ =>
      ⟨by rw [f₁.1.1.sp, f₂.1.1.sp]; exact (sPub_of hxy.2.2).sp, by simp⟩) movz2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => (ALsr x a ∧ a.syms=x.syms) ∧ isa.eval (.nonzero .x .x9) a = some false
    let B : State → State → Prop := fun x t => (x.gpr .x4).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (slay p x) a.gpr a.v a.mem t ∧ t.syms=x.syms
    have hent := ghost_step (P := SP2 p) (A := A) (B := B) (c := .block (enter .x7 p signSaves))
      (AArch64.taintRel [.x7] (fun a b ⟨x, y, hxy, f₁, f₂⟩ => ⟨by rw [f₁.1.1.1.sp, f₂.1.1.1.sp]; exact (sPub_of hxy.2.2).sp,
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [f₁.1.1.1.get .x7, f₂.1.1.1.get .x7]; exact (sPub_of hxy.2.2).x7⟩) (enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre x' → A x' a' →
            WP isa (.block (enter .x7 p signSaves)) a' (B x') := fun x' a' hx ⟨⟨⟨o, e⟩, hy⟩, ef⟩ => by
          have h8 : (x'.gpr .x4).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have hL := slay_ok hp (sPre_of hx) h8
          exact WP.mono_syms (enter_ok hL rfl (by decide) rfl (o.get .x7) (by rw [o.sp]; rfl) (by rw [o.rd]; rfl)
            (by rw [o.wr]; rfl) (o.get .x4) (signSaves_vals o) (by decide)) fun t hc hyt => ⟨h8, a', o.mem, hc, hyt.trans hy⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.1.2, ← (sPub_of hxy.2.2).x4, ← f₁.1.2]; exact hc⟩⟩) fun _ _ h => h) (RelCT.seq (RelCT.mono (RelCT.exists_ fun tab => signBody_tr tab v hS hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca, sya⟩,
      ⟨h8y, b', mb, cb, syb⟩⟩ => ?_) fun _ _ h => h) (AArch64.taintRel [.x28] (fun a b h => ⟨h.2, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1⟩) leave_taint))
    have hx := sPre_of hxy.1
    have hy := sPre_of hxy.2.1
    have hpub := sPub_of hxy.2.2
    have e := slay_eq hx hy hpub
    refine ⟨rootsAt x, slay p x, a'.gpr, b'.gpr, a'.v, b'.v, a'.mem, b'.mem, slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨⟨x, hx, h8x, rfl, ma.symm⟩, roots_ctx hx (by simpa only [ma] using ca) sya, paired_ctx hx (by simpa only [ma] using ca) sya, rootsAt_syms sya⟩,
      ⟨⟨y, hy, h8y, e.symm, mb.symm⟩, roots_ctx hy (by simpa only [mb] using cb) syb, paired_ctx hy (by simpa only [mb] using cb) syb,
        (rootsAt_syms syb).trans hpub.roots.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.x0, ← hpub.x1, ← hpub.x2, ← hpub.x3, ← hpub.x4, ← hpub.x5] at lk
    unfold signI
    rw [ma, mb]
    exact lk


end VG.Proof.MlDsa.AArch64.Message.Paired
