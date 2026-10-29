module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCallTiming

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.Framework.Offset

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Message/PairedBodyTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots PairedRoots pairedSignRootConsts)
variable {p : Params}

theorem muHash_depth (v : Proof.Sha3.AArch64.Permutation) :
    16*(muHash v.callee (.slotOff fKey 64)).aarch64Depth≤16 := by
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hd : DLe 1 (muHash v.callee (.slotOff fKey 64)) := by
    unfold muHash kabs kpad ksqz callA
    dle_tac
  have := hd.le; omega

theorem signBody_tr (tab : Addr × Addr × Addr) (v : Proof.Sha3.AArch64.Permutation) {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m t => SOk p L m ∧ StaticRoots 16 t ∧ PairedRoots 16 t ∧ rootsAt t=tab)
      (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c signArgs))
      fun a b => a.gpr .x28 = b.gpr .x28 ∧ a.sp = b.sp := by
  have side : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ R) ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.key + BitVec.ofNat 64 64, 64⟩ := fun L hL => by
    have := hL.hKey
    have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
    have hst : Region.Sub ⟨L.ST, 200⟩ L.XS := by
      have := Offset.sub_base L.X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [x0] using this
    exact ⟨⟨_, List.mem_append_left _ hL.inKey, w⟩, (hL.xKey.symm.sub_left w.sub).sub_right hst,
      (hL.xKey.symm.sub_left w.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
  have mh := muHash_tr v (I := signI p) (Φ := fun L m t => SOk p L m ∧ StaticRoots 16 t ∧ PairedRoots 16 t ∧ rootsAt t=tab) (tr := .slotOff fKey 64) (by decide) rfl
    (fun L => L.key + BitVec.ofNat 64 64) (fun L g vv m t hc => hc.slotOffV 64) side
  have mh' := two_wp (I := signI p) (Φ := fun L m t => SOk p L m ∧ StaticRoots 16 t ∧ PairedRoots 16 t ∧ rootsAt t=tab) (Ψ := fun L m t => SOk p L m ∧ MuOk L m t ∧ StaticRoots 16 t ∧ PairedRoots 16 t ∧ rootsAt t=tab) mh
    fun L g vv m₀ t hL hc ⟨hφ,hr,rp,htab⟩ => by
      have := hL.hKey
      have w : Within ⟨L.key + BitVec.ofNat 64 64, 64⟩ L.KEY := within_off _ (by omega)
      obtain ⟨a, b, c, d⟩ := side L hL
      refine WP.mono_syms (VG.Proof.MlDsa.AArch64.Sign.WP.pairedRoots (hr.phase (muHash_depth v) (by decide) (muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl (fun t' hc' => hc'.slotOffV 64)
        a b c d)) rp (muHash_depth v) (by decide)) fun t' ⟨⟨⟨hc',hμ⟩,hr'⟩,rp'⟩ hsy => ⟨hc',hφ,?_,hr',rp',by rw [rootsAt_syms hsy,htab]⟩
      unfold MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  refine RelCT.postDep (F := fun x x' => x'.gpr .x28 = x.gpr .x28 ∧ x'.sp = x.sp)
    (mh'.seq (signCall_tr tab hS hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g vv m₀} {t : State}, L.Ok → Ctx L g vv m₀ t → (SOk p L m₀ ∧ StaticRoots 16 t ∧ PairedRoots 16 t ∧ rootsAt t=tab) →
        WP isa (.seq (muHash v.callee (.slotOff fKey 64)) (callA n c signArgs)) t
          fun t' => t'.gpr .x28 = t.gpr .x28 ∧ t'.sp = t.sp := fun hL hc ⟨hφ,hr,rp,htab⟩ => by
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d⟩ := side _ hL
      refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.WP.pairedRoots (hr.phase (muHash_depth v) (by decide) (muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc' => hc'.slotOffV 64) a b c d)) rp (muHash_depth v) (by decide)) fun t₁ ⟨⟨⟨hc₁,_⟩,hr₁⟩,rp₁⟩ => ?_)
      exact WP.mono (signCall_ok hS hp hσ h8 hc₁ hr₁ rp₁) fun s' ⟨hf, _⟩ =>
        ⟨hf.x28.trans hc.x28.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.x28, c₂.x28], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩


end VG.Proof.MlDsa.AArch64.Message.Paired
end

end

@[expose] public section

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
