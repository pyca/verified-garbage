import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

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
