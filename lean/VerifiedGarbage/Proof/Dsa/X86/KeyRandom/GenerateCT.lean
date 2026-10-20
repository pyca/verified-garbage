module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.PrepareCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Public
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sample
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.SampleCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.SampledCT

/-! # Sampling and derivation follow the disclosed trace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem prepared_step {s t : State} (A : KeyABI s) (h : Ready s t) (hc : checked s = true)
    (used : slot t.mem (rBase s) oUsed = 0) :
    WP isa (.seq prepare (.block [.alu .cmp .eax (.imm 0)])) t fun u =>
      (∃ d, Smp s 0 d u) ∧ u.zf = some false := by
  have hql := rQBytes_le A
  have hq := checked_q hc
  refine WP.seq (WP.mono (prepare_ok A h) fun u ⟨ax, P, hu, ou, _⟩ => ?_)
  refine wp_cmpi fun v fv _ z => WP.block_nil ?_
  have hv := hu.fupd fv
  have usedV : slot v.mem (rBase s) oUsed = 0 := by
    rw [fv.mem, outs_low ou (e := oQ) (by decide) (by decide) (by decide)]; exact used
  have prepared := P hq
  rw [ax] at z
  change 1 < Spec.Dsa.decodeBE (rQBytes s) at hq
  simp only [hq, ite_true] at z
  refine ⟨⟨(slot v.mem (rBase s) oDraws).toNat, ?_⟩, ?_⟩
  · exact ⟨hv, by rw [fv.mem]; exact prepared.q, by rw [fv.mem]; exact prepared.width,
      by rw [fv.mem]; exact prepared.mask, usedV, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun i hi => by rw [fv.mem]; exact prepared.nonce i (by omega), Nat.zero_le _⟩
  · rw [z]; rfl

theorem generate_ct (F : DeriveFn) {s₁ s₂ t₁ t₂ : State}
    (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (hc₁ : checked s₁ = true) (hc₂ : checked s₂ = true)
    (hr : (rResult s₁).status = (rResult s₂).status) (ht : (rResult s₁).trace = (rResult s₂).trace)
    (R₁ : Ready s₁ t₁) (R₂ : Ready s₂ t₂)
    (used₁ : slot t₁.mem (rBase s₁) oUsed = 0) (used₂ : slot t₂.mem (rBase s₂) oUsed = 0)
    {tr₁ tr₂ : List Leak} {u₁ u₂ : State}
    (x₁ : Exec isa (generate F.name F.code) t₁ tr₁ u₁)
    (x₂ : Exec isa (generate F.name F.code) t₂ tr₂ u₂) : tr₁ = tr₂ := by
  have htr : (draw s₁).trace = (draw s₂).trace := by rw [← draw_trace A₁ hc₁, ← draw_trace A₂ hc₂, ht]
  unfold generate at x₁ x₂
  cases x₁ with | seq p₁ r₁ => cases r₁ with | seq c₁ b₁ =>
  cases x₂ with | seq p₂ r₂ => cases r₂ with | seq c₂ b₂ =>
  have ep := (prepare_ct _ _ _ _ _ _ ⟨pubOf s₁, ⟨s₁, A₁, rfl, R₁⟩, s₂, A₂, e.symm, R₂⟩ p₁ p₂).1
  have ct : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (by taint_decide)
  have ec := (ct _ _ _ _ _ _ trivial c₁ c₂).1
  obtain ⟨⟨d₁, S₁⟩, z₁⟩ := post_of_exec (prepared_step A₁ R₁ hc₁ used₁) (.seq p₁ c₁)
  obtain ⟨⟨d₂, S₂⟩, z₂⟩ := post_of_exec (prepared_step A₂ R₂ hc₂ used₂) (.seq p₂ c₂)
  cases b₁ with
  | iteT f₁ _ => simp only [eval, z₁] at f₁; contradiction
  | iteF _ b₁ =>
  cases b₂ with
  | iteT f₂ _ => simp only [eval, z₂] at f₂; contradiction
  | iteF _ b₂ =>
  cases b₁ with | seq sa₁ sd₁ =>
  cases b₂ with | seq sa₂ sd₂ =>
  have es := (sample_ct _ _ _ _ _ _ ⟨⟨pubOf s₁, 0, (draw s₁).trace⟩,
    ⟨s₁, A₁, rfl, ⟨d₁, S₁⟩, checked_q hc₁, by rw [← draw_spl]⟩,
    s₂, A₂, e.symm, ⟨d₂, S₂⟩, checked_q hc₂, by rw [← draw_spl, htr]⟩ sa₁ sa₂).1
  obtain ⟨O₁, ax₁, _⟩ := post_of_exec (sample_ok A₁ S₁ (checked_q hc₁)) sa₁
  obtain ⟨O₂, ax₂, _⟩ := post_of_exec (sample_ok A₂ S₂ (checked_q hc₂)) sa₂
  rw [← draw_spl] at O₁ ax₁ O₂ ax₂
  have ed := sampled_ct F A₁ A₂ e hk hc₁ hc₂ hr (sample_status_eq e htr) O₁ O₂ ax₁ ax₂ sd₁ sd₂
  simp only [ep, ec, es, ed]
end VG.Proof.Dsa.X86.KeyRandom
