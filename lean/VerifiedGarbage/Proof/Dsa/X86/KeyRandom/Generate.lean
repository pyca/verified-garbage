module

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sample
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sampled

/-! # Prepare and sample a private scalar after accepting the domain -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem generate_ok (F : DeriveFn) {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t)
    (hc : checked s₀ = true) (saved : Saved s₀ t.mem) (used : slot t.mem (rBase s₀) oUsed = 0) :
    WP isa (generate F.name F.code) t (Fin s₀) := by
  have hq := checked_q hc
  have hql := rQBytes_le A
  have hfit := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold generate
  refine WP.seq (WP.mono (prepare_ok A h) fun u ⟨ax, P, hu, ou, _⟩ => ?_)
  have low : ∀ d, d + 4 ≤ oQ → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low ou (by decide) hd (by unfold oQ at hd; omega)
  refine WP.seq (wp_cmpi fun v fv _ z => WP.block_nil ?_)
  have hv := hu.fupd fv
  have savedV : Saved s₀ v.mem := by
    rw [fv.mem]; exact saved.of_slots fun d _ hd => low d (by unfold oQ; omega)
  have usedV : slot v.mem (rBase s₀) oUsed = 0 := by rw [fv.mem, low _ (by decide)]; exact used
  have prepared := P hq
  rw [ax] at z
  change 1 < Spec.Dsa.decodeBE (rQBytes s₀) at hq
  simp only [hq, ite_true] at z
  refine WP.ite false (by simp only [eval, z]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
  have initial : Smp s₀ 0 (slot v.mem (rBase s₀) oDraws).toNat v := by
    refine ⟨hv, by rw [fv.mem]; exact prepared.q, by rw [fv.mem]; exact prepared.width,
      by rw [fv.mem]; exact prepared.mask, usedV, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun i hi => by rw [fv.mem]; exact prepared.nonce i (by omega), Nat.zero_le _⟩
  refine WP.seq (WP.mono (sample_ok A initial hq) fun w ⟨O, eax, _, ow, _⟩ => ?_)
  rw [← draw_spl] at O eax
  exact sampled_ok F A hc O (savedV.of_slots fun d _ hd => outs_low ow (by decide) hd (by omega)) eax

end VG.Proof.Dsa.X86.KeyRandom
