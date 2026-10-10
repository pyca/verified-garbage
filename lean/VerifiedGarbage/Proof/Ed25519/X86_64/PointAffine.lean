import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Invert

/-! Normalization calls X25519's verified inversion, `vg_gf25519_r64_invert`: the proofs
are of the code with it inlined. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr E F DivstepInv)

variable {fld : Arith} [EdArith fld]

theorem invertWide_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa VG.Impl.X25519.X86_64.invertFn s fun t =>
      (∀ r, r ∉ Proof.X25519.X86_64.clob → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Proof.X25519.X86_64.Outside base 512 256 s.mem t.mem ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hg, hr, hw, hm, hv⟩ :=
    Proof.X25519.X86_64.invertFn_pow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hg, rfl, rfl, hm, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := by
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (pointAffine fld).inline s fun t => RbxKeep base s t ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  simp only [Code.inline, VG.Impl.X25519.X86_64.invertCall]
  refine WP.seq (WP.mono (invertWide_ok hs) fun t ⟨hg, hr, hw, hm, hv⟩ => ?_)
  have ht : Scratch t base := ⟨(hg _ (by decide) (by decide)).trans hs.rdi, hw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCodeWide_ok ht affineOps) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hg r hr hb), ku.rd.trans hr,
    ku.wr.trans hw, (hm.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv]
    have he : env t.mem base 0 = env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hm.fe (Or.inl (by decide)) (by decide)]
    rw [he]
  · rw [vu, (affine_eval _).2, hv]
    have he : env t.mem base 1 = env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hm.fe (Or.inl (by decide)) (by decide)]
    rw [he]

end VG.Proof.Ed25519.X86_64
