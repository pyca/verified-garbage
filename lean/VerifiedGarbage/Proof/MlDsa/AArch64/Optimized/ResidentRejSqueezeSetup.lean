import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_mov wp_addImm wp_movz)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Four (squeezeSetup)

theorem squeezePointers_ok (s : State) : WP isa (.block ((squeezeSetup 0 0).take 6)) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27] s t ∧ t.gpr .x22 = s.gpr .x19 ∧
      t.gpr .x23 = s.gpr .x19+BitVec.ofNat 64 400 ∧
      (∀ k < 4,t.gpr (bReg k) = s.gpr .x19+BitVec.ofNat 64 (oBuf+1008*k)) := by
  change WP isa (.block [_,_,_,_,_,_]) s _
  refine wp_mov fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun t h6 e6 =>
        WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).mono (by simp)
  · rw [h6.get .x22,h5.get .x22,h4.get .x22,h3.get .x22,h2.get .x22,e1]
  · rw [h6.get .x23,h5.get .x23,h4.get .x23,h3.get .x23,e2,h1.get .x19]
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = _
      rw [h6.get .x24,h5.get .x24,h4.get .x24,e3,h2.get .x19,h1.get .x19]
    · change t.gpr .x25 = _
      rw [h6.get .x25,h5.get .x25,e4,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x26 = _
      rw [h6.get .x26,e5,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x27 = _
      rw [e6,h5.get .x19,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]

theorem squeezeSetupZero_ok (n : Nat) (hn : n<65536) (s : State) : WP isa (.block (squeezeSetup 0 n)) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧ t.gpr .x22 = s.gpr .x19 ∧
      t.gpr .x23 = s.gpr .x19+BitVec.ofNat 64 400 ∧
      (∀ k < 4,t.gpr (bReg k) = s.gpr .x19+BitVec.ofNat 64 (oBuf+1008*k)) ∧ t.gpr .x28 = BitVec.ofNat 64 n := by
  simp only [squeezeSetup,BEq.rfl,ite_true,List.append_nil]
  change WP isa (.block [_,_,_,_,_,_,_]) s _
  refine wp_mov fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
        wp_movz fun t h7 e7 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_,?_⟩
  · exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).mono (by simp)
  · rw [h7.get .x22,h6.get .x22,h5.get .x22,h4.get .x22,h3.get .x22,h2.get .x22,e1]
  · rw [h7.get .x23,h6.get .x23,h5.get .x23,h4.get .x23,h3.get .x23,e2,h1.get .x19]
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = _
      rw [h7.get .x24,h6.get .x24,h5.get .x24,h4.get .x24,e3,h2.get .x19,h1.get .x19]
    · change t.gpr .x25 = _
      rw [h7.get .x25,h6.get .x25,h5.get .x25,e4,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x26 = _
      rw [h7.get .x26,h6.get .x26,e5,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x27 = _
      rw [h7.get .x27,e6,h5.get .x19,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
  · rw [e7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.natCast_eq_ofNat,BitVec.toNat_ofNat]
    omega

theorem squeezeSetupZero_env {v : Nat} {σ s : State} (he : Env v σ s) :
    WP isa (.block (squeezeSetup 0 5)) s fun t => Env v σ t ∧
      t.mem=s.mem ∧ t.gpr .x22=stateP σ 0 ∧ t.gpr .x23=stateP σ 1 ∧
      (∀k<4,t.gpr (bReg k)=bufP σ k) := by
  refine WP.mono (squeezeSetupZero_ok 5 (by decide) s)
    fun t ⟨ht,h22,h23,hbuf,_⟩ => ?_
  refine ⟨he.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),ht.mem,?_,?_,?_⟩
  · rw [h22,he.x19]
    change scr σ=scr σ+BitVec.ofNat 64 0
    simp
  · rw [h23,he.x19]; rfl
  · intro k hk
    rw [hbuf k hk,he.x19]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
