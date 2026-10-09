import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

structure Inv (s₀ : State) (v : Nat→Nat) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0=coeffAddr (s₀.gpr .x0) (4*i)
  x1 : s.gpr .x1=coeffAddr (s₀.gpr .x1) (4*i)
  x2 : s.gpr .x2=coeffAddr (s₀.gpr .x2) (4*i)
  consts : VConsts s
  keep : Keep [.x0,.x1,.x2,.x9,.x10,.x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀k<256,(coeffAt s.mem (s₀.gpr .x0) k).toNat=
    if k<4*i then v k else (coeffAt s₀.mem (s₀.gpr .x0) k).toNat

theorem inv_step {s₀ s t : State} {v : Nat→Nat} {i : Nat}
    (hi : i<64) (h : Inv s₀ v i s) {x : BitVec 128}
    (hm : t.mem=s.mem.write (s.gpr .x0) 16 x) (hx : Lanes x (fun e=>v (4*i+e)))
    (hc : VConsts t) (h0 : t.gpr .x0=s.gpr .x0+16)
    (h1 : t.gpr .x1=s.gpr .x1+16) (h2 : t.gpr .x2=s.gpr .x2+16)
    (hk : Keep [.x0,.x1,.x2,.x12] s t) : Inv s₀ v (i+1) t where
  x0 := by rw [h0,h.x0];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x0) (4*i) 4
  x1 := by rw [h1,h.x1];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x1) (4*i) 4
  x2 := by rw [h2,h.x2];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x2) (4*i) 4
  consts := hc
  keep := (h.keep.trans hk).mono
  frame := by
    rw [hm,h.x0]
    exact h.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega) _ hk]
    by_cases he : 4*i≤k ∧ k<4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega),ite_eq_left (by omega)]
      exact congrArg v (by omega)
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k<4*(i+1))=(k<4*i) := propext (by omega)
      simp only [hh]

theorem pro_ok (s₀ : State) (v : Nat→Nat) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.consts++([.movz .x .x12 64 0] : List Instr))) s₀
      fun s=>Inv s₀ v 0 s ∧ s.gpr .x12=BitVec.ofNat 64 64 := by
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun t ⟨hc,hm,hk⟩=>?_
  have scalar : WP isa (.block [.movz .x .x12 64 0]) t fun u=>
      u.gpr .x12=BitVec.ofNat 64 64 ∧ u.mem=t.mem ∧ u.v=t.v := by arun [State.write]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x12] scalar (by decide))
    fun u ⟨⟨h12,hum,huv⟩,ku⟩=>⟨?_,h12⟩
  have keep := hk.trans ku
  refine ⟨?_,?_,?_,?_,keep.mono,?_,?_⟩
  · rw [keep.get .x0];simp [coeffAddr]
  · rw [keep.get .x1];simp [coeffAddr]
  · rw [keep.get .x2];simp [coeffAddr]
  · exact ⟨by rw [huv];exact hc.q,by rw [huv];exact hc.qi⟩
  · rw [hum,hm];exact Frame.refl _ _
  · intro k _;rw [hum,hm];simp

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
