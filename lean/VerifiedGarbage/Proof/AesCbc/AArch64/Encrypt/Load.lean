module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.State
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Read-only lookahead and fixed entry padding. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

def loaded (s : State) (off : Nat) : State :=
  s.setV .v0 (s.mem.readW (s.gpr .x2+BitVec.ofNat 64 off) 128 ^^^ s.v .v7)

theorem load_ok (s : State) (off : Nat) (ho : off%16=0 ∧ off<65536)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.block [.ldrq .v0 .x2 off,.vop (.logic .eor .v0 .v0 .v7)]) s fun t =>
      t=loaded s off := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrq ho ha,?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some,
    setV_v_self,setV_v_of_ne _ _ (by decide : VReg.v7≠.v0)]
  exact ⟨_,rfl,by rw [setV_setV]; rfl⟩

theorem loaded_frame (s : State) (off : Nat) : VFrame [.v0] s (loaded s off) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  exact setV_v_of_ne _ _ (Ne.symm (fun h => hr (by simpa only [List.mem_singleton] using h.symm)))

theorem padding_ok (s : State) (n : Nat) :
    WP isa (.block (List.replicate n (Instr.movz .x .x12 0 0))) s fun t =>
      t.mem=s.mem ∧ t.v=s.v ∧ (∀ r,r≠.x12 → t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨rfl,rfl,fun _ _ => rfl,rfl,rfl⟩
  | succ n ih =>
    rw [List.replicate_succ,WP.block_cons_iff]
    have he : exec (.movz .x .x12 0 0) s=some (s.write .x .x12 0) := by
      simp only [exec,show 16*0 < Size.x.bits by decide,ite_true]
      rfl
    refine ⟨_,he,WP.mono (ih (s.write .x .x12 0)) fun t ⟨hm,hv,hg,hr,hw⟩ => ?_⟩
    exact ⟨hm,hv,fun r hr => (hg r hr).trans (gpr_write_of_ne _ _ _ hr),hr,hw⟩

theorem entry_ok {s₀ s : State} (hp : UPre s₀) (hk : 0 < N s₀)
    (hE : Env s₀ s) (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4)
    (hch : s.v .v31 ^^^ s.v .v30=chain s₀ 0) (hm : s.mem=s₀.mem) :
    WP isa (.block (Impl.AesCbc.AArch64.Encrypt.enter (R s₀))) s (Inv s₀ 0) := by
  rw [Impl.AesCbc.AArch64.Encrypt.enter]
  rw [show ([Instr.ldrq .v0 .x2 0,.vop (.logic .eor .v0 .v0 .v7),.align 5] : List Instr)=
    [.ldrq .v0 .x2 0,.vop (.logic .eor .v0 .v0 .v7)]++[.align 5] from rfl,
    List.append_assoc,WP.block_append_iff]
  refine WP.mono (load_ok s 0 (by decide) (by
    rw [h2,BitVec.add_zero,hE.wr,hp.wr]
    exact ⟨dataR s₀,List.mem_append_right _ (by simp),by simpa only [BitVec.add_zero] using Offset.contains_base (Dp s₀) (d:=0) (n:=16) (k:=16*N s₀) (by omega) (by have := hp.data_wrap; omega)⟩))
    fun t ht => ?_
  subst ht
  simp only [List.singleton_append]
  rw [WP.block_cons_iff]
  refine ⟨_,rfl,WP.mono (padding_ok _ _) fun u ⟨um,uv,ug,ur,uw⟩ => ?_⟩
  have lf := loaded_frame s 0
  have E₁ := hE.vframe lf (by decide)
  have E₂ := E₁.transfer (fun _ _ => congrFun uv _) (ug _ (by decide)) (ug _ (by decide))
    (ug _ (by decide)) um ur uw
  refine ⟨Nat.zero_le _,E₂,?_,?_,?_,?_,?_⟩
  · exact (ug _ (by decide)).trans (by simpa only [loaded,State.setV,blk,Nat.mul_zero,BitVec.add_zero] using h2)
  · rw [ug _ (by decide)]
    exact (by simpa only [loaded,State.setV,Nat.sub_zero] using h3.trans (x4_ofNat s₀))
  · rw [uv]; exact hch
  · intro i hi; rw [um]; change s.mem _=_; rw [hm]; rfl
  · intro _
    rw [uv]
    simp only [loaded,State.setV,reduceCtorEq,ite_true,ite_false,
      blk,Nat.mul_zero,BitVec.add_zero,h2,hm]
end VG.Proof.AesCbc.AArch64.Encrypt
