module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.State
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesCbc.AArch64.Encrypt.Load`, which only this module used -/

section

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
    exact ⟨dataR s₀,List.mem_append_right _ (by simp),by simpa only [BitVec.add_zero] using Offset.contains_base (Dp s₀) (d:=0) (n:=16) (k:=16*N s₀) (by omega_using [hk]) (by have := hp.data_wrap; omega_using [])⟩))
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

end

end


/-! Stream state between the early count update and the delayed store. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

structure Core (s₀ : State) (k j : Nat) (s : State) : Prop where
  env : Env s₀ s
  ptr : s.gpr .x2=blk s₀ k
  count : s.gpr .x3=BitVec.ofNat 64 (N s₀-j)
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀)

theorem Inv.core {s₀ s : State} {k : Nat} (h : Inv s₀ k s) : Core s₀ k k s :=
  ⟨h.env,h.ptr,h.count,h.data⟩

theorem Core.vframe {s₀ s t : State} {k j : Nat} {rs : List VReg}
    (h : Core s₀ k j s) (hf : VFrame rs s t) (hr : ∀ r ∈ rs,r ∈ live) : Core s₀ k j t :=
  ⟨h.env.vframe hf hr,by rw [hf.gpr]; exact h.ptr,by rw [hf.gpr]; exact h.count,by rw [hf.mem]; exact h.data⟩

theorem dec_ok {s₀ s : State} {k : Nat} (hk : k < N s₀) (h : Core s₀ k k s) :
    WP isa (.block [.subImm .x .x3 .x3 1]) s fun t => Core s₀ k (k+1) t ∧ t.v=s.v := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm:=1) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨h.env.transfer (fun _ _ => rfl) (gpr_write_of_ne _ _ _ (by decide)) (gpr_write_of_ne _ _ _ (by decide))
      (gpr_write_of_ne _ _ _ (by decide)) rfl rfl rfl,
    by simpa only [gpr_write_of_ne _ _ _ (by decide : Reg.x2≠.x3)] using h.ptr,?_,h.data⟩,rfl⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,ite_true,h.count]
  rw [Offset.ofNat_sub_ofNat (by omega_using [hk]),show N s₀-k-1=N s₀-(k+1) by omega_using []]

theorem first4_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀)
    (hi : Inv s₀ k s) :
    WP isa (.block (Impl.AesCbc.AArch64.Encrypt.first ++ ([.subImm .x .x3 .x3 1] : List Instr) ++
      Impl.AesCbc.AArch64.Encrypt.rounds 1 4)) s fun t =>
      Core s₀ k (k+1) t ∧ RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 5 t := by
  rw [List.append_assoc,WP.block_append_iff]
  have heq : s.v .v31 ^^^ s.v .v0=input s₀ k ^^^ s.v .v16 := by
    rw [hi.ready hk,hi.env.folded]
    unfold input
    rw [←hi.chain]
    have swap (a b c : BitVec 128) : a ^^^ (b ^^^ c)=b ^^^ (a ^^^ c) := by
      rw [←BitVec.xor_assoc,BitVec.xor_comm a b,BitVec.xor_assoc]
    simp only [BitVec.xor_comm,swap]
  refine WP.mono (first_ok hi.env.keys (input s₀ k) heq) fun s₁ ⟨i₁,f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dec_ok hk (hi.core.vframe f₁ (by decide))) fun s₂ ⟨c₂,v₂⟩ => ?_
  have i₂ : RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 1 s₂ := by rw [RInv,v₂]; exact i₁
  exact WP.mono (rounds_ok c₂.env.keys i₂ 4 (by have := hp.rounds; omega_using [this]))
    fun t ⟨it,ft⟩ => ⟨c₂.vframe ft (by decide),it⟩
end VG.Proof.AesCbc.AArch64.Encrypt
