module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Core
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! Commit a ciphertext without disturbing the prepared successor. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

theorem Env.store {s₀ s t : State} (h : Env s₀ s) (hv : t.v=s.v) (hg : t.gpr=s.gpr)
    (hf : Frame [dataR s₀] s.mem t.mem) (hr : t.rd=s.rd) (hw : t.wr=s.wr) : Env s₀ t :=
  ⟨h.keys.of_v live_regs (fun _ _ => congrFun hv _) (congrFun hg _) (congrFun hg _),
    by rw [hv]; exact h.folded,by rw [hg]; exact h.iv,h.frame.trans hf,hr.trans h.rd,hw.trans h.wr⟩

def outState (s : State) : State := s.setV .v1 (s.v .v31 ^^^ s.v .v30)

theorem output_ok (s : State) :
    WP isa (.block [.vop (.logic .eor .v1 .v31 .v30)]) s fun t => t=outState s := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some]
  exact ⟨_,rfl,rfl⟩

theorem output_frame (s : State) : VFrame [.v1] s (outState s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun r hr => setV_v_of_ne _ _ (Ne.symm (fun h => hr (by simpa only [List.mem_singleton] using h.symm)))⟩

theorem store_advance_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀)
    (hc : Core s₀ k (k+1) s) (hval : st (s.v .v31 ^^^ s.v .v30)=output s₀ k)
    (hn : k+1 < N s₀ → s.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ s.v .v7) :
    WP isa (.block [.vop (.logic .eor .v1 .v31 .v30),.strq .v1 .x2 0,.addImm .x .x2 .x2 16])
      s (Inv s₀ (k+1)) := by
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (output_ok s) fun t ht => ?_
  subst ht
  let u := outState s
  have fu := output_frame s
  have cu := hc.vframe fu (by decide)
  have hv : ∀ j (hj : j < ([VReg.v1] : List VReg).length), ∀ i < 16,
      vbyte (u.v ([VReg.v1][j])) i=(output s₀ (k+0+j)).getD i 0 := by
    intro j hj i hi
    have hj0 : j=0 := by simpa using (Nat.eq_zero_of_le_zero (by simpa using hj))
    subst hj0
    have hh := congrArg (fun x : Spec.Aes.State => x.getD i 0) hval
    simpa only [Nat.add_zero,List.getElem_cons_zero,u,outState,setV_v_self,getD_st _ hi] using hh
  change WP isa (.block (VG.Impl.Aes.AArch64.Aese.stData [.v1] 0 ++ [.addImm .x .x2 .x2 16])) u _
  rw [WP.block_append_iff]
  refine WP.mono (stData_ok (m₀:=s₀.mem) (n:=N s₀) (c:=k) (F:=output s₀)
    (by have := hp.data_wrap; omega) [.v1] 0 u cu.ptr (by decide) (by simp only [List.length_singleton,Nat.add_zero]; omega)
    (by rw [cu.env.wr,hp.wr]; simp) (by simpa using cu.data) hv)
    fun v ⟨hd,hf,hg,hv,_,hr,hw⟩ => ?_
  have ev := cu.env.store hv hg hf hr hw
  have hch : v.v .v31 ^^^ v.v .v30=chain s₀ (k+1) := by
    rw [hv,fu.v _ (by decide),fu.v _ (by decide),chain_succ]
    exact value_pack hval
  have hn' : k+1 < N s₀ → v.v .v0=s₀.mem.readW (blk s₀ (k+1)) 128 ^^^ v.v .v7 := by
    rw [hv,fu.v _ (by decide),fu.v _ (by decide)]
    exact hn
  have pv := (congrFun hg .x2).trans cu.ptr
  have cv := (congrFun hg .x3).trans cu.count
  rw [WP.block_cons_iff]
  refine ⟨_,exec_addImm_x (imm:=16) (by decide),WP.block_nil ?_⟩
  refine ⟨by omega,ev.transfer (fun _ _ => rfl) (gpr_write_of_ne _ _ _ (by decide)) (gpr_write_of_ne _ _ _ (by decide))
    (gpr_write_of_ne _ _ _ (by decide)) rfl rfl rfl,
    ?_,?_,hch,by change EcbInv s₀.mem v.mem (Dp s₀) (N s₀) (k+1) (output s₀); exact hd,hn'⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,ite_true,pv]
    change (Dp s₀+BitVec.ofNat 64 (16*k))+BitVec.ofNat 64 16=Dp s₀+BitVec.ofNat 64 (16*(k+1))
    exact Offset.add_add_eq (Dp s₀) (by omega)
  · exact (gpr_write_of_ne _ _ _ (by decide : Reg.x3≠.x2)).trans cv
end VG.Proof.AesCbc.AArch64.Encrypt
