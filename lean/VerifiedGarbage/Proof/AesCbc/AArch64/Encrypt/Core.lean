module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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
  rw [Offset.ofNat_sub_ofNat (by omega),show N s₀-k-1=N s₀-(k+1) by omega]

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
  exact WP.mono (rounds_ok c₂.env.keys i₂ 4 (by have := hp.rounds; omega))
    fun t ⟨it,ft⟩ => ⟨c₂.vframe ft (by decide),it⟩
end VG.Proof.AesCbc.AArch64.Encrypt
