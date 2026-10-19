module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Link
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt)

theorem zero_no_link (sc : Reg) (st : Nat) :
    ∀i∈instrs (.block (zeroState sc st) : Prog isa),clobbers i .x30 = false := by
  simp only [zeroState,ptrTo]
  split <;> simp [instrs,clobbers, dstOf]

theorem zeroSave_ok {sc : Reg} {st wk rate : Nat} {s₀ : State}
    (hS : HSetup sc st wk rate s₀)
    (hoff : (wk+600)%8=0 ∧ wk+600<32768) :
    WP isa (.block (zeroState sc st ++ ([.str .x .x30 sc (wk+600)] : List Instr))) s₀ fun t=>
      Kept [STr sc st s₀,WKr sc wk s₀] s₀ t ∧
      stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=Spec.Sha3.zero ∧
      t.mem.readW (linkSlot sc wk s₀) 64=s₀.gpr .x30 := by
  rw [WP.block_append_iff]
  have hg : Rg s₀ s₀ := ⟨rfl,rfl,rfl,fun _ _ _=>rfl⟩
  refine WP.mono (Proof.Sha3.AArch64.WP.gprs (rs:=[.x30]) (hn:=.inl rfl) (zeroState_ok hS hg)
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact zero_no_link sc st)) fun s₁ ⟨⟨hk,hz⟩,hl⟩=>?_
  refine WP.mono (saveLink_ok hS hk.rg hoff) fun t ⟨kt,_,saved,hstate⟩=>?_
  exact ⟨(hk.mono (by simp)).trans (kt.mono (by simp)),hstate.trans hz,
    saved.trans (hl .x30 (List.mem_singleton_self _))⟩
end VG.Proof.MlKem.AArch64.FixedHash
