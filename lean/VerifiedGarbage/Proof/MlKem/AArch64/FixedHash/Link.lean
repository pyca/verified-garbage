module
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt)

abbrev linkSlot (sc : Reg) (wk : Nat) (s₀ : State) : Addr :=
  s₀.gpr sc + BitVec.ofNat 64 wk + 600

theorem link_covers {sc : Reg} {st wk rate : Nat} {s₀ s : State}
    (hS : HSetup sc st wk rate s₀) (hg : Rg s₀ s) :
    InRegions s.wr (linkSlot sc wk s₀) 8 := by
  rw [hg.wr]
  exact Covers.tail hS.cov _ _ ⟨_,List.mem_singleton_self _,
    Offset.contains_base _ (d:=600) (by decide) (by decide)⟩

theorem saveLink_ok {sc : Reg} {st wk rate : Nat} {s₀ s : State}
    (hS : HSetup sc st wk rate s₀) (hg : Rg s₀ s)
    (hoff : (wk+600)%8=0 ∧ wk+600<32768) :
    WP isa (.block [.str .x .x30 sc (wk+600)]) s fun t=>
      Kept [WKr sc wk s₀] s t ∧ t.gpr=s.gpr ∧
      t.mem.readW (linkSlot sc wk s₀) 64=s.gpr .x30 ∧
      stateAt t.mem (s₀.gpr sc+BitVec.ofNat 64 st)=
        stateAt s.mem (s₀.gpr sc+BitVec.ofNat 64 st) := by
  have addr : s.gpr sc+BitVec.ofNat 64 (wk+600)=linkSlot sc wk s₀ := by
    rw [hg.cs sc hS.hsc.1 hS.hsc.2,BitVec.ofNat_add,← BitVec.add_assoc]
    rfl
  refine wp_strx hoff addr (link_covers hS hg) fun t ht=>wp_nil ?_
  have fr : Frame [WKr sc wk s₀] s.mem t.mem := by
    rw [ht.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d:=600) (by decide) (by decide))
  refine ⟨⟨fun r _ _=>congrFun ht.gpr r,ht.sp,ht.rd,ht.wr,fr,ht.vcs⟩,
    ht.gpr,?_,?_⟩
  · rw [ht.mem]; exact Mem.readW_writeW_self64 _ _ _
  · apply Proof.Sha3.stateAt_congr
    intro i hi
    apply fr
    intro r hr hc
    rw [List.mem_singleton.mp hr] at hc
    exact hS.d _ (contains_off (by omega) (by decide)) hc

theorem restoreLink_ok {sc : Reg} {st wk rate : Nat} {s₀ s : State}
    (hS : HSetup sc st wk rate s₀) (hg : Rg s₀ s)
    (hoff : (wk+600)%8=0 ∧ wk+600<32768) :
    WP isa (.block [.ldr .x .x30 sc (wk+600)]) s fun t=>
      Kept [] s t ∧ t.mem=s.mem ∧
      t.gpr .x30=s.mem.readW (linkSlot sc wk s₀) 64 := by
  have addr : s.gpr sc+BitVec.ofNat 64 (wk+600)=linkSlot sc wk s₀ := by
    rw [hg.cs sc hS.hsc.1 hS.hsc.2,BitVec.ofNat_add,← BitVec.add_assoc]
    rfl
  have hin : InRegions (s.rd++s.wr) (linkSlot sc wk s₀) 8 := in_rd_wr (link_covers hS hg)
  refine wp_ldrx hoff addr hin fun t ht et=>wp_nil ?_
  exact ⟨⟨fun r _ hn=>ht.get r (by simpa using hn),ht.sp,ht.rd,ht.wr,by rw [ht.mem]; exact Frame.refl _ _,ht.keep.vcs⟩,ht.mem,et⟩

end VG.Proof.MlKem.AArch64.FixedHash
