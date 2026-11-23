module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Impl.AesGcm.X86.DirectGather (loopSetup tagSetup)

abbrev slotSetupFrame (W : BitVec 32) (o q : Nat) (Z : Addr) : List Region :=
  [⟨w64 W+BitVec.ofNat 64 o,4⟩,⟨w64 W+BitVec.ofNat 64 q,4⟩,⟨Z,4⟩]

structure SetupPost (s : State) (W sp : BitVec 32) (i j o q : Nat) (Z : Addr) (t : State) : Prop where
  first : slotv t.mem W o = s.mem.readW (argA sp i) 32
  second : slotv t.mem W q = s.mem.readW (argA sp j) 32
  zero : t.mem.readW Z 32 = 0
  frame : Frame (slotSetupFrame W o q Z) s.mem t.mem
  regs : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

private theorem setup_ok {s : State} {W sp : BitVec 32} (h : KeepEnv W sp 12 s)
    (i j o q : Nat) (r : Reg) (d : Nat) (Z : Addr)
    (hi : i<12) (hj : j<12) (ho : o+4≤2560) (hq : q+4≤2560)
    (mo : o%4=0) (mq : q%4=0) (ne : o ≠ q) (hr : r ≠ .eax)
    (hz : addr (s.gpr r) d = Z) (perm : InRegions s.wr Z 4)
    (sep1 : Mem.Sep (w64 W+BitVec.ofNat 64 o) 4 Z 4)
    (sep2 : Mem.Sep (w64 W+BitVec.ofNat 64 q) 4 Z 4) :
    WP isa (.block (keep i o ++ keep j q ++ ([.mov .eax (imm 0),.store (at_ r d) .eax] : List Instr))) s
      (SetupPost s W sp i j o q Z) := by
  let ps : List (Nat × Nat) := [(i,o),(j,q)]
  obtain ⟨u,run,slots,fr,regs,rd,wr⟩ := keeps_ok ps (by
    intro a ha; simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨hi,ho,mo⟩
    · exact ⟨hj,hq,mq⟩) (by simpa [ps] using ne) h
  have keep : runBlock isa (keep i o ++ keep j q) s = some u := by simpa [ps] using run
  have zero : ∃ t, runBlock isa [.mov .eax (imm 0),.store (at_ r d) .eax] u = some t ∧
      t.mem=u.mem.writeW Z (0#32) ∧ (∀ a, a≠.eax → t.gpr a=u.gpr a) ∧ t.rd=u.rd ∧ t.wr=u.wr := by
    have az : w64 (u.gpr r+BitVec.ofNat 32 d)=Z := (congrArg (fun v => addr v d) (regs r hr)).trans hz
    refine ⟨setMem (u.setReg .eax 0) (u.mem.writeW Z (0#32)),by xrun [hr,az,wr,perm],rfl,?_,rfl,rfl⟩
    intro a ha; exact gpr_setReg_of_ne _ _ ha
  obtain ⟨t,fin,mem,regs',rd',wr'⟩ := zero
  apply WP.of_runBlock
  refine ⟨t,runBlock_app_of keep fin,?_,?_,?_,?_,fun a ha => (regs' a ha).trans (regs a ha),rd'.trans rd,wr'.trans wr⟩
  · rw [slotv_eq,mem,Mem.readW_writeW_sep sep1 (by decide)]
    exact slots (i,o) (by simp [ps])
  · rw [slotv_eq,mem,Mem.readW_writeW_sep sep2 (by decide)]
    exact slots (j,q) (by simp [ps])
  · rw [mem,Mem.readW_writeW_self32]; rfl
  · rw [mem]
    apply Frame.writeW _ (by simp [slotSetupFrame]) _ (Region.contains_self Z 4)
    exact fr.mono (by simp [ps,slotSetupFrame,keepR])

theorem loopSetup_ok {s : State} {W sp : BitVec 32} (h : KeepEnv W sp 12 s) :
    WP isa (.block loopSetup) s (SetupPost s W sp 9 10 rO tglO (w64 W+BitVec.ofNat 64 xlO)) :=
  setup_ok h 9 10 rO tglO .ebp xlO _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [h.ebp]; exact addr_eq (by change W.toNat+160<2^32; omega_using [h.fw]))
    (in_off h.wW (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))

theorem tagSetup_ok {s : State} {W sp : BitVec 32} (h : KeepEnv W sp 12 s)
    (perm : InRegions s.wr (w64 sp) 4) (sep : (⟨w64 sp,4⟩ : Region).Disjoint ⟨w64 W,2560⟩) :
    WP isa (.block tagSetup) s (SetupPost s W sp 6 7 dataO lenO (w64 sp)) :=
  setup_ok h 6 7 dataO lenO .esp 0 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [addr,h.esp]) perm
    ((sep.sub_right (Lay.wSub (d:=dataO) (n:=4) (by decide))).symm)
    ((sep.sub_right (Lay.wSub (d:=lenO) (n:=4) (by decide))).symm)

end VG.Proof.AesGcm.X86.DirectGather
end
