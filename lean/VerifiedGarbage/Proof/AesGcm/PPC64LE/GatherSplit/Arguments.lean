module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Tail
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: recover the first descriptor and restore the shared caller arguments.
/-! # Arguments for the split-seal call -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (GatherPre)


def firstArgsState (s : State) (S : Addr) : State :=
  (((s.write .r11 (s.gpr .r10 <<< 4)).write .r11 S).write .r9 (s.mem.readW S 64)).write .r10 (s.mem.readW (S+8) 64)


theorem firstArgs_ok {s : State} {S : Addr} {count : Nat}
    (hn : s.gpr .r7=S+BitVec.ofNat 64 (16*count))
    (hc : s.gpr .r10=BitVec.ofNat 64 count)
    (hr : InRegions (s.rd++s.wr) S 8)
    (hl : InRegions (s.rd++s.wr) (S+8) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.GatherSplit.firstArgs) s (· = firstArgsState s S) := by
  have ho : s.gpr .r10 <<< 4=BitVec.ofNat 64 (16*count) := by
    rw [hc,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 count*BitVec.ofNat 64 16=_
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  let a := s.write .r11 (s.gpr .r10 <<< 4)
  let b := a.write .r11 S
  let c := b.write .r9 (s.mem.readW S 64)
  have hb : exec (.sub .r11 .r7 .r11) a=some b := by
    rw [exec_sub]
    change some (a.write .r11 (s.gpr .r7-(s.gpr .r10 <<< 4)))=some b
    rw [hn,ho,BitVec.add_sub_cancel]
  have hload : exec (.load .d .r9 .r11 0) b=some c := by
    rw [exec_load_d (by decide) ⟨by decide,by decide⟩ (by simpa only [a,b,RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write_self,BitVec.add_zero] using hr)]
    simp only [b,RegUpd.gpr_write_self,BitVec.add_zero,RegUpd.mem_write]
    rfl
  rw [Impl.AesGcm.PPC64LE.GatherSplit.firstArgs]
  refine WP.block_cons_iff.mpr ⟨a,exec_lsl (sh := 4) (by decide),WP.block_cons_iff.mpr ⟨b,hb,
    WP.block_cons_iff.mpr ⟨c,hload,?_⟩⟩⟩
  change InRegions (s.rd++s.wr) (S+8#64) 8 at hl
  have hlast : exec (.load .d .r10 .r11 8) c=some (firstArgsState s S) := by
    rw [exec_load_d (by decide) ⟨by decide,by decide⟩ (by simpa only [a,b,c,RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using hl)]
    simp only [c,b,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,RegUpd.mem_write]
    rfl
  exact WP.block_cons_iff.mpr ⟨_,hlast,WP.block_nil rfl⟩


abbrev restoreRegs : List (Reg × Nat) :=
  [(.r3,104),(.r4,112),(.r5,120),(.r6,128),(.r7,136),(.r8,144)]


theorem restoreArgs_ok {s u : State} (hb : u.gpr .r12=Gather.Pf s)
    (hw : u.wr=Gather.FR s::s.wr) (hs : Gather.Slots s u.mem) :
    WP isa (.block (Impl.AesGcm.PPC64LE.SealGather.callArgs.take 6)) u
      (Spill.Restored s.gpr restoreRegs u) := by
  have saved : Spill.Saved (Gather.Pf s) s.gpr restoreRegs u.mem := by
    intro p hp
    simp only [restoreRegs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
    exacts [hs.c,hs.r,hs.n,hs.nl,hs.a,hs.al]
  have hin : ∀ p∈restoreRegs,
      InRegions (u.rd++u.wr) (Gather.Pf s+BitVec.ofNat 64 p.2) 8 := by
    intro p hp
    have bounds : 32≤p.2 ∧ p.2+8≤160 := by
      simp only [restoreRegs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨r,hr,hc⟩ := Gather.fr_in s bounds.1 bounds.2 s.wr
    exact ⟨r,List.mem_append_right _ (by rw [hw]; exact hr),hc⟩
  exact Spill.restore_wp (by decide) hb (by decide) (by decide) hin saved

end VG.Proof.AesGcm.PPC64LE.GatherSplit
