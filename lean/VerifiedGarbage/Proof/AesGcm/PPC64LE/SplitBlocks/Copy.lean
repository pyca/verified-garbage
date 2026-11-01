module

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
public import VerifiedGarbage.Proof.Aes.Memory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Value
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: isolate vector-copy execution from the wrapper's call composition.
/-! # Copy the external prefix remaining before the GCM block tail -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks.Copy
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks (U)
open VG.Proof.Aes.PPC64LE.Crypto (Local)

def registers : List Reg := [.r0,.r11,.r17,.r19]

def value (base : State) (i : Nat) : Spec.Aes.State :=
  Spec.Aes.stateAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))

structure Config (base : State) (total count : Nat) : Prop where
  bound : count≤total
  size : 16*total≤2^64
  left : base.gpr .r19=BitVec.ofNat 64 count
  reads : ∀ i<count, InRegions (base.rd++base.wr) (base.gpr .r17+BitVec.ofNat 64 (16*i)) 16
  writes : ∀ i<count, InRegions base.wr (base.gpr .r30+BitVec.ofNat 64 (16*i)) 16
  disjoint : (⟨base.gpr .r17,16*count⟩ : Region).Disjoint ⟨base.gpr .r30,16*total⟩

structure Inv (base : State) (total count k : Nat) (s : State) : Prop where
  bound : k≤count
  keep : Keep registers base s
  vectors : ∀ r, r≠U → s.vpr r=base.vpr r
  zero : s.gpr .r0=0
  source : s.gpr .r17=base.gpr .r17+BitVec.ofNat 64 (16*k)
  dest : s.gpr .r11=base.gpr .r30+BitVec.ofNat 64 (16*k)
  left : s.gpr .r19=BitVec.ofNat 64 (count-k)
  processed : VG.Proof.Aes.Memory.Processed base.mem s.mem (base.gpr .r30) total k (value base)
  frame : Frame [⟨base.gpr .r30,16*total⟩] base.mem s.mem

structure Result (base : State) (total count : Nat) (s : State) : Prop where
  keep : Keep registers base s
  vectors : ∀ r, r≠U → s.vpr r=base.vpr r
  source : s.gpr .r17=base.gpr .r17+BitVec.ofNat 64 (16*count)
  left : s.gpr .r19=0
  processed : VG.Proof.Aes.Memory.Processed base.mem s.mem (base.gpr .r30) total count (value base)
  frame : Frame [⟨base.gpr .r30,16*total⟩] base.mem s.mem

structure StepResult (base s : State) : Prop where
  keep : Keep [.r11,.r17,.r19] base s
  vectors : ∀ r, r≠U → s.vpr r=base.vpr r
  mem : s.mem=base.mem.write (base.gpr .r11) 16 (base.mem.read (base.gpr .r17) 16)
  source : s.gpr .r17=base.gpr .r17+16
  dest : s.gpr .r11=base.gpr .r11+16
  left : s.gpr .r19=base.gpr .r19-1

theorem advance_ok (s : State) :
    WP isa (.block ([.addi .r17 .r17 16,.addi .r11 .r11 16,.subi .r19 .r19 1] : List Instr)) s
      (· = ((s.write .r17 (s.gpr .r17+16)).write .r11 (s.gpr .r11+16)).write .r19 (s.gpr .r19-1)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,
    exec_addi (n := .r17) (imm := 16) (by decide) (by decide),
    exec_addi (n := .r11) (imm := 16) (by decide) (by decide),
    exec_subi (n := .r19) (imm := 1) (by decide) (by decide),RegUpd.gpr_write,
    reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl

theorem step_ok (s : State) (hz : s.gpr .r0=0)
    (hr : InRegions (s.rd++s.wr) (s.gpr .r17) 16) (hw : InRegions s.wr (s.gpr .r11) 16) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.copyStep) s (StepResult s) := by
  change WP isa (.block (([.lxvd2x U .r17 .r0] : List Instr)++
    ([.stxvd2x U .r11 .r0] : List Instr)++
    [.addi .r17 .r17 16,.addi .r11 .r11 16,.subi .r19 .r19 1])) s _
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (Blocks.rawLoad_ok U .r17 .r0 s (by decide) (by simpa only [hz,show (0 : BitVec 64)=0#64 from rfl,BitVec.add_zero] using hr))
    fun u ⟨hu,hf⟩ => ?_
  have hwu : InRegions u.wr (u.gpr .r11+u.gpr .r0) 16 := by
    simpa only [hf.wr,hf.gpr,hz,show (0 : BitVec 64)=0#64 from rfl,BitVec.add_zero] using hw
  refine WP.mono (Blocks.rawStore_ok U .r11 .r0 u (by decide) hwu) fun v hv => ?_
  subst v
  refine WP.mono (advance_ok _) fun t ht => ?_
  subst t
  have hk := ((Local.write {u with mem := u.mem.write (u.gpr .r11+u.gpr .r0) 16 (swapDwords (u.vpr U))}
      .r17 (u.gpr .r17+16)).trans (Local.write _ .r11 (u.gpr .r11+16))).trans
      (Local.write _ .r19 (u.gpr .r19-1))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · refine ⟨fun r hr => ?_,?_,?_⟩
    · exact (hk.keep.gpr (by simpa only [List.mem_append,List.mem_cons,List.mem_singleton,
        List.not_mem_nil,or_false,not_or,and_assoc,and_comm,and_left_comm] using hr)).trans (congrFun hf.gpr r)
    · simpa only [RegUpd.rd_write] using hf.rd
    · simpa only [RegUpd.wr_write] using hf.wr
  · intro r hr
    simpa only [vpr_write] using hf.v r (by simpa only [List.mem_singleton] using hr)
  · simp only [RegUpd.mem_write,hf.mem,hf.gpr,hu,hz,show (0 : BitVec 64)=0#64 from rfl,BitVec.add_zero,swapDwords_involutive]
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hf.gpr]
  · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hf.gpr]
  · simp only [RegUpd.gpr_write_self,hf.gpr]

theorem inv_step {base : State} {total count k : Nat} (cfg : Config base total count)
    (hk : k<count) {s : State} (hs : Inv base total count k s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.copyStep) s (Inv base total count (k+1)) := by
  have hr : InRegions (s.rd++s.wr) (s.gpr .r17) 16 := by
    rw [hs.keep.2.1,hs.keep.2.2,hs.source]; exact cfg.reads k hk
  have hw : InRegions s.wr (s.gpr .r11) 16 := by
    rw [hs.keep.2.2,hs.dest]; exact cfg.writes k hk
  have hread : s.mem.read (base.gpr .r17+BitVec.ofNat 64 (16*k)) 16=
      base.mem.read (base.gpr .r17+BitVec.ofNat 64 (16*k)) 16 :=
    hs.frame.read (r := ⟨base.gpr .r17,16*count⟩)
      (Offset.contains_base _ (d := 16*k) (n := 16) (k := 16*count) (by omega)
        (by have := cfg.bound; have := cfg.size; omega))
      (by simpa only [List.mem_singleton,forall_eq] using cfg.disjoint) (by decide)
  have hp := hs.processed.store cfg.size (show k<total by have := cfg.bound; omega)
    (v := base.mem.read (base.gpr .r17+BitVec.ofNat 64 (16*k)) 16) (by
      intro i hi
      change VG.VectorCrypto.vbyte (base.mem.read _ 16) i=(value base k).getD i 0
      rw [← VG.Proof.Aes.Vector.getD_st _ hi,VG.Proof.Aes.PPC64LE.Crypto.stateAt_read16]
      rfl)
  refine WP.mono (step_ok s hs.zero hr hw) fun t ht => ?_
  refine ⟨by omega,(hs.keep.trans ht.keep).mono (by simp [registers]),
    fun r hr => (ht.vectors r hr).trans (hs.vectors r hr),
    (ht.keep.gpr (by decide)).trans hs.zero,?_,?_,?_,?_,?_⟩
  · rw [ht.source,hs.source]
    change base.gpr .r17+BitVec.ofNat 64 (16*k)+BitVec.ofNat 64 16=_
    rw [Offset.add_add]
    exact congrArg (fun j => base.gpr .r17+BitVec.ofNat 64 j) (by omega)
  · rw [ht.dest,hs.dest]
    change base.gpr .r30+BitVec.ofNat 64 (16*k)+BitVec.ofNat 64 16=_
    rw [Offset.add_add]
    exact congrArg (fun j => base.gpr .r30+BitVec.ofNat 64 j) (by omega)
  · rw [ht.left,hs.left]
    change BitVec.ofNat 64 (count-k)-BitVec.ofNat 64 1=_
    rw [Offset.ofNat_sub_ofNat (show 1≤count-k by omega),Nat.sub_sub]
  · rw [ht.mem,hs.source,hs.dest,hread]; exact hp.1
  · rw [ht.mem,hs.source,hs.dest,hread]; exact hs.frame.trans hp.2


theorem loop_ok {base s : State} {total count k : Nat} (cfg : Config base total count)
    (hk : k<count) (hs : Inv base total count k s) :
    WP isa (.loop (.block Impl.AesGcm.PPC64LE.SplitBlocks.copyStep) (.nonzero .d .r19)) s
      (Inv base total count count) := by
  refine WP.loop (M := isa)
    (fun m t => ∃ j, m=count-j ∧ j<count ∧ Inv base total count j t)
    (fun m t ht => ?_) (count-k) s ⟨k,rfl,hk,hs⟩
  obtain ⟨j,rfl,hj,ht⟩ := ht
  refine WP.mono (inv_step cfg hj ht) fun u hu => ?_
  have hev : eval (.nonzero .d .r19) u=some (u.gpr .r19 != 0) := by
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq]
  by_cases he : j+1=count
  · left
    refine ⟨?_,he ▸ hu⟩
    rw [hu.left,he,Nat.sub_self] at hev
    exact hev.trans (by decide)
  · right
    have hne : u.gpr .r19 ≠ 0 := by
      intro hz
      have hh := congrArg BitVec.toNat hz
      rw [hu.left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := cfg.bound; have := cfg.size; omega)] at hh
      exact he (by change count-(j+1)=0 at hh; omega)
    exact ⟨hev.trans (by simpa using hne),count-(j+1),by omega,j+1,rfl,by omega,hu⟩


def initialState (base : State) : State := (base.write .r11 (base.gpr .r30)).write .r0 0

theorem initial_ok (base : State) :
    WP isa (.block [Impl.Aes.PPC64LE.Crypto.mov .r11 .r30,.li .r0 0]) base (· = initialState base) := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.mov,runBlock_cons,runStep_some,runBlock_nil,
    exec_logic,BitVec.or_self,exec_li (imm := 0) (by decide),Option.some.injEq,exists_eq_left']
  rfl

theorem initial_inv {base : State} {total count : Nat} (cfg : Config base total count) :
    Inv base total count 0 (initialState base) := by
  refine ⟨by omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ((Local.write base .r11 _).trans (Local.write _ .r0 _)).keep.mono (by simp [registers])
  · intro r _; simp only [initialState,vpr_write]
  · exact RegUpd.gpr_write_self ..
  · simp only [initialState,RegUpd.gpr_write,reduceCtorEq,ite_false,Nat.mul_zero,
      BitVec.add_zero]
  · simp only [initialState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false,Nat.mul_zero,
      BitVec.add_zero]
  · simpa only [initialState,RegUpd.gpr_write,reduceCtorEq,ite_false,Nat.sub_zero] using cfg.left
  · simpa only [initialState,RegUpd.mem_write] using VG.Proof.Aes.Memory.Processed.refl base.mem (base.gpr .r30) total (value base)
  · simpa only [initialState,RegUpd.mem_write] using Frame.refl [⟨base.gpr .r30,16*total⟩] base.mem


theorem ok (base : State) (total count : Nat) (cfg : Config base total count) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.copyPrefix base (Result base total count) := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.copyPrefix]
  by_cases hz : count=0
  · subst count
    refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,cfg.left]; rfl)
      (fun _ => ?_) (by simp)
    refine WP.block_nil ⟨Keep.refl _ _,fun _ _ => rfl,?_,cfg.left,?_,Frame.refl _ _⟩
    · simp only [Nat.mul_zero,BitVec.add_zero]
    · exact VG.Proof.Aes.Memory.Processed.refl _ _ _ _
  · refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · have hne : base.gpr .r19≠0 := by
        intro he
        have hh := congrArg BitVec.toNat (cfg.left.symm.trans he)
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := cfg.bound; have := cfg.size; omega)] at hh
        exact hz hh
      simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
        Option.some.injEq,beq_eq_false_iff_ne] using hne
    · apply WP.seq
      refine WP.mono (initial_ok base) fun s hs => ?_
      subst s
      refine WP.mono (loop_ok cfg (by omega) (initial_inv cfg)) fun t ht => ?_
      exact ⟨ht.keep,ht.vectors,ht.source,ht.left.trans (by rw [Nat.sub_self]; rfl),
        ht.processed,ht.frame⟩



theorem Result.blockAt {base s : State} {total count i : Nat} (hs : Result base total count s)
    (hc : count≤total) (hi : i<total) :
    Spec.Gcm.blockAt s.mem (base.gpr .r30+BitVec.ofNat 64 (16*i))=
      if i<count then Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))
      else Spec.Gcm.blockAt base.mem (base.gpr .r30+BitVec.ofNat 64 (16*i)) := by
  by_cases hic : i<count
  · rw [ite_eq_left hic]
    apply VG.Proof.Aes.PPC64LE.Crypto.aesState_inj
    rw [VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt,hs.processed.stateAt hic hc]
    exact (VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt ..).symm
  · rw [ite_eq_right hic]
    apply VG.Proof.Aes.PPC64LE.Crypto.aesState_inj
    rw [VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt,VG.Proof.Aes.PPC64LE.Crypto.aesState_blockAt]
    exact hs.processed.original (by omega) hi

end VG.Proof.AesGcm.PPC64LE.SplitBlocks.Copy
