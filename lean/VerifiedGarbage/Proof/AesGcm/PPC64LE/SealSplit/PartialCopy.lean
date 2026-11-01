module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealSplit
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: a source prefix's last partial block uses the existing byte-copy loop.
/-! # Copy only the incomplete source block before fused seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.PartialCopy
open VG VG.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)


def registers : List Reg := [.r0,.r3,.r4,.r5,.r6,.r11]

structure Config (base : State) (total count : Nat) : Prop where
  bound : count≤total
  size : total<2^64
  countReg : base.gpr .r8=BitVec.ofNat 64 count
  reads : Covers [⟨base.gpr .r7,count⟩] (base.rd++base.wr)
  writes : Covers [⟨base.gpr .r27,total⟩] base.wr
  disjoint : (⟨base.gpr .r7,count⟩ : Region).Disjoint ⟨base.gpr .r27,total⟩


def setupState (s : State) : State :=
  let rem := s.gpr .r8 &&& 15#64
  let whole := s.gpr .r8-rem
  ((((s.write .r0 15).write .r5 rem).write .r11 whole).write .r3 (s.gpr .r7+whole)).write .r4 (s.gpr .r27+whole)


theorem setup_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.partialArgs) s (· = setupState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SealSplit.partialArgs,runBlock_cons,runStep_some,runBlock_nil,
    exec_li (imm := 15) (by decide),exec_logic,exec_sub,exec_add,RegUpd.gpr_write,
    reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  rfl


theorem setup_keep (s : State) : Keep registers s (setupState s) := by
  obtain ⟨_,_,_,he,hk⟩ := WP.keep registers (setup_ok s) (by decide) (by decide)
  subst he
  exact hk


theorem setup_values {base : State} {total count : Nat} (cfg : Config base total count) :
    (setupState base).gpr .r3=base.gpr .r7+BitVec.ofNat 64 (count-count%16) ∧
    (setupState base).gpr .r4=base.gpr .r27+BitVec.ofNat 64 (count-count%16) ∧
    (setupState base).gpr .r5=BitVec.ofNat 64 (count%16) := by
  have hc : count<2^64 := Nat.lt_of_le_of_lt cfg.bound cfg.size
  have hm : base.gpr .r8 &&& 15#64=BitVec.ofNat 64 (count%16) := by
    simpa only [cfg.countReg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc] using and15 (base.gpr .r8)
  have hw : base.gpr .r8-BitVec.ofNat 64 (count%16)=BitVec.ofNat 64 (count-count%16) := by
    rw [cfg.countReg,Offset.ofNat_sub_ofNat (Nat.mod_le _ _)]
  simp only [setupState,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hm,hw,and_self]

structure Result (base : State) (count : Nat) (s : State) : Prop where
  keep : Keep registers base s
  sp : s.sp=base.sp
  lr : s.lr=base.lr
  mem : s.mem=writeBytes base.mem (base.gpr .r27+BitVec.ofNat 64 (count-count%16))
    (bytesAt base.mem (base.gpr .r7+BitVec.ofNat 64 (count-count%16)) (count%16))


theorem ok (base : State) (total count : Nat) (cfg : Config base total count) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.partialCopy base (Result base count) := by
  rw [Impl.AesGcm.PPC64LE.SealSplit.partialCopy]
  apply WP.seq
  refine WP.mono (setup_ok base) fun s hs => ?_
  subst s
  obtain ⟨h3,h4,h5⟩ := setup_values cfg
  have hk := setup_keep base
  by_cases hz : count%16=0
  · refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,h5,hz]; rfl)
      (fun _ => WP.block_nil ⟨hk,rfl,rfl,?_⟩) (by simp)
    simp only [hz,bytesAt,List.range_zero,List.map_nil,writeBytes_nil]
    rfl
  · have hne : (setupState base).gpr .r5≠0 := by
      rw [h5]
      intro he
      exact hz ((ofNat_eq_zero (n := count%16) (by omega)).mp he)
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    have lp : LoopPre (setupState base)
        (base.gpr .r7+BitVec.ofNat 64 (count-count%16))
        (base.gpr .r27+BitVec.ofNat 64 (count-count%16)) (count%16) := by
      refine ⟨h3,h4,h5,by omega,by omega,?_,?_,?_⟩
      · rw [hk.2.1,hk.2.2]
        exact covers_off cfg.reads (by omega) (Nat.lt_of_le_of_lt cfg.bound cfg.size)
      · rw [hk.2.2]
        exact Covers.trans (Covers.of_sub (by
          intro r hr
          rw [List.mem_singleton] at hr
          subst r
          exact ⟨⟨base.gpr .r27,total⟩,by simp,count-count%16,rfl,by change count-count%16+count%16≤total; have := cfg.bound; omega⟩)) cfg.writes
      · exact (cfg.disjoint.sub_left (Offset.sub_base _ (d := count-count%16) (n := count%16) (k := count) (by omega))).sub_right
          (Offset.sub_base _ (d := count-count%16) (n := count%16) (k := total) (by have := cfg.bound; omega))
    refine WP.mono (copyLoop_ok _ lp) fun t ⟨hm,ht⟩ => ?_
    refine ⟨?_,ht.keeps.2.2.1,ht.keeps.2.2.2,hm⟩
    have hlk : Keep registers (setupState base) t := by
      refine ⟨fun r hr => ?_,ht.keeps.1,ht.keeps.2.1⟩
      simp only [registers,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      exact ht.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1
    exact (hk.trans hlk).mono (by simp)



theorem Result.frame {base s : State} {count : Nat} (hs : Result base count s) :
    Frame [⟨base.gpr .r27+BitVec.ofNat 64 (count-count%16),count%16⟩] base.mem s.mem := by
  rw [hs.mem]
  exact writeBytes_frame' _ (length_bytesAt _ _ _)


theorem Result.source {base s : State} {total count k : Nat} (cfg : Config base total count)
    (hs : Result base count s) (hk : k≤count) :
    bytesAt s.mem (base.gpr .r7) k=bytesAt base.mem (base.gpr .r7) k := by
  apply VG.Proof.Cmac.bytesAt_frame hs.frame _ (by have := cfg.bound; have := cfg.size; omega)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (cfg.disjoint.sub_left (Region.sub_prefix hk)).sub_right
    (Offset.sub_base _ (d := count-count%16) (n := count%16) (k := total) (by have := cfg.bound; omega))


theorem bytes_drop (m : Mem) (D : Addr) (n k : Nat) (hk : k≤n) :
    (bytesAt m D n).drop k=bytesAt m (D+BitVec.ofNat 64 k) (n-k) := by
  have he := bytesAt_add m D k (n-k)
  rw [show k+(n-k)=n by omega] at he
  rw [he]
  exact List.drop_left' (length_bytesAt _ _ _)


theorem Result.plaintext {base s : State} {total count : Nat} (cfg : Config base total count)
    (hs : Result base count s) :
    bytesAt base.mem (base.gpr .r7) (count-count%16) ++
      bytesAt s.mem (base.gpr .r27+BitVec.ofNat 64 (count-count%16)) (total-(count-count%16))=
    bytesAt base.mem (base.gpr .r7) count ++
      bytesAt base.mem (base.gpr .r27+BitVec.ofNat 64 count) (total-count) := by
  rw [hs.mem,bytesAt_writeBytes_prefix _ _ _
    (by rw [length_bytesAt]; have := cfg.bound; omega) (by have := cfg.size; omega)]
  rw [length_bytesAt,Offset.add_add]
  have he : count-count%16+count%16=count := by omega
  rw [he,← List.append_assoc]
  have hp := bytesAt_add base.mem (base.gpr .r7) (count-count%16) (count%16)
  rw [he] at hp
  rw [← hp]
  congr 2
  omega


theorem Result.input {base s : State} {total count : Nat} (cfg : Config base total count)
    (hs : Result base count s) :
    bytesAt s.mem (base.gpr .r7) (count-count%16) ++ (bytesAt s.mem (base.gpr .r27) total).drop (count-count%16)=
      bytesAt base.mem (base.gpr .r7) count ++ (bytesAt base.mem (base.gpr .r27) total).drop count := by
  rw [Result.source cfg hs (by omega),bytes_drop _ _ _ _ (by have := cfg.bound; omega),bytes_drop _ _ _ _ cfg.bound]
  exact Result.plaintext cfg hs

end VG.Proof.AesGcm.PPC64LE.SealSplit.PartialCopy
