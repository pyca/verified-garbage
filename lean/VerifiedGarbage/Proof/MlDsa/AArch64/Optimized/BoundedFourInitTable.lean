import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def tableMemory (m : Mem) (p : Addr) : Nat → Mem
 | 0 => m
 | n+1 => initEntryMemory (tableMemory m p n) p n

def TablePrefix (m : Mem) (p : Addr) (n : Nat) : Prop := ∀mask<n,
 m.read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
 m.readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=BitVec.ofNat 64 (acceptedIndices mask).length

theorem tableMemory_prefix (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    TablePrefix (tableMemory m p n) p n := by
  induction n with
  | zero => intro mask hm; omega
  | succ n ih =>
    have hprev := ih (by omega)
    intro mask hm
    by_cases he : mask=n
    · subst mask; exact initEntryMemory_read _ p (by omega)
    · have hother := initEntryMemory_other (tableMemory m p n) p (by omega : n<16) (by omega : mask<16) he
      have hp := hprev mask (by omega)
      exact ⟨hother.1.trans hp.1,hother.2.trans hp.2⟩

theorem TablePrefix.table {m : Mem} {p : Addr} (h : TablePrefix m p 16) : TableAt m (p+6000) := by
  intro mask hm
  have e0 : (p+6000)+BitVec.ofNat 64 (64*mask)=p+BitVec.ofNat 64 (6000+64*mask) := by
    change (p+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*mask)=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have e1 : (p+BitVec.ofNat 64 (6000+64*mask))+32=p+BitVec.ofNat 64 (6000+64*mask+32) := by
    change (p+BitVec.ofNat 64 (6000+64*mask))+BitVec.ofNat 64 32=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [e0,e1]
  exact h mask hm

theorem tableMemory_table (m : Mem) (p : Addr) : TableAt (tableMemory m p 16) (p+6000) :=
  (tableMemory_prefix m p (by decide : 16≤16)).table

def tablePrefixCode (n : Nat) : List Instr := (List.range n).flatMap (entryInit true)

theorem tablePrefixCode_ok {n : Nat} (hn : n≤16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀mask<n,∀off∈[0,8,32],InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+off)) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v → t.mem=tableMemory s.mem (s.gpr .x19) n →
      WP isa (.block rest) t Q) :
    WP isa (.block (tablePrefixCode n++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact k s (Keep.refl _ _) rfl rfl
  | succ n ih =>
    have he : tablePrefixCode (n+1)=tablePrefixCode n++entryInit true n := by
      simp only [tablePrefixCode,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [he,List.append_assoc]
    refine ih (by omega) (by intro mask hm; exact hw mask (by omega)) fun a ha hav ham => ?_
    refine entryInit_ok (by omega) (by
      intro off hoff
      rw [ha.wr,ha.get .x19]
      exact hw n (by omega) off hoff) fun t ht htv htm =>
        k t ((ha.trans ht).mono (by simp)) (htv.trans hav) ?_
    rw [htm,ham,ha.get .x19]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
