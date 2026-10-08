import VerifiedGarbage.Proof.P256.Linear.Complement
import VerifiedGarbage.Proof.P256.Linear.Scale

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def aRegs : List Reg := [.x1,.x2,.x8,.x9,.x10,.x11,.x12,.x13,.x16]
def formRegs : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x16,.x17]
def tripleA (a : Nat) : List Instr := loads [.x9,.x10,.x11,.x12] a++shift1++addTriple

theorem tripleA_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ha8 : a%8=0) (hz : s.gpr .x17=0) :
    WP isa (.block (tripleA a)) s fun t =>
      regsVal t [.x9,.x10,.x11,.x12,.x16]=3*wordsVal s.mem base a 4 ∧ Keeps aRegs s t := by
  unfold tripleA
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok [.x9,.x10,.x11,.x12] hs ha ha8 (by constructor <;> decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=wordsVal s.mem base a 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift1_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  have z2 : s2.gpr .x17=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),hz]
  refine WP.mono (addTriple_ok s2 z2) fun t ⟨e3,k3⟩ => ?_
  have p2 : regsVal s2 [.x9,.x10,.x11,.x12]=regsVal s1 [.x9,.x10,.x11,.x12] :=
    regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
  have hA := wordsVal_lt s.mem base a 4
  rw [p2,e2,e1] at e3
  refine ⟨?_,((k1.mono (by unfold aRegs; sub_regs)).trans
    (k2.mono (by unfold aRegs; sub_regs))).trans (k3.mono (by unfold aRegs; sub_regs))⟩
  rw [e3]
  omega

def times12A (a : Nat) : List Instr := tripleA a++shift2

theorem times12A_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ha8 : a%8=0) (hz : s.gpr .x17=0) :
    WP isa (.block (times12A a)) s fun t =>
      regsVal t [.x1,.x2,.x8,.x13,.x16]=12*wordsVal s.mem base a 4 ∧ Keeps aRegs s t := by
  unfold times12A
  rw [WP.block_append_iff]
  refine WP.mono (tripleA_ok hs ha ha8 hz) fun s1 ⟨e1,k1⟩ => ?_
  have hA := wordsVal_lt s.mem base a 4
  have ht : (s1.gpr .x16).toNat<2^62 := by
    simp only [regsVal,Nat.mul_zero,Nat.add_zero] at e1
    omega
  refine WP.mono (shift2_ok s1 ht) fun t ⟨e2,k2⟩ => ?_
  refine ⟨?_,k1.trans (k2.mono (by unfold aRegs; sub_regs))⟩
  rw [e2,e1]
  omega

def form38 (a b : Nat) : List Instr :=
  complement b++shift3++tripleA a++addAcc .x9 .x10 .x11 .x12 .x16

theorem form38_ok {s : State} {base : Addr} {size a b : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (hb : b+32≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (form38 a b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=
        3*wordsVal s.mem base a 4+8*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold form38
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (complement_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=p-wordsVal s.mem base b 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift3_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  rw [WP.block_append_iff]
  have hs2 := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)
  refine WP.mono (tripleA_ok hs2 ha ha8 (by rw [k2.gpr _ (by decide),z1])) fun s3 ⟨e3,k3⟩ => ?_
  refine WP.mono (addAcc_ok s3 .x9 .x10 .x11 .x12 .x16 (by decide)) fun t ⟨e4,k4⟩ => ?_
  have p3 : regsVal s3 [.x3,.x4,.x5,.x6,.x7]=regsVal s2 [.x3,.x4,.x5,.x6,.x7] :=
    regsVal_congr fun r hr => k3.gpr r (by revert r; decide)
  rw [k2.mem,k1.mem] at e3
  rw [p3,e3,e2,e1] at e4
  have hA := wordsVal_lt s.mem base a 4
  refine ⟨?_,?_,(((k1.mono (by unfold formRegs; sub_regs)).trans
    (k2.mono (by unfold formRegs; sub_regs))).trans
    (k3.mono (by unfold formRegs aRegs; sub_regs))).trans (k4.mono (by unfold formRegs; sub_regs))⟩
  · rw [e4]
    simp only [p_value] at hB ⊢
    omega
  · rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide),z1]

def nineB (b : Nat) : List Instr :=
  complement b++shift3++addAcc .x9 .x10 .x11 .x12 .x17

theorem nineB_ok {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (nineB b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=9*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold nineB
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (complement_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=p-wordsVal s.mem base b 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift3_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  refine WP.mono (addAcc_ok s2 .x9 .x10 .x11 .x12 .x17 (by decide)) fun t ⟨e3,k3⟩ => ?_
  have z2 : s2.gpr .x17=0 := by rw [k2.gpr _ (by decide),z1]
  have pp : regsVal s2 [.x9,.x10,.x11,.x12,.x17]=regsVal s1 [.x9,.x10,.x11,.x12] := by
    have e : regsVal s2 [.x9,.x10,.x11,.x12]=regsVal s1 [.x9,.x10,.x11,.x12] :=
      regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
    simp only [regsVal,z2,show (0:BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero] at e ⊢
    exact e
  rw [pp,e2,e1] at e3
  refine ⟨?_,by rw [k3.gpr _ (by decide),z2],((k1.mono (by unfold formRegs; sub_regs)).trans
    (k2.mono (by unfold formRegs; sub_regs))).trans (k3.mono (by unfold formRegs; sub_regs))⟩
  rw [e3]
  simp only [p_value] at hB ⊢
  omega

def form129 (a b : Nat) : List Instr := nineB b++times12A a++addAcc .x1 .x2 .x8 .x13 .x16

theorem form129_ok {s : State} {base : Addr} {size a b : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (hb : b+32≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (form129 a b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=
        12*wordsVal s.mem base a 4+9*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold form129
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nineB_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (times12A_ok (hs.of_keeps k1 (by decide)) ha ha8 z1) fun s2 ⟨e2,k2⟩ => ?_
  refine WP.mono (addAcc_ok s2 .x1 .x2 .x8 .x13 .x16 (by decide)) fun t ⟨e3,k3⟩ => ?_
  have p2 : regsVal s2 [.x3,.x4,.x5,.x6,.x7]=regsVal s1 [.x3,.x4,.x5,.x6,.x7] :=
    regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
  rw [k1.mem] at e2
  rw [p2,e2,e1] at e3
  have hA := wordsVal_lt s.mem base a 4
  refine ⟨?_,by rw [k3.gpr _ (by decide),k2.gpr _ (by decide),z1],
    (k1.trans (k2.mono (by unfold formRegs aRegs; sub_regs))).trans (k3.mono (by unfold formRegs; sub_regs))⟩
  rw [e3]
  simp only [p_value] at hB ⊢
  omega


end VG.Proof.P256.Linear
