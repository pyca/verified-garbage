module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow4
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow5
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow6
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulRow7
import VerifiedGarbage.Proof.Framework.Block

/-! Two successive product rows reuse each pair of input loads. -/

-- separate module: compose arithmetic rows before their scratch-memory stores
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def pair2Code : List Instr := (row2LowCode++row2HighCode)++(row3LowCode++row3HighCode)
def pair2Out : List Reg := .x17::row3Out

theorem pair2_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pair2Code) s fun t =>
      regsVal t pair2Out = regsVal s row2In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pair2Out) s t := by
  rw [pair2Code,WP.block_append_iff]
  refine WP.mono (row2_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (row3_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::row2Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u row2Out = (u.gpr .x17).toNat+2^64*regsVal u row3In := by
    have hr : row2Out=.x17::row3In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x17=u.gpr .x17 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pair2Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pair4Code : List Instr := (row4LowCode++row4HighCode)++(row5LowCode++row5HighCode)
def pair4Out : List Reg := .x20::row5Out

theorem pair4_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pair4Code) s fun t =>
      regsVal t pair4Out = regsVal s row4In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pair4Out) s t := by
  rw [pair4Code,WP.block_append_iff]
  refine WP.mono (row4_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (row5_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::row4Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u row4Out = (u.gpr .x20).toNat+2^64*regsVal u row5In := by
    have hr : row4Out=.x20::row5In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x20=u.gpr .x20 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pair4Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pair6Code : List Instr := (row6LowCode++row6HighCode)++(row7LowCode++row7HighCode)
def pair6Out : List Reg := .x22::row7Out

theorem pair6_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pair6Code) s fun t =>
      regsVal t pair6Out = regsVal s row6In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pair6Out) s t := by
  rw [pair6Code,WP.block_append_iff]
  refine WP.mono (row6_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (row7_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::row6Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u row6Out = (u.gpr .x22).toNat+2^64*regsVal u row7In := by
    have hr : row6Out=.x22::row7In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x22=u.gpr .x22 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pair6Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pair0Code : List Instr := row0Arithmetic++(row1LowCode++row1HighCode)
def pair0Out : List Reg := .x15::row1Out

theorem pair0_value (s : State) :
    WP isa (.block pair0Code) s fun t =>
      regsVal t pair0Out = ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps (.x2::.x14::pair0Out) s t := by
  rw [pair0Code,WP.block_append_iff]
  refine WP.mono (row0_arithmetic_value_zero s) fun u ⟨hu,z,ku⟩ => ?_
  refine WP.mono (row1_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉row0Clob from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u row0Out = (u.gpr .x15).toNat+2^64*regsVal u row1In := by
    have hr : row0Out=.x15::row1In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x15=u.gpr .x15 := kt.gpr _ (by decide)
  refine ⟨?_,(kt.gpr _ (by decide)).trans z,
    (ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pair0Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

end VG.Proof.Mont.AArch64.P521Field
