module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulFirst
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow4
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow5
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow6
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow7
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMemory
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamInvariant
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMulRow8
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamBounds
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem point_chunk_ok {s : State} {pa po : Addr} {ra ro : Reg} {size cap a o so ao : Nat} {r0 r1 : Reg}
    {code : List Instr} {out next clob : List Reg} {P B : Nat}
    (ha : Ptr s ra pa size) (ht : PtrW s ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hr : ra∉[Reg.x3,.x4])
    (hs : so+16≤64) (hs8 : so%8=0) (hd : ao+16≤72) (hd8 : ao%8=0)
    (hnd : r0≠r1) (ho : out=[r0,r1]++next)
    (hcA : ra∉clob) (hcO : ro∉clob)
    (hn : ∀r∈next,r∉([.x3,.x4] : List Reg))
    (hread : ∀m,Outside (off po o) so 16 s.mem m →
      word m (off pa a) ao=word s.mem (off pa a) ao ∧ word m (off pa a) (ao+8)=word s.mem (off pa a) (ao+8))
    (arith : WP isa (.block code) s fun u => regsVal u out=P ∧ regsVal u bRegs=B ∧ u.gpr .x2=0 ∧ Keeps clob s u) :
    WP isa (.block (code++(storesR ro [r0,r1] (o+so)++loadsR ra [.x3,.x4] (a+ao)))) s fun t =>
      wordsVal t.mem (off po o) so 2 + 2^128*regsVal t next=P ∧
      t.gpr .x3=word s.mem (off pa a) ao ∧ t.gpr .x4=word s.mem (off pa a) (ao+8) ∧
      regsVal t bRegs=B ∧ t.gpr .x2=0 ∧
      KeepRegs (.x3::.x4::clob) s t ∧ Outside (off po o) so 16 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono arith fun u ⟨prod,bval,z,ku⟩ => ?_
  refine WP.mono (point_spill_load (ha.of_keeps ku hcA)
    (ht.of_keepRegs (VG.Proof.Mont.AArch64.Keeps.regs ku) hcO)
    hA hO ha8 ho8 hs hs8 hd hd8 hr hnd (fun m hm => by
      rw [ku.mem] at hm ⊢
      exact hread m hm)) fun t ⟨stored,a0,a1,kt,ot⟩ => ?_
  have eout : regsVal u out=regsVal u [r0,r1]+2^128*regsVal u next := by
    rw [ho,regsVal_append]
    rfl
  have en : regsVal t next=regsVal u next := regsVal_congr fun r hr => kt.gpr r (hn r hr)
  have eb : regsVal t bRegs=B := by
    rw [regsVal_congr (s:=u) (fun r hr => kt.gpr r
      ((show ∀r∈bRegs,r∉([.x3,.x4] : List Reg) from by decide) r hr))]
    exact bval
  refine ⟨?_,?_,?_,eb,(kt.gpr _ (by decide)).trans z,
    ((VG.Proof.Mont.AArch64.Keeps.regs ku).mono (by sub_regs)).trans
      (kt.mono (by sub_regs)),?_⟩
  · rw [stored,en,←eout]; exact prod
  · rw [a0,ku.mem]
  · rw [a1,ku.mem]
  · rw [ku.mem] at ot; exact ot

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)
open VG.Proof.Ed25519.AArch64 (Keeps)

def pointMulStreamClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25]

structure PointStreamInv (s₀ : State) (pa pt : Addr) (B i : Nat) (rs : List Reg) (s : State) : Prop where
  product : wordsVal s.mem pt 0 i+2^(64*i)*regsVal s rs=wordsVal s₀.mem pa 0 i*B
  b : regsVal s bRegs=B
  zero : s.gpr .x2=0
  a0 : s.gpr .x3=word s₀.mem pa (8*i)
  a1 : s.gpr .x4=word s₀.mem pa (8*i+8)
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs pointMulStreamClob s₀ s

theorem point_stream_step {s₀ s : State} {pa po : Addr} {ra ro : Reg} {size cap a o B i : Nat} {rs next out clob : List Reg}
    {code : List Instr} {r0 r1 : Reg}
    (ha : Ptr s₀ ra pa size) (ht : PtrW s₀ ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (hr : ra∉[Reg.x3,.x4])
    (stable : StableInput s₀ (off pa a) (off po o)) (inv : PointStreamInv s₀ (off pa a) (off po o) B i rs s)
    (hi : i+4≤9) (hout : out=[r0,r1]++next) (hnd : r0≠r1)
    (hcA : ra∉clob) (hcO : ro∉clob)
    (hn : ∀r∈next,r∉([.x3,.x4] : List Reg))
    (hc : ∀r∈(.x3::.x4::clob),r∈pointMulStreamClob)
    (arith : WP isa (.block code) s fun u =>
      regsVal u out=regsVal s rs+((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*B ∧
      regsVal u bRegs=B ∧ u.gpr .x2=0 ∧ Keeps clob s u) :
    WP isa (.block (code++(storesR ro [r0,r1] (o+8*i)++loadsR ra [.x3,.x4] (a+8*(i+2))))) s
      (PointStreamInv s₀ (off pa a) (off po o) B (i+2) next) := by
  have ha' := ha.of_keepRegs inv.kept hra
  have ht' := ht.of_keepRegs inv.kept hro
  have hread : ∀m,Outside (off po o) (8*i) 16 s.mem m →
      word m (off pa a) (8*(i+2))=word s.mem (off pa a) (8*(i+2)) ∧
      word m (off pa a) (8*(i+2)+8)=word s.mem (off pa a) (8*(i+2)+8) := by
    intro m hm
    have hm' := inv.memory.trans (hm.mono (by omega_arith) (by omega_arith))
    exact ⟨(stable m hm' _ (by omega_arith)).trans (stable s.mem inv.memory _ (by omega_arith)).symm,
      (stable m hm' _ (by omega_arith)).trans (stable s.mem inv.memory _ (by omega_arith)).symm⟩
  refine WP.mono (point_chunk_ok ha' ht' hA hO ha8 ho8 hr (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hnd hout hcA hcO hn hread arith)
    fun t ⟨prod,a0,a1,b,z,k,om⟩ => ?_
  have whole := inv.memory.trans (om.mono (by omega_arith) (by omega_arith))
  have C : (s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat=wordsVal s₀.mem (off pa a) (8*i) 2 := by
    rw [inv.a0,inv.a1]
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  rw [C] at prod
  have hprefix := spill_prefix (i:=i) (by omega_arith) om
  have hA := wordsVal_split s₀.mem (off pa a) 0 i 2
  simp only [Nat.zero_add] at hA
  have hp : 2^(64*(i+2))=2^(64*i)*2^128 := by
    rw [Nat.mul_add,Nat.pow_add,show (64*2 : Nat)=128 from rfl]
  refine ⟨?_,b,z,?_,?_,whole,inv.kept.trans (k.mono hc)⟩
  · rw [hprefix,hp,hA]
    exact extend_product inv.product prod
  · rw [a0,stable s.mem inv.memory _ (by omega_arith)]
  · rw [a1,stable s.mem inv.memory _ (by omega_arith)]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.AArch64.Interleave

def pointMulRow1Prefix : List Instr := pointMulRow1LowCode.take 18
def pointMulRow1Suffix : List Instr := pointMulRow1LowCode.drop 18++pointMulRow1HighCode

def pointMulRow1Actual : List Instr := pointMulRow1Prefix++
  ([.movz .x .x2 0 0] : List Instr)++pointMulRow1Suffix

theorem insert_independent {pre post : List Instr} {i : Instr} {xb : Reg}
    (hind : Indeps xb pre [i]) (s : State) :
    runBlock isa (pre++i::post) s=runBlock isa (i::(pre++post)) s := by
  have comm := comm_block (fun x hx => hind x hx i List.mem_cons_self) s
  calc
    runBlock isa (pre++i::post) s =
        ((runBlock isa pre s).bind (exec i)).bind (runBlock isa post) := by
      rw [VG.AArch64.Interleave.runBlock_append,Option.bind_assoc]
      rfl
    _ = ((exec i s).bind (runBlock isa pre)).bind (runBlock isa post) :=
      congrArg (fun o => o.bind (runBlock isa post)) comm.symm
    _ = runBlock isa (i::(pre++post)) s := by
      rw [Option.bind_assoc]
      change _ = (exec i s).bind (runBlock isa (pre++post))
      congr 1
      funext u
      exact (VG.AArch64.Interleave.runBlock_append pre post u).symm

theorem pointMulRow1_moveZero (s : State) :
    runBlock isa pointMulRow1Actual s=
      runBlock isa (([.movz .x .x2 0 0] : List Instr)++
        (pointMulRow1LowCode++pointMulRow1HighCode)) s := by
  have hind : Indeps .x26 pointMulRow1Prefix [.movz .x .x2 0 0] := indeps_of_check (by decide)
  have h := insert_independent (post:=pointMulRow1Suffix) hind s
  have hlow : pointMulRow1Prefix++pointMulRow1Suffix=
      pointMulRow1LowCode++pointMulRow1HighCode := by
    rw [pointMulRow1Prefix,pointMulRow1Suffix,←List.append_assoc,List.take_append_drop]
  simpa only [pointMulRow1Actual,List.append_assoc,List.singleton_append,hlow] using h

theorem pointMulRow1_init_ok (s : State) :
    WP isa (.block (([.movz .x .x2 0 0] : List Instr)++
      (pointMulRow1LowCode++pointMulRow1HighCode))) s fun t =>
      regsVal t pointMulRow1Out=regsVal s pointMulRow1In+(s.gpr .x4).toNat*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps (.x2::.x14::pointMulRow1Out) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (movz0_ok s .x2) fun u ⟨z,ku⟩ => ?_
  refine WP.mono (pointMulRow1_value u z) fun t ⟨value,kr⟩ => ?_
  have hi : regsVal u pointMulRow1In=regsVal s pointMulRow1In := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈pointMulRow1In,r∉[Reg.x2] from by decide) r hr)
  have hb : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉[Reg.x2] from by decide) r hr)
  exact ⟨by rw [value,hi,ku.gpr .x4 (by decide),hb],
    (kr.gpr .x2 (by decide)).trans z,(ku.mono (by decide)).trans (kr.mono (by decide))⟩

theorem pointMulRow1_actual_ok (s : State) :
    WP isa (.block pointMulRow1Actual) s fun t =>
      regsVal t pointMulRow1Out=regsVal s pointMulRow1In+(s.gpr .x4).toNat*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps (.x2::.x14::pointMulRow1Out) s t := by
  obtain ⟨t,ht,hpost⟩ := runBlock_of_WP (pointMulRow1_init_ok s)
  exact WP.of_runBlock ⟨t,(pointMulRow1_moveZero s).trans ht,hpost⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def pointMulPair2Code : List Instr := (pointMulRow2LowCode++pointMulRow2HighCode)++(pointMulRow3LowCode++pointMulRow3HighCode)
def pointMulPair2Out : List Reg := .x17::pointMulRow3Out

theorem pointMulPair2_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulPair2Code) s fun t =>
      regsVal t pointMulPair2Out = regsVal s pointMulRow2In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pointMulPair2Out) s t := by
  rw [pointMulPair2Code,WP.block_append_iff]
  refine WP.mono (pointMulRow2_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (pointMulRow3_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::pointMulRow2Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u pointMulRow2Out = (u.gpr .x17).toNat+2^64*regsVal u pointMulRow3In := by
    have hr : pointMulRow2Out=.x17::pointMulRow3In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x17=u.gpr .x17 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointMulPair2Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pointMulPair4Code : List Instr := (pointMulRow4LowCode++pointMulRow4HighCode)++(pointMulRow5LowCode++pointMulRow5HighCode)
def pointMulPair4Out : List Reg := .x20::pointMulRow5Out

theorem pointMulPair4_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulPair4Code) s fun t =>
      regsVal t pointMulPair4Out = regsVal s pointMulRow4In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pointMulPair4Out) s t := by
  rw [pointMulPair4Code,WP.block_append_iff]
  refine WP.mono (pointMulRow4_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (pointMulRow5_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::pointMulRow4Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u pointMulRow4Out = (u.gpr .x20).toNat+2^64*regsVal u pointMulRow5In := by
    have hr : pointMulRow4Out=.x20::pointMulRow5In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x20=u.gpr .x20 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointMulPair4Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pointMulPair6Code : List Instr := (pointMulRow6LowCode++pointMulRow6HighCode)++(pointMulRow7LowCode++pointMulRow7HighCode)
def pointMulPair6Out : List Reg := .x22::pointMulRow7Out

theorem pointMulPair6_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulPair6Code) s fun t =>
      regsVal t pointMulPair6Out = regsVal s pointMulRow6In +
        ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      Keeps (.x14::pointMulPair6Out) s t := by
  rw [pointMulPair6Code,WP.block_append_iff]
  refine WP.mono (pointMulRow6_value s hz) fun u ⟨hu,ku⟩ => ?_
  have z : u.gpr .x2=0 := (ku.gpr _ (by decide)).trans hz
  refine WP.mono (pointMulRow7_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉(.x14::pointMulRow6Out) from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u pointMulRow6Out = (u.gpr .x22).toNat+2^64*regsVal u pointMulRow7In := by
    have hr : pointMulRow6Out=.x22::pointMulRow7In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x22=u.gpr .x22 := kt.gpr _ (by decide)
  refine ⟨?_,(ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointMulPair6Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

def pointMulPair0Code : List Instr := pointMulRow0Arithmetic++pointMulRow1Actual
def pointMulPair0Out : List Reg := .x15::pointMulRow1Out

theorem pointMulPair0_value (s : State) :
    WP isa (.block pointMulPair0Code) s fun t =>
      regsVal t pointMulPair0Out = ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps (.x2::.x14::pointMulPair0Out) s t := by
  rw [pointMulPair0Code,WP.block_append_iff]
  refine WP.mono (pointMulRow0_arithmetic_value_zero s) fun u ⟨hu,z,ku⟩ => ?_
  refine WP.mono (pointMulRow1_actual_ok u) fun t ⟨ht,z2,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉pointMulRow0Clob from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u pointMulRow0Out = (u.gpr .x15).toNat+2^64*regsVal u pointMulRow1In := by
    have hr : pointMulRow0Out=.x15::pointMulRow1In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x15=u.gpr .x15 := kt.gpr _ (by decide)
  refine ⟨?_,z2,
    (ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointMulPair0Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem point_first_pair_loaded {s : State} {pa pb : Addr} {ra rb : Reg} {size cap a b : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap)
    (hA : a+72≤size) (hB : b+72≤cap) (ha8 : a%8=0) (hb8 : b%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) :
    WP isa (.block ((loadsR ra [.x3,.x4] a++loadsR rb bRegs b)++pointMulPair0Code)) s fun t =>
      regsVal t pointMulPair0Out = wordsVal s.mem (off pa a) 0 2 * wordsVal s.mem (off pb b) 0 9 ∧
      regsVal t bRegs = wordsVal s.mem (off pb b) 0 9 ∧
      t.gpr .x2=0 ∧ Keeps pointMulStreamClob s t := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadsR_ok [.x3,.x4] ha (a:=a) (by simp only [List.length_cons,List.length_nil]; omega_arith) ha8 (by decide)
    (fun h => hra ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)))
    fun u ⟨au,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bRegs (hb.of_keeps ku (fun h => hrb
      ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) rb h)))
    (a:=b) (by simpa only [show bRegs.length=9 from rfl] using hB) hb8 (by decide)
    (fun h => hrb ((show ∀r∈bRegs,r∈pointMulStreamClob from by decide) rb h))) fun v ⟨bv,kv,_⟩ => ?_
  have av : (v.gpr .x3).toNat+2^64*(v.gpr .x4).toNat=wordsVal s.mem (off pa a) 0 2 := by
    rw [kv.gpr _ (by decide),kv.gpr _ (by decide)]
    change regsVal u [.x3,.x4]=wordsVal s.mem pa a 2 at au
    rw [wordsVal_off,Nat.add_zero]
    simpa only [regsVal,Nat.mul_zero,Nat.add_zero] using au
  have bv' : regsVal v bRegs=wordsVal s.mem (off pb b) 0 9 := by
    change regsVal v bRegs=wordsVal u.mem pb b 9 at bv
    rw [wordsVal_off,Nat.add_zero]
    rw [bv,ku.mem]
  refine WP.mono (pointMulPair0_value v) fun t ⟨prod,z,kt⟩ => ?_
  have bt : regsVal t bRegs=regsVal v bRegs := regsVal_congr fun r hr =>
    kt.gpr r ((show ∀r∈bRegs,r∉(.x2::.x14::pointMulPair0Out) from by decide) r hr)
  exact ⟨by rw [prod,av,bv'],bt.trans bv',z,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)

def pointFirstStreamCode (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  ((loadsR ra [.x3,.x4] a++loadsR rb bRegs b)++pointMulPair0Code)++
    (storesR ro [.x15,.x16] o++loadsR ra [.x3,.x4] (a+16))

theorem point_stream_init {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+64≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o)) :
    WP isa (.block (pointFirstStreamCode ra a rb b ro o)) s
      (PointStreamInv s (off pa a) (off po o) (wordsVal s.mem (off pb b) 0 9) 2 pointMulRow2In) := by
  have hread : ∀m,Outside (off po o) 0 16 s.mem m →
      word m (off pa a) 16=word s.mem (off pa a) 16 ∧
      word m (off pa a) 24=word s.mem (off pa a) 24 := by
    intro m hm
    have hwide := hm.mono (o':=0) (n':=64) (by decide) (by decide)
    exact ⟨stable m hwide 16 (by decide),stable m hwide 24 (by decide)⟩
  have hr : ra∉[Reg.x3,.x4] := fun h => hra
    ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)
  have h := point_chunk_ok ha ht hA hO ha8 ho8 hr
    (so:=0) (ao:=16) (by decide) (by decide) (by decide) (by decide)
    (r0:=.x15) (r1:=.x16) (out:=pointMulPair0Out) (next:=pointMulRow2In)
    (by decide) rfl hra hro (by decide) hread
    (point_first_pair_loaded ha hb hA hB ha8 hb8 hra hrb)
  change WP isa (.block (pointFirstStreamCode ra a rb b ro o)) s _ at h
  refine WP.mono h fun t ⟨prod,a0,a1,bval,z,k,om⟩ => ?_
  exact ⟨prod,bval,z,a0,a1,om.mono (by decide) (by decide),k.mono (by decide)⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)

def pointStage2Code (ra : Reg) (a : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulPair2Code++(storesR ro [.x17,.x19] (o+16)++loadsR ra [.x3,.x4] (a+32))

theorem point_stage2_ok {s₀ s : State} {pa po : Addr} {ra ro : Reg} {size cap a o B : Nat}
    (ha : Ptr s₀ ra pa size) (ht : PtrW s₀ ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s₀ (off pa a) (off po o))
    (inv : PointStreamInv s₀ (off pa a) (off po o) B 2 pointMulRow2In s) :
    WP isa (.block (pointStage2Code ra a ro o)) s
      (PointStreamInv s₀ (off pa a) (off po o) B 4 pointMulRow4In) := by
  have hr : ra∉[Reg.x3,.x4] := fun h => hra
    ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)
  have hc : ∀r∈(.x14::pointMulPair2Out),r∈pointMulStreamClob := by decide
  exact point_stream_step ha ht hA hO ha8 ho8 hra hro hr stable inv (by decide)
    (out:=pointMulPair2Out) (r0:=.x17) (r1:=.x19)
    rfl (by decide) (fun h => hra (hc ra h)) (fun h => hro (hc ro h)) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pointMulPair2_value s inv.zero))

def pointStage4Code (ra : Reg) (a : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulPair4Code++(storesR ro [.x20,.x21] (o+32)++loadsR ra [.x3,.x4] (a+48))

theorem point_stage4_ok {s₀ s : State} {pa po : Addr} {ra ro : Reg} {size cap a o B : Nat}
    (ha : Ptr s₀ ra pa size) (ht : PtrW s₀ ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s₀ (off pa a) (off po o))
    (inv : PointStreamInv s₀ (off pa a) (off po o) B 4 pointMulRow4In s) :
    WP isa (.block (pointStage4Code ra a ro o)) s
      (PointStreamInv s₀ (off pa a) (off po o) B 6 pointMulRow6In) := by
  have hr : ra∉[Reg.x3,.x4] := fun h => hra
    ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)
  have hc : ∀r∈(.x14::pointMulPair4Out),r∈pointMulStreamClob := by decide
  exact point_stream_step ha ht hA hO ha8 ho8 hra hro hr stable inv (by decide)
    (out:=pointMulPair4Out) (r0:=.x20) (r1:=.x21)
    rfl (by decide) (fun h => hra (hc ra h)) (fun h => hro (hc ro h)) (by decide) (by decide)
    (arithmetic_frame inv.b inv.zero (by decide) (by decide) (pointMulPair4_value s inv.zero))

def pointStream6Code (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointFirstStreamCode ra a rb b ro o++(pointStage2Code ra a ro o++pointStage4Code ra a ro o)

theorem point_stream6_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+64≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o)) :
    WP isa (.block (pointStream6Code ra a rb b ro o)) s
      (PointStreamInv s (off pa a) (off po o) (wordsVal s.mem (off pb b) 0 9) 6 pointMulRow6In) := by
  rw [pointStream6Code,WP.block_append_iff]
  refine WP.mono (point_stream_init ha hb ht hA hB hO ha8 hb8 ho8 hra hrb hro stable) fun u inv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (point_stage2_ok ha ht hA hO ha8 ho8 hra hro stable inv) fun v inv' => ?_
  exact point_stage4_ok ha ht hA hO ha8 ho8 hra hro stable inv'

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def pointMulRow0Z2Out : List Reg := [.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x1]
def pointMulRow0Z2Clob : List Reg := .x2::.x14::pointMulRow0Z2Out
def pointMulRow0Z2Arithmetic : List Instr := [
  .mul .x .x15 .x3 .x5,
  .umulh .x16 .x3 .x5,
  .mul .x .x14 .x3 .x6,
  .umulh .x17 .x3 .x6,
  .adds .x .x16 .x16 .x14,
  .mul .x .x14 .x3 .x7,
  .umulh .x19 .x3 .x7,
  .adcs .x .x17 .x17 .x14,
  .mul .x .x14 .x3 .x8,
  .umulh .x20 .x3 .x8,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x3 .x9,
  .umulh .x21 .x3 .x9,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x3 .x10,
  .umulh .x22 .x3 .x10,
  .adcs .x .x21 .x21 .x14,
  .mul .x .x14 .x3 .x11,
  .umulh .x23 .x3 .x11,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x3 .x12,
  .umulh .x24 .x3 .x12,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x3 .x13,
  .umulh .x1 .x3 .x13,
  .adcs .x .x24 .x24 .x14,
  .adc .x .x1 .x1 .x2]

theorem pointMulRow0Z2_arithmetic_words_zero (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulRow0Z2Arithmetic) s fun t =>
      pointMulRow0Z2Out.map t.gpr = firstRow (s.gpr .x3) (bRegs.map s.gpr) ∧
      t.gpr .x2=0 ∧ Keeps pointMulRow0Z2Clob s t := by
  apply WP.of_runBlock
  simp only [pointMulRow0Z2Arithmetic,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left',hz]
  refine ⟨?_,trivial,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow0Z2Out,bRegs,List.map_cons,List.map_nil,firstRow,firstChain,
      addCarry,carryOut,mulHi,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow0Z2Clob,pointMulRow0Z2Out]
    reg_keeps

theorem pointMulRow0Z2_arithmetic_value_zero (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulRow0Z2Arithmetic) s fun t =>
      regsVal t pointMulRow0Z2Out = (s.gpr .x3).toNat*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps pointMulRow0Z2Clob s t := by
  refine WP.mono (pointMulRow0Z2_arithmetic_words_zero s hz) fun t ⟨h,z,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,firstRow_value,value_map_gpr] at e
  exact ⟨e,z,k⟩


end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def pointMulPair0Z2Code : List Instr := pointMulRow0Z2Arithmetic++(pointMulRow1LowCode++pointMulRow1HighCode)
def pointMulPair0Z2Out : List Reg := .x15::pointMulRow1Out

theorem pointMulPair0Z2_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block pointMulPair0Z2Code) s fun t =>
      regsVal t pointMulPair0Z2Out = ((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat)*regsVal s bRegs ∧
      t.gpr .x2=0 ∧ Keeps (.x2::.x14::pointMulPair0Z2Out) s t := by
  rw [pointMulPair0Z2Code,WP.block_append_iff]
  refine WP.mono (pointMulRow0Z2_arithmetic_value_zero s hz) fun u ⟨hu,z,ku⟩ => ?_
  refine WP.mono (pointMulRow1_value u z) fun t ⟨ht,kt⟩ => ?_
  have a : u.gpr .x4=s.gpr .x4 := ku.gpr _ (by decide)
  have b : regsVal u bRegs=regsVal s bRegs := regsVal_congr fun r hr =>
    ku.gpr r ((show ∀r∈bRegs,r∉pointMulRow0Z2Clob from by decide) r hr)
  rw [a,b] at ht
  have hm : regsVal u pointMulRow0Z2Out = (u.gpr .x15).toNat+2^64*regsVal u pointMulRow1In := by
    have hr : pointMulRow0Z2Out=.x15::pointMulRow1In := rfl
    rw [hr,regsVal]
  have hh : t.gpr .x15=u.gpr .x15 := kt.gpr _ (by decide)
  refine ⟨?_,(kt.gpr _ (by decide)).trans z,
    (ku.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [pointMulPair0Z2Out,regsVal,hh,Nat.add_mul,Nat.mul_assoc]
  omega_using [hu,ht,hm]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)

theorem point_first_pair_loaded_z2 {s : State} {pa pb : Addr} {ra rb : Reg} {size cap a b : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap)
    (hA : a+72≤size) (hB : b+72≤cap) (ha8 : a%8=0) (hb8 : b%8=0)
    (hz : s.gpr .x2=0) (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) :
    WP isa (.block ((loadsR ra [.x3,.x4] a++loadsR rb bRegs b)++pointMulPair0Z2Code)) s fun t =>
      regsVal t pointMulPair0Z2Out = wordsVal s.mem (off pa a) 0 2 * wordsVal s.mem (off pb b) 0 9 ∧
      regsVal t bRegs = wordsVal s.mem (off pb b) 0 9 ∧
      t.gpr .x2=0 ∧ Keeps pointMulStreamClob s t := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadsR_ok [.x3,.x4] ha (a:=a) (by simp only [List.length_cons,List.length_nil]; omega_arith) ha8 (by decide)
    (fun h => hra ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)))
    fun u ⟨au,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bRegs (hb.of_keeps ku (fun h => hrb
      ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) rb h)))
    (a:=b) (by simpa only [show bRegs.length=9 from rfl] using hB) hb8 (by decide)
    (fun h => hrb ((show ∀r∈bRegs,r∈pointMulStreamClob from by decide) rb h))) fun v ⟨bv,kv,_⟩ => ?_
  have av : (v.gpr .x3).toNat+2^64*(v.gpr .x4).toNat=wordsVal s.mem (off pa a) 0 2 := by
    rw [kv.gpr _ (by decide),kv.gpr _ (by decide)]
    change regsVal u [.x3,.x4]=wordsVal s.mem pa a 2 at au
    rw [wordsVal_off,Nat.add_zero]
    simpa only [regsVal,Nat.mul_zero,Nat.add_zero] using au
  have bv' : regsVal v bRegs=wordsVal s.mem (off pb b) 0 9 := by
    change regsVal v bRegs=wordsVal u.mem pb b 9 at bv
    rw [wordsVal_off,Nat.add_zero]
    rw [bv,ku.mem]
  have zv : v.gpr .x2=0 := (kv.gpr .x2 (by decide)).trans ((ku.gpr .x2 (by decide)).trans hz)
  refine WP.mono (pointMulPair0Z2_value v zv) fun t ⟨prod,z,kt⟩ => ?_
  have bt : regsVal t bRegs=regsVal v bRegs := regsVal_congr fun r hr =>
    kt.gpr r ((show ∀r∈bRegs,r∉(.x2::.x14::pointMulPair0Z2Out) from by decide) r hr)
  exact ⟨by rw [prod,av,bv'],bt.trans bv',z,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)

structure PointTailInv (s₀ : State) (pa pt : Addr) (B : Nat) (s : State) : Prop where
  product : wordsVal s.mem pt 0 8+2^512*regsVal s pointMulRow8In=wordsVal s₀.mem pa 0 8*B
  b : regsVal s bRegs=B
  zero : s.gpr .x2=0
  top : s.gpr .x3=word s₀.mem pa 64
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs pointMulStreamClob s₀ s

def pointStage6Code (ra : Reg) (a : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointMulPair6Code++(storesR ro [.x22,.x23] (o+48)++([.ldr .x .x3 ra (a+64)] : List Instr))

theorem point_stage6_ok {s₀ s : State} {pa po : Addr} {ra ro : Reg} {size cap a o B : Nat}
    (ha : Ptr s₀ ra pa size) (ht : PtrW s₀ ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s₀ (off pa a) (off po o)) (inv : PointStreamInv s₀ (off pa a) (off po o) B 6 pointMulRow6In s) :
    WP isa (.block (pointStage6Code ra a ro o)) s (PointTailInv s₀ (off pa a) (off po o) B) := by
  rw [pointStage6Code,WP.block_append_iff]
  refine WP.mono (pointMulPair6_value s inv.zero) fun u ⟨prod,ku⟩ => ?_
  have hread : ∀m,Outside (off po o) 48 16 u.mem m → word m (off pa a) 64=word u.mem (off pa a) 64 := by
    intro m hm
    rw [ku.mem] at hm ⊢
    have hw := inv.memory.trans (hm.mono (o':=0) (n':=64) (by decide) (by decide))
    exact (stable m hw 64 (by decide)).trans (stable s.mem inv.memory 64 (by decide)).symm
  have hc : ∀r∈(.x14::pointMulPair6Out),r∈pointMulStreamClob := by decide
  refine WP.mono (point_spill_load_last
    ((ha.of_keepRegs inv.kept hra).of_keeps ku (fun h => hra (hc ra h)))
    ((ht.of_keepRegs inv.kept hro).of_keepRegs
      (VG.Proof.Mont.AArch64.Keeps.regs ku) (fun h => hro (hc ro h))) hA hO ha8 ho8 (by decide) hread)
    fun t ⟨stored,atop,kt,om⟩ => ?_
  have en : regsVal t pointMulRow8In=regsVal u pointMulRow8In := regsVal_congr fun r hr =>
    kt.gpr r ((show ∀r∈pointMulRow8In,r∉([.x3] : List Reg) from by decide) r hr)
  have eout : regsVal u pointMulPair6Out=regsVal u [.x22,.x23]+2^128*regsVal u pointMulRow8In := by
    have ho : pointMulPair6Out=([.x22,.x23] : List Reg)++pointMulRow8In := rfl
    rw [ho,regsVal_append]
    rfl
  have C : (s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat=wordsVal s₀.mem (off pa a) 48 2 := by
    rw [inv.a0,inv.a1]
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  rw [inv.b,C] at prod
  have chunk : wordsVal t.mem (off po o) 48 2+2^128*regsVal t pointMulRow8In =
      regsVal s pointMulRow6In+wordsVal s₀.mem (off pa a) 48 2*B := by
    rw [stored,en,←eout]; exact prod
  have om' : Outside (off po o) 48 16 s.mem t.mem := by rw [ku.mem] at om; exact om
  have whole := inv.memory.trans (om'.mono (o':=0) (n':=64) (by decide) (by decide))
  have hprefix := spill_prefix (i:=6) (by decide) om'
  have hA := wordsVal_split s₀.mem (off pa a) 0 6 2
  simp only [Nat.zero_add] at hA
  have hp := Nat.pow_add (2 : Nat) 384 128
  simp only [Nat.reduceAdd] at hp
  refine ⟨?_,?_,?_,?_,whole,?_⟩
  · rw [hprefix,hp,hA]
    have e := extend_product inv.product chunk
    simp only [Nat.reduceMul] at e ⊢
    exact e
  · rw [regsVal_congr (s:=u) (fun r hr => kt.gpr r
      ((show ∀r∈bRegs,r∉([.x3] : List Reg) from by decide) r hr))]
    rw [regsVal_congr (s:=s) (fun r hr => ku.gpr r
      ((show ∀r∈bRegs,r∉(.x14::pointMulPair6Out) from by decide) r hr))]
    exact inv.b
  · rw [kt.gpr _ (by decide),ku.gpr _ (by decide),inv.zero]
  · rw [atop,ku.mem,stable s.mem inv.memory 64 (by decide)]
  · exact inv.kept.trans (((VG.Proof.Mont.AArch64.Keeps.regs ku).mono (by decide)).trans
      (kt.mono (by decide)))


def pointStreamRest (ra : Reg) (a : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointStage2Code ra a ro o++(pointStage4Code ra a ro o++pointStage6Code ra a ro o)

theorem point_stream_rest_ok {s₀ s : State} {pa po : Addr} {ra ro : Reg} {size cap a o B : Nat}
    (ha : Ptr s₀ ra pa size) (ht : PtrW s₀ ro po cap)
    (hA : a+72≤size) (hO : o+64≤cap) (ha8 : a%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s₀ (off pa a) (off po o))
    (inv : PointStreamInv s₀ (off pa a) (off po o) B 2 pointMulRow2In s) :
    WP isa (.block (pointStreamRest ra a ro o)) s
      (PointTailInv s₀ (off pa a) (off po o) B) := by
  rw [pointStreamRest,WP.block_append_iff]
  refine WP.mono (point_stage2_ok ha ht hA hO ha8 ho8 hra hro stable inv) fun u inv' => ?_
  rw [WP.block_append_iff]
  refine WP.mono (point_stage4_ok ha ht hA hO ha8 ho8 hra hro stable inv') fun v inv'' => ?_
  exact point_stage6_ok ha ht hA hO ha8 ho8 hra hro stable inv''

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)

def pointFirstStreamZ2Code (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  ((loadsR ra [.x3,.x4] a++loadsR rb bRegs b)++pointMulPair0Z2Code)++
    (storesR ro [.x15,.x16] o++loadsR ra [.x3,.x4] (a+16))

theorem point_stream_init_z2 {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+64≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hz : s.gpr .x2=0) (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o)) :
    WP isa (.block (pointFirstStreamZ2Code ra a rb b ro o)) s
      (PointStreamInv s (off pa a) (off po o) (wordsVal s.mem (off pb b) 0 9) 2 pointMulRow2In) := by
  have hread : ∀m,Outside (off po o) 0 16 s.mem m →
      word m (off pa a) 16=word s.mem (off pa a) 16 ∧
      word m (off pa a) 24=word s.mem (off pa a) 24 := by
    intro m hm
    have hwide := hm.mono (o':=0) (n':=64) (by decide) (by decide)
    exact ⟨stable m hwide 16 (by decide),stable m hwide 24 (by decide)⟩
  have hr : ra∉[Reg.x3,.x4] := fun h => hra
    ((show ∀r∈[Reg.x3,.x4],r∈pointMulStreamClob from by decide) ra h)
  have h := point_chunk_ok ha ht hA hO ha8 ho8 hr
    (so:=0) (ao:=16) (by decide) (by decide) (by decide) (by decide)
    (r0:=.x15) (r1:=.x16) (out:=pointMulPair0Out) (next:=pointMulRow2In)
    (by decide) rfl hra hro (by decide) hread
    (point_first_pair_loaded_z2 ha hb hA hB ha8 hb8 hz hra hrb)
  change WP isa (.block (pointFirstStreamZ2Code ra a rb b ro o)) s _ at h
  refine WP.mono h fun t ⟨prod,a0,a1,bval,z,k,om⟩ => ?_
  exact ⟨prod,bval,z,a0,a1,om.mono (by decide) (by decide),k.mono (by decide)⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure PointMulProductInv (s₀ : State) (pa pt : Addr) (B : Nat) (s : State) : Prop where
  product : wordsVal s.mem pt 0 8+2^512*regsVal s pointMulRow8In=wordsVal s₀.mem pa 0 9*B
  zero : s.gpr .x2=0
  memory : Outside pt 0 64 s₀.mem s.mem
  kept : KeepRegs pointMulStreamClob s₀ s

theorem point_finish_product {s₀ s : State} {pa pt : Addr} {B : Nat}
    (inv : PointTailInv s₀ pa pt B s)
    (ha : wordsVal s₀.mem pa 0 9<2^521) (hb : B<2^521) :
    WP isa (.block (pointMulRow8LowCode++pointMulRow8HighCode)) s (PointMulProductInv s₀ pa pt B) := by
  have ae := wordsVal_succ_top s₀.mem pa 0 8
  simp only [Nat.reduceAdd,Nat.reduceMul,Nat.zero_add] at ae
  have atop := top_limb_bound (L:=wordsVal s₀.mem pa 0 8)
    (A:=wordsVal s₀.mem pa 0 9) (top:=(word s₀.mem pa 64).toNat) ae ha
  have aTopReg : (s.gpr .x3).toNat<512 := by rw [inv.top]; exact atop
  have be : B=regsVal s pointMulBLowRegs+2^512*(s.gpr .x13).toNat := by
    rw [←inv.b]
    have hbr : bRegs=pointMulBLowRegs++[.x13] := rfl
    rw [hbr,regsVal_append]
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,
      show pointMulBLowRegs.length=8 from rfl,Nat.reduceMul]
  have btop := top_limb_bound (L:=regsVal s pointMulBLowRegs) (A:=B)
    (top:=(s.gpr .x13).toNat) be hb
  have hpref := wordsVal_lt s₀.mem pa 0 8
  simp only [Nat.reduceMul] at hpref
  have ht := tail_acc_bound (P:=wordsVal s₀.mem pa 0 8)
    (S:=wordsVal s.mem pt 0 8) (T:=regsVal s pointMulRow8In) (B:=B) hpref inv.product
  have hbound := final_row_bound (T:=regsVal s pointMulRow8In) (B:=B) (s.gpr .x3) ht hb aTopReg
  have hbound' : regsVal s pointMulRow8In+(s.gpr .x3).toNat*regsVal s bRegs<2^576 := by
    rw [inv.b]; exact hbound
  refine WP.mono (pointMulRow8_value s (mulHi_small _ _ aTopReg btop) hbound') fun t ⟨prod,k⟩ => ?_
  refine ⟨?_,(k.gpr _ (by decide)).trans inv.zero,?_,?_⟩
  · rw [inv.b,inv.top] at prod
    have e := last_limb_identity inv.product prod
    rw [←ae] at e
    rw [k.mem]
    exact e
  · rw [k.mem]; exact inv.memory
  · exact inv.kept.trans ((VG.Proof.Mont.AArch64.Keeps.regs k).mono (by decide))


end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def pointMulProductCode (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointFirstStreamCode ra a rb b ro o++
    (pointStreamRest ra a ro o++(pointMulRow8LowCode++pointMulRow8HighCode))

def pointMulProductZ2Code (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) : List Instr :=
  pointFirstStreamZ2Code ra a rb b ro o++
    (pointStreamRest ra a ro o++(pointMulRow8LowCode++pointMulRow8HighCode))

theorem point_mul_product_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+64≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o))
    (ha' : wordsVal s.mem (off pa a) 0 9<2^521) (hb' : wordsVal s.mem (off pb b) 0 9<2^521) :
    WP isa (.block (pointMulProductCode ra a rb b ro o)) s
      (PointMulProductInv s (off pa a) (off po o) (wordsVal s.mem (off pb b) 0 9)) := by
  rw [pointMulProductCode,WP.block_append_iff]
  refine WP.mono (point_stream_init ha hb ht hA hB hO ha8 hb8 ho8 hra hrb hro stable) fun u inv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (point_stream_rest_ok ha ht hA hO ha8 ho8 hra hro stable inv) fun v tail => ?_
  exact point_finish_product tail ha' hb'

theorem point_mul_product_z2_ok {s : State} {pa pb po : Addr} {ra rb ro : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ht : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+64≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hz : s.gpr .x2=0)
    (hra : ra∉pointMulStreamClob) (hrb : rb∉pointMulStreamClob) (hro : ro∉pointMulStreamClob)
    (stable : StableInput s (off pa a) (off po o))
    (ha' : wordsVal s.mem (off pa a) 0 9<2^521) (hb' : wordsVal s.mem (off pb b) 0 9<2^521) :
    WP isa (.block (pointMulProductZ2Code ra a rb b ro o)) s
      (PointMulProductInv s (off pa a) (off po o) (wordsVal s.mem (off pb b) 0 9)) := by
  rw [pointMulProductZ2Code,WP.block_append_iff]
  refine WP.mono (point_stream_init_z2 ha hb ht hA hB hO ha8 hb8 ho8 hz hra hrb hro stable) fun u inv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (point_stream_rest_ok ha ht hA hO ha8 ho8 hra hro stable inv) fun v tail => ?_
  exact point_finish_product tail ha' hb'

end VG.Proof.Mont.AArch64.P521Field
