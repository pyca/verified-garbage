module

public import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Proof.P256.EcdhInverse.Extract
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import Mathlib.Data.BitVec
import VerifiedGarbage.Proof.P256.EcdhInverse.Shift
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Algebra.Group.Int.Defs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Data.Finset.Attr
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Core
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Divstep.WordBasic
import Mathlib.Tactic.Ring.RingNF
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Divstep.Batch
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import Mathlib.Algebra.Order.Group.Nat
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Divstep.Packed

/-! ### `P256.EcdhInverse.MachineExtract`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def extract20a : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x8 .x4 .x28,
   .lsl .x .x8 .x8 22,
   .lsr .x .x26 .x8 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x8 .x26 .x8 43,
   .movz .x .x11 0 0,
   .movk .x .x11 16 1,
   .lsl .x .x28 .x11 21,
   .add .x .x11 .x11 .x28,
   .add .x .x9 .x4 .x11,
   .lsr .x .x26 .x9 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x9 .x26 .x9 42,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x10 .x5 .x28,
   .lsl .x .x10 .x10 22,
   .lsr .x .x26 .x10 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x10 .x26 .x10 43,
   .add .x .x11 .x5 .x11,
   .lsr .x .x26 .x11 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x11 .x26 .x11 42]

theorem extract20a_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract20a) s fun t =>
      t.gpr .x8=((s.gpr .x4+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x9=(s.gpr .x4+2199024304128).sshiftRight 42 ∧
      t.gpr .x10=((s.gpr .x5+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x11=(s.gpr .x5+2199024304128).sshiftRight 42 ∧
      Keeps [.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract20a,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,
    show (22:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide,show (42:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h8,h9,h10,h11,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h8,h9,h10,h11,h26,h28,↓reduceIte]

def extract20b : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x12 .x4 .x28,
   .lsl .x .x12 .x12 22,
   .lsr .x .x26 .x12 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x12 .x26 .x12 43,
   .movz .x .x15 0 0,
   .movk .x .x15 16 1,
   .lsl .x .x28 .x15 21,
   .add .x .x15 .x15 .x28,
   .add .x .x13 .x4 .x15,
   .lsr .x .x26 .x13 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x13 .x26 .x13 42,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x14 .x5 .x28,
   .lsl .x .x14 .x14 22,
   .lsr .x .x26 .x14 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x14 .x26 .x14 43,
   .add .x .x15 .x5 .x15,
   .lsr .x .x26 .x15 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x15 .x26 .x15 42]

theorem extract20b_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract20b) s fun t =>
      t.gpr .x12=((s.gpr .x4+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x13=(s.gpr .x4+2199024304128).sshiftRight 42 ∧
      t.gpr .x14=((s.gpr .x5+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x15=(s.gpr .x5+2199024304128).sshiftRight 42 ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract20b,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,
    show (22:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide,show (42:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h12,h13,h14,h15,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h12,h13,h14,h15,h26,h28,↓reduceIte]

def extract19 : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x12 .x4 .x28,
   .lsl .x .x12 .x12 21,
   .lsr .x .x26 .x12 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x12 .x26 .x12 43,
   .movz .x .x15 0 0,
   .movk .x .x15 16 1,
   .lsl .x .x28 .x15 21,
   .add .x .x15 .x15 .x28,
   .add .x .x13 .x4 .x15,
   .lsr .x .x26 .x13 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x13 .x26 .x13 43,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x14 .x5 .x28,
   .lsl .x .x14 .x14 21,
   .lsr .x .x26 .x14 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x14 .x26 .x14 43,
   .add .x .x15 .x5 .x15,
   .lsr .x .x26 .x15 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x15 .x26 .x15 43]

theorem extract19_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract19) s fun t =>
      t.gpr .x12=((s.gpr .x4+1048576) <<< 21).sshiftRight 43 ∧
      t.gpr .x13=(s.gpr .x4+2199024304128).sshiftRight 43 ∧
      t.gpr .x14=((s.gpr .x5+1048576) <<< 21).sshiftRight 43 ∧
      t.gpr .x15=(s.gpr .x5+2199024304128).sshiftRight 43 ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract19,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h12,h13,h14,h15,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h12,h13,h14,h15,h26,h28,↓reduceIte]

theorem extract20a_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 20 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 20) (hlo : m.lo 20)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract20a) s fun t =>
      t.gpr .x8=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^20 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega_arith
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^20 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega_arith
  have hu : -(2:Int)^(20-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega_arith
  have hq : -(2:Int)^(20-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega_arith
  refine WP.mono (extract20a_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

theorem extract20b_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 20 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 20) (hlo : m.lo 20)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract20b) s fun t =>
      t.gpr .x12=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^20 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega_arith
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^20 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega_arith
  have hu : -(2:Int)^(20-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega_arith
  have hq : -(2:Int)^(20-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega_arith
  refine WP.mono (extract20b_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

theorem extract19_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 19 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 19) (hlo : m.lo 19)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract19) s fun t =>
      t.gpr .x12=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^19 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega_arith
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^19 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega_arith
  have hu : -(2:Int)^(19-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega_arith
  have hq : -(2:Int)^(19-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega_arith
  refine WP.mono (extract19_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 21).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 43=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 21).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 43=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Compose`, which only this module used -/

section

/-! ### `Divstep.NegInput`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Divstep

/-- Change the simultaneous sign of the input pair, keeping its transition matrix. -/
def MSt.negInput (t : MSt) : MSt := {t with f := -t.f, g := -t.g}

theorem mstep_negInput {t : MSt} (hf : t.f%2=1) :
    mstep t.negInput=(mstep t).negInput := by
  have hg : (-t.g)%2=t.g%2 := by omega_using []
  unfold mstep MSt.negInput
  simp only [hg]
  split
  · rename_i h
    congr 1
    dsimp only
    omega_using [hf, h]
  · rename_i h
    congr 1
    rcases Int.emod_two_eq_zero_or_one t.g with hg|hg <;> simp only [hg]
    all_goals omega_arith

theorem msteps_negInput {t : MSt} (hf : t.f%2=1) (n : Nat) :
    msteps n t.negInput=(msteps n t).negInput := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [msteps,mstep_negInput hf,ih (mstep_f_odd hf)]
    rfl

theorem msteps_init_negInput (d f g : Int) (hf : f%2=1) (n : Nat) :
    msteps n (MSt.init d (-f) (-g))=(msteps n (MSt.init d f g)).negInput :=
  msteps_negInput (t:=MSt.init d f g) hf n

end VG.Proof.Divstep

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG.Proof.Divstep

theorem second_input_cong {d f g a b : Int} (hf : f%2=1)
    (ha : a%2^44=(-f)%2^44) (hb : b%2^44=(-g)%2^44) :
    (msteps 20 (MSt.init d a b)).cong
      (msteps 20 (MSt.init d f g)).negInput 24 := by
  have hodd : a%2=1 := by norm_num at ha; omega_using [hf, ha]
  have hinit : (MSt.init d a b).cong (MSt.init d (-f) (-g)) 44 :=
    ⟨rfl,rfl,rfl,rfl,rfl,ha,hb⟩
  have h := msteps_cong hodd hinit 20 (by decide)
  rw [msteps_init_negInput d f g hf 20] at h
  exact h

theorem second_output_cong {a b c : Int}
    (ha : a%2^44=(-b)%2^44) (hb : b%2^24=(-c)%2^24) :
    a%2^24=c%2^24 := by
  norm_num at *
  omega_using [hb, ha]

theorem third_input_cong {d f g a b : Int} (hf : f%2=1)
    (ha : a%2^24=f%2^24) (hb : b%2^24=g%2^24) :
    (msteps 19 (MSt.init d a b)).cong (msteps 19 (MSt.init d f g)) 5 := by
  have hodd : a%2=1 := by norm_num at ha; omega_using [hf, ha]
  exact msteps_cong (t:=MSt.init d a b) (t':=MSt.init d f g) (N:=24) hodd
    ⟨rfl,rfl,rfl,rfl,rfl,ha,hb⟩ 19 (by decide)

/-- Compose the three transition matrices independently of the low-word representation. -/
theorem matrix59 (d f g : Int) :
    let a := msteps 20 (MSt.init d f g)
    let b := msteps 20 (MSt.init a.d a.f a.g)
    let c := msteps 19 (MSt.init b.d b.f b.g)
    msteps 59 (MSt.init d f g) =
      ⟨c.d,c.f,c.g,
       c.u*(b.u*a.u+b.v*a.q)+c.v*(b.q*a.u+b.r*a.q),
       c.u*(b.u*a.v+b.v*a.r)+c.v*(b.q*a.v+b.r*a.r),
       c.q*(b.u*a.u+b.v*a.q)+c.r*(b.q*a.u+b.r*a.q),
       c.q*(b.u*a.v+b.v*a.r)+c.r*(b.q*a.v+b.r*a.r)⟩ := by
  dsimp only
  rw [show (59:Nat)=40+19 by decide,msteps_add,
    show (40:Nat)=20+20 by decide,msteps_add]
  rw [msteps_gen 20 (msteps 20 (MSt.init d f g)),msteps_gen 19]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Chunk`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Encode`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem encode_row (x : BitVec 64) {k : Nat} (hk : k=41 ∨ k=62) :
    (x &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^k)) =
      BitVec.ofInt 64 ((x.toNat%2^20 : Nat)- (2^k : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_and]
  have ha : x.toNat%1048576<1048576 := Nat.mod_lt _ (by decide)
  have hp : x.toNat &&& (0xfffff : BitVec 64).toNat=x.toNat%1048576 := by
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 20
  rw [hp]
  rcases hk with rfl|rfl
  all_goals
    norm_num only [BitVec.toNat_ofInt]
    rw [Nat.or_comm]
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 17592183947264
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 18446741874686296064=18446741874686296064 by decide,←ho]
    omega_using []
  · have ho := Nat.shiftLeft_add_eq_or_of_lt (by exact ha : x.toNat%1048576<2^20) 13194139533312
    norm_num only [Nat.shiftLeft_eq] at ho
    rw [show Int.toNat 13835058055282163712=13835058055282163712 by decide,←ho]
    omega_using []


def encodeCode : List Instr :=
  [.movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x4 .x2 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 65024 2,
   .movk .x .x28 65535 3,
   .logic .orr .x .x4 .x4 .x28,
   .movz .x .x28 65535 0,
   .movk .x .x28 15 1,
   .logic .and .x .x5 .x3 .x28,
   .movz .x .x28 0 0,
   .movk .x .x28 49152 3,
   .logic .orr .x .x5 .x5 .x28]

theorem encodeCode_ok (s : State) :
    WP isa (.block encodeCode) s fun t =>
      t.gpr .x4=BitVec.ofInt 64 (((s.gpr .x2).toNat%2^20 : Nat)-(2^41 : Int)) ∧
      t.gpr .x5=BitVec.ofInt 64 (((s.gpr .x3).toNat%2^20 : Nat)-(2^62 : Int)) ∧
      Keeps [.x4,.x5,.x28] s t := by
  apply WP.of_runBlock
  simp only [encodeCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (16*2:Nat)<Size.x.bits by decide,
    show (16*3:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change ((s.gpr .x2 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^41)))=_
    exact encode_row _ (Or.inl rfl)
  · change ((s.gpr .x3 &&& 0xfffff) ||| BitVec.ofInt 64 (-(2^62)))=_
    exact encode_row _ (Or.inr rfl)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h4,h5,h28⟩ := hr
    simp only [RegUpd.gpr_write,h4,h5,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Rounds`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Round`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Step`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Update before halving the second packed row. The incoming zero flag is its parity. -/
def updateStep : List Instr :=
  [.cselc .x .x6 .x4 .x27 .ne,.ccmp .x .x1 0 8 .ne,
   .csneg .x .x1 .x1 .x1 .lt,.csneg .x .x6 .x6 .x6 .lt,
   .cselc .x .x4 .x5 .x4 .ge,.add .x .x5 .x5 .x6,.addImm .x .x1 .x1 2]

def halfStep : List Instr :=
  [.lsr .x .x26 .x5 63,.sub .x .x26 .x27 .x26,.extr .x .x5 .x26 .x5 1]

def roundStep : List Instr := updateStep ++ [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem updateStep_run (s : State) (h27 : s.gpr .x27=0) {odd neg : Bool}
    (hz : s.zf = !odd) (hn : (s.gpr .x1).msb=neg) :
    WP isa (.block updateStep) s fun t =>
      t.gpr .x1=(if odd && !neg then -s.gpr .x1+2 else s.gpr .x1+2) ∧
      t.gpr .x4=(if odd && !neg then s.gpr .x5 else s.gpr .x4) ∧
      t.gpr .x5=s.gpr .x5+(if odd then (if neg then s.gpr .x4 else -s.gpr .x4) else 0) ∧
      Keeps [.x1,.x4,.x5,.x6] s t := by
  apply WP.of_runBlock
  have hadd (x : BitVec 64) : x + 18446744073709551615#64 + 1#64 = x := by
    rw [BitVec.add_assoc,show 18446744073709551615#64 + 1#64 = 0 by decide]
    exact BitVec.add_zero x
  have hflag : (s.gpr .x1 + BitVec.allOnes Size.x.bits + 1#Size.x.bits).msb = neg := by
    change (s.gpr .x1 + 18446744073709551615#64 + 1#64).msb=neg
    rw [hadd]
    exact hn
  cases odd <;> cases neg <;>
  · simp only [updateStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
      RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,exists_eq_left',and_self,
      h27,hz,CondCode.holds,State.flagsAdd,toInt_not0,int_m1p1,
      RegUpd.nf_write,RegUpd.zf_write,RegUpd.vf_write,Bool.not_true,Bool.not_false,
      Bool.bne_false,Bool.and_true,Bool.and_false,
      Bool.toNat_true,Int.natCast_one,show (2:Nat)<4096 by decide,
      show (0:Nat)<32 ∧ (8:Nat)<16 by decide,
      show Nat.testBit 8 3=true by decide,show Nat.testBit 8 0=false by decide,
      Bool.false_eq_true]
    refine ⟨?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
    · simp [hflag]
    · simp [hflag]
    · simp [hflag]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      obtain ⟨h1,h4,h5,h6⟩ := hr
      simp only [RegUpd.gpr_write,h1,h4,h5,h6,↓reduceIte]


theorem halfStep_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block halfStep) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧ t.zf=s.zf ∧
      Keeps [.x5,.x26] s t := by
  apply WP.of_runBlock
  simp only [halfStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  refine ⟨?_,rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,↓reduceIte]


def testHalf : List Instr := [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem testHalf_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block testHalf) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧
      t.zf=decide (t.gpr .x5 &&& 1 = 0) ∧ Keeps [.x5,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [testHalf,halfStep,List.cons_append,List.nil_append,
    runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show (16*0:Nat)<Size.x.bits by decide,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    RegUpd.zf_write,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  have he : ((s.gpr .x27-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 := by
    rw [h27,show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simpa only [h27] using he
  · rw [show (((0 : BitVec 64)-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 by simpa only [h27] using he]
    simp only [half_parity]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Bounds`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG.Proof.Divstep

/-- Packed initial rows and all their successors fit signed63 bits. -/
def rowBounds (t : MSt) : Prop :=
  -(2^62)≤t.f ∧ t.f<2^62 ∧ -(2^62)≤t.g ∧ t.g<2^62

theorem rowBounds_step {t : MSt} (h : rowBounds t) : rowBounds (mstep t) := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  unfold rowBounds mstep
  split
  · simp only
    omega_using [hf, hf', hg, hg']
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,Int.zero_mul,Int.add_zero]
      omega_using [hf, hf', hg, hg']
    · simp only [ho,one_mul]
      omega_using [hf, hf', hg, hg']

theorem rowBounds_steps {t : MSt} (h : rowBounds t) (n : Nat) : rowBounds (msteps n t) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [msteps_succ]; exact rowBounds_step ih

theorem packed_initial_bounds (d : Int) {a b : Nat} (ha : a<2^20) (hb : b<2^20) :
    rowBounds (MSt.init d ((a:Int)-2^41) ((b:Int)-2^62)) := by
  unfold rowBounds MSt.init
  simp only at *
  omega_using [ha, hb]

/-- The unhalved second row is still a representable signed64-bit integer. -/
theorem row_numerator_bound {t : MSt} (h : rowBounds t) :
    let z := if 0≤t.d ∧ t.g%2=1 then t.g - t.f else t.g + t.g%2*t.f;
    -(2^63)≤z ∧ z<2^63 := by
  rcases h with ⟨hf,hf',hg,hg'⟩
  dsimp only
  split
  · omega_using [hf, hf', hg, hg']
  · rcases Int.emod_two_eq_zero_or_one t.g with hz|ho
    · simp only [hz,Int.zero_mul,Int.add_zero]
      omega_using [hg, hg']
    · simp only [ho,one_mul]
      omega_using [hf, hf', hg, hg']

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

structure RowState (t : MSt) (s : State) : Prop where
  d : s.gpr .x1=BitVec.ofInt 64 t.d
  f : s.gpr .x4=BitVec.ofInt 64 t.f
  g : s.gpr .x5=BitVec.ofInt 64 t.g
  zero : s.gpr .x27=0
  parity : s.zf=decide (t.g%2=0)

def numerator (t : MSt) : Int :=
  if 0≤t.d ∧ t.g%2=1 then t.g-t.f else t.g+t.g%2*t.f

theorem updateStep_int {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) :
    WP isa (.block updateStep) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (numerator t) ∧ Keeps [.x1,.x4,.x5,.x6] s a := by
  have hz : s.zf = !decide (t.g%2=1) := by
    rw [hs.parity]
    rcases Int.emod_two_eq_zero_or_one t.g with h|h <;> simp [h]
  have hn : (s.gpr .x1).msb=decide (t.d<0) := by rw [hs.d]; exact msb_ofInt hd
  refine WP.mono (updateStep_run s hs.zero hz hn) fun a ⟨ad,af,ag,hk⟩ => ?_
  rw [hs.d] at ad
  rw [hs.f,hs.g] at af
  rw [hs.f,hs.g] at ag
  have e2 : BitVec.ofInt 64 2=(2 : BitVec 64) := by decide
  by_cases hg : t.g%2=1
  · by_cases hd0 : 0≤t.d
    · have hn0 : ¬t.d<0 := by omega_using [hd0]
      simp only [hg,hn0,decide_true,decide_false,Bool.not_false,
        Bool.and_true,Bool.false_eq_true,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,and_self,↓reduceIte]
      refine ⟨?_,af,?_,hk⟩
      · rw [show (2-t.d:Int)= -t.d+2 by omega_using [],BitVec.ofInt_add,BitVec.ofInt_neg,e2]
        exact ad
      · rw [ofInt_sub']
        simpa only [BitVec.sub_eq_add_neg] using ag
    · have hdn : t.d<0 := by omega_using [hd0]
      simp only [hg,hdn,decide_true,Bool.not_true,Bool.and_false,↓reduceIte] at ad af ag
      simp only [mstep,numerator,hg,hd0,false_and,↓reduceIte,one_mul]
      refine ⟨?_,af,?_,hk⟩
      · rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad
      · rw [BitVec.ofInt_add]; exact ag
  · have hg0 : t.g%2=0 := by omega_using [hg]
    simp only [hg,decide_false,Bool.false_and,Bool.false_eq_true,↓reduceIte,add_zero] at ad af ag
    simp only [mstep,numerator,hg0,show ¬(0:Int)=1 by decide,and_false,↓reduceIte,zero_mul,add_zero]
    refine ⟨?_,af,ag,hk⟩
    rw [BitVec.ofInt_add,e2,BitVec.add_comm]; exact ad


theorem numerator_half (t : MSt) : numerator t / 2 = (mstep t).g := by
  unfold numerator mstep
  split <;> rfl

theorem roundStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block roundStep) s fun a => RowState (mstep t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  have he : roundStep=updateStep++testHalf := by
    simp only [roundStep,testHalf,List.append_assoc]
  rw [he,WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (testHalf_run a a27) fun b ⟨bg,bz,kb⟩ => ?_
  have bg' : b.gpr .x5=BitVec.ofInt 64 (mstep t).g := by
    have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t / 2)=_
    rw [numerator_half]
  refine ⟨⟨?_,?_,bg',?_,?_⟩,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact a27
  · rw [bz,bg']
    simp only [ofInt_parity]

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def rounds : Nat → List Instr
  | 0 => []
  | n+1 => roundStep++rounds n

theorem rounds_ok {t : MSt} {s : State} (hs : RowState t s) (hb : rowBounds t)
    (n : Nat) (hd : |t.d|+2*n<2^62) :
    WP isa (.block (rounds n)) s fun a => RowState (msteps n t) a ∧
      Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  induction n generalizing t s with
  | zero =>
    exact WP.block_nil ⟨hs,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | succ n ih =>
    rw [rounds,WP.block_append_iff]
    have hdr : -(2^63)≤t.d ∧ t.d<2^63 := by
      have := le_abs_self t.d
      have := neg_abs_le t.d
      omega_arith
    refine WP.mono (roundStep_ok hs hdr hb) fun a ⟨ha,ka⟩ => ?_
    have hdn : |(mstep t).d|+2*n<2^62 := by
      have h := mstep_d t
      norm_num only [Nat.cast_add,Nat.cast_one] at hd
      omega_using [h, hd]
    refine WP.mono (ih ha (rowBounds_step hb) hdn) fun b ⟨hb,kb⟩ => ?_
    exact ⟨hb,ka.trans kb⟩

/-- The last half does not need to prepare parity for another step. -/
theorem lastStep_ok {t : MSt} {s : State} (hs : RowState t s)
    (hd : -(2^63)≤t.d ∧ t.d<2^63) (hb : rowBounds t) :
    WP isa (.block (updateStep++halfStep)) s fun a =>
      a.gpr .x1=BitVec.ofInt 64 (mstep t).d ∧
      a.gpr .x4=BitVec.ofInt 64 (mstep t).f ∧
      a.gpr .x5=BitVec.ofInt 64 (mstep t).g ∧
      a.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s a := by
  rw [WP.block_append_iff]
  refine WP.mono (updateStep_int hs hd) fun a ⟨ad,af,ag,ka⟩ => ?_
  have a27 : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hs.zero
  refine WP.mono (halfStep_run a a27) fun b ⟨bg,_,kb⟩ => ?_
  refine ⟨?_,?_,?_,?_,(ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide)]; exact ad
  · rw [kb.gpr _ (by decide)]; exact af
  · have hnum : -(2^63)≤numerator t ∧ numerator t<2^63 := row_numerator_bound hb
    rw [bg,ag,signed_shift_ofInt hnum]
    change BitVec.ofInt 64 (numerator t/2)=_
    rw [numerator_half]
  · rw [kb.gpr _ (by decide)]; exact a27

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x Keeps.trans Keeps.mono)

def parityCode : List Instr := [.movz .x .x28 1 0,.tst .x .x5 .x28]

theorem parityCode_ok (s : State) :
    WP isa (.block parityCode) s fun t =>
      t.zf=decide (s.gpr .x5 &&& 1=0) ∧ Keeps [.x28] s t := by
  apply WP.of_runBlock
  simp only [parityCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide]
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [RegUpd.gpr_write,hr,↓reduceIte]

def encoded (s : State) (d : Int) : MSt :=
  MSt.init d (((s.gpr .x2).toNat%2^20:Nat)-(2^41:Int))
    (((s.gpr .x3).toNat%2^20:Nat)-(2^62:Int))

theorem encode_parity_ok (s : State) (d : Int) (hd : s.gpr .x1=BitVec.ofInt 64 d)
    (hz : s.gpr .x27=0) :
    WP isa (.block (encodeCode++parityCode)) s fun t =>
      RowState (encoded s d) t ∧ Keeps [.x4,.x5,.x28] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (encodeCode_ok s) fun a ⟨af,ag,ka⟩ => ?_
  refine WP.mono (parityCode_ok a) fun b ⟨bz,kb⟩ => ?_
  refine ⟨⟨?_,?_,?_,?_,?_⟩,ka.trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hd
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact ag
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hz
  · rw [bz,ag]; simp only [ofInt_parity]; rfl

theorem encoded_bounds (s : State) (d : Int) : rowBounds (encoded s d) :=
  packed_initial_bounds d (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

def chunkCode (n : Nat) : List Instr :=
  encodeCode++parityCode++rounds n++updateStep++halfStep

theorem chunkCode_ok (s : State) (d : Int) (n : Nat)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hbound : |d|+2*(n+1)<2^62) :
    WP isa (.block (chunkCode n)) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).d ∧
      t.gpr .x4=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).f ∧
      t.gpr .x5=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).g ∧
      t.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s t := by
  rw [chunkCode,show encodeCode++parityCode++rounds n++updateStep++halfStep=
    (encodeCode++parityCode)++rounds n++(updateStep++halfStep) by simp only [List.append_assoc],
    WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (encode_parity_ok s d hd hz) fun a ⟨ha,ka⟩ => ?_
  have hn : |(encoded s d).d|+2*n<2^62 := by
    change |d|+2*n<2^62
    norm_num only [Nat.cast_add,Nat.cast_one] at hbound
    omega_using [hbound]
  refine WP.mono (rounds_ok ha (encoded_bounds s d) n hn) fun b ⟨hb,kb⟩ => ?_
  have hd' : -(2^63)≤(msteps n (encoded s d)).d ∧
      (msteps n (encoded s d)).d<2^63 := by
    have hm := msteps_d (encoded s d) n
    have hl := neg_abs_le (msteps n (encoded s d)).d
    have hh := le_abs_self (msteps n (encoded s d)).d
    omega_using [hn, hm, hl, hh]
  refine WP.mono (lastStep_ok hb hd' (rowBounds_steps (encoded_bounds s d) n))
    fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  rw [msteps_succ]
  exact ⟨td,tf,tg,tz,((ka.mono (by decide)).trans kb).trans kt⟩

theorem encoded_cong (s : State) (d : Int) :
    (encoded s d).cong (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals
    dsimp only [encoded,MSt.init]
    norm_num
    omega_using []

theorem encoded_odd (s : State) (d : Int) (hf : (s.gpr .x2).toNat%2=1) :
    (encoded s d).f%2=1 := by
  dsimp only [encoded,MSt.init]
  norm_num
  omega_using [hf]

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.First40`, which only this module used -/

section

/-! ### `P256.EcdhInverse.ChunkMatrix`, which only this module used -/

section

/-! ### `P256.EcdhInverse.LowUpdate`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def lowUpdateA : List Instr :=
  [.mul .x .x6 .x8 .x2,
   .mul .x .x7 .x9 .x3,
   .mul .x .x2 .x10 .x2,
   .mul .x .x3 .x11 .x3,
   .add .x .x4 .x6 .x7,
   .add .x .x5 .x2 .x3,
   .lsr .x .x26 .x4 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x2 .x26 .x4 20,
   .lsr .x .x26 .x5 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x3 .x26 .x5 20]

theorem lowUpdateA_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block lowUpdateA) s fun t =>
      t.gpr .x2=(s.gpr .x8*s.gpr .x2+s.gpr .x9*s.gpr .x3).sshiftRight 20 ∧
      t.gpr .x3=(s.gpr .x10*s.gpr .x2+s.gpr .x11*s.gpr .x3).sshiftRight 20 ∧
      Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x26] s t := by
  apply WP.of_runBlock
  simp only [lowUpdateA,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (63:Nat)<Size.x.bits by decide,
    show (20:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h2,h3,h4,h5,h6,h7,h26⟩ := hr
    simp only [RegUpd.gpr_write,h2,h3,h4,h5,h6,h7,h26,↓reduceIte]

def lowUpdateB : List Instr :=
  [.mul .x .x6 .x12 .x2,
   .mul .x .x7 .x13 .x3,
   .mul .x .x2 .x14 .x2,
   .mul .x .x3 .x15 .x3,
   .add .x .x4 .x6 .x7,
   .add .x .x5 .x2 .x3,
   .lsr .x .x26 .x4 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x2 .x26 .x4 20,
   .lsr .x .x26 .x5 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x3 .x26 .x5 20]

theorem lowUpdateB_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block lowUpdateB) s fun t =>
      t.gpr .x2=(s.gpr .x12*s.gpr .x2+s.gpr .x13*s.gpr .x3).sshiftRight 20 ∧
      t.gpr .x3=(s.gpr .x14*s.gpr .x2+s.gpr .x15*s.gpr .x3).sshiftRight 20 ∧
      Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x26] s t := by
  apply WP.of_runBlock
  simp only [lowUpdateB,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (63:Nat)<Size.x.bits by decide,
    show (20:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h2,h3,h4,h5,h6,h7,h26⟩ := hr
    simp only [RegUpd.gpr_write,h2,h3,h4,h5,h6,h7,h26,↓reduceIte]

theorem shifted_lincomb (x y : BitVec 64) (u v : Int) :
    (((BitVec.ofInt 64 u*x+BitVec.ofInt 64 v*y).sshiftRight 20).toNat:Int)%2^44 =
      ((u*x.toNat+v*y.toNat)/2^20)%2^44 := by
  have hx : x=BitVec.ofInt 64 x.toNat := by simp
  have hy : y=BitVec.ofInt 64 y.toNat := by simp
  conv_lhs => rw [hx,hy,←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_add]
  exact shifted_low44 _

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def lowMatrix (s : State) (d : Int) : MSt :=
  msteps 20 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)

theorem neg_row_div {m : MSt} {f g : Int} (h : m.rel 20 f g) :
    (-m.u*f+-m.v*g)/2^20 = -m.f ∧ (-m.q*f+-m.r*g)/2^20 = -m.g := by
  obtain ⟨hf,hg⟩ := h
  have hf' : -m.u*f+-m.v*g=-(2^20*m.f) := by nlinarith only [hf]
  have hg' : -m.q*f+-m.r*g=-(2^20*m.g) := by nlinarith only [hg]
  rw [hf',hg']
  norm_num
  omega_using []

def chunk20A : List Instr := chunkCode 19++extract20a++lowUpdateA

theorem chunk20A_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+40<2^62) :
    WP isa (.block chunk20A) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix s d).d ∧
      t.gpr .x8=BitVec.ofInt 64 (-(lowMatrix s d).u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-(lowMatrix s d).v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-(lowMatrix s d).q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-(lowMatrix s d).r) ∧
      ((t.gpr .x2).toNat:Int)%2^44=(-(lowMatrix s d).f)%2^44 ∧
      ((t.gpr .x3).toNat:Int)%2^44=(-(lowMatrix s d).g)%2^44 ∧
      Keeps [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  rw [chunk20A,WP.block_append_iff,WP.block_append_iff]
  have hodd := encoded_odd s d hf
  have hcon := msteps_cong hodd (encoded_cong s d) 20 (by omega_using [])
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hcon
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 20
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 20
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 20
  refine WP.mono (chunkCode_ok s d 19 hd hz (by exact hbound)) fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  refine WP.mono (extract20a_ok t _ _ (msteps 20 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl tf tg tz) fun a ⟨au,av,aq,ar,ka⟩ => ?_
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact tz
  refine WP.mono (lowUpdateA_run a az) fun b ⟨bf,bg,kb⟩ => ?_
  have a2 : a.gpr .x2=s.gpr .x2 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have a3 : a.gpr .x3=s.gpr .x3 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have hrel := msteps_mat (d:=d) (g:=(s.gpr .x3).toNat) (show ((s.gpr .x2).toNat:Int)%2=1 by omega_using [hf]) 20
  obtain ⟨nf,ng⟩ := neg_row_div hrel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,
    ((kt.mono (by decide)).trans (ka.mono (by decide))).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide),td,cd]; rfl
  · rw [kb.gpr _ (by decide),au,cu]; rfl
  · rw [kb.gpr _ (by decide),av,cv]; rfl
  · rw [kb.gpr _ (by decide),aq,cq]; rfl
  · rw [kb.gpr _ (by decide),ar,cr]; rfl
  · rw [bf,au,av,a2,a3,cu,cv,shifted_lincomb,nf]; rfl
  · rw [bg,aq,ar,a2,a3,cq,cr,shifted_lincomb,ng]; rfl

def chunk20B : List Instr := chunkCode 19++extract20b++lowUpdateB

theorem chunk20B_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+40<2^62) :
    WP isa (.block chunk20B) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix s d).d ∧
      t.gpr .x12=BitVec.ofInt 64 (-(lowMatrix s d).u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-(lowMatrix s d).v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-(lowMatrix s d).q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-(lowMatrix s d).r) ∧
      ((t.gpr .x2).toNat:Int)%2^44=(-(lowMatrix s d).f)%2^44 ∧
      ((t.gpr .x3).toNat:Int)%2^44=(-(lowMatrix s d).g)%2^44 ∧
      Keeps [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  rw [chunk20B,WP.block_append_iff,WP.block_append_iff]
  have hodd := encoded_odd s d hf
  have hcon := msteps_cong hodd (encoded_cong s d) 20 (by omega_using [])
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hcon
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 20
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 20
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 20
  refine WP.mono (chunkCode_ok s d 19 hd hz (by exact hbound)) fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  refine WP.mono (extract20b_ok t _ _ (msteps 20 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl tf tg tz) fun a ⟨au,av,aq,ar,ka⟩ => ?_
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact tz
  refine WP.mono (lowUpdateB_run a az) fun b ⟨bf,bg,kb⟩ => ?_
  have a2 : a.gpr .x2=s.gpr .x2 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have a3 : a.gpr .x3=s.gpr .x3 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have hrel := msteps_mat (d:=d) (g:=(s.gpr .x3).toNat) (show ((s.gpr .x2).toNat:Int)%2=1 by omega_using [hf]) 20
  obtain ⟨nf,ng⟩ := neg_row_div hrel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,
    ((kt.mono (by decide)).trans (ka.mono (by decide))).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide),td,cd]; rfl
  · rw [kb.gpr _ (by decide),au,cu]; rfl
  · rw [kb.gpr _ (by decide),av,cv]; rfl
  · rw [kb.gpr _ (by decide),aq,cq]; rfl
  · rw [kb.gpr _ (by decide),ar,cr]; rfl
  · rw [bf,au,av,a2,a3,cu,cv,shifted_lincomb,nf]; rfl
  · rw [bg,aq,ar,a2,a3,cq,cr,shifted_lincomb,ng]; rfl

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def packedClob : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x26,.x28]

def first40 : List Instr := chunk20A++chunk20B

theorem first40_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+80<2^62) :
    let a := lowMatrix s d
    let b := msteps 20 (MSt.init a.d a.f a.g)
    WP isa (.block first40) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 b.d ∧
      t.gpr .x8=BitVec.ofInt 64 (-a.u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-a.v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-a.q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-a.r) ∧
      t.gpr .x12=BitVec.ofInt 64 (-b.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-b.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-b.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-b.r) ∧
      ((t.gpr .x2).toNat:Int)%2^24=b.f%2^24 ∧
      ((t.gpr .x3).toNat:Int)%2^24=b.g%2^24 ∧
      Keeps packedClob s t := by
  dsimp only
  rw [first40,WP.block_append_iff]
  refine WP.mono (chunk20A_ok s d hd hz hf (by omega_using [hbound]))
    fun a ⟨ad,au,av,aq,ar,af,ag,ka⟩ => ?_
  have hodd : (lowMatrix s d).f%2=1 :=
    msteps_f_odd (t:=MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) (by dsimp only [MSt.init]; omega_using [hf]) 20
  have haodd : (a.gpr .x2).toNat%2=1 := by norm_num at af; omega_using [hodd, af]
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hz
  have hb : |(lowMatrix s d).d|+40<2^62 := by
    have h := msteps_d (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20
    change |(lowMatrix s d).d|≤|d|+2*20 at h
    omega_using [hbound, h]
  have hc := second_input_cong (d:=(lowMatrix s d).d) hodd af ag
  obtain ⟨cd,cu,cv,cq,cr,cf,cg⟩ := hc
  refine WP.mono (chunk20B_ok a (lowMatrix s d).d ad az haodd hb)
    fun b ⟨bd,bu,bv,bq,br,bf,bg,kb⟩ => ?_
  dsimp only [MSt.negInput] at cd cu cv cq cr cf cg
  change (lowMatrix a (lowMatrix s d).d).d=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).d at cd
  change (lowMatrix a (lowMatrix s d).d).u=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).u at cu
  change (lowMatrix a (lowMatrix s d).d).v=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).v at cv
  change (lowMatrix a (lowMatrix s d).d).q=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).q at cq
  change (lowMatrix a (lowMatrix s d).d).r=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).r at cr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    (ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [bd,cd]
  · rw [kb.gpr _ (by decide)]; exact au
  · rw [kb.gpr _ (by decide)]; exact av
  · rw [kb.gpr _ (by decide)]; exact aq
  · rw [kb.gpr _ (by decide)]; exact ar
  · rw [bu,cu]
  · rw [bv,cv]
  · rw [bq,cq]
  · rw [br,cr]
  · exact second_output_cong bf cf
  · exact second_output_cong bg cg

end VG.Proof.P256.EcdhInverse

end

end

/-! ### `P256.EcdhInverse.Chunk19`, which only this module used -/

section

/-! ### `P256.EcdhInverse.Matrix`, which only this module used -/

section

/-! Fixed matrix multiplication blocks in the packed divstep batch. -/

@[expose] public section

namespace VG.Proof.P256.EcdhInverse.Matrix
open VG VG.AArch64 VG.Proof.Ed25519.AArch64

def first : List Instr :=
  [.mul .x .x2 .x12 .x8,.mul .x .x3 .x12 .x9,
   .mul .x .x6 .x14 .x8,.mul .x .x7 .x14 .x9,
   .madd .x .x8 .x13 .x10 .x2,.madd .x .x9 .x13 .x11 .x3,
   .madd .x .x16 .x15 .x10 .x6,.madd .x .x17 .x15 .x11 .x7]

theorem first_ok (s : State) : WP isa (.block first) s fun t =>
    t.gpr .x8=s.gpr .x12*s.gpr .x8+s.gpr .x13*s.gpr .x10 ∧
    t.gpr .x9=s.gpr .x12*s.gpr .x9+s.gpr .x13*s.gpr .x11 ∧
    t.gpr .x16=s.gpr .x14*s.gpr .x8+s.gpr .x15*s.gpr .x10 ∧
    t.gpr .x17=s.gpr .x14*s.gpr .x9+s.gpr .x15*s.gpr .x11 ∧
    t.nf=s.nf ∧ t.zf=s.zf ∧ t.c=s.c ∧ t.vf=s.vf ∧
    Keeps [.x2,.x3,.x6,.x7,.x8,.x9,.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [first,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def final : List Instr :=
  [.mul .x .x2 .x12 .x8,.sub .x .x2 .x27 .x2,
   .mul .x .x3 .x12 .x9,.sub .x .x3 .x27 .x3,
   .mul .x .x4 .x14 .x8,.sub .x .x4 .x27 .x4,
   .mul .x .x5 .x14 .x9,.sub .x .x5 .x27 .x5,
   .mul .x .x26 .x13 .x16,.sub .x .x10 .x2 .x26,
   .mul .x .x26 .x13 .x17,.sub .x .x11 .x3 .x26,
   .mul .x .x26 .x15 .x16,.sub .x .x12 .x4 .x26,
   .mul .x .x26 .x15 .x17,.sub .x .x13 .x5 .x26]

theorem final_ok (s : State) (h27 : s.gpr .x27=0) : WP isa (.block final) s fun t =>
    t.gpr .x10= -(s.gpr .x12*s.gpr .x8)-s.gpr .x13*s.gpr .x16 ∧
    t.gpr .x11= -(s.gpr .x12*s.gpr .x9)-s.gpr .x13*s.gpr .x17 ∧
    t.gpr .x12= -(s.gpr .x14*s.gpr .x8)-s.gpr .x15*s.gpr .x16 ∧
    t.gpr .x13= -(s.gpr .x14*s.gpr .x9)-s.gpr .x15*s.gpr .x17 ∧
    Keeps [.x2,.x3,.x4,.x5,.x10,.x11,.x12,.x13,.x26] s t := by
  apply WP.of_runBlock
  simp only [final,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left',h27,zero_sub]
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def moves : List Instr :=
  [.logic .orr .x .x4 .x10 .x10,.logic .orr .x .x5 .x11 .x11,
   .logic .orr .x .x6 .x12 .x12,.logic .orr .x .x7 .x13 .x13]

theorem moves_ok (s : State) : WP isa (.block moves) s fun t =>
    t.gpr .x4=s.gpr .x10 ∧ t.gpr .x5=s.gpr .x11 ∧
    t.gpr .x6=s.gpr .x12 ∧ t.gpr .x7=s.gpr .x13 ∧ Keeps [.x4,.x5,.x6,.x7] s t := by
  apply WP.of_runBlock
  simp only [moves,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.or_self,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps
end VG.Proof.P256.EcdhInverse.Matrix

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def matA (s : State) := s.gpr .x12*s.gpr .x8+s.gpr .x13*s.gpr .x10
def matB (s : State) := s.gpr .x12*s.gpr .x9+s.gpr .x13*s.gpr .x11
def matC (s : State) := s.gpr .x14*s.gpr .x8+s.gpr .x15*s.gpr .x10
def matD (s : State) := s.gpr .x14*s.gpr .x9+s.gpr .x15*s.gpr .x11

structure MatState (s t : State) : Prop where
  a : t.gpr .x8=matA s
  b : t.gpr .x9=matB s
  c : t.gpr .x16=matC s
  d : t.gpr .x17=matD s

theorem MatState.keep {s t u : State} {rs : List Reg} (h : MatState s t)
    (hk : Keeps rs t u) (hr : ∀r∈[Reg.x8,.x9,.x16,.x17],r∉rs) : MatState s u :=
  ⟨(hk.gpr _ (hr _ (by simp))).trans h.a,(hk.gpr _ (hr _ (by simp))).trans h.b,
   (hk.gpr _ (hr _ (by simp))).trans h.c,(hk.gpr _ (hr _ (by simp))).trans h.d⟩

def chunk19Rows : List Instr := (encodeCode++parityCode)++rounds 10++Matrix.first++
  rounds 8++(updateStep++halfStep)

def chunk19Regs : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x16,.x17,.x26,.x28]

theorem chunk19Rows_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hbound : |d|+38<2^62) :
    WP isa (.block chunk19Rows) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (msteps 19 (encoded s d)).d ∧
      t.gpr .x4=BitVec.ofInt 64 (msteps 19 (encoded s d)).f ∧
      t.gpr .x5=BitVec.ofInt 64 (msteps 19 (encoded s d)).g ∧
      t.gpr .x27=0 ∧ MatState s t ∧ Keeps chunk19Regs s t := by
  have cut : chunk19Rows=(encodeCode++parityCode)++(rounds 10++(Matrix.first++
    (rounds 8++(updateStep++halfStep)))) := by simp only [chunk19Rows,List.append_assoc]
  rw [cut]
  apply WP.block_append
  refine WP.mono (encode_parity_ok s d hd hz) fun a ⟨ha,ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (rounds_ok ha (encoded_bounds s d) 10 (by change |d|+20<2^62; omega_using [hbound]))
    fun b ⟨hb,kb⟩ => ?_
  apply WP.block_append
  refine WP.mono (Matrix.first_ok b) fun c ⟨ca,cb,cc,cd,_,cz,_,_,kc⟩ => ?_
  have hc : RowState (msteps 10 (encoded s d)) c := ⟨
    (kc.gpr _ (by decide)).trans hb.d,(kc.gpr _ (by decide)).trans hb.f,
    (kc.gpr _ (by decide)).trans hb.g,(kc.gpr _ (by decide)).trans hb.zero,cz.trans hb.parity⟩
  have hmat : MatState s c := by
    have keep (r : Reg) (hr : r∈[Reg.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]) : b.gpr r=s.gpr r :=
      ((ka.mono (by decide)).trans kb).gpr r ((show ∀r∈[Reg.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15],
        r∉[Reg.x1,.x4,.x5,.x6,.x26,.x28] by decide) r hr)
    refine ⟨?_,?_,?_,?_⟩
    all_goals simp only [matA,matB,matC,matD,ca,cb,cc,cd,keep .x8 (by simp),keep .x9 (by simp),
      keep .x10 (by simp),keep .x11 (by simp),keep .x12 (by simp),keep .x13 (by simp),
      keep .x14 (by simp),keep .x15 (by simp)]
  have h10 := msteps_d (encoded s d) 10
  have hd8 : |(msteps 10 (encoded s d)).d|+2*(8:Nat)<2^62 := by
    change |(msteps 10 (encoded s d)).d|≤|d|+2*10 at h10
    norm_num at h10 ⊢
    omega_using [hbound, h10]
  apply WP.block_append
  refine WP.mono (rounds_ok hc (rowBounds_steps (encoded_bounds s d) 10) 8 hd8)
    fun e ⟨he,ke⟩ => ?_
  have he' : RowState (msteps 18 (encoded s d)) e := by
    rw [show (18:Nat)=10+8 by decide,msteps_add]
    exact he
  have hd18 : -(2^63)≤(msteps 18 (encoded s d)).d ∧ (msteps 18 (encoded s d)).d<2^63 := by
    have h18 := msteps_d (encoded s d) 18
    change |(msteps 18 (encoded s d)).d|≤|d|+2*18 at h18
    have := neg_abs_le (msteps 18 (encoded s d)).d
    have := le_abs_self (msteps 18 (encoded s d)).d
    norm_num at h18 ⊢
    omega_arith
  refine WP.mono (lastStep_ok he' hd18 (rowBounds_steps (encoded_bounds s d) 18))
    fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  have em : mstep (msteps 18 (encoded s d))=msteps 19 (encoded s d) := (msteps_succ ..).symm
  refine ⟨em ▸ td,em ▸ tf,em ▸ tg,tz,(hmat.keep ke (by decide)).keep kt (by decide),?_⟩
  exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
    (ke.mono (by decide))).trans (kt.mono (by decide))

def lowMatrix19 (s : State) (d : Int) : MSt :=
  msteps 19 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)

def chunk19 : List Instr := chunk19Rows++extract19++Matrix.final++Matrix.moves

def chunk19AllRegs : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x26,.x28]

theorem chunk19_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+38<2^62) :
    WP isa (.block chunk19) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix19 s d).d ∧
      t.gpr .x4= -(BitVec.ofInt 64 (-(lowMatrix19 s d).u)*matA s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).v)*matC s ∧
      t.gpr .x5= -(BitVec.ofInt 64 (-(lowMatrix19 s d).u)*matB s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).v)*matD s ∧
      t.gpr .x6= -(BitVec.ofInt 64 (-(lowMatrix19 s d).q)*matA s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).r)*matC s ∧
      t.gpr .x7= -(BitVec.ofInt 64 (-(lowMatrix19 s d).q)*matB s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).r)*matD s ∧
      Keeps chunk19AllRegs s t := by
  rw [chunk19]
  simp only [List.append_assoc]
  apply WP.block_append
  have hodd := encoded_odd s d hf
  have hc := msteps_cong hodd (encoded_cong s d) 19 (by omega_using [])
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hc
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 19
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 19
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 19
  refine WP.mono (chunk19Rows_ok s d hd hz hbound) fun a ⟨ad,af,ag,az,am,ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (extract19_ok a _ _ (msteps 19 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl af ag az) fun b ⟨bu,bv,bq,br,kb⟩ => ?_
  have bm := am.keep kb (by decide)
  have bz : b.gpr .x27=0 := (kb.gpr _ (by decide)).trans az
  apply WP.block_append
  refine WP.mono (Matrix.final_ok b bz) fun c ⟨c10,c11,c12,c13,kc⟩ => ?_
  refine WP.mono (Matrix.moves_ok c) fun t ⟨t4,t5,t6,t7,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,(((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ad,cd]
    rfl
  · rw [t4,c10,bu,bv,bm.a,bm.c,cu,cv]; rfl
  · rw [t5,c11,bu,bv,bm.b,bm.d,cu,cv]; rfl
  · rw [t6,c12,bq,br,bm.a,bm.c,cq,cr]; rfl
  · rw [t7,c13,bq,br,bm.b,bm.d,cq,cr]; rfl

end VG.Proof.P256.EcdhInverse

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

theorem packed_eq : Impl.P256.EcdhInverse.packed=first40++chunk19 := by decide +kernel

theorem negative_pair (a b c d : Int) :
    BitVec.ofInt 64 (-a)*BitVec.ofInt 64 (-b)+BitVec.ofInt 64 (-c)*BitVec.ofInt 64 (-d)=
      BitVec.ofInt 64 (a*b+c*d) := by
  rw [←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_add]
  apply congrArg (BitVec.ofInt 64)
  ring

theorem negative_product (a b c d : Int) :
    -(BitVec.ofInt 64 (-a)*BitVec.ofInt 64 b)-BitVec.ofInt 64 (-c)*BitVec.ofInt 64 d=
      BitVec.ofInt 64 (a*b+c*d) := by
  rw [←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_neg,←ofInt_sub']
  apply congrArg (BitVec.ofInt 64)
  ring

theorem packed_low_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+118<2^62) :
    let m := msteps 59 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)
    WP isa (.block Impl.P256.EcdhInverse.packed) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 m.d ∧
      t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧
      t.gpr .x6=BitVec.ofInt 64 m.q ∧
      t.gpr .x7=BitVec.ofInt 64 m.r ∧ Keeps packedClob s t := by
  let a := lowMatrix s d
  let b := msteps 20 (MSt.init a.d a.f a.g)
  let c := msteps 19 (MSt.init b.d b.f b.g)
  have hfull := matrix59 d (s.gpr .x2).toNat (s.gpr .x3).toNat
  change msteps 59 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)=
    ⟨c.d,c.f,c.g,c.u*(b.u*a.u+b.v*a.q)+c.v*(b.q*a.u+b.r*a.q),
      c.u*(b.u*a.v+b.v*a.r)+c.v*(b.q*a.v+b.r*a.r),
      c.q*(b.u*a.u+b.v*a.q)+c.r*(b.q*a.u+b.r*a.q),
      c.q*(b.u*a.v+b.v*a.r)+c.r*(b.q*a.v+b.r*a.r)⟩ at hfull
  dsimp only
  rw [hfull,packed_eq,WP.block_append_iff]
  have haodd : a.f%2=1 := msteps_f_odd
    (t:=MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) (by dsimp only [MSt.init]; omega_arith) 20
  have hbodd : b.f%2=1 := msteps_f_odd (t:=MSt.init a.d a.f a.g) haodd 20
  have hbd : |b.d|+38<2^62 := by
    have ha := msteps_d (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20
    have hb := msteps_d (MSt.init a.d a.f a.g) 20
    change |a.d|≤|d|+2*20 at ha
    -- `(MSt.init a.d a.f a.g).d` is `a.d` by a lemma: matching them by `change` unfolds
    -- `a` (`msteps 20 …`) first.
    rw [show ∀ x y z, (MSt.init x y z).d = x from fun _ _ _ => rfl] at hb
    change |b.d|≤|a.d|+2*20 at hb
    omega_arith
  refine WP.mono (first40_ok s d hd hz hf (by omega_arith))
    fun t ⟨td,tu,tv,tq,tr,bu,bv,bq,br,tf,tg,kt⟩ => ?_
  have tzero : t.gpr .x27=0 := by rw [kt.gpr _ (by decide)]; exact hz
  have todd : (t.gpr .x2).toNat%2=1 := by
    change ((t.gpr .x2).toNat:Int)%2^24=b.f%2^24 at tf
    norm_num at tf
    omega_arith
  have hc := third_input_cong (d:=b.d) hbodd tf tg
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hc
  change (lowMatrix19 t b.d).d=c.d at cd
  change (lowMatrix19 t b.d).u=c.u at cu
  change (lowMatrix19 t b.d).v=c.v at cv
  change (lowMatrix19 t b.d).q=c.q at cq
  change (lowMatrix19 t b.d).r=c.r at cr
  have ma : matA t=BitVec.ofInt 64 (b.u*a.u+b.v*a.q) := by
    rw [matA,bu,tu,bv,tq]; exact negative_pair _ _ _ _
  have mb : matB t=BitVec.ofInt 64 (b.u*a.v+b.v*a.r) := by
    rw [matB,bu,tv,bv,tr]; exact negative_pair _ _ _ _
  have mc : matC t=BitVec.ofInt 64 (b.q*a.u+b.r*a.q) := by
    rw [matC,bq,tu,br,tq]; exact negative_pair _ _ _ _
  have md : matD t=BitVec.ofInt 64 (b.q*a.v+b.r*a.r) := by
    rw [matD,bq,tv,br,tr]; exact negative_pair _ _ _ _
  refine WP.mono (chunk19_ok t b.d td tzero todd hbd) fun v ⟨vd,vu,vv,vq,vr,kv⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,kt.trans (kv.mono (by decide))⟩
  · rw [vd,cd]
  · rw [vu,cu,cv,ma,mc]; exact negative_product _ _ _ _
  · rw [vv,cu,cv,mb,md]; exact negative_product _ _ _ _
  · rw [vq,cq,cr,ma,mc]; exact negative_product _ _ _ _
  · rw [vr,cq,cr,mb,md]; exact negative_product _ _ _ _

theorem packed_ok (s : State) (d f g : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d)
    (hfword : s.gpr .x2=BitVec.ofInt 64 f) (hgword : s.gpr .x3=BitVec.ofInt 64 g)
    (hz : s.gpr .x27=0) (hfodd : f%2=1) (hbound : |d|+118<2^62) :
    let m := msteps 59 (MSt.init d f g)
    WP isa (.block Impl.P256.EcdhInverse.packed) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 m.d ∧ t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧ t.gpr .x6=BitVec.ofInt 64 m.q ∧
      t.gpr .x7=BitVec.ofInt 64 m.r ∧ Keeps packedClob s t := by
  have hf : ((s.gpr .x2).toNat:Int)%2^64=f%2^64 := by
    rw [hfword,toNat_ofInt64,Int.emod_emod]
  have hg : ((s.gpr .x3).toNat:Int)%2^64=g%2^64 := by
    rw [hgword,toNat_ofInt64,Int.emod_emod]
  have ho : (s.gpr .x2).toNat%2=1 := by norm_num at hf; omega_arith
  have hc : (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat).cong (MSt.init d f g) 64 :=
    ⟨rfl,rfl,rfl,rfl,rfl,hf,hg⟩
  have h := msteps_cong (show ((s.gpr .x2).toNat:Int)%2=1 by omega_arith) hc 59 (by decide)
  obtain ⟨ed,eu,ev,eq,er,_,_⟩ := h
  refine WP.mono (packed_low_ok s d hd hz ho hbound) fun t ⟨td,tu,tv,tq,tr,kt⟩ => ?_
  exact ⟨td.trans (congrArg (BitVec.ofInt 64) ed),tu.trans (congrArg (BitVec.ofInt 64) eu),
    tv.trans (congrArg (BitVec.ofInt 64) ev),tq.trans (congrArg (BitVec.ofInt 64) eq),
    tr.trans (congrArg (BitVec.ofInt 64) er),kt⟩

end VG.Proof.P256.EcdhInverse
