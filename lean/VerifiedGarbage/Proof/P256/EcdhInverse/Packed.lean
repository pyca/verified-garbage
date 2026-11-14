module

public import VerifiedGarbage.Impl.P256.EcdhInverse
public import VerifiedGarbage.Proof.P256.EcdhInverse.Chunk
public import VerifiedGarbage.Proof.P256.EcdhInverse.MachineExtract
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
import VerifiedGarbage.Proof.P256.EcdhInverse.Compose
import Mathlib.Tactic.NormNum.Core
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Divstep.WordBasic
import Mathlib.Tactic.Ring.RingNF
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

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
