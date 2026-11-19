module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
meta import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
meta import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth
public import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.Proof.Ffdh.Arm.Output
meta import VerifiedGarbage.Proof.Bignum.Arm.Store64
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Spec.Rsa.FixedBaseComb
meta import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth
meta import VerifiedGarbage.TCB.Code

/-! ### `Ffdh.Arm.CombPrecomputeMetadataAll`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CombPrecomputeRows`, which this module and modules that import it used -/

section

/-! Public division by five determines the exact fixed comb schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

theorem combRowsStep_ok (s : State) {m : Nat} (large : 5≤m) (fit : m<2^32)
    (value : s.gpr .r3=BitVec.ofNat 32 m) (zero : s.gpr .r2=0) :
    WP isa (.block rowsStep) s fun t =>
      (t.gpr .r3=BitVec.ofNat 32 (m-5) ∧ t.gpr .r6=s.gpr .r6+1 ∧
        t.gpr .r7=(if 5≤m-5 then 1 else 0) ∧ t.z=decide (m-5<5) ∧ t.mem=s.mem) ∧
      Rest [.r3,.r6,.r7] s t := by
  have sub : BitVec.ofNat 32 m - 5 = BitVec.ofNat 32 (m-5) := by
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) large
  have val : (BitVec.ofNat 32 (m-5)).toNat=m-5 := by
    exact Nat.mod_eq_of_lt (by omega_using [fit])
  refine withRest_all (c := .block rowsStep) [.r3,.r6,.r7] ?_ (by rfl) rfl
  unfold rowsStep
  ffrun [value,zero,sub,val]
  by_cases next : 5≤m-5
  · have last : ¬m-5<5 := by omega_using [next]
    simp only [show (5 : BitVec 32).toNat=5 from rfl,
      next,last,ite_true,decide_true,decide_false]
    decide
  · have last : m-5<5 := by omega_using [next]
    simp only [show (5 : BitVec 32).toNat=5 from rfl,
      next,last,ite_false,decide_true,decide_false]
    decide

theorem combRowsLoop_ok (s : State) {N : Nat} (positive : 0<N) (fit : N+4<2^32)
    (value : s.gpr .r3=BitVec.ofNat 32 (N+4)) (zero : s.gpr .r2=0) (start : s.gpr .r6=0) :
    WP isa (.loop (.block rowsStep) .ne) s fun t =>
      t.gpr .r6=BitVec.ofNat 32 ((N+4)/5) ∧ t.mem=s.mem ∧ Rest [.r3,.r6,.r7] s t := by
  let I := fun k t => ∃ i : Nat, 5≤k ∧ k≤N+4 ∧ k+5*i=N+4 ∧
    t.gpr .r3=BitVec.ofNat 32 k ∧ t.gpr .r6=BitVec.ofNat 32 i ∧ t.gpr .r2=0 ∧
    t.mem=s.mem ∧ Rest [.r3,.r6,.r7] s t
  refine WP.loop (M := isa) I ?_ (N+4) s ?_
  · intro k u hu
    obtain ⟨i,large,bound,parts,r3,r6,r2,memU,restU⟩ := hu
    refine WP.mono (combRowsStep_ok u large (by omega_using [fit, bound]) r3 r2) ?_
    rintro v ⟨⟨r3V,r6V,_r7V,zeroV,memV⟩,restV⟩
    have count : v.gpr .r6=BitVec.ofNat 32 (i+1) := by
      rw [r6V,r6]
      change BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
      exact (BitVec.ofNat_add _ _).symm
    by_cases last : k-5<5
    · left
      refine ⟨?_,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some false
        simp only [zeroV,last,decide_true,Bool.not_true]
      · rw [count,show i+1=(N+4)/5 by omega_using [large, parts, last]]
    · right
      refine ⟨?_,k-5,by omega_using [large],i+1,by omega_using [last],by omega_using [bound],by omega_using [large, parts],r3V,count,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some true
        simp only [zeroV,last,decide_false,Bool.not_false]
      · exact (restV.gpr .r2 (by simp)).trans r2
  · exact ⟨0,by omega_using [positive],by omega_using [],by omega_using [],value,start,zero,rfl,Rest.refl _ _⟩

theorem combRowsCount_ok (s : State) {base : BitVec 32} {len N : Nat}
    (locals : Locals base len s) (positive : 0<N) (fit : N+4<2^32)
    (value : s.gpr .r1=BitVec.ofNat 32 N) :
    WP isa rowsCount s fun t =>
      t.gpr .r6=BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N) ∧
      t.mem=s.mem.writeW (off (State.addr s.sp) 44) (BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N)) ∧
      Frame [⟨off (State.addr s.sp) 44,4⟩] s.mem t.mem ∧ Rest [.r2,.r3,.r6,.r7,.r12] s t := by
  have init : WP isa (.block [.dp .add .r3 .r1 (.imm 4),.mov .r6 (.imm 0),.mov .r2 (.imm 0)]) s fun u =>
      (u.gpr .r3=BitVec.ofNat 32 (N+4) ∧ u.gpr .r6=0 ∧ u.gpr .r2=0 ∧ u.mem=s.mem) ∧
      Rest [.r2,.r3,.r6] s u := by
    refine withRest_all (c := .block [.dp .add .r3 .r1 (.imm 4),.mov .r6 (.imm 0),.mov .r2 (.imm 0)])
      [.r2,.r3,.r6] ?_ (by rfl) rfl
    ffrun [value]
    exact (BitVec.ofNat_add N 4).symm
  rw [rowsCount,WP.seq_iff]
  refine WP.mono init ?_
  rintro u ⟨⟨r3,r6,r2,memU⟩,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (combRowsLoop_ok u positive fit r3 r2 r6) ?_
  rintro v ⟨count,memV,restV⟩
  have rest : Rest [.r2,.r3,.r6,.r7,.r12] s v :=
    (restU.mono (by simp)).trans (restV.mono (by simp))
  have equal : (N+4)/5=VG.Spec.Rsa.FixedBaseComb.rows N := by
    unfold VG.Spec.Rsa.FixedBaseComb.rows VG.Spec.Rsa.FixedBaseComb.teeth
    omega_using []
  rw [equal] at count
  refine WP.mono (localStore_ok v .r6 (locals.after rest) (by decide : 44+4≤72) (by decide)) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [rest.sp,memV,memU,count] at memT
  rw [rest.sp,memV,memU] at frameT
  exact ⟨(restT.gpr .r6 (by simp)).trans count,memT,frameT,
    rest.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CombPrecomputeMetadata`, which this module and modules that import it used -/

section

/-! Public metadata counters recover the reviewed sampling width and comb row count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

def combLowMask (h : Nat) : BitVec 32 := BitVec.ofNat 32 (2^h-1)

theorem combBitCountStep_ok (s : State) {h : Nat} (positive : 0<h) (bound : h≤8)
    (mask : s.gpr .r3 = combLowMask h) :
    WP isa (.block bitCountStep) s fun t =>
      (t.gpr .r1 = s.gpr .r1+1 ∧ t.gpr .r3 = combLowMask (h-1) ∧
      t.z = decide (h=1) ∧ t.mem=s.mem) ∧ Rest [.r1,.r3] s t := by
  have cases : h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 := by omega_using [positive, bound]
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (refine withRest_all (c := .block bitCountStep) [.r1,.r3] ?_ (by rfl) rfl
     unfold bitCountStep
     ffrun [mask,combLowMask]
     decide)

theorem combBitLoop_ok (s : State) {h : Nat} (positive : 0<h) (bound : h≤8)
    (mask : s.gpr .r3 = combLowMask h) :
    WP isa (.loop (.block bitCountStep) .ne) s fun t =>
      t.gpr .r1 = s.gpr .r1+BitVec.ofNat 32 h ∧ t.gpr .r3=0 ∧
      t.mem=s.mem ∧ Rest [.r1,.r3] s t := by
  let I := fun k t => 0<k ∧ k≤h ∧ t.gpr .r3=combLowMask k ∧
    t.gpr .r1=s.gpr .r1+BitVec.ofNat 32 (h-k) ∧ t.mem=s.mem ∧ Rest [.r1,.r3] s t
  refine WP.loop (M := isa) I ?_ h s ?_
  · intro k u hu
    obtain ⟨posK,leH,maskU,countU,memU,restU⟩ := hu
    refine WP.mono (combBitCountStep_ok u posK (by omega_using [bound, leH]) maskU) ?_
    rintro v ⟨⟨countV,maskV,zeroV,memV⟩,restV⟩
    have reg : v.gpr .r1=s.gpr .r1+BitVec.ofNat 32 (h-k+1) := by
      rw [countV,countU,BitVec.add_assoc]
      change s.gpr .r1 + (BitVec.ofNat 32 (h-k)+BitVec.ofNat 32 1)=_
      rw [← BitVec.ofNat_add]
    by_cases last : k=1
    · left
      refine ⟨?_,?_,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some false
        simp only [zeroV,last,decide_true,Bool.not_true]
      · rw [reg,show h-k+1=h by omega_using [positive, last]]
      · rw [maskV,last]
        rfl
    · right
      refine ⟨?_,k-1,by omega_using [posK],by omega_using [posK, last],by omega_using [leH],maskV,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some true
        simp only [zeroV,show (k=1)=False by simp only [last],decide_false,Bool.not_false]
      · rw [reg,show h-k+1=h-(k-1) by omega_using [posK, leH]]
  · refine ⟨positive,by omega_using [],mask,?_,rfl,Rest.refl _ _⟩
    rw [Nat.sub_self]
    exact (BitVec.add_zero _).symm

theorem combBitCount_ok (s : State) {base : BitVec 32} {len h : Nat}
    (locals : Locals base len s) (positive : 0<h) (bound : h≤8)
    (mask : s.mem.readW (off (State.addr s.sp) 68) 32 = combLowMask h) :
    WP isa bitCount s fun t => t.gpr .r1=BitVec.ofNat 32 h ∧ t.gpr .r3=0 ∧
      t.mem=s.mem ∧ Rest [.r1,.r3] s t := by
  rw [bitCount,WP.seq_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 68) (by decide)
    (addr_add (by have := locals.space.nowrap; omega_using [this])) (locals.read (by decide)) fun u load => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun v mov => WP.block_nil ?_
  have maskV : v.gpr .r3=combLowMask h := by rw [mov.other .r3 (by decide),load.gpr,mask]
  have rest : Rest [.r1,.r3] s v := (load.rest (by simp)).trans (mov.rest (by simp))
  refine WP.mono (combBitLoop_ok v positive bound maskV) ?_
  rintro t ⟨count,zero,mem,restT⟩
  refine ⟨?_,zero,mem.trans (mov.mem.trans load.mem),rest.trans restT⟩
  rw [count,mov.gpr]
  exact BitVec.zero_add _

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CombPrecomputeBitsSave`, which this module and modules that import it used -/

section

/-! Save the exact bit count recovered from its byte width and high-byte mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_lsl op2_reg dpVal)

theorem combBitsSave_ok (s : State) {base : BitVec 32} {len width h : Nat}
    (locals : Locals base len s) (positive : 0<width)
    (saved : s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 width)
    (count : s.gpr .r1=BitVec.ofNat 32 h) :
    WP isa (.block bitsSave) s fun t =>
      t.gpr .r1=BitVec.ofNat 32 (8*(width-1)+h) ∧
      t.mem=s.mem.writeW (off (State.addr s.sp) 16) (BitVec.ofNat 32 (8*(width-1)+h)) ∧
      Frame [⟨off (State.addr s.sp) 16,4⟩] s.mem t.mem ∧ Rest [.r1,.r6,.r12] s t := by
  unfold bitsSave
  refine wp_loadStack (a := off (State.addr s.sp) 20) (by decide)
    (addr_add (by have := locals.space.nowrap; omega_using [this])) (locals.read (by decide)) fun u load => ?_
  refine wp_dp (op2_imm (by decide)) fun v sub => ?_
  refine wp_mov (op2_lsl (by decide)) fun w shift => ?_
  refine wp_dp (op2_reg _ _) fun z add => ?_
  have r6 : v.gpr .r6=BitVec.ofNat 32 (width-1) := by
    rw [sub.gpr,dpVal,load.gpr,saved]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have r6Shift : w.gpr .r6=BitVec.ofNat 32 (8*(width-1)) := by
    rw [shift.gpr,r6,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (width-1) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have r1 : z.gpr .r1=BitVec.ofNat 32 (8*(width-1)+h) := by
    rw [add.gpr,dpVal,shift.other .r1 (by decide),sub.other .r1 (by decide),load.other .r1 (by decide),count,r6Shift]
    rw [← BitVec.ofNat_add,Nat.add_comm]
  have rest : Rest [.r1,.r6,.r12] s z :=
    (load.rest (by simp)).trans ((sub.rest (by simp)).trans ((shift.rest (by simp)).trans (add.rest (by simp))))
  have mem : z.mem=s.mem := add.mem.trans (shift.mem.trans (sub.mem.trans load.mem))
  refine WP.mono (localStore_ok z .r1 (locals.after rest) (by decide : 16+4≤72) (by decide)) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [rest.sp,mem,r1] at memT
  rw [rest.sp,mem] at frameT
  exact ⟨(restT.gpr .r1 (by simp)).trans r1,memT,frameT,rest.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CombPrecomputeHeader`, which only this module used -/

section

/-! Three canonical 64-bit metadata words, written by native 32-bit stores. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

private theorem outputWrite {s : State} {ctx : BitVec 32} {d : Nat}
    (h : OutputBuffer ctx 24 s) (fit : d+4≤24) :
    InRegions s.wr (off (State.addr ctx) d) 4 := by
  obtain ⟨r,hr,contains⟩ := h.writable
  refine ⟨r,hr,?_⟩
  change (off (State.addr ctx) d-r.base).toNat+4≤r.len
  have eq : off (State.addr ctx) d-r.base=(State.addr ctx-r.base)+BitVec.ofNat 64 d := by
    simp only [off,BitVec.sub_eq_add_neg]
    ac_rfl
  rw [eq,BitVec.toNat_add,BitVec.toNat_ofNat]
  have hmod := Nat.mod_le ((State.addr ctx-r.base).toNat+d%2^64) (2^64)
  change (State.addr ctx-r.base).toNat+24≤r.len at contains
  have dfit : d<2^64 := by omega_using [fit]
  rw [Nat.mod_eq_of_lt dfit] at *
  omega_using [fit, contains]

def combHeaderWord (slot d : Nat) : List Instr :=
  [.ldrSp .r1 slot] ++ VG.Impl.Bignum.Arm.store64 .r1 .r2 .r4 d

private theorem zero_high_nat {N : Nat} (fit : N<2^32) :
    ((0 : BitVec 32) ++ BitVec.ofNat 32 N)=BitVec.ofNat 64 N := by
  rw [zero_high_addr]
  apply BitVec.eq_of_toNat_eq
  simp only [State.addr,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega_using [fit]

theorem combHeaderWord_ok (s : State) {base ctx : BitVec 32} {len slot d N : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (slotFit : slot+4≤72) (dstFit : d+8≤24) (valueFit : N<2^32)
    (source : s.mem.readW (off (State.addr s.sp) slot) 32=BitVec.ofNat 32 N)
    (ptr : s.gpr .r4=ctx) (zero : s.gpr .r2=0) :
    WP isa (.block (combHeaderWord slot d)) s fun t =>
      t.mem=s.mem.writeW (off (State.addr ctx) d) (BitVec.ofNat 64 N) ∧
      Frame [⟨off (State.addr ctx) d,8⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  rw [combHeaderWord,WP.block_append_iff]
  refine WP.mono (localLoad_ok s .r1 locals slotFit) ?_
  rintro u ⟨r1,memU,restU⟩
  have ptrU : u.gpr .r4=ctx := (restU.gpr .r4 (by simp)).trans ptr
  have wsU := ws.after restU
  have highU : u.gpr .r2=0 := (restU.gpr .r2 (by simp)).trans zero
  have offset : off (State.addr ctx) d + BitVec.ofNat 64 4=off (State.addr ctx) (d+4) :=
    Offset.add_add _ _ _
  refine WP.mono (store64_ok u .r1 .r2 .r4 d (off (State.addr ctx) d) (by omega_using [dstFit])
    (by rw [ptrU]; exact addr_add (by have := ws.fits; omega_using [dstFit, this]))
    (by rw [ptrU,offset]; exact addr_add (by have := ws.fits; omega_using [dstFit, this]))
    (outputWrite wsU (by omega_using [dstFit])) (by rw [offset]; exact outputWrite wsU (by omega_using [dstFit]))) ?_
  rintro t ⟨memT,restT⟩
  rw [highU,r1,source,zero_high_nat valueFit,memU] at memT
  refine ⟨memT,?_,restU.trans (restT.mono (by simp))⟩
  rw [memT]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem combHeader_ok (s : State) {base ctx : BitVec 32} {len N width d : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (separate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr ctx,24⟩)
    (nFit : N<2^32) (wFit : width<2^32) (dFit : d<2^32)
    (savedCtx : s.mem.readW (off (State.addr s.sp) 4) 32=ctx)
    (savedN : s.mem.readW (off (State.addr s.sp) 16) 32=BitVec.ofNat 32 N)
    (savedWidth : s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 width)
    (savedRows : s.mem.readW (off (State.addr s.sp) 44) 32=BitVec.ofNat 32 d) :
    WP isa (.block header) s fun t =>
      t.mem=((s.mem.writeW (off (State.addr ctx) 0) (BitVec.ofNat 64 N)).writeW
        (off (State.addr ctx) 8) (BitVec.ofNat 64 width)).writeW
        (off (State.addr ctx) 16) (BitVec.ofNat 64 d) ∧
      Frame [⟨State.addr ctx,24⟩] s.mem t.mem ∧ Rest [.r1,.r2,.r4] s t := by
  have whole {m m' : Mem} {off0 : Nat} (fit : off0+8≤24)
      (frame : Frame [⟨off (State.addr ctx) off0,8⟩] m m') :
      Frame [⟨State.addr ctx,24⟩] m m' := by
    apply frame.sub
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ fit⟩
  have readStack {m m' : Mem} {slot : Nat} (fit : slot+4≤72)
      (frame : Frame [⟨State.addr ctx,24⟩] m m') :
      m'.readW (off (State.addr s.sp) slot) 32=m.readW (off (State.addr s.sp) slot) 32 :=
    frame.readW (r := ⟨State.addr s.sp,72⟩) (Offset.contains_base _ fit (by omega_using [fit]))
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)
  change WP isa (.block ([.ldrSp .r4 4,.mov .r2 (.imm 0)] ++
    (combHeaderWord 16 0 ++ (combHeaderWord 20 8 ++ combHeaderWord 44 16)))) s _
  rw [WP.block_append_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide)
    (addr_add (by have := locals.space.nowrap; omega_using [this])) (locals.read (by decide)) fun a load => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u move => WP.block_nil ?_
  have restU : Rest [.r1,.r2,.r4] s u := (load.rest (by simp)).trans (move.rest (by simp))
  have memU : u.mem=s.mem := move.mem.trans load.mem
  have ptrU : u.gpr .r4=ctx := (move.other .r4 (by decide)).trans (load.gpr.trans savedCtx)
  rw [WP.block_append_iff]
  refine WP.mono (combHeaderWord_ok u (locals.after restU) (ws.after restU) (by decide) (by decide) nFit
    (by rw [restU.sp,memU]; exact savedN) ptrU move.gpr) ?_
  rintro v ⟨memV,frameV,restV⟩
  have rV : Rest [.r1,.r2,.r4] s v := restU.trans (restV.mono (by simp))
  have fV : Frame [⟨State.addr ctx,24⟩] s.mem v.mem := by rw [memU] at frameV; exact whole (by decide) frameV
  have widthV : v.mem.readW (off (State.addr v.sp) 20) 32=BitVec.ofNat 32 width := by
    rw [rV.sp,readStack (by decide) fV,savedWidth]
  have ptrV : v.gpr .r4=ctx := (restV.gpr .r4 (by simp)).trans ptrU
  have zeroV : v.gpr .r2=0 := (restV.gpr .r2 (by simp)).trans move.gpr
  rw [WP.block_append_iff]
  refine WP.mono (combHeaderWord_ok v (locals.after rV) (ws.after rV) (by decide) (by decide) wFit
    widthV ptrV zeroV) ?_
  rintro w ⟨memW,frameW,restW⟩
  have rW : Rest [.r1,.r2,.r4] s w := rV.trans (restW.mono (by simp))
  have fW : Frame [⟨State.addr ctx,24⟩] s.mem w.mem := fV.trans (whole (by decide) frameW)
  have rowsW : w.mem.readW (off (State.addr w.sp) 44) 32=BitVec.ofNat 32 d := by
    rw [rW.sp,readStack (by decide) fW,savedRows]
  have ptrW : w.gpr .r4=ctx := (restW.gpr .r4 (by simp)).trans ptrV
  have zeroW : w.gpr .r2=0 := (restW.gpr .r2 (by simp)).trans zeroV
  refine WP.mono (combHeaderWord_ok w (locals.after rW) (ws.after rW) (by decide) (by decide) dFit
    rowsW ptrW zeroW) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [memW,memV,memU] at memT
  exact ⟨memT,fW.trans (whole (by decide) frameT),rW.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end


/-! The policy width becomes a canonical immutable three-word context header. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

def combMetadataWrites (s : State) (ctx : BitVec 32) : List Region :=
  [⟨off (State.addr s.sp) 16,4⟩,⟨off (State.addr s.sp) 44,4⟩,⟨State.addr ctx,24⟩]

def combMetadataClobbers : List Reg := [.r1,.r2,.r3,.r4,.r6,.r7,.r12]

theorem combMetadata_ok (s : State) {base ctx : BitVec 32} {len N : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (separate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr ctx,24⟩)
    (positive : 0<N) (bound : N≤8192)
    (savedCtx : s.mem.readW (off (State.addr s.sp) 4) 32=ctx)
    (savedWidth : s.mem.readW (off (State.addr s.sp) 20) 32=
      BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N))
    (savedMask : s.mem.readW (off (State.addr s.sp) 68) 32=
      (VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32) :
    WP isa metadata s fun t =>
      let w := VG.Proof.Ffdh.ScalarWidth.width N
      let d := VG.Spec.Rsa.FixedBaseComb.rows N
      let m := (s.mem.writeW (off (State.addr s.sp) 16) (BitVec.ofNat 32 N)).writeW
        (off (State.addr s.sp) 44) (BitVec.ofNat 32 d)
      t.mem=((m.writeW (off (State.addr ctx) 0) (BitVec.ofNat 64 N)).writeW
        (off (State.addr ctx) 8) (BitVec.ofNat 64 w)).writeW
        (off (State.addr ctx) 16) (BitVec.ofNat 64 d) ∧
      Frame (combMetadataWrites s ctx) s.mem t.mem ∧ Rest combMetadataClobbers s t := by
  let h := VG.Proof.Ffdh.ScalarWidth.headBits N
  have headPositive : 0<h := by
    dsimp [h]
    unfold VG.Proof.Ffdh.ScalarWidth.headBits VG.Proof.Ffdh.ScalarWidth.width
    omega_using [positive]
  have headBound : h≤8 := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).1
  have maskValue : (VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32=combLowMask h := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,VG.Proof.Ffdh.ScalarWidth.mask_toNat,combLowMask,BitVec.toNat_ofNat]
    rfl
  have widthPositive := VG.Proof.Ffdh.ScalarWidth.width_pos N
  have widthBound : VG.Proof.Ffdh.ScalarWidth.width N≤1024 := by
    unfold VG.Proof.Ffdh.ScalarWidth.width
    omega_using [bound]
  have rowsBound : VG.Spec.Rsa.FixedBaseComb.rows N≤1639 := by
    unfold VG.Spec.Rsa.FixedBaseComb.rows VG.Spec.Rsa.FixedBaseComb.teeth
    omega_using [bound]
  rw [metadata,WP.seq_iff]
  refine WP.mono (combBitCount_ok s locals headPositive headBound (savedMask.trans maskValue)) ?_
  rintro u ⟨countU,_zeroU,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (combBitsSave_ok u (locals.after restU) widthPositive
    (by rw [restU.sp,memU]; exact savedWidth) countU) ?_
  rintro v ⟨countV,memV,frameV,restV⟩
  have parts := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).2
  change 8*(VG.Proof.Ffdh.ScalarWidth.width N-1)+h=N at parts
  rw [parts] at countV memV
  have rV : Rest combMetadataClobbers s v :=
    (restU.mono (by simp [combMetadataClobbers])).trans (restV.mono (by simp [combMetadataClobbers]))
  rw [restU.sp,memU] at memV frameV
  rw [WP.seq_iff]
  refine WP.mono (combRowsCount_ok v (locals.after rV) positive (by omega_using [bound]) countV) ?_
  rintro w ⟨_countW,memW,frameW,restW⟩
  have rW : Rest combMetadataClobbers s w := rV.trans (restW.mono (by simp [combMetadataClobbers]))
  rw [rV.sp] at memW frameW
  have localsFrame : Frame [⟨off (State.addr s.sp) 16,4⟩,⟨off (State.addr s.sp) 44,4⟩] s.mem w.mem :=
    (frameV.mono (by simp)).trans (frameW.mono (by simp))
  have localRead (slot : Nat) (sep16 : slot+4≤16 ∨ 20≤slot) (sep44 : slot+4≤44 ∨ 48≤slot)
      (fit : slot+4≤72) :
      w.mem.readW (off (State.addr w.sp) slot) 32=s.mem.readW (off (State.addr s.sp) slot) 32 := by
    rw [rW.sp]
    apply localsFrame.readW (r := ⟨off (State.addr s.sp) slot,4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact Offset.disjoint _ sep16 (by omega_using [fit]) (by decide)
    · exact Offset.disjoint _ sep44 (by omega_using [fit]) (by decide)
  have nSaved : w.mem.readW (off (State.addr w.sp) 16) 32=BitVec.ofNat 32 N := by
    rw [rW.sp]
    rw [frameW.readW (r := ⟨off (State.addr s.sp) 16,4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r
          exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide)]
    rw [memV,Mem.readW_writeW_self32]
  have dSaved : w.mem.readW (off (State.addr w.sp) 44) 32=BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N) := by
    rw [rW.sp,memW,Mem.readW_writeW_self32]
  refine WP.mono (combHeader_ok w (locals.after rW) (ws.after rW) (by rw [rW.sp]; exact separate)
    (by omega_using [bound]) (by omega_using [widthBound]) (by omega_using [rowsBound])
    ((localRead 4 (by decide) (by decide) (by decide)).trans savedCtx) nSaved
    ((localRead 20 (by decide) (by decide) (by decide)).trans savedWidth) dSaved) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [memW,memV] at memT
  refine ⟨memT,?_,rW.trans (restT.mono (by simp [combMetadataClobbers]))⟩
  exact (localsFrame.mono (by simp [combMetadataWrites])).trans (frameT.mono (by simp [combMetadataWrites]))

end VG.Proof.Ffdh.Arm

end

end

/-! Metadata loops branch only on the public scalar width and mask. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont VG.Impl.Ffdh.Arm.CombPrecompute

private theorem loadPublic_ct {base : BitVec 32} {len d : Nat} {r : Reg} {value : BitVec 32}
    (fit : d+4≤72) :
    RelCT isa (fun s t => (Locals base len s ∧ s.mem.readW (off (State.addr s.sp) d) 32=value) ∧
      (Locals base len t ∧ t.mem.readW (off (State.addr t.sp) d) 32=value) ∧ s.sp=t.sp)
      (.block [.ldrSp r d]) (fun s t => s.gpr r=t.gpr r ∧ s.sp=t.sp) := by
  intro s t tr1 tr2 u v h e1 e2
  have leak := loadStack_ct r d _ _ _ _ _ _ h.2.2 e1 e2
  obtain ⟨_,u',run1,reg1,_⟩ := localLoad_ok s r h.1.1 fit
  obtain ⟨_,rfl⟩ := Exec.det e1 run1
  obtain ⟨_,v',run2,reg2,_⟩ := localLoad_ok t r h.2.1.1 fit
  obtain ⟨_,rfl⟩ := Exec.det e2 run2
  exact ⟨leak.1,(reg1.trans h.1.2).trans (reg2.trans h.2.1.2).symm,leak.2⟩

theorem combBitCount_ct {base : BitVec 32} {len : Nat} {mask : BitVec 32} :
    RelCT isa (fun s t => (Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 68) 32=mask) ∧
      (Locals base len t ∧ t.mem.readW (off (State.addr t.sp) 68) 32=mask) ∧ s.sp=t.sp)
      bitCount (fun _ _ => True) := by
  unfold bitCount
  -- Loading the public mask is separated from the fixed-count initialization.
  have load := loadPublic_ct (base:=base) (len:=len) (value:=mask) (r:=.r3) (d:=68) (by decide)
  have mov : RelCT isa (fun s t=>s.gpr .r3=t.gpr .r3 ∧ s.sp=t.sp)
      (.block [.mov .r1 (.imm 0)]) (fun s t=>s.gpr .r3=t.gpr .r3 ∧ s.sp=t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    have trace : RelCT isa (fun _ _=>True) (.block [.mov .r1 (.imm 0)]) (fun _ _=>True) := by
      apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _
      exact Taint.agree_ofRegs (by simp)
    exact ⟨(trace _ _ _ _ _ _ trivial e1 e2).1,
      (Exec.gpr (h:=e1) (by decide)).trans
        (h.1.trans (Exec.gpr (h:=e2) (by decide)).symm),
      (Exec.sp e1).trans (h.2.trans (Exec.sp e2).symm)⟩
  exact (RelCT.block_append (load.seq mov)).seq (by
    apply RelCT.taint (A:=taint) (Taint.ofRegs [.r3]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1)

theorem combBitsSave_ct : RelCT isa (fun s t => s.sp=t.sp) (.block bitsSave) (fun _ _ => True) := by
  have arithmetic : RelCT isa (fun s t => s.sp=t.sp)
      (.block [.dp .sub .r6 .r6 (.imm 1),.mov .r6 (.shifted .r6 .lsl 3),.dp .add .r1 .r1 (.reg .r6)])
      (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h)
    apply RelCT.taint (A:=taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  change RelCT isa _ (.block ([.ldrSp .r6 20] ++
    ([.dp .sub .r6 .r6 (.imm 1),.mov .r6 (.shifted .r6 .lsl 3),.dp .add .r1 .r1 (.reg .r6)] ++
      ([.addSp .r12 0] ++ [.str .r1 .r12 16])))) _
  exact (RelCT.block_append ((loadStack_ct .r6 20).seq
    (RelCT.block_append (arithmetic.seq (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r1 16))))))).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

theorem combRowsCount_ct :
    RelCT isa (fun s t => s.gpr .r1=t.gpr .r1 ∧ s.sp=t.sp) rowsCount (fun _ _ => True) := by
  have counter : RelCT isa (fun s t => s.gpr .r1=t.gpr .r1 ∧ s.sp=t.sp)
      (.seq (.block [.dp .add .r3 .r1 (.imm 4),.mov .r6 (.imm 0),.mov .r2 (.imm 0)])
        (.loop (.block rowsStep) .ne)) (fun s t => s.sp=t.sp) := by
    apply relCT_keep_sp _ (fun _ _ h => h.2)
    apply RelCT.taint (A:=taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  unfold rowsCount
  exact (RelCT.assoc (counter.seq (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r6 44))))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem combHeader_ct {base ctx : BitVec 32} {len : Nat} :
    RelCT isa (fun s t => (Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx) ∧
      (Locals base len t ∧ t.mem.readW (off (State.addr t.sp) 4) 32=ctx) ∧ s.sp=t.sp)
      (.block header) (fun _ _ => True) := by
  have rest : RelCT isa (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp)
      (.block [.mov .r2 (.imm 0),.ldrSp .r1 16,.str .r1 .r4 0,.str .r2 .r4 4,
        .ldrSp .r1 20,.str .r1 .r4 8,.str .r2 .r4 12,.ldrSp .r1 44,
        .str .r1 .r4 16,.str .r2 .r4 20]) (fun _ _ => True) := by
    have load (d : Nat) : RelCT isa (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp)
        (.block [.ldrSp .r1 d]) (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp) := by
      intro s t tr1 tr2 u v h e1 e2
      have leak := loadStack_ct .r1 d _ _ _ _ _ _ h.2 e1 e2
      have a := Exec.gpr (r:=.r4) (h:=e1) (hn:=Or.inl rfl) (by simp [instrs,clobbers,dstOf])
      have b := Exec.gpr (r:=.r4) (h:=e2) (hn:=Or.inl rfl) (by simp [instrs,clobbers,dstOf])
      exact ⟨leak.1,a.trans (h.1.trans b.symm),leak.2⟩
    have plain (is : List Instr) (safe : ∀ i∈is,clobbers i .r4=false)
        (checked : (taint.check (Taint.ofRegs [.r4]) (.block is) (.block [])).isSome=true) :
        RelCT isa (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp) (.block is)
          (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp) := by
      intro s t tr1 tr2 u v h e1 e2
      have trace : RelCT isa (fun s t => s.gpr .r4=t.gpr .r4) (.block is) (fun _ _=>True) := by
        apply RelCT.taint (A:=taint) (Taint.ofRegs [.r4]) _ checked
        intro s t h
        apply Taint.agree_ofRegs
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h
      exact ⟨(trace _ _ _ _ _ _ h.1 e1 e2).1,
        (Exec.gpr (r:=.r4) (h:=e1) (by simpa only [instrs] using safe)).trans (h.1.trans (Exec.gpr (r:=.r4) (h:=e2) (by simpa only [instrs] using safe)).symm),
        (Exec.sp e1).trans (h.2.trans (Exec.sp e2).symm)⟩
    have mov := plain [.mov .r2 (.imm 0)] (by decide) (by taint_decide)
    have stores (d : Nat) (hd : d=0 ∨ d=8 ∨ d=16) :
        RelCT isa (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp)
          (.block [.str .r1 .r4 d,.str .r2 .r4 (d+4)])
          (fun s t => s.gpr .r4=t.gpr .r4 ∧ s.sp=t.sp) := by
      rcases hd with rfl|rfl|rfl <;> exact plain _ (by decide) (by taint_decide)
    have last := RelCT.block_append ((load 44).seq (stores 16 (by simp)))
    have mid := RelCT.block_append ((stores 8 (by simp)).seq last)
    have mid := RelCT.block_append ((load 20).seq mid)
    have mid := RelCT.block_append ((stores 0 (by simp)).seq mid)
    have mid := RelCT.block_append ((load 16).seq mid)
    exact (RelCT.block_append (mov.seq mid)).mono (fun _ _ h=>h) (fun _ _ _=>trivial)

  change RelCT isa _ (.block ([.ldrSp .r4 4] ++ _)) _
  exact RelCT.block_append ((loadPublic_ct (by decide)).seq rest)

private theorem metadataCtx_after {s t : State} {ctx : BitVec 32} {d : Nat}
    (slot : d=16 ∨ d=44) (sp : t.sp=s.sp)
    (frame : Frame [⟨off (State.addr s.sp) d,4⟩] s.mem t.mem)
    (saved : s.mem.readW (off (State.addr s.sp) 4) 32=ctx) :
    t.mem.readW (off (State.addr t.sp) 4) 32=ctx := by
  rw [sp]
  apply Eq.trans _ saved
  apply frame.readW (r:=⟨off (State.addr s.sp) 4,4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rcases slot with rfl|rfl <;> exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem combMetadata_ct {base ctx : BitVec 32} {len N : Nat}
    (positive : 0<N) (bound : N≤8192) :
    RelCT isa (fun s t =>
      (Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx ∧
        s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N) ∧
        s.mem.readW (off (State.addr s.sp) 68) 32=(VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32) ∧
      (Locals base len t ∧ t.mem.readW (off (State.addr t.sp) 4) 32=ctx ∧
        t.mem.readW (off (State.addr t.sp) 20) 32=BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N) ∧
        t.mem.readW (off (State.addr t.sp) 68) 32=(VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32) ∧ s.sp=t.sp)
      metadata (fun _ _ => True) := by
  let h := VG.Proof.Ffdh.ScalarWidth.headBits N
  have headPositive : 0<h := by
    dsimp [h]
    unfold VG.Proof.Ffdh.ScalarWidth.headBits VG.Proof.Ffdh.ScalarWidth.width
    omega_using [positive]
  have headBound : h≤8 := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).1
  have maskValue : (VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32=combLowMask h := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,VG.Proof.Ffdh.ScalarWidth.mask_toNat,combLowMask,BitVec.toNat_ofNat]
    rfl
  let Input := fun s : State => Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx ∧
    s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N) ∧
    s.mem.readW (off (State.addr s.sp) 68) 32=(VG.Proof.Ffdh.ScalarWidth.mask N).setWidth 32
  let First := fun s : State => Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx ∧
    s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width N) ∧
    s.gpr .r1=BitVec.ofNat 32 h
  let Second := fun s : State => Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx ∧
    s.gpr .r1=BitVec.ofNat 32 N
  let Last := fun s : State => Locals base len s ∧ s.mem.readW (off (State.addr s.sp) 4) 32=ctx
  have count (s : State) (hs : Input s) : WP isa bitCount s First := by
    refine WP.mono (combBitCount_ok s hs.1 headPositive headBound (hs.2.2.2.trans maskValue)) ?_
    rintro t ⟨count,_,mem,rest⟩
    exact ⟨hs.1.after rest,by rw [rest.sp,mem];exact hs.2.1,
      by rw [rest.sp,mem];exact hs.2.2.1,count⟩
  have bits (s : State) (hs : First s) : WP isa (.block bitsSave) s Second := by
    refine WP.mono (combBitsSave_ok s hs.1 (VG.Proof.Ffdh.ScalarWidth.width_pos N) hs.2.2.1 hs.2.2.2) ?_
    rintro t ⟨count,_mem,frame,rest⟩
    have parts := (VG.Proof.Ffdh.ScalarWidth.headBits_parts N).2
    change 8*(VG.Proof.Ffdh.ScalarWidth.width N-1)+h=N at parts
    exact ⟨hs.1.after rest,metadataCtx_after (by simp) rest.sp frame hs.2.1,by rw [parts] at count;exact count⟩
  have rows (s : State) (hs : Second s) : WP isa rowsCount s Last := by
    refine WP.mono (combRowsCount_ok s hs.1 positive (by omega_using [bound]) hs.2.2) ?_
    rintro t ⟨_,_,frame,rest⟩
    exact ⟨hs.1.after rest,metadataCtx_after (by simp) rest.sp frame hs.2.1⟩
  unfold metadata
  refine relCT_chain ((combBitCount_ct (base:=base) (len:=len)).mono
    (fun _ _ hs=>⟨⟨hs.1.1,hs.1.2.2.2⟩,⟨hs.2.1.1,hs.2.1.2.2.2⟩,hs.2.2⟩) (fun _ _ hs=>hs)) count count ?_
  refine relCT_chain (combBitsSave_ct.mono (fun _ _ hs=>hs.2.2) (fun _ _ hs=>hs)) bits bits ?_
  exact relCT_chain (combRowsCount_ct.mono
    (fun _ _ hs=>⟨hs.1.2.2.trans hs.2.1.2.2.symm,hs.2.2⟩) (fun _ _ hs=>hs)) rows rows
      (combHeader_ct (base:=base) (len:=len) (ctx:=ctx))

end VG.Proof.Ffdh.Arm
