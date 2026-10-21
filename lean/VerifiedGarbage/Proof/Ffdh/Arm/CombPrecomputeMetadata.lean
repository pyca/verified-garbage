module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
import VerifiedGarbage.Proof.Ffdh.GenerationPrecomputeWidth
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.Code

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
  have cases : h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (refine withRest (c := .block bitCountStep) [.r1,.r3] ?_ (by
      intro r hr i hi
      simp only [instrs,bitCountStep,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl <;> simp [clobbers,dstOf] at * <;> grind) rfl
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
    refine WP.mono (combBitCountStep_ok u posK (by omega) maskU) ?_
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
      · rw [reg,show h-k+1=h by omega]
      · rw [maskV,last]
        rfl
    · right
      refine ⟨?_,k-1,by omega,by omega,by omega,maskV,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some true
        simp only [zeroV,show (k=1)=False by simp only [last],decide_false,Bool.not_false]
      · rw [reg,show h-k+1=h-(k-1) by omega]
  · refine ⟨positive,by omega,mask,?_,rfl,Rest.refl _ _⟩
    rw [Nat.sub_self]
    exact (BitVec.add_zero _).symm

theorem combBitCount_ok (s : State) {base : BitVec 32} {len h : Nat}
    (locals : Locals base len s) (positive : 0<h) (bound : h≤8)
    (mask : s.mem.readW (off (State.addr s.sp) 68) 32 = combLowMask h) :
    WP isa bitCount s fun t => t.gpr .r1=BitVec.ofNat 32 h ∧ t.gpr .r3=0 ∧
      t.mem=s.mem ∧ Rest [.r1,.r3] s t := by
  rw [bitCount,WP.seq_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 68) (by decide)
    (addr_add (by have := locals.space.nowrap; omega)) (locals.read (by decide)) fun u load => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun v mov => WP.block_nil ?_
  have maskV : v.gpr .r3=combLowMask h := by rw [mov.other .r3 (by decide),load.gpr,mask]
  have rest : Rest [.r1,.r3] s v := (load.rest (by simp)).trans (mov.rest (by simp))
  refine WP.mono (combBitLoop_ok v positive bound maskV) ?_
  rintro t ⟨count,zero,mem,restT⟩
  refine ⟨?_,zero,mem.trans (mov.mem.trans load.mem),rest.trans restT⟩
  rw [count,mov.gpr]
  exact BitVec.zero_add _

end VG.Proof.Ffdh.Arm
