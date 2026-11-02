module

public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
import VerifiedGarbage.Proof.Bignum.Arm.CombScanBody
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl

/-! Exactly 32 readonly rows are scanned for every secret comb digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem init_state_ok (s : State) {base table : BitVec 32} {len w M g N d : Nat}
    (h : ArithmeticReady base len w s) (tableReady : CombTable table w M g N s)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (hd : d<32) (digit : s.mem.readW (off (State.addr base) 196) 32=BitVec.ofNat 32 d)
    (saved : s.mem.readW (off (State.addr base) 232) 32=table) :
    WP isa (.block VG.Impl.Bignum.Arm.CombScan.init) s fun t =>
      Inv base table len w M g N d 0 t ∧ HeaderKeeps base s.mem t.mem ∧
      ArrayKeeps base w s.mem t.mem ∧ Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8≤8*len := h.width ▸ h.layout.2.2.1
  refine WP.mono (init_ok s h saved) ?_
  rintro t ⟨mem,rest⟩
  have ctl : CtlOnly base s.mem t.mem := by
    rw [mem]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ready,frame⟩ := h.after_ctl ctl rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  have headers : HeaderKeeps base s.mem t.mem := by rw [mem]; exact header_of_writes _ _ _ _
  obtain ⟨entry,index⟩ := header_after_writes s.mem base table (BitVec.ofNat 32 0)
  refine ⟨⟨ready,table_after_frame tableReady separate frame rest,separate,hd,?_,
    fun impossible => (Nat.not_lt_zero _ impossible).elim,?_,by rw [mem]; exact index⟩,
    headers,arrays_of_ctl fits h.workspace.nowrap ctl,frame,rest_round rest⟩
  · rw [headers 196 (by decide) (by decide) (by decide)]; exact digit
  · rw [mem]
    simpa only [Nat.mul_zero,BitVec.add_zero] using entry

theorem loop_ok (s : State) {base table : BitVec 32} {len w M g N d : Nat}
    (h : Inv base table len w M g N d 0 s) :
    WP isa (.loop VG.Impl.Bignum.Arm.CombScan.body .ne) s fun t =>
      Inv base table len w M g N d 32 t ∧ HeaderKeeps base s.mem t.mem ∧
      ArrayKeeps base w s.mem t.mem ∧ Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j+k=32 ∧ 0<k ∧ Inv base table len w M g N d j t ∧
    HeaderKeeps base s.mem t.mem ∧ ArrayKeeps base w s.mem t.mem ∧
    Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M:=isa) I ?_ 32 s ⟨0,rfl,by decide,h,HeaderKeeps.refl _ _,ArrayKeeps.refl _ _ _,Frame.refl _ _,Rest.refl _ _⟩
  intro k t current
  obtain ⟨j,total,positive,inv,headers,arrays,frame,rest⟩ := current
  refine WP.mono (body_ok t inv (by omega)) ?_
  rintro u ⟨next,zero,headersU,arraysU,frameU,restU⟩
  by_cases last : j+1=32
  · left
    refine ⟨?_,last ▸ next,headers.trans headersU,arrays.trans arraysU,frame.trans frameU,rest.trans restU⟩
    change some (!u.z)=some false
    simp only [zero,last,decide_true,Bool.not_true]
  · right
    refine ⟨?_,k-1,by omega,j+1,by omega,by omega,next,
      headers.trans headersU,arrays.trans arraysU,frame.trans frameU,rest.trans restU⟩
    change some (!u.z)=some true
    simp only [zero,decide_eq_false last,Bool.not_false]

theorem code_ok (s : State) {base table : BitVec 32} {len w M g N d : Nat}
    (h : ArithmeticReady base len w s) (tableReady : CombTable table w M g N s)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (hd : d<32) (digit : s.mem.readW (off (State.addr base) 196) 32=BitVec.ofNat 32 d)
    (saved : s.mem.readW (off (State.addr base) 232) 32=table) :
    WP isa VG.Impl.Bignum.Arm.CombScan.code s fun t =>
      ArithmeticReady base len w t ∧ CombTable table w M g N t ∧
      numAt t.mem (State.addr base) w 1=
        Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent N d) M*2^(64*w)%M ∧
      HeaderKeeps base s.mem t.mem ∧ ArrayKeeps base w s.mem t.mem ∧
      Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombScan.code
  rw [WP.seq_iff]
  refine WP.mono (init_state_ok s h tableReady separate hd digit saved) ?_
  rintro u ⟨initial,headers,arrays,frame,rest⟩
  refine WP.mono (loop_ok u initial) ?_
  rintro t ⟨final,headersT,arraysT,frameT,restT⟩
  exact ⟨final.ready,final.table,final.selected hd,headers.trans headersT,arrays.trans arraysT,
    frame.trans frameT,rest.trans restT⟩

end VG.Proof.Bignum.Arm.CombScan
