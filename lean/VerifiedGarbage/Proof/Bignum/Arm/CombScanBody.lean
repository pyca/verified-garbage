module

public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
public import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl
import VerifiedGarbage.Proof.Bignum.Arm.CombScanSelect

/-! Every scanned row advances the public cursor and preserves the selected value. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem body_ok (s : State) {base table : BitVec 32} {len w M g N d j : Nat}
    (h : Inv base table len w M g N d j s) (hj : j<32) :
    WP isa VG.Impl.Bignum.Arm.CombScan.body s fun t =>
      Inv base table len w M g N d (j+1) t ∧ t.z=decide (j+1=32) ∧
      HeaderKeeps base s.mem t.mem ∧ ArrayKeeps base w s.mem t.mem ∧
      Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8≤8*len := h.ready.width ▸ h.ready.layout.2.2.1
  have nowrap := h.ready.workspace.nowrap
  unfold VG.Impl.Bignum.Arm.CombScan.body
  rw [WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (bit_ok s h.ready h.digitLt hj h.digit h.index) ?_
  rintro u ⟨bit,memU,restU⟩
  have readyU := h.ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  refine WP.mono (args_ok u (entryPtr:=table+BitVec.ofNat 32 (8*w*j)) readyU (by rw [memU]; exact h.entry)) ?_
  rintro v ⟨p0,p10,p12,count,memV,restV⟩
  have tableU : CombTable table w M g N u := by
    exact ⟨h.table.positive,h.table.fits,by rw [restU.rd,restU.wr]; exact h.table.readable,
      fun digit hd => by rw [memU]; exact h.table.values digit hd⟩
  have bitV : (v.gpr .r11).toNat≤1 := by
    rw [restV.gpr .r11 (by simp),bit]; split <;> decide
  rw [WP.seq_iff]
  have selection := select_ok v readyU tableU h.separate memV (rest_round restV) hj
    p0 p10 p12 count bitV
  rw [WP.seq_iff] at selection
  refine WP.mono selection fun y hy => ?_
  rw [WP.seq_iff]
  refine WP.mono hy ?_
  rintro y ⟨readyY,value,outside,_,frameY,restY⟩
  rw [restV.gpr .r11 (by simp),bit,memU] at value
  rw [memU] at outside frameY
  have allRestY := (rest_round restU).trans restY
  have tableY := table_after_frame h.table h.separate frameY allRestY
  have hdr (e : Nat) (he : e+4≤256) :
      y.mem.readW (off (State.addr base) e) 32=s.mem.readW (off (State.addr base) e) 32 :=
    outside_read32 outside (Or.inl (by simp only [arrAt,Proof.Rsa.Mont.hdrBytes]; omega)) (by omega)
  refine WP.mono (next_ok y readyY hj ((hdr 220 (by decide)).trans h.entry)
    ((hdr 228 (by decide)).trans h.index)) ?_
  rintro t ⟨memT,zero,restT⟩
  have ctl : CtlOnly base y.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have ptr : t.gpr .r0=base := (restT.gpr .r0 (by simp)).trans readyY.ptr
  obtain ⟨readyT,frameT⟩ := readyY.after_ctl ctl restT ptr
  have tableT := table_after_frame tableY h.separate frameT restT
  have headersT : HeaderKeeps base y.mem t.mem := by rw [memT]; exact header_of_writes _ _ _ _
  have arraysT := arrays_of_ctl fits nowrap ctl
  have num1 : numAt t.mem (State.addr base) w 1=numAt y.mem (State.addr base) w 1 :=
    ctl_num (len:=len) ctl (Nat.le_trans (arrAt_le (by decide : 1+1≤8)) fits) nowrap
  obtain ⟨entryT,indexT⟩ := header_after_writes y.mem base
    (table+BitVec.ofNat 32 (8*w*(j+1))) (BitVec.ofNat 32 (j+1))
  refine ⟨⟨readyT,tableT,h.separate,h.digitLt,?_,?_,by rw [memT]; exact entryT,
    by rw [memT]; exact indexT⟩,zero,(header_of_outside outside).trans headersT,
    (arrays_of_outside fits nowrap outside).trans arraysT,frameY.trans frameT,allRestY.trans (rest_round restT)⟩
  · rw [headersT 196 (by decide) (by decide) (by decide),hdr 196 (by decide)]
    exact h.digit
  · intro selected
    rw [num1,value]
    by_cases equal : d=j
    · subst d
      simp only [ite_true,show (1:BitVec 32).toNat=1 from rfl,Nat.one_ne_zero,ite_false]
    · simp only [equal,ite_false,show (0:BitVec 32).toNat=0 from rfl,ite_true]
      exact h.selected (by omega)

end VG.Proof.Bignum.Arm.CombScan
