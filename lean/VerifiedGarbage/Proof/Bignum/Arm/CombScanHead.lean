module

import VerifiedGarbage.Proof.Bignum.Arm.CombScanSelect
import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Framework.Block

/-! The secret equality mask leaves only public row addresses in the controls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest)

structure SelectInput (base table : BitVec 32) (len w M g N d j : Nat) (s : State) : Prop where
  p0 : s.gpr .r0=base+BitVec.ofNat 32 (arrAt w 1)
  p10 : s.gpr .r10=base+BitVec.ofNat 32 (arrAt w 1)
  p12 : s.gpr .r12=table+BitVec.ofNat 32 (8*w*j)
  count : s.gpr .lr=BitVec.ofNat 32 (2*w)
  bit : (s.gpr .r11).toNat≤1
  source : ∃ s0, Inv base table len w M g N d j s0 ∧ s.mem=s0.mem ∧ Rest roundClobbers s0 s

theorem head_ok (s : State) {base table : BitVec 32} {len w M g N d j : Nat}
    (h : Inv base table len w M g N d j s) (hj : j<32) :
    WP isa (.block (scanBit++scanArgs)) s (SelectInput base table len w M g N d j) := by
  apply WP.block_append_iff.mpr
  refine WP.mono (bit_ok s h.ready h.digitLt hj h.digit h.index) ?_
  rintro u ⟨bit,memU,restU⟩
  have readyU := h.ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  refine WP.mono (args_ok u (entryPtr:=table+BitVec.ofNat 32 (8*w*j)) readyU (by rw [memU]; exact h.entry)) ?_
  rintro v ⟨p0,p10,p12,count,memV,restV⟩
  refine ⟨p0,p10,p12,count,?_,s,h,memV.trans memU,(rest_round restU).trans (rest_round restV)⟩
  rw [restV.gpr .r11 (by simp),bit]
  split <;> decide

theorem selection_ready (s : State) {base table : BitVec 32} {len w M g N d j : Nat}
    (h : SelectInput base table len w M g N d j s) (hj : j<32) :
    WP isa (.seq selectRow (.block [.ldrSp .r0 0])) s fun t => t.gpr .r0=base := by
  obtain ⟨p0,p10,p12,count,bit,s0,input,mem,rest⟩ := h
  exact WP.mono (select_ok s input.ready input.table input.separate mem rest hj p0 p10 p12 count bit)
    fun _ h => h.1.ptr

end VG.Proof.Bignum.Arm.CombScan
