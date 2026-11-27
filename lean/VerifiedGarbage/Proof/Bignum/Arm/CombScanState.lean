module

import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
public import VerifiedGarbage.Impl.Bignum.Arm.Select
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.SelectReadBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Bignum.Arm.CombScanSelect`, which this module and modules that import it used -/

section

/-! The ordinary RSA selector reads one dense, external comb row. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SelectReadRow.lean`, which only this module imported.
section

/-! A masked row reuses the RSA selector with an external read-only source. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem selectReadRow_ok (s : State) {dst src : BitVec 32} {n : Nat}
    (ctx : SelectReadCtx s dst src n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = dst) (hp10 : s.gpr .r10 = dst) (hp12 : s.gpr .r12 = src)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectRow s (SelectReadInv s dst src n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectReadInv s dst src n i t
  rw [selectRow, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (selectReadBody_ok ctx hi (by omega) hc) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa using
        (keep.regs .r0 (by simp)).trans hp0
    · simpa using
        (keep.regs .r10 (by simp)).trans hp10
    · simpa using
        (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; exact Frame.refl _ _
    · simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem val32_rebase (m : Mem) (base : Addr) (a b k : Nat) :
    val32 m (off base a) b k=val32 m base (a+b) k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    simp only [val32,w32,Offset.add_add,ih,Nat.add_assoc]

theorem frame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨off base o,n⟩] m m') (hn : o+n<2^64) : Outside base o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  change (x-off base o).toNat+1≤n at hc
  simp only [off] at hc
  have hi := (Offset.lt_iff x base (d:=o) (n:=n) (by omega_using [hn])).mp (by omega_using [hc])
  change (x-base).toNat<o ∨ o+n≤(x-base).toNat at hx
  omega_using [hi, hx]

theorem select_ok (s : State) {s0 : State} {base table : BitVec 32} {len w M g N j : Nat}
    (h : ArithmeticReady base len w s0) (tableReady : CombTable table w M g N s0)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (mem : s.mem=s0.mem) (rest : Rest roundClobbers s0 s) (hj : j<32)
    (p0 : s.gpr .r0=base+BitVec.ofNat 32 (arrAt w 1))
    (p10 : s.gpr .r10=base+BitVec.ofNat 32 (arrAt w 1))
    (p12 : s.gpr .r12=table+BitVec.ofNat 32 (8*w*j))
    (count : s.gpr .lr=BitVec.ofNat 32 (2*w)) (bit : (s.gpr .r11).toNat≤1) :
    WP isa (.seq selectRow (.block [.ldrSp .r0 0])) s fun t =>
      ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 1=(if (s.gpr .r11).toNat=0 then
        numAt s0.mem (State.addr base) w 1 else
        Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent N j) M*2^(64*w)%M) ∧
      Outside (State.addr base) (arrAt w 1) (8*w) s0.mem t.mem ∧
      Keeps (State.addr base) len w 1 s0.mem t.mem ∧
      Frame [⟨State.addr base,8*len⟩] s0.mem t.mem ∧ Rest roundClobbers s0 t := by
  have fits : arrAt w 8≤8*len := h.width ▸ h.layout.2.2.1
  have arrayFits : arrAt w 1+8*w≤8*len := by have := array_end_le (w:=w) (show 1<8 by decide); omega_using [fits, this]
  have entryFits : 8*w*j+8*w≤32*(8*w) := by
    have bound := Nat.mul_le_mul_left (8*w) (show j+1≤32 by omega_using [hj])
    simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_comm (8*w) 32] using bound
  let dst := base+BitVec.ofNat 32 (arrAt w 1)
  let src := table+BitVec.ofNat 32 (8*w*j)
  have dstAddr : State.addr dst=off (State.addr base) (arrAt w 1) := addr_add (by have := h.workspace.nowrap; have := tableReady.positive; omega_arith)
  have srcAddr : State.addr src=off (State.addr table) (8*w*j) := addr_add (by have := tableReady.fits; have := tableReady.positive; omega_arith)
  have dstVal : dst.toNat=base.toNat+arrAt w 1 := by
    simp only [dst,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := h.workspace.nowrap; have := tableReady.positive; omega_arith),
      Nat.mod_eq_of_lt (by have := h.workspace.nowrap; have := tableReady.positive; omega_arith)]
  have srcVal : src.toNat=table.toNat+8*w*j := by
    simp only [src,BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := tableReady.fits; have := tableReady.positive; omega_arith),
      Nat.mod_eq_of_lt (by have := tableReady.fits; have := tableReady.positive; omega_arith)]
  have ctx : SelectReadCtx s dst src (2*w) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [dstVal]; have := h.workspace.nowrap; omega_using [arrayFits, this]
    · rw [srcVal]; have := tableReady.fits; omega_using [entryFits, this]
    · have := h.workspace.nowrap; have := tableReady.fits; omega_using [this]
    · rw [dstAddr,rest.wr]
      exact ⟨_,h.workspace.writable,Offset.contains_base _ (by omega_using [arrayFits]) (by have := h.workspace.nowrap; omega_using [dstVal])⟩
    · rw [srcAddr,rest.rd,rest.wr]
      exact VG.CallLay.inRegions_sub tableReady.readable (by omega_using [entryFits]) (by have := tableReady.fits; omega_using [this])
    · rw [srcAddr,dstAddr]
      exact (separate.sub_left (Offset.sub_base _ (by omega_using [entryFits]))).sub_right (Offset.sub_base _ (by omega_using [arrayFits] : arrAt w 1+4*(2*w)≤8*len))
  rw [WP.seq_iff]
  refine WP.mono (selectReadRow_ok s ctx (by have := tableReady.positive; omega_using [this]) p0 p10 p12 count bit) ?_
  intro v inv
  have value := inv.value
  simp only [dstAddr,srcAddr,val32_rebase,Nat.add_zero,mem] at value
  rw [←numAt_native,←numAt_native,tableReady.values j hj] at value
  have narrow : Frame [⟨off (State.addr base) (arrAt w 1),8*w⟩] s0.mem v.mem := by
    simpa only [dstAddr,show 4*(2*w)=8*w by omega_using [],mem] using inv.frame
  have outside := frame_outside narrow (by have := h.workspace.nowrap; omega_using [arrayFits, this])
  have frame := outside_workspace outside arrayFits
  have keeps := outside_array_keeps outside (by have := h.workspace.nowrap; omega_using [this] : 8*len<2^64)
  have restV : Rest roundClobbers s0 v := rest.trans (inv.rest.mono (by decide))
  refine WP.mono (restoreBase_ok v (by rw [restV.rd,restV.wr,restV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restV.sp)) ?_
  rintro t ⟨ptrT,memT,restT⟩
  rw [←memT] at value outside frame keeps
  have allRest := restV.trans (restT.mono (by decide))
  exact ⟨(h.after_array (by decide) keeps frame allRest ptrT).1,value,outside,keeps,frame,allRest⟩

end VG.Proof.Bignum.Arm.CombScan

end

end

/-! Scan invariants retain the table and every arithmetic array but array one. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

def HeaderKeeps (base : BitVec 32) (m m' : Mem) : Prop := ∀ d, d+4≤256 →
  (d+4≤220 ∨ 224≤d) → (d+4≤228 ∨ 232≤d) →
  m'.readW (off (State.addr base) d) 32=m.readW (off (State.addr base) d) 32

def ArrayKeeps (base : BitVec 32) (w : Nat) (m m' : Mem) : Prop := ∀ q<8, q≠1 →
  numAt m' (State.addr base) w q=numAt m (State.addr base) w q

theorem HeaderKeeps.refl (base : BitVec 32) (m : Mem) : HeaderKeeps base m m := fun _ _ _ _ => rfl

theorem HeaderKeeps.trans {base : BitVec 32} {m m' m'' : Mem}
    (h : HeaderKeeps base m m') (h' : HeaderKeeps base m' m'') : HeaderKeeps base m m'' :=
  fun d hd ha hb => (h' d hd ha hb).trans (h d hd ha hb)

theorem ArrayKeeps.refl (base : BitVec 32) (w : Nat) (m : Mem) : ArrayKeeps base w m m := fun _ _ _ => rfl

theorem ArrayKeeps.trans {base : BitVec 32} {w : Nat} {m m' m'' : Mem}
    (h : ArrayKeeps base w m m') (h' : ArrayKeeps base w m' m'') : ArrayKeeps base w m m'' :=
  fun q hq ne => (h' q hq ne).trans (h q hq ne)

theorem header_of_writes (m : Mem) (base : BitVec 32) (a b : BitVec 32) :
    HeaderKeeps base m ((m.writeW (off (State.addr base) 220) a).writeW (off (State.addr base) 228) b) := by
  intro d hd ha hb
  exact read_after_writes m base a b ha hb (by decide) (by decide) hd

theorem header_of_outside {base : BitVec 32} {w : Nat} {m m' : Mem}
    (outside : Outside (State.addr base) (arrAt w 1) (8*w) m m') : HeaderKeeps base m m' := by
  intro d hd _ _
  exact outside_read32 outside (Or.inl (by simp only [arrAt,Proof.Rsa.Mont.hdrBytes]; omega_using [hd])) (by omega_using [hd])

theorem arrays_of_outside {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (fits : arrAt w 8≤8*len) (nowrap : base.toNat+8*len≤2^32)
    (outside : Outside (State.addr base) (arrAt w 1) (8*w) m m') : ArrayKeeps base w m m' := by
  intro q hq ne
  have endQ := array_end_le (w:=w) hq
  have separate := array_sep (w:=w) ne
  rw [numAt_native,numAt_native]
  exact outside.val32 (by omega_using [separate]) (by omega_using [fits, nowrap, endQ])

theorem arrays_of_ctl {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (fits : arrAt w 8≤8*len) (nowrap : base.toNat+8*len≤2^32)
    (ctl : CtlOnly base m m') : ArrayKeeps base w m m' := by
  intro q hq _
  exact ctl_num (len:=len) ctl (Nat.le_trans (arrAt_le (by omega_using [hq])) fits) nowrap

theorem table_after_frame {base table : BitVec 32} {len w M g N : Nat} {s t : State} {rs : List Reg}
    (h : CombTable table w M g N s)
    (separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩)
    (frame : Frame [⟨State.addr base,8*len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CombTable table w M g N t := by
  refine ⟨h.positive,h.fits,?_,?_⟩
  · rw [rest.rd,rest.wr]; exact h.readable
  · intro digit hd
    rw [←h.values digit hd]
    apply val32_congr
    intro j hj
    have efit : 8*w*digit+8*w≤32*(8*w) := by
      have bound := Nat.mul_le_mul_left (8*w) (show digit+1≤32 by omega_using [hd])
      simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_comm (8*w) 32] using bound
    apply congrArg BitVec.toNat
    exact frame.readW (r:=⟨State.addr table,32*(8*w)⟩)
      (Offset.contains_base _ (by omega_using [hj, efit]) (by have := h.fits; omega_using [hj, efit, this]))
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)

structure Inv (base tablePtr : BitVec 32) (len w M g N d j : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  table : CombTable tablePtr w M g N s
  separate : Region.Disjoint ⟨State.addr tablePtr,32*(8*w)⟩ ⟨State.addr base,8*len⟩
  digitLt : d<32
  digit : s.mem.readW (off (State.addr base) 196) 32=BitVec.ofNat 32 d
  selected : d<j → numAt s.mem (State.addr base) w 1=
    Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent N d) M*2^(64*w)%M
  entry : s.mem.readW (off (State.addr base) 220) 32=tablePtr+BitVec.ofNat 32 (8*w*j)
  index : s.mem.readW (off (State.addr base) 228) 32=BitVec.ofNat 32 j

end VG.Proof.Bignum.Arm.CombScan
