module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp
meta import VerifiedGarbage.Impl.Bignum.Arm.CombExp
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Bignum.Arm.CombScan
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Arm.CombExpArgs
public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
meta import VerifiedGarbage.Proof.Bignum.Arm.CombScan
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Impl.Bignum.Arm.CombScan
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Spec.Rsa.FixedBaseComb
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
meta import VerifiedGarbage.Proof.Rsa.FixedBaseComb
meta import VerifiedGarbage.Proof.Bignum.Arm.CombExpArgs
meta import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Ffdh.CombBitBytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
meta import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
meta import VerifiedGarbage.Proof.Bignum.Arm.CombTableState
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.CallLay
public import Init.Prelude
meta import Init.Prelude
import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.CombScanControl
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CombScanState
import VerifiedGarbage.Proof.Bignum.Arm.CombScanBody
meta import VerifiedGarbage.Proof.Bignum.Arm.CombScanBody

/-! ### `Bignum.Arm.CombScanCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CombScanHead`, which only this module used -/

section

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

end

end


/-! A full 32-entry scan has no digit-dependent addresses or branches. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm

private theorem next_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombScan.next) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private theorem init_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombScan.init) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private theorem selection_ct {base table : BitVec 32} {len w M g N d1 d2 j : Nat} :
    RelCT isa (fun s t => SelectInput base table len w M g N d1 j s ∧
      SelectInput base table len w M g N d2 j t ∧ s.sp=t.sp)
      (.seq selectRow (.block [.ldrSp .r0 0])) (fun _ _ => True) := by
  have row : RelCT isa (fun s t => SelectInput base table len w M g N d1 j s ∧
      SelectInput base table len w M g N d2 j t ∧ s.sp=t.sp) selectRow (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨selectRow_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.p0.trans h.2.1.p0.symm,h.1.p10.trans h.2.1.p10.symm,
        h.1.p12.trans h.2.1.p12.symm,h.1.count.trans h.2.1.count.symm⟩ e1 e2,trivial⟩
  exact ((relCT_keep_sp row (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_ct {base table : BitVec 32} {len w M g N d1 d2 j : Nat} (hj : j<32) :
    RelCT isa (fun s t => Inv base table len w M g N d1 j s ∧
      Inv base table len w M g N d2 j t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombScan.body (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombScan.body
  refine relCT_chain
    (scanHead_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => head_ok s h hj) (fun s h => head_ok s h hj) ?_
  apply RelCT.assoc
  exact relCT_chain selection_ct
    (fun s h => selection_ready s h hj) (fun s h => selection_ready s h hj)
    (next_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem loop_ct {base table : BitVec 32} {len w M g N d1 d2 : Nat} :
    RelCT isa (fun s t => Inv base table len w M g N d1 0 s ∧
      Inv base table len w M g N d2 0 t ∧ s.sp=t.sp)
      (.loop VG.Impl.Bignum.Arm.CombScan.body .ne) (fun _ _ => True) := by
  let I := fun k s t => ∃ j, j+k=32 ∧ 0<k ∧ Inv base table len w M g N d1 j s ∧
    Inv base table len w M g N d2 j t ∧ s.sp=t.sp
  have step : ∀ k, RelCT isa (I k) VG.Impl.Bignum.Arm.CombScan.body fun u v =>
      isa.eval .ne u=isa.eval .ne v ∧ (isa.eval .ne u=some false → True) ∧
      (isa.eval .ne u=some true → ∃ m<k, I m u v) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j,total,positive,left,right,sp⟩ := h
    obtain ⟨trace,sp'⟩ := relCT_keep_sp (body_ct (by omega_using [total, positive] : j<32)) (fun _ _ h => h.2.2)
      s t tr1 tr2 u v ⟨left,right,sp⟩ e1 e2
    obtain ⟨_,_,run1,next1,zero1,_,_,_,_⟩ := body_ok s left (by omega_using [total, positive])
    obtain ⟨_,_,run2,next2,zero2,_,_,_,_⟩ := body_ok t right (by omega_using [total, positive])
    obtain ⟨_,rfl⟩ := Exec.det e1 run1
    obtain ⟨_,rfl⟩ := Exec.det e2 run2
    refine ⟨trace,?_,fun _ => trivial,?_⟩
    · change some (!u.z)=some (!v.z)
      rw [zero1,zero2]
    · intro again
      have notLast : j+1≠32 := by
        intro last
        change some (!u.z)=some true at again
        simp only [zero1,last,decide_true,Bool.not_true,Option.some.injEq,Bool.false_eq_true] at again
      exact ⟨k-1,by omega_using [positive],j+1,by omega_using [total, positive],by omega_using [total, positive, notLast],next1,next2,sp'⟩
  exact (RelCT.loop I step 32).mono (fun _ _ h => ⟨0,rfl,by decide,h.1,h.2.1,h.2.2⟩) (fun _ _ h => h)

structure Input (base table : BitVec 32) (len w M g N digit : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  tableReady : CombTable table w M g N s
  separate : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩
  digitLt : digit<32
  digitValue : s.mem.readW (VG.Proof.Mont.off (State.addr base) 196) 32=BitVec.ofNat 32 digit
  saved : s.mem.readW (VG.Proof.Mont.off (State.addr base) 232) 32=table

theorem code_ct {base table : BitVec 32} {len w M g N d1 d2 : Nat} :
    RelCT isa (fun s t => Input base table len w M g N d1 s ∧
      Input base table len w M g N d2 t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombScan.code (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombScan.code
  exact relCT_chain
    (init_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (init_state_ok s h.ready h.tableReady h.separate h.digitLt h.digitValue h.saved) fun _ k => k.1)
    (fun s h => WP.mono (init_state_ok s h.ready h.tableReady h.separate h.digitLt h.digitValue h.saved) fun _ k => k.1)
    loop_ct

end VG.Proof.Bignum.Arm.CombScan

end

end

/-! ### `Bignum.Arm.CombExpGatherCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CombDigitCT`, which only this module used -/

section

/-! Gathering a digit addresses and branches only on public bit positions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm

/-- Exponent values remain secret; the five gather controls are public. -/
def Public (s t : State) : Prop :=
  ∀ r ∈ ([.r4,.r5,.r6,.r7,.r8] : List Reg), s.gpr r = t.gpr r

theorem code_ct : ConstantTime isa (fun _ => True) Public VG.Impl.Bignum.Arm.CombDigit.code := by
  apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r4,.r5,.r6,.r7,.r8])
  · intro s t _ _ h
    exact Taint.agree_ofRegs h
  · taint_decide

end VG.Proof.Bignum.Arm.CombDigit

end

end

/-! The five public gather controls agree for independent secret exponent bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

private theorem args_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

private def Args (source : BitVec 32) (bytes N i : Nat) (s : State) : Prop :=
  s.gpr .r4=source ∧ s.gpr .r5=BitVec.ofNat 32 bytes ∧ s.gpr .r6=BitVec.ofNat 32 i ∧
  s.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N) ∧ s.gpr .r8=BitVec.ofNat 32 N

theorem gather_ct {base source table : BitVec 32} {len w bytes N M g E1 E2 i : Nat}
    {P1 P2 : State→Prop} (fits : i+1<2^32) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i P1 s ∧
      RowInput base source table len w bytes N M g E2 i P2 t ∧ s.sp=t.sp)
      (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) (fun _ _ => True) := by
  have wp (s : State) {P : State→Prop} {E : Nat} (h : RowInput base source table len w bytes N M g E i P s) :
      WP isa (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) s (Args source bytes N i) :=
    WP.mono (digitArgs_ok s h.power.ready h.controls h.counter fits) fun _ h =>
      ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
  have digitCT : RelCT isa (fun s t => Args source bytes N i s ∧ Args source bytes N i t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombDigit.code (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    refine ⟨CombDigit.code_ct s t tr1 tr2 u v trivial trivial ?_ e1 e2,trivial⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.1.1.trans h.2.1.1.symm
    · exact h.1.2.1.trans h.2.1.2.1.symm
    · exact h.1.2.2.1.trans h.2.1.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.1.2.2.2.1.symm
    · exact h.1.2.2.2.2.trans h.2.1.2.2.2.2.symm
  exact relCT_chain
    (args_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => wp s h) (fun s h => wp s h) digitCT

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! ### `Bignum.Arm.CombExpKernelAt`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CombExpBackend`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CombDigitLoad`, which this module and modules that import it used -/

section

/-! Big-endian exponent bytes are read at public, bounded bit positions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev loadClobbers : List Reg := [.r2,.r11,.r12]

structure Source (src : BitVec 32) (bs : List Byte) (s : State) : Prop where
  fits : src.toNat + bs.length ≤ 2^32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) bs.length
  bytes : ∀ j (hj : j < bs.length), s.mem (State.addr src + BitVec.ofNat 64 j) = bs[j]'hj

theorem load_ok (s : State) {src : BitVec 32} {bs : List Byte} {k : Nat}
    (source : Source src bs s) (bound : k < 8*bs.length) (size : bs.length < 2^32)
    (ptr : s.gpr .r4 = src) (length : s.gpr .r5 = BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (indexFit : k < 2^32) :
    WP isa (.block VG.Impl.Bignum.Arm.CombDigit.load) s fun t =>
      t.gpr .r11 = (bs[bs.length-1-k/8]'(by omega_using [bound])).setWidth 32 ∧
      t.gpr .r2 = BitVec.ofNat 32 (k%8) ∧ t.z = decide (k%8=0) ∧
      t.mem = s.mem ∧ Rest loadClobbers s t := by
  have quotient : BitVec.ofNat 32 k >>> 3 = BitVec.ofNat 32 (k/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexFit]
    rw [Nat.shiftRight_eq_div_pow]
    change k/8 = k/8%2^32
    rw [Nat.mod_eq_of_lt (by omega_using [indexFit])]
  have rem : BitVec.ofNat 32 k &&& 7 = BitVec.ofNat 32 (k%8) := by
    change BitVec.ofNat 32 k &&& BitVec.ofNat 32 (2^3-1) = _
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
  have offset : (BitVec.ofNat 32 bs.length - BitVec.ofNat 32 (k/8)) - 1 =
      BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [BitVec.ofNat_sub_ofNat_of_le bs.length (k/8) (by omega_using [indexFit]) (by omega_using [bound])]
    change BitVec.ofNat 32 (bs.length-k/8) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (bs.length-k/8) 1 (by decide) (by omega_using [bound])]
    congr 1
    omega_using []
  unfold VG.Impl.Bignum.Arm.CombDigit.load
  refine wp_mov (by rfl) fun a one => ?_
  refine wp_dp (op2_reg _ _) fun b two => ?_
  refine wp_dp (op2_imm (by decide)) fun c three => ?_
  refine wp_dp (op2_reg _ _) fun d four => ?_
  have kept : Rest loadClobbers s d :=
    (((one.rest (by decide)).trans (two.rest (by decide))).trans
      (three.rest (by decide))).trans (four.rest (by decide))
  have address : d.gpr .r12 = src + BitVec.ofNat 32 (bs.length-1-k/8) := by
    rw [four.gpr,three.gpr,two.gpr,one.gpr]
    change c.gpr .r4 + (a.gpr .r5 - (s.gpr .r9 >>> 3) - 1) = _
    rw [three.other .r4 (by decide),two.other .r4 (by decide),one.other .r4 (by decide),
      one.other .r5 (by decide),ptr,length,index,quotient,offset]
  have addr : State.addr (d.gpr .r12 + BitVec.ofNat 32 0) =
      State.addr src + BitVec.ofNat 64 (bs.length-1-k/8) := by
    rw [address,BitVec.add_zero]
    exact VG.Arm.addr_add (by have := source.fits; omega_using [this])
  have read : InRegions (d.rd ++ d.wr) (State.addr src + BitVec.ofNat 64 (bs.length-1-k/8)) 1 := by
    rw [kept.rd,kept.wr]
    exact VG.CallLay.inRegions_sub source.readable (by omega_using [bound]) (by have := source.fits; omega_using [size])
  refine wp_ldrb (by decide) addr read fun e five => ?_
  refine wp_dp (op2_imm (by decide)) fun f six => ?_
  refine wp_cmp (op2_imm (by decide)) fun t seven zero => WP.block_nil ?_
  have count : f.gpr .r2 = BitVec.ofNat 32 (k%8) := by
    rw [six.gpr]
    change e.gpr .r9 &&& 7 = _
    rw [five.other .r9 (by decide),kept.gpr .r9 (by decide),index,rem]
  refine ⟨?_,(congrArg (fun f => f .r2) seven.gpr).trans count,?_,?_,?_⟩
  · rw [seven.gpr,six.other .r11 (by decide),five.gpr]
    rw [four.mem,three.mem,two.mem,one.mem,source.bytes _ (by omega_using [bound])]
  · rw [zero,count]
    change (BitVec.ofNat 32 (k%8) - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero,ofNat_beq_zero (by omega_using [])]
  · exact seven.mem.trans (six.mem.trans (five.mem.trans (four.mem.trans (three.mem.trans (two.mem.trans one.mem)))))
  · exact ((kept.trans (five.rest (by decide))).trans
      (six.rest (by decide))).trans (seven.rest _)

end VG.Proof.Bignum.Arm.CombDigit

end

end

/-! ### `Bignum.Arm.CombExpShared`, which only this module used -/

section

/-! Read-only context and exponent facts persist through the shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def withInvariant {base : BitVec 32} {len w : Nat} {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (Q : State→Prop)
    (stableQ : ∀ {s t : State}, Frame regions s.mem t.mem → Rest roundClobbers s t → Q s → Q t) :
    TwoExp.Montgomery base len w (fun s=>P s ∧ Q s) regions where
  op := A.op
  workspace := A.workspace
  stable := by
    intro s t frame rest h
    exact ⟨A.stable frame rest h.1,stableQ (frame.mono (by simpa using A.workspace)) rest h.2⟩
  op_ok := by
    intro s o a b ready h ho ha hb ho0 operand
    refine WP.mono (A.op_ok s o a b ready h.1 ho ha hb ho0 operand) ?_
    rintro t ⟨readyT,modulus,bound,value,keeps,pt,frame,rest⟩
    exact ⟨readyT,modulus,bound,value,keeps,⟨pt,stableQ frame rest h.2⟩,frame,rest⟩

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! Every callable RSA Montgomery backend supports the same immutable comb context. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombExpReadOnly.lean`, which only this module imported.
section

/-! The immutable exponent and table lie outside every arithmetic write region. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ReadOnly (source table : BitVec 32) (w M g N : Nat) (bs : List Byte)
    (regions : List Region) (s : State) : Prop where
  exponent : CombDigit.Source source bs s
  entries : CombTable table w M g N s
  sourceSeparate : ∀ r∈regions, (⟨State.addr source,bs.length⟩:Region).Disjoint r
  tableSeparate : ∀ r∈regions, (⟨State.addr table,32*(8*w)⟩:Region).Disjoint r

theorem ReadOnly.after_frame {source table : BitVec 32} {w M g N : Nat} {bs : List Byte}
    {regions : List Region} {s t : State} {rs : List Reg}
    (h : ReadOnly source table w M g N bs regions s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t) :
    ReadOnly source table w M g N bs regions t := by
  have entryFits (digit : Nat) (hd : digit<32) (j : Nat) (hj : j<2*w) :
      8*w*digit+4*j+4≤32*(8*w) := by
    have last := Nat.mul_le_mul_left (8*w) (show digit+1≤32 by omega_using [hd])
    have limb := Nat.mul_le_mul_left 4 (show j+1≤2*w by omega_using [hj])
    rw [Nat.mul_add,Nat.mul_one] at last
    omega_using [hj, last]
  refine ⟨⟨h.exponent.fits,?_,?_⟩,⟨h.entries.positive,h.entries.fits,?_,?_⟩,
    h.sourceSeparate,h.tableSeparate⟩
  · rw [rest.rd,rest.wr]; exact h.exponent.readable
  · intro j hj
    exact (frame.bytes h.sourceSeparate (by change bs.length≤2^64; have := h.exponent.fits; omega_using [this]) hj).trans (h.exponent.bytes j hj)
  · rw [rest.rd,rest.wr]; exact h.entries.readable
  · intro digit hd
    rw [←h.entries.values digit hd]
    apply val32_congr
    intro j hj
    apply congrArg BitVec.toNat
    apply frame.readW (r:=⟨State.addr table,32*(8*w)⟩) _ h.tableSeparate (by decide)
    exact Offset.contains_base _ (entryFits digit hd j hj) (by
      have := entryFits digit hd j hj
      have := h.entries.fits
      omega_arith)

end VG.Proof.Bignum.Arm.CombExp
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Arm.FrameStack

def writeRegions (base sp : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr base,8*len⟩,belowA sp 48]

abbrev Persistent (base source table sp : BitVec 32) (len w M g N : Nat) (bs : List Byte) (s : State) : Prop :=
  TwoExp.CallReady base sp len s ∧ ReadOnly source table w M g N bs (writeRegions base sp len) s

def arithmetic (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) :
    TwoExp.Montgomery base len w (Persistent base source table sp len w M g N bs)
      (writeRegions base sp len) :=
  withInvariant (TwoExp.sharedMontgomery base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk)
    (ReadOnly source table w M g N bs (writeRegions base sp len))
    (by intro s t frame rest h; exact h.after_frame frame rest)

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! ### `Bignum.Arm.CombExpChoose`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CombExpStore`, which this module and modules that import it used -/

section

/-! Store the gathered secret digit without changing the public comb controls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem saveDigit_ok {base source table : BitVec 32} {len w bytes N M g E i : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bytes N s)
    (counter : Counter base i s) :
    WP isa (.block [.str .r11 .r0 196]) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧ Counter base i t ∧
      t.mem.readW (off (State.addr base) 196) 32=s.gpr .r11 ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256≤8*len := by
    have fits := h.ready.width ▸ h.ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at fits
    omega_using [fits]
  refine wp_str (a:=off (State.addr base) 196) (by decide)
    (by rw [h.ready.ptr]; exact addr_add (by have := h.ready.workspace.nowrap; omega_using [size, this]))
    (h.ready.workspace.write (by omega_using [size])) fun t update => WP.block_nil ?_
  have rest : Rest roundClobbers s t := (update.rest []).mono (by decide)
  obtain ⟨powerT,frame⟩ := h.after_header (d:=196) (by decide) (by decide) update.mem (update.rest [])
    ((update.rest []).gpr .r0 (by decide) |>.trans h.ready.ptr)
  have outside := writeW32_outside s.mem (State.addr base) (d:=196) (s.gpr .r11) (by decide)
  rw [←update.mem] at outside
  have controlsT : Controls base source table bytes N t := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact (outside_read32 outside (d:=128) (by decide) (by decide)).trans controls.sourcePtr
    · exact (outside_read32 outside (d:=132) (by decide) (by decide)).trans controls.byteCount
    · exact (outside_read32 outside (d:=136) (by decide) (by decide)).trans controls.bitCount
    · exact (outside_read32 outside (d:=204) (by decide) (by decide)).trans controls.spacing
    · exact (outside_read32 outside (d:=232) (by decide) (by decide)).trans controls.tablePtr
  refine ⟨powerT,A.stable frame rest hp,controlsT,?_,?_,frame.mono (by simpa using A.workspace),rest⟩
  · exact (outside_read32 outside (d:=192) (by decide) (by decide)).trans counter
  · rw [update.mem,Mem.readW_writeW_self32]

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! ### `Bignum.Arm.CombExpGather`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CombDigitBit`, which only this module used -/

section

/-! A guarded public-position read returns exactly one exponent bit. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitGuard.lean`, which only this module imported.
section

/-! The bounded public index comparison needs only the existing Z condition. -/

section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

theorem guard_value {k N : Nat} (hk : k < 2^31) (hn : N < 2^31) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 N) >>> 31 = if k<N then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : k < 2^32), Nat.mod_eq_of_lt (by omega : N < 2^32)]
  simp only [Nat.shiftRight_eq_div_pow]
  split
  · rw [show (1 : BitVec 32).toNat = 1 by decide]
    omega
  · rw [show (0 : BitVec 32).toNat = 0 by decide]
    omega

theorem guard_ok (s : State) {k N : Nat} (hk : k < 2^31) (hn : N < 2^31)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (width : s.gpr .r8 = BitVec.ofNat 32 N) :
    WP isa (.block [.dp .sub .r12 .r9 (.reg .r8), .mov .r12 (.shifted .r12 .lsr 31),
      .cmp .r12 (.imm 0)]) s fun t =>
      t.z = !decide (k<N) ∧ t.mem = s.mem ∧ Rest [.r12] s t := by
  refine wp_dp (op2_reg _ _) fun u one => ?_
  refine wp_mov (by rfl) fun v two => ?_
  refine wp_cmp (op2_imm (by decide)) fun t three zero => WP.block_nil ?_
  have value : v.gpr .r12 = if k<N then 1 else 0 := by
    rw [two.gpr,one.gpr]
    change (s.gpr .r9 - s.gpr .r8) >>> 31 = _
    rw [index,width,guard_value hk hn]
  refine ⟨?_,three.mem.trans (two.mem.trans one.mem),
    ((one.rest (by simp)).trans (two.rest (by simp))).trans (three.rest _)⟩
  rw [zero,value]
  by_cases h : k<N
  · simp only [ite_eq_left h,decide_eq_true h]
    rfl
  · simp only [ite_eq_right h,decide_eq_false h]
    rfl

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitShift.lean`, which only this module imported.
section

/-! Public-count shifts use only modeled immediate shift instructions. -/

section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

private theorem step_ok (s : State) {k : Nat} (positive : 0 < k) (fit : k < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 k) :
    WP isa (.block [.mov .r11 (.shifted .r11 .lsr 1), .subs .r2 .r2 (.imm 1)]) s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> 1 ∧ t.gpr .r2 = BitVec.ofNat 32 (k-1) ∧
      t.z = decide (k=1) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  refine wp_mov (by rfl) fun u one => ?_
  refine wp_subs (op2_imm (by decide)) fun t two zero => WP.block_nil ?_
  have mid : u.gpr .r2 = BitVec.ofNat 32 k := (one.other .r2 (by decide)).trans count
  have sub : u.gpr .r2 - 1 = BitVec.ofNat 32 (k-1) := by
    rw [mid]
    change BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k-1)
    exact BitVec.ofNat_sub_ofNat_of_le k 1 (by decide) (by omega)
  refine ⟨(two.other .r11 (by decide)).trans one.gpr, two.gpr.trans sub, ?_,
    two.mem.trans one.mem, (one.rest (by simp)).trans (two.rest (by simp))⟩
  rw [zero,sub,ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem shift_ok (s : State) {n : Nat} (positive : 0 < n) (fit : n < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.shift s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  let I := fun k t => 0 < k ∧ k ≤ n ∧ t.gpr .r2 = BitVec.ofNat 32 k ∧
    t.gpr .r11 = s.gpr .r11 >>> (n-k) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t
  unfold VG.Impl.Bignum.Arm.CombDigit.shift
  refine WP.loop (M := isa) I ?_ n s ⟨positive,by omega,count,by simp,rfl,Rest.refl _ _⟩
  intro k t h
  obtain ⟨positiveK,leK,countK,word,mem,rest⟩ := h
  refine WP.mono (step_ok t positiveK (by omega) countK) ?_
  rintro u ⟨wordU,countU,zeroU,memU,restU⟩
  have next : u.gpr .r11 = s.gpr .r11 >>> (n-(k-1)) := by
    rw [wordU,word,←BitVec.shiftRight_add]
    congr 1
    omega
  by_cases last : k=1
  · left
    refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
    · change some (!u.z) = some false
      simp only [zeroU,last,decide_true,Bool.not_true]
    · simpa only [last,Nat.sub_self,Nat.sub_zero] using next
    · change u.gpr .r2 = BitVec.ofNat 32 0
      simpa only [last,Nat.sub_self] using countU
  · right
    refine ⟨?_, k-1,by omega,by omega,by omega,countU,next,memU.trans mem,rest.trans restU⟩
    change some (!u.z) = some true
    simp only [zeroU,decide_eq_false last,Bool.not_false]

end VG.Proof.Bignum.Arm.CombDigit
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev bitClobbers : List Reg := [.r2,.r11,.r12]

theorem Source.of_mem {src : BitVec 32} {bs : List Byte} {s t : State} {rs : List Reg}
    (h : Source src bs s) (mem : t.mem=s.mem) (rest : Rest rs s t) : Source src bs t := by
  refine ⟨h.fits,?_,?_⟩
  · rw [rest.rd,rest.wr]; exact h.readable
  · intro j hj; rw [mem]; exact h.bytes j hj

private theorem shiftedBit (b : Byte) (r : Nat) :
    (b.setWidth 32 >>> r) &&& 1 = BitVec.ofNat 32 (b.toNat / 2^r % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega_using [] : b.toNat < 2^32)]
  change (b.toNat >>> r) &&& 1 = (b.toNat / 2^r % 2)%2^32
  rw [Nat.and_one_is_mod,Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (by omega_using [] : b.toNat / 2^r % 2 < 2^32)).symm

private theorem optionalShift_ok (s : State) {r : Nat} (bound : r<8)
    (count : s.gpr .r2=BitVec.ofNat 32 r) (zero : s.z=decide (r=0)) :
    WP isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s fun t =>
      t.gpr .r11=s.gpr .r11>>>r ∧ t.mem=s.mem ∧ Rest [.r2,.r11] s t := by
  by_cases h : r=0
  · subst r
    have run : Exec isa (.ite .ne VG.Impl.Bignum.Arm.CombDigit.shift (.block [])) s
        [.branch false] s := .iteF (by change some (!s.z)=_; simp [zero]) (.block rfl)
    exact ⟨_,s,run,by simp,rfl,Rest.refl _ _⟩
  · obtain ⟨tr,t,run,word,_,mem,rest⟩ := shift_ok s (by omega_using [h]) (by omega_using [bound]) count
    exact ⟨_,t,.iteT (by change some (!s.z)=_; simp [zero,h]) run,word,mem,rest⟩

/-- The bit is zero when its public index is outside the declared width. -/
theorem bit_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.bit s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (if h:k<N then
        (bs[bs.length-1-k/8]'(by omega_using [widthBound, h])).toNat / 2^(k%8) % 2 else 0) ∧
      t.mem=s.mem ∧ Rest bitClobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombDigit.bit
  rw [WP.seq_iff]
  refine WP.mono (guard_ok s indexFit widthFit index width) ?_
  rintro u ⟨zero,memU,restU⟩
  by_cases inside : k<N
  · have condition : isa.eval .ne u=some true := by change some (!u.z)=_; simp [zero,inside]
    apply WP.ite true condition
    · intro _
      rw [WP.seq_iff]
      refine WP.mono (load_ok u (source.of_mem memU restU) (by omega_using [widthBound, inside]) size
        ((restU.gpr .r4 (by decide)).trans ptr) ((restU.gpr .r5 (by decide)).trans length)
        ((restU.gpr .r9 (by decide)).trans index) (by omega_using [indexFit])) ?_
      rintro v ⟨byte,count,zeroV,memV,restV⟩
      rw [WP.seq_iff]
      refine WP.mono (optionalShift_ok v (by omega_using []) count zeroV) ?_
      rintro z ⟨shifted,memZ,restZ⟩
      refine wp_dp (op2_imm (by decide)) fun t last => WP.block_nil ?_
      refine ⟨?_,last.mem.trans (memZ.trans (memV.trans memU)),?_⟩
      · rw [last.gpr]
        change z.gpr .r11 &&& 1 = _
        rw [shifted,byte,shiftedBit]
        simp only [dite_eq_left inside]
      · exact (((restU.mono (by decide)).trans restV).trans
          (restZ.mono (by decide))).trans (last.rest (by decide))
    · intro impossible; cases impossible
  · have condition : isa.eval .ne u=some false := by change some (!u.z)=_; simp [zero,inside]
    apply WP.ite false condition
    · intro impossible; cases impossible
    · intro _
      refine wp_mov (op2_imm (by decide)) fun t last => WP.block_nil ?_
      refine ⟨?_,last.mem.trans memU,(restU.mono (by decide)).trans (last.rest (by decide))⟩
      rw [last.gpr]
      simp only [dite_eq_right inside]
      rfl

end VG.Proof.Bignum.Arm.CombDigit

end

end

/-! The evaluator's public header produces exactly the mathematical comb digit. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitTooth.lean`, which only this module imported.
section

/-! One tooth appends one bit at its fixed place in the comb digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

abbrev clobbers : List Reg := [.r2,.r9,.r10,.r11,.r12]

def value (bs : List Byte) (N k : Nat) : Nat :=
  if k<N then ((bs.getD (bs.length-1-k/8) 0).toNat / 2^(k%8)) % 2 else 0

theorem value_lt (bs : List Byte) (N k : Nat) : value bs N k < 2 := by
  unfold value
  split
  · exact Nat.mod_lt _ (by decide)
  · omega_using []

private theorem appendBit {a b j : Nat} (ha : a<2^j) (hb : b<2) (hj : j<5) :
    BitVec.ofNat 32 a ||| (BitVec.ofNat 32 b <<< j) = BitVec.ofNat 32 (a+2^j*b) := by
  have pow : 2^j≤16 := Nat.pow_le_pow_right (by decide) (by omega_using [hj] : j≤4)
  have product : 2^j*b≤16 := calc
    2^j*b ≤ 2^j*1 := Nat.mul_le_mul_left _ (by omega_using [hb])
    _ ≤ 16 := by simpa only [Nat.mul_one] using pow
  have aa : a<2^32 := by omega_using [ha, pow]
  have sum : a+2^j*b<2^32 := by omega_using [ha, pow, product]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt aa,Nat.mod_eq_of_lt (by omega_using [hb] : b<2^32)]
  have shift : b<<<j<2^32 := by rw [Nat.shiftLeft_eq,Nat.mul_comm]; omega_using [product]
  rw [Nat.mod_eq_of_lt shift,Nat.mod_eq_of_lt sum]
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq]
  rw [Nat.mul_comm b (2^j),Nat.add_comm]

theorem tooth_ok (s : State) {src : BitVec 32} {bs : List Byte} {k N d a j : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (indexFit : k<2^31) (widthFit : N<2^31) (_nextFit : k+d<2^32)
    (digitBound : a<2^j) (tooth : j<5)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (index : s.gpr .r9=BitVec.ofNat 32 k) (width : s.gpr .r8=BitVec.ofNat 32 N)
    (stride : s.gpr .r7=BitVec.ofNat 32 d) (digit : s.gpr .r10=BitVec.ofNat 32 a) :
    WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (k+d) ∧
      t.gpr .r10=BitVec.ofNat 32 (a+2^j*value bs N k) ∧
      t.mem=s.mem ∧ Rest clobbers s t := by
  unfold VG.Impl.Bignum.Arm.CombDigit.tooth
  rw [WP.seq_iff]
  refine WP.mono (bit_ok s source widthBound size indexFit widthFit ptr length index width) ?_
  rintro u ⟨bit,memU,restU⟩
  have result : u.gpr .r11=BitVec.ofNat 32 (value bs N k) := by
    rw [bit]
    congr 1
    unfold value
    split
    · rw [←List.getElem_eq_getD 0]
    · rfl
  have old : u.gpr .r10=BitVec.ofNat 32 a := (restU.gpr .r10 (by decide)).trans digit
  have operand : (if j=0 then Op2.reg .r11 else .shifted .r11 .lsl j).eval u =
      some (u.gpr .r11<<<j) := by
    by_cases h : j=0
    · subst j; simp [Op2.eval]
    · simp only [ite_eq_right h,Op2.eval]
      rw [ite_eq_left (by omega_using [tooth, h] : 1≤j ∧ j≤31)]
  refine wp_dp operand fun v one => ?_
  refine wp_dp (op2_reg _ _) fun t two => WP.block_nil ?_
  refine ⟨?_,?_,two.mem.trans (one.mem.trans memU),?_⟩
  · rw [two.gpr]
    change v.gpr .r9+v.gpr .r7=_
    rw [one.other .r9 (by decide),one.other .r7 (by decide),restU.gpr .r9 (by decide),
      restU.gpr .r7 (by decide),index,stride,←BitVec.ofNat_add]
  · rw [two.other .r10 (by decide),one.gpr]
    change u.gpr .r10 ||| (u.gpr .r11<<<j)=_
    rw [old,result,appendBit digitBound (value_lt _ _ _) tooth]
  · exact ((restU.mono (by decide)).trans (one.rest (by decide))).trans
      (two.rest (by decide))

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigit.lean`, which only this module imported.
section

/-! Five statically fixed teeth produce the complete secret digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

def prefixValue (bs : List Byte) (N i d : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => prefixValue bs N i d j + 2^j*value bs N (i+j*d)

theorem prefixValue_lt (bs : List Byte) (N i d j : Nat) : prefixValue bs N i d j<2^j := by
  induction j with
  | zero => simp [prefixValue]
  | succ j ih =>
    have bit := value_lt bs N (i+j*d)
    have product : 2^j*value bs N (i+j*d) ≤ 2^j := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^j) (show value bs N (i+j*d)≤1 by omega_using [bit])
    simp only [prefixValue,Nat.pow_succ]
    omega_using [ih, product]

private structure GatherInv (s0 : State) (bs : List Byte) (N i d j : Nat) (s : State) : Prop where
  index : s.gpr .r9=BitVec.ofNat 32 (i+j*d)
  digit : s.gpr .r10=BitVec.ofNat 32 (prefixValue bs N i d j)
  mem : s.mem=s0.mem
  rest : Rest clobbers s0 s

/-- Raw byte semantics; the public-width bridge identifies this with the comb digit. -/
theorem code_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i d : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*d<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i) (stride : s.gpr .r7=BitVec.ofNat 32 d)
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest clobbers s t := by
  have step (j : Nat) (hj : j<5) (t : State) (h : GatherInv s bs N i d j t) :
      WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) t (GatherInv s bs N i d (j+1)) := by
    have posBound : j*d≤5*d := Nat.mul_le_mul_right d (by omega_using [hj])
    have nextBound : (j+1)*d≤5*d := Nat.mul_le_mul_right d (by omega_using [hj])
    refine WP.mono (tooth_ok t (source.of_mem h.mem h.rest) widthBound size
      (by omega_using [positions, posBound]) widthFit (by omega_using [positions, posBound]) (prefixValue_lt bs N i d j) hj
      ((h.rest.gpr .r4 (by decide)).trans ptr)
      ((h.rest.gpr .r5 (by decide)).trans length)
      h.index ((h.rest.gpr .r8 (by decide)).trans width)
      ((h.rest.gpr .r7 (by decide)).trans stride) h.digit) ?_
    rintro u ⟨index,digit,mem,rest⟩
    refine ⟨?_,digit,mem.trans h.mem,h.rest.trans rest⟩
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using index
  unfold VG.Impl.Bignum.Arm.CombDigit.code
  rw [WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun a one => ?_
  refine wp_mov (op2_imm (by decide)) fun b two => WP.block_nil ?_
  have init : GatherInv s bs N i d 0 b := by
    refine ⟨?_,?_,two.mem.trans one.mem,(one.rest (by decide)).trans (two.rest (by decide))⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (two.other .r9 (by decide)).trans (one.gpr.trans row)
    · exact two.gpr
  rw [WP.seq_iff]
  refine WP.mono (step 0 (by decide) b init) ?_
  intro s1 h1
  rw [WP.seq_iff]
  refine WP.mono (step 1 (by decide) s1 h1) ?_
  intro s2 h2
  rw [WP.seq_iff]
  refine WP.mono (step 2 (by decide) s2 h2) ?_
  intro s3 h3
  rw [WP.seq_iff]
  refine WP.mono (step 3 (by decide) s3 h3) ?_
  intro s4 h4
  rw [WP.seq_iff]
  refine WP.mono (step 4 (by decide) s4 h4) ?_
  intro s5 h5
  refine wp_mov (op2_reg _ _) fun t last => WP.block_nil ?_
  have result : t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) := last.gpr.trans h5.digit
  have bounded : prefixValue bs N i d 5<32 := prefixValue_lt bs N i d 5
  refine ⟨result,?_,last.mem.trans h5.mem,h5.rest.trans (last.rest (by decide))⟩
  rw [result,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [bounded])]
  exact bounded

end VG.Proof.Bignum.Arm.CombDigit
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CombDigitValue.lean`, which only this module imported.
section

/-! The gathered five-byte bits are the reviewed comb's exponent columns. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm

theorem value_eq_bit (bs : List Byte) (N k : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    value bs N k=VG.Proof.Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip bs) k := by
  unfold value VG.Proof.Rsa.FixedBaseComb.bit
  by_cases inside : k<N
  · rw [ite_eq_left inside]
    rw [←List.getElem_eq_getD 0]
    exact (VG.Proof.Ffdh.CombBitBytes.os2ip_bit bs k (by omega_using [size, inside])).symm
  · rw [ite_eq_right inside]
    have limit : Spec.Rsa.os2ip bs<2^k :=
      Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega_using [inside]))
    rw [Nat.div_eq_of_lt limit]

theorem prefixValue_eq_digit (bs : List Byte) (N i : Nat) (size : N≤8*bs.length)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    prefixValue bs N i (Spec.Rsa.FixedBaseComb.rows N) 5=
      VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i := by
  simp only [prefixValue,value_eq_bit bs N _ size bound,VG.Proof.Rsa.FixedBaseComb.digit,
    Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,show 2^4=16 from rfl,
    Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.zero_add]

theorem code_digit_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i)
    (stride : s.gpr .r7=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N))
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ VG.Proof.X25519.Arm.Rest clobbers s t := by
  simpa only [prefixValue_eq_digit bs N i widthBound bound] using
    code_ok s source widthBound size positions widthFit ptr length row stride width

end VG.Proof.Bignum.Arm.CombDigit
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem gather_ok {base source table : BitVec 32} {len w N M g E i : Nat} {bs : List Byte}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bs.length N s)
    (counter : Counter base (i+1) s) (fits : i+1<2^32)
    (bytes : CombDigit.Source source bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (bound : Spec.Rsa.os2ip bs<2^N) :
    WP isa (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bs.length N t ∧ Counter base (i+1) t ∧
      t.gpr .r11=BitVec.ofNat 32 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (digitArgs_ok s h.ready controls counter fits) ?_
  rintro u ⟨src,byteLen,row,stride,width,memU,restU⟩
  have ru : Rest roundClobbers s u := restU.mono (by decide)
  have frameU : Frame [⟨State.addr base,8*len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have pu := A.stable frameU ru hp
  have powerU := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  refine WP.mono (CombDigit.code_digit_ok u (bytes.of_mem memU restU) widthBound size positions widthFit
    bound src byteLen row stride width) ?_
  rintro t ⟨digit,digitBound,memT,restT⟩
  have rt : Rest roundClobbers u t := restT.mono (by decide)
  have frameT : Frame [⟨State.addr base,8*len⟩] u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have mem : t.mem=s.mem := memT.trans memU
  have rest := ru.trans rt
  refine ⟨powerU.of_mem memT restT ((restT.gpr .r0 (by decide)).trans powerU.ready.ptr),
    A.stable frameT rt pu,?_,?_,digit,digitBound,mem,rest⟩
  · exact controls.after_header (by intro d hd; rw [mem])
  · change t.mem.readW _ _=_
    rw [mem]
    exact counter

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! The concrete gather and complete readonly scan supply the evaluator kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem choose_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) (s : State) (i E : Nat)
    (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) (counterFit : i+1<2^32)
    (h : Power base len w M g E s) (hp : Persistent base source table sp len w M g N bs s)
    (controls : Controls base source table bs.length N s) (counter : Counter base (i+1) s) :
    WP isa VG.Impl.Bignum.Arm.CombExp.choose s fun t =>
      Power base len w M g E t ∧ Persistent base source table sp len w M g N bs t ∧
      Controls base source table bs.length N t ∧ Counter base (i+1) t ∧
      numAt t.mem (State.addr base) w 1<M ∧
      numAt t.mem (State.addr base) w 1%M=
        g^(Spec.Rsa.FixedBaseComb.exponent N (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i))*2^(64*w)%M ∧
      Frame (writeRegions base sp len) s.mem t.mem ∧ Rest roundClobbers s t := by
  let A := arithmetic backend base source table sp len w M g N bs
  have gathered := gather_ok A s h hp controls counter counterFit hp.2.exponent widthBound size positions widthFit scalarFit
  rw [WP.seq_iff] at gathered
  rw [VG.Impl.Bignum.Arm.CombExp.choose,WP.seq_iff]
  refine WP.mono gathered ?_
  intro a gather
  rw [WP.seq_iff]
  refine WP.mono gather ?_
  rintro u ⟨powerU,pu,controlsU,counterU,digitU,_,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveDigit_ok A u powerU pu controlsU counterU) ?_
  rintro v ⟨powerV,pv,controlsV,counterV,digitV,frameV,restV⟩
  have sep : Region.Disjoint ⟨State.addr table,32*(8*w)⟩ ⟨State.addr base,8*len⟩ :=
    pv.2.tableSeparate _ (by simp [writeRegions])
  refine WP.mono (CombScan.code_ok v powerV.ready pv.2.entries sep
    (VG.Proof.Rsa.FixedBaseComb.digit_lt N (Spec.Rsa.os2ip bs) i) (digitV.trans digitU) controlsV.tablePtr) ?_
  rintro t ⟨readyT,_,selected,header,arrays,frameT,restT⟩
  have powerT : Power base len w M g E t := by
    refine ⟨readyT,(arrays 0 (by decide) (by decide)).trans powerV.modulus,powerV.coprime,?_,?_,
      (arrays 7 (by decide) (by decide)).trans powerV.one,(arrays 4 (by decide) (by decide)).trans powerV.r2⟩
    · rw [arrays 6 (by decide) (by decide)]; exact powerV.bound
    · rw [arrays 6 (by decide) (by decide)]; exact powerV.value
  have controlsT : Controls base source table bs.length N t :=
    ⟨(header 128 (by decide) (by decide) (by decide)).trans controlsV.sourcePtr,
      (header 132 (by decide) (by decide) (by decide)).trans controlsV.byteCount,
      (header 136 (by decide) (by decide) (by decide)).trans controlsV.bitCount,
      (header 204 (by decide) (by decide) (by decide)).trans controlsV.spacing,
      (header 232 (by decide) (by decide) (by decide)).trans controlsV.tablePtr⟩
  have positive : 0<M := by
    have larger := powerV.ready.modulus
    rw [powerV.modulus] at larger
    omega_using [larger]
  have frameU : Frame (writeRegions base sp len) s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  refine ⟨powerT,A.stable frameT restT pv,controlsT,
    (header 192 (by decide) (by decide) (by decide)).trans counterV,?_,?_,
    frameU.trans (frameV.trans (frameT.mono (by simpa using A.workspace))),restU.trans (restV.trans restT)⟩
  · rw [selected]; exact Nat.mod_lt _ positive
  · rw [selected,Nat.mod_mod,powMod_eq,Nat.mod_mul_mod]

def kernel (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte)
    (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) :
    Kernel base source table len w bs.length N M g (Spec.Rsa.os2ip bs)
      (Persistent base source table sp len w M g N bs) (writeRegions base sp len) where
  arithmetic := arithmetic backend base source table sp len w M g N bs
  choose_ok := by
    intro s i E hi h hp controls counter
    exact choose_ok backend base source table sp len w M g N bs s i E widthBound size
      (by omega_using [scheduleFit, hi]) widthFit scalarFit (by omega_using [scheduleFit, hi]) h hp controls counter

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! Public byte counts index kernels independently of the secret exponent list. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

def kernelAt (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes M g N : Nat) (bs : List Byte) (length : bs.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) :
    Kernel base source table len w bytes N M g (Spec.Rsa.os2ip bs)
      (Persistent base source table sp len w M g N bs) (writeRegions base sp len) where
  arithmetic := arithmetic backend base source table sp len w M g N bs
  choose_ok := by
    intro s i E hi h hp controls counter
    have result := choose_ok backend base source table sp len w M g N bs s i E
      (by simpa only [length] using widthBound) (by simpa only [length] using size)
      (by omega_using [scheduleFit, hi]) widthFit scalarFit (by omega_using [scheduleFit, hi]) h hp (by simpa only [length] using controls) counter
    refine WP.mono result ?_
    rintro t ⟨power,p,controlsT,counterT,bound,value,frame,rest⟩
    exact ⟨power,p,by simpa only [length] using controlsT,counterT,bound,value,frame,rest⟩

end VG.Proof.Bignum.Arm.CombExp

end

end

/-! Independent secret exponents use the same five gathers and full table scan. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

private structure GatheredInput (base source table : BitVec 32) (len w bytes N M g E i digit : Nat)
    (P : State→Prop) (s : State) : Prop extends RowInput base source table len w bytes N M g E i P s where
  value : s.gpr .r11=BitVec.ofNat 32 digit
  bound : digit<32

private theorem gathered_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E i : Nat) (bs : List Byte) (length : bs.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit : Spec.Rsa.os2ip bs<2^N) (countFit : i+1<2^32)
    (s : State) (h : RowInput base source table len w bytes N M g E i
      (Persistent base source table sp len w M g N bs) s) :
    WP isa (.seq (.block VG.Impl.Bignum.Arm.CombExp.digitArgs) VG.Impl.Bignum.Arm.CombDigit.code) s
      (GatheredInput base source table len w bytes N M g E i
        (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i)
        (Persistent base source table sp len w M g N bs)) := by
  let A := arithmetic backend base source table sp len w M g N bs
  refine WP.mono (gather_ok A s h.power h.persistent (by simpa only [length] using h.controls) h.counter
    countFit h.persistent.2.exponent (by simpa only [length] using widthBound)
    (by simpa only [length] using size) positions widthFit scalarFit) ?_
  rintro t ⟨power,p,controls,counter,digit,_,_,_⟩
  exact ⟨⟨power,p,by simpa only [length] using controls,counter⟩,digit,VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _⟩

private theorem savedScan_ok (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E i digit : Nat) (bs : List Byte)
    (s : State) (h : GatheredInput base source table len w bytes N M g E i digit
      (Persistent base source table sp len w M g N bs) s) :
    WP isa (.block [.str .r11 .r0 196]) s (CombScan.Input base table len w M g N digit) := by
  let A := arithmetic backend base source table sp len w M g N bs
  refine WP.mono (saveDigit_ok A s h.power h.persistent h.controls h.counter) ?_
  rintro t ⟨power,p,controls,_,digitValue,_,_⟩

  exact ⟨power.ready,p.2.entries,p.2.tableSeparate _ (by simp [writeRegions]),h.bound,
    digitValue.trans h.value,controls.tablePtr⟩

private theorem save_ct : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
    (.block [.str .r11 .r0 196]) (fun _ _ => True) := by
  apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem choose_ct (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes N M g E1 E2 i : Nat) (bs1 bs2 : List Byte)
    (length1 : bs1.length=bytes) (length2 : bs2.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit1 : Spec.Rsa.os2ip bs1<2^N) (scalarFit2 : Spec.Rsa.os2ip bs2<2^N)
    (hi : i<Spec.Rsa.FixedBaseComb.rows N) :
    RelCT isa (fun s t => RowInput base source table len w bytes N M g E1 i
        (Persistent base source table sp len w M g N bs1) s ∧
      RowInput base source table len w bytes N M g E2 i
        (Persistent base source table sp len w M g N bs2) t ∧ s.sp=t.sp)
      VG.Impl.Bignum.Arm.CombExp.choose (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.CombExp.choose
  apply RelCT.assoc
  refine relCT_chain (gather_ct (by omega_using [scheduleFit, hi]))
    (fun s h => gathered_ok backend base source table sp len w bytes N M g E1 i bs1 length1
      widthBound size (by omega_using [scheduleFit, hi]) widthFit scalarFit1 (by omega_using [scheduleFit, hi]) s h)
    (fun s h => gathered_ok backend base source table sp len w bytes N M g E2 i bs2 length2
      widthBound size (by omega_using [scheduleFit, hi]) widthFit scalarFit2 (by omega_using [scheduleFit, hi]) s h) ?_
  exact relCT_chain
    (save_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => savedScan_ok backend base source table sp len w bytes N M g E1 i _ bs1 s h)
    (fun s h => savedScan_ok backend base source table sp len w bytes N M g E2 i _ bs2 s h)
    CombScan.code_ct

end VG.Proof.Bignum.Arm.CombExp
