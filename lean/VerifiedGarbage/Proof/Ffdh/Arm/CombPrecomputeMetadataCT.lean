module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadataAll
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
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBitsSave
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeBitsSave
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadata
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMetadata
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeRows
meta import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeRows
import VerifiedGarbage.Proof.Ffdh.ScalarWidth
meta import VerifiedGarbage.Proof.Ffdh.ScalarWidth

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
    omega
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
    refine WP.mono (combRowsCount_ok s hs.1 positive (by omega) hs.2.2) ?_
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
