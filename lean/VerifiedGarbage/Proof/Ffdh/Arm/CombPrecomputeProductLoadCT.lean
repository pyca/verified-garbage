module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeArgs
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeMem
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Readonly context imports have public addresses, widths, and table indices. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_mov op2_imm)

private theorem loadEntry_ct {p : Inputs} {sp : BitVec 32} {digit o : Nat} (ho : o<8) :
    RelCT isa (fun s t => (Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit) ∧
      (Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 digit) ∧ s.sp=t.sp)
      (.seq (.block (VG.Impl.Ffdh.Arm.CombPrecompute.tableArgs ++
        ([.mov .r2 (.imm (BitVec.ofNat 32 o))] : List Instr))) VG.Impl.Bignum.Arm.importArray) (fun _ _ => True) := by
  let Input := fun s : State => Memory p sp s ∧ s.gpr .r3=BitVec.ofNat 32 digit
  let dst := p.output+BitVec.ofNat 32 (24+8*p.w*(digit+2))
  let Ready := fun s : State => SmallFnReady p.base p.len p.w o s ∧ s.gpr .r4=dst
  have args (s : State) (h : Input s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.CombPrecompute.tableArgs ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) s Ready := by
    have fit := h.1.ready.layout.2.2.1
    rw [h.1.ready.width] at fit
    have size : 52≤8*p.len := by simp only [arrAt,Proof.Rsa.Mont.hdrBytes] at fit; omega
    have header := nativeHeader_of_layout s.mem p.base h.1.ready.workspace.nowrap
      (Nat.le_refl _) h.1.ready.layout
    rw [h.1.ready.width] at header
    rw [WP.block_append_iff]
    refine WP.mono (combTableArgs_raw_ok s h.1.ready.workspace h.1.context.locals size h.1.ready.ptr
      header.count (h.1.context.saved 4 (by simp [slots])) h.2) ?_
    rintro u ⟨⟨dstU,ptrU,memU⟩,restU⟩
    rw [combTableAddress] at dstU
    refine wp_mov (op2_imm (by
      apply encodable_byte
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : o<2^32)]
      omega)) fun v moved => WP.block_nil ?_
    have memV := moved.mem.trans memU
    exact ⟨⟨h.1.ready.workspace.congr (moved.wr.trans restU.wr),
      by rw [memV]; exact h.1.ready.layout,
      by rw [memV]; exact h.1.ready.width,
      (moved.other .r0 (by decide)).trans ptrU,moved.gpr⟩,
      (moved.other .r4 (by decide)).trans dstU⟩
  have load : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.sp=t.sp)
      (.block [.ldrSp .r4 4]) (fun s t => s.gpr .r0=t.gpr .r0) := by
    intro s t tr1 tr2 u v h e1 e2
    have ku : u.gpr .r0=s.gpr .r0 := Exec.gpr (h:=e1) (hn:=Or.inl rfl) (by decide)
    have kv : v.gpr .r0=t.gpr .r0 := Exec.gpr (h:=e2) (hn:=Or.inl rfl) (by decide)
    exact ⟨(loadStack_ct .r4 4 _ _ _ _ _ _ h.2 e1 e2).1,ku.trans (h.1.trans kv.symm)⟩
  have restTrace : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
      (.block ([.ldr .r1 .r0 48, .mov .r1 (.shifted .r1 .lsl 3),
        .dp .add .r3 .r3 (.imm 2), .mul .r3 .r3 .r1,
        .dp .add .r4 .r4 (.reg .r3), .dp .add .r4 .r4 (.imm 24)] ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) (fun _ _ => True) := by
    have cases : o=0 ∨ o=1 ∨ o=2 ∨ o=3 ∨ o=4 ∨ o=5 ∨ o=6 ∨ o=7 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
       intro s t h
       apply Taint.agree_ofRegs
       intro r hr
       simp only [List.mem_singleton] at hr
       subst r
       exact h)
  have trace : RelCT isa (fun s t => Input s ∧ Input t ∧ s.sp=t.sp)
      (.block (VG.Impl.Ffdh.Arm.CombPrecompute.tableArgs ++
        [.mov .r2 (.imm (BitVec.ofNat 32 o))])) (fun _ _ => True) :=
    (RelCT.block_append (load.seq restTrace)).mono
      (fun _ _ h => ⟨h.1.1.ready.ptr.trans h.2.1.1.ready.ptr.symm,h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain trace args args ((importArray_ct ho).mono
    (fun _ _ h => ⟨h.1.1,h.2.1.1,h.1.2,h.2.1.2⟩) (fun _ _ h => h))


theorem productLoad_ct {p : Inputs} {sp : BitVec 32} {low : Nat} :
    RelCT isa (fun s t =>
      (Memory p sp s ∧ s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) ∧
      (Memory p sp t ∧ t.mem.readW (off (State.addr t.sp) 40) 32=BitVec.ofNat 32 low) ∧ s.sp=t.sp)
      VG.Impl.Ffdh.Arm.CombPrecompute.productLoad (fun _ _ => True) := by
  have loaded (s : State) (h : Memory p sp s ∧
      s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low) :
      WP isa (.block [.ldrSp .r3 40]) s (fun t => Memory p sp t ∧ t.gpr .r3=BitVec.ofNat 32 low) := by
    refine WP.mono (localLoad_ok s .r3 h.1.context.locals (d:=40) (by decide)) ?_
    rintro t ⟨reg,mem,rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ready.ptr),reg.trans h.2⟩
  unfold VG.Impl.Ffdh.Arm.CombPrecompute.productLoad
  have combined := relCT_chain ((loadStack_ct .r3 40).mono
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) loaded loaded
    (loadEntry_ct (digit:=low) (o:=1) (by decide))
  intro s t tr1 tr2 u v h e1 e2
  apply combined s t tr1 tr2 u v h
  · cases e1 with
    | seq args body =>
      rw [Exec.block_iff,List.append_assoc,execBlock_append] at args
      obtain ⟨⟨ta,a⟩,ra,rest⟩ := Option.bind_eq_some_iff.mp args
      obtain ⟨⟨tb,b⟩,rb,eq⟩ := Option.map_eq_some_iff.mp rest
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      simpa only [List.append_assoc,BitVec.ofNat_eq_ofNat] using (Exec.seq (Exec.block ra) (Exec.seq (Exec.block rb) body))
  · cases e2 with
    | seq args body =>
      rw [Exec.block_iff,List.append_assoc,execBlock_append] at args
      obtain ⟨⟨ta,a⟩,ra,rest⟩ := Option.bind_eq_some_iff.mp args
      obtain ⟨⟨tb,b⟩,rb,eq⟩ := Option.map_eq_some_iff.mp rest
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      simpa only [List.append_assoc,BitVec.ofNat_eq_ofNat] using (Exec.seq (Exec.block ra) (Exec.seq (Exec.block rb) body))

end VG.Proof.Ffdh.Arm.CombBuilder
