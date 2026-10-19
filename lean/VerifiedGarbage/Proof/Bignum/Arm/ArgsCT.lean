module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Public pointers loaded from Montgomery metadata

The pointed-to operand and the Montgomery inverse remain secret. Only the
workspace pointer and the pointer loaded from its metadata are related.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (wp_ldr)

theorem productArgs_ct {base : BitVec 32} {size tmp a : Nat}
    (ht : tmp + 20 ≤ size) :
    RelCT isa (fun s t =>
      Workspace s base size ∧ Workspace t base size ∧
      s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧ t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      s.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a ∧
      t.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a)
      (.block productArgs) (fun _ _ => True) := by
  let P := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
    s.gpr .r1 = base + BitVec.ofNat 32 a
  have first : RelCT isa (fun s t =>
      Workspace s base size ∧ Workspace t base size ∧
      s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧ t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      s.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a ∧
      t.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a)
      (.block [.ldr .r1 .r0 16]) (fun s t => P s ∧ P t) := by
    have ct := RelCT.taint (A := taint) (c := .block [.ldr .r1 .r0 16])
      (Taint.ofRegs [.r0]) (P := fun s t => s.gpr .r0 = t.gpr .r0)
      (fun s t h => Taint.agree_ofRegs (by simpa using h)) (by taint_decide)
    have one (s : State) (ws : Workspace s base size)
        (p : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
        (m : s.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a) :
        WP isa (.block [.ldr .r1 .r0 16]) s P := by
      refine wp_ldr (by decide) (ws.ea p (by omega)) (ws.read ht) fun t u => WP.block_nil ?_
      exact ⟨(u.other .r0 (by decide)).trans p, u.gpr.trans m⟩
    exact (RelCT.wp (ct.mono (fun _ _ h => h.2.2.1.trans h.2.2.2.1.symm) (fun _ _ h => h))
      (fun s t h => ⟨one s h.1 h.2.2.1 h.2.2.2.2.1, one t h.2.1 h.2.2.2.1 h.2.2.2.2.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  unfold productArgs
  change RelCT isa _ (.block ([.ldr .r1 .r0 16] ++ _)) _
  apply RelCT.block_append
  refine first.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm


theorem reductionArgs_ct {base : BitVec 32} {size top acc : Nat}
    (ht : top + 48 ≤ size) :
    RelCT isa (fun s t =>
      Workspace s base size ∧ Workspace t base size ∧
      s.gpr .r0 = base + BitVec.ofNat 32 top ∧ t.gpr .r0 = base + BitVec.ofNat 32 top ∧
      s.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc ∧
      t.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc)
      (.block reductionArgs) (fun _ _ => True) := by
  let pre : List Instr := [.ldr .lr .r0 16, .ldr .r12 .r0 24, .ldr .r1 .r0 28, .ldr .r0 .r0 44]
  let P := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc
  have one (s : State) (ws : Workspace s base size)
      (p : s.gpr .r0 = base + BitVec.ofNat 32 top)
      (m : s.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc) :
      WP isa (.block pre) s P := by
    unfold pre
    refine wp_ldr (by decide) (ws.ea p (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
    have p1 := (u1.other .r0 (by decide)).trans p
    have w1 := ws.congr u1.wr
    refine wp_ldr (by decide) (w1.ea p1 (by omega)) (w1.read (by omega)) fun s2 u2 => ?_
    have p2 := (u2.other .r0 (by decide)).trans p1
    have w2 := w1.congr u2.wr
    refine wp_ldr (by decide) (w2.ea p2 (by omega)) (w2.read (by omega)) fun s3 u3 => ?_
    have p3 := (u3.other .r0 (by decide)).trans p2
    have w3 := w2.congr u3.wr
    refine wp_ldr (by decide) (w3.ea p3 (by omega)) (w3.read ht) fun t u4 => WP.block_nil ?_
    change t.gpr .r0 = _
    rw [u4.gpr, u3.mem, u2.mem, u1.mem, m]
  have ct := RelCT.taint (A := taint) (c := .block pre)
    (Taint.ofRegs [.r0]) (P := fun s t => s.gpr .r0 = t.gpr .r0)
    (fun s t h => Taint.agree_ofRegs (by simpa using h)) (by dsimp [pre]; taint_decide)
  have first := RelCT.wp (ct.mono
    (P' := fun (s t : State) => Workspace s base size ∧ Workspace t base size ∧
      s.gpr .r0 = base + BitVec.ofNat 32 top ∧ t.gpr .r0 = base + BitVec.ofNat 32 top ∧
      s.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc ∧
      t.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc)
    (fun _ _ h => h.2.2.1.trans h.2.2.2.1.symm) (fun _ _ h => h))
    (fun s t h => ⟨one s h.1 h.2.2.1 h.2.2.2.2.1, one t h.2.1 h.2.2.2.1 h.2.2.2.2.2⟩)
  change RelCT isa _ (.block (pre ++ [.ldr .r2 .r0 0, .mul .r1 .r1 .r2, .mov .r11 (.imm 0)])) _
  apply RelCT.block_append
  refine first.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r0]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  simpa only [List.mem_singleton, forall_eq] using h.2.1.trans h.2.2.symm

end VG.Proof.Bignum.Arm
