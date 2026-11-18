module

import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.RowFull
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Bignum.Arm.RowFullCT`, which this module and modules that import it used -/

section

/-! # ARMv7 Montgomery row-loop leakage: pointers and the word count are public -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem rowFull_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr) rowFull := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r12, .lr]) ?_ (by taint_decide)
  intro s t _ _ ⟨h0, h12, hcount⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h12
  · exact hcount

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.ArgsCT`, which this module and modules that import it used -/

section

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
      refine wp_ldr (by decide) (ws.ea p (by omega_using [ht])) (ws.read ht) fun t u => WP.block_nil ?_
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
    refine wp_ldr (by decide) (ws.ea p (by omega_using [ht])) (ws.read (by omega_using [ht])) fun s1 u1 => ?_
    have p1 := (u1.other .r0 (by decide)).trans p
    have w1 := ws.congr u1.wr
    refine wp_ldr (by decide) (w1.ea p1 (by omega_using [ht])) (w1.read (by omega_using [ht])) fun s2 u2 => ?_
    have p2 := (u2.other .r0 (by decide)).trans p1
    have w2 := w1.congr u2.wr
    refine wp_ldr (by decide) (w2.ea p2 (by omega_using [ht])) (w2.read (by omega_using [ht])) fun s3 u3 => ?_
    have p3 := (u3.other .r0 (by decide)).trans p2
    have w3 := w2.congr u3.wr
    refine wp_ldr (by decide) (w3.ea p3 (by omega_using [ht])) (w3.read ht) fun t u4 => WP.block_nil ?_
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

end

end

/-! # Relational leakage proofs for the three Montgomery stages -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

/-- Metadata may contain a different secret inverse in each run. -/
def StageReady (base : BitVec 32) (size tmp a b mod acc n i ptr : Nat) (s : State) : Prop :=
  RoundCtx s base size tmp a b mod acc n ∧
  (∃ inv, RoundMeta s.mem base tmp a b mod acc n i inv) ∧
  s.gpr .r0 = base + BitVec.ofNat 32 ptr

theorem pair_posts {P Q : State → Prop} {code : Prog isa}
    (ct : RelCT isa (fun s t => P s ∧ P t) code (fun _ _ => True))
    (wp : ∀ s, P s → WP isa code s Q) :
    RelCT isa (fun s t => P s ∧ P t) code (fun s t => Q s ∧ Q t) :=
  (ct.wp (fun s t h => ⟨wp s h.1, wp t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem productStage_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i tmp s ∧
      StageReady base size tmp a b mod acc n i tmp t) productStage (fun _ _ => True) := by
  let P := StageReady base size tmp a b mod acc n i tmp
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block productArgs) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨cs, ⟨is, hs⟩, ps⟩ := h.1
    obtain ⟨ct, ⟨it, ht⟩, pt⟩ := h.2
    exact productArgs_ct (a := a + 4 * i) (by have := cs.tmpFits; omega_using [this])
      s t tr1 tr2 u v ⟨cs.workspace, ct.workspace, ps, pt, hs.aPtr, ht.aPtr⟩ e1 e2
  have wp (s : State) (h : P s) : WP isa (.block productArgs) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have fits := ctx.aFits
    exact WP.mono (productArgs_ok s ctx.workspace ctx.tmpFits (by omega_using [hi, fits])
      ptr hdr.aPtr hdr.count hdr.bPtr hdr.accPtr) (fun _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
  unfold productStage
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨rowFull_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩

end VG.Proof.Bignum.Arm
