module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtGiven
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtGiven
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # Preparing a factor with its given `R² mod p` is constant-time

The copy's addresses and count are the factor's given value's, the narrow
workspace's and its width, which both runs share; the selection and
`R² mod X` computed from 1 are constant-time; the width test reads only
public lengths. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

section
variable {g : CrtGeometry} {a : BitVec 32} {j : Fin 6} {v : Nat}

/-- A block that only moves registers. -/
theorem moveBlock_ct {P : State → State → Prop} (d n : Reg) :
    RelCT isa P (.block [.mov d (.reg n)]) (fun _ _ => True) :=
  single_ct (fun _ _ _ => by simp [addrs]) (fun _ _ _ _ _ _ _ => trivial)

/-- Ready for the selection: the narrow workspace, and frame slot 48 readable. -/
def SelectIn (g : CrtGeometry) (v : Nat) (s : State) : Prop :=
  ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4 ∧ s.sp.toNat + 52 ≤ 2 ^ 32

theorem selectIn_smallConst (x : State) (h : SelectIn g v x) :
    WP isa (smallConst 7 1) x (SelectIn g v) := by
  obtain ⟨h, read, fit⟩ := h
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.width ▸ h.layout.2.2.1
  have nNow := h.workspace.nowrap
  refine WP.mono (smallConstLayout_ok x 1 h.workspace h.layout h.width h.ptr
    (by decide : 7 < 8) (by decide) (by decide) h.stackRead h.stackSep h.saved) ?_
  rintro w ⟨_, _, _, outside7, frame7, rest7, ptrW⟩
  exact ⟨(h.after_array (by decide : 7 ≠ 0) (outside_array_keeps outside7 (len := workspaceWords g.words) (by omega_using [nNow]))
    frame7 rest7 ptrW).1, by rw [rest7.rd, rest7.wr, rest7.sp]; exact read, by rw [rest7.sp]; exact fit⟩

theorem selectPart_ct :
    RelCT isa (fun s t => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp)
      (.seq (smallConst 7 1) (.seq (.block [.ldrSp .r11 48]) (selectArray 4 7 4))) (fun _ _ => True) := by
  have small := (smallConst_ct (base := crtN g.base g.words) (len := workspaceWords g.words) (w := v) (o := 7) 1
    (by decide) (by decide) (by decide)).mono (P' := fun (s t : State) => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have load : RelCT isa (fun s t => SelectIn g v s ∧ SelectIn g v t ∧ s.sp = t.sp) (.block [.ldrSp .r11 48])
      (fun _ _ => True) :=
    (loadStack_ct .r11 48).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have loadWP (s : State) (h : SelectIn g v s) : WP isa (.block [.ldrSp .r11 48]) s (SelectIn g v) := by
    refine wp_loadStack (a := off (State.addr s.sp) 48) (by decide) (addr_add (by have := h.2.2; omega_using [this])) h.2.1
      fun t ld => WP.block_nil ?_
    exact ⟨h.1.of_mem ld.mem (ld.rest (by decide : Reg.r11 ∈ [Reg.r11]))
      (by rw [ld.other .r0 (by decide)]; exact h.1.ptr), by rw [ld.rd, ld.wr, ld.sp]; exact h.2.1,
      by rw [ld.sp]; exact h.2.2⟩
  have select := selectArray_ct (base := crtN g.base g.words) (len := workspaceWords g.words) (w := v)
    (by decide : 4 < 8) (by decide : 7 < 8) (by decide : 4 < 8)
  exact crt_seq_ct small (fun s h => selectIn_smallConst s h) (fun s h => selectIn_smallConst s h)
    (crt_seq_ct load loadWP loadWP (select.mono
      (fun _ _ h => ⟨⟨h.1.1.workspace, h.1.1.layout, h.1.1.width, h.1.1.ptr⟩,
        ⟨h.2.1.1.workspace, h.2.1.1.layout, h.2.1.1.width, h.2.1.1.ptr⟩, h.2.2⟩) (fun _ _ _ => trivial)))

def R0Eq (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0

/-- An instruction that keeps r0 and accesses memory only through r0 and the stack. -/
def r0Instruction : Instr → Bool
  | .ldr t n _ => decide (n = .r0) && decide (t ≠ .r0)
  | .ldrSp t _ => decide (t ≠ .r0)
  | .dp _ d _ _ => decide (d ≠ .r0)
  | .mov d _ => decide (d ≠ .r0)
  | .cmp _ _ => true
  | _ => false

theorem r0Instruction_ct {i : Instr} (hi : r0Instruction i = true) :
    RelCT isa R0Eq (.block [i]) R0Eq := by
  apply single_ct
  · intro s t h
    cases i <;> simp_all [r0Instruction, addrs, R0Eq]
  · intro s t u v h e1 e2
    have keep : clobbers i .r0 = false := by
      cases i <;> simp_all [r0Instruction, clobbers, dstOf] <;> first | exact Ne.symm hi | exact (Ne.symm hi.2)
    exact ⟨(exec_sp e1).trans (h.1.trans (exec_sp e2).symm),
      (exec_gpr keep e1).trans (h.2.trans (exec_gpr keep e2).symm)⟩

theorem r0Block_keep_ct (code : List Instr) (h : code.all r0Instruction = true) :
    RelCT isa R0Eq (.block code) R0Eq := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact RelCT.block_append ((r0Instruction_ct h.1).seq (ih h.2))

theorem r2CopyHead_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) :
    RelCT isa (fun s t => CopyIn g bs1 j v s ∧ CopyIn g bs2 j v t ∧ s.sp = t.sp)
      (.block (r2Source (56 + 8 * j.val) ++ lowArgs 4)) (fun _ _ => True) := by
  have split : r2Source (56 + 8 * j.val) ++ lowArgs 4 =
      (r2Source (56 + 8 * j.val) ++ (lowArgs 4).dropLast) ++ [.mov .r0 (.reg .r4)] := by
    simp [lowArgs]
  rw [split]
  refine RelCT.block_append (((r0Block_keep_ct _ ?_).mono (fun _ _ h => ⟨h.2.2, ?_⟩) (fun _ _ _ => trivial)).seq
    (moveBlock_ct .r0 .r4))
  · rcases hj with rfl | rfl <;> decide
  · exact h.1.ready.ptr.trans h.2.1.ready.ptr.symm

theorem r2Copy_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => CopyIn g bs1 j v s ∧ CopyIn g bs2 j v t ∧ s.sp = t.sp)
      (r2Copy (56 + 8 * j.val)) (fun _ _ => True) := by
  let H := fun (bs : Fin 7 → List Byte) (z : State) => ∃ s0, CopyIn g bs j v s0 ∧ CopyHead g a j v s0 z
  let C := fun (bs : Fin 7 → List Byte) (x : State) => ∃ s0, CopyIn g bs j v s0 ∧ Copied g a j v s0 x
  have headWP (s : State) {bs : Fin 7 → List Byte} (h : CopyIn g bs j v s) :
      WP isa (.block (r2Source (56 + 8 * j.val) ++ lowArgs 4)) s (H bs) :=
    (copyHead_ok s hj ha h).mono fun z hz => ⟨s, h, hz⟩
  have copyCT : RelCT isa (fun s t => H bs1 s ∧ H bs2 t ∧ s.sp = t.sp)
      (.seq copyBytes (.block [.mov .r0 (.reg .r5)])) (fun _ _ => True) := by
    refine RelCT.seq (R := fun _ _ => True) ?_ (moveBlock_ct .r0 .r5)
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨⟨_, _, ⟨s0, s5, slr, s1, _⟩⟩, ⟨_, _, ⟨t0, t5, tlr, t1, _⟩⟩, _⟩ := h
    exact ⟨copyBytes_ct s t tr1 tr2 u w trivial trivial
      ⟨s0.trans t0.symm, s1.trans t1.symm, slr.trans tlr.symm⟩ e1 e2, trivial⟩
  have copyWP (z : State) {bs : Fin 7 → List Byte} (h : H bs z) :
      WP isa (.seq copyBytes (.block [.mov .r0 (.reg .r5)])) z (C bs) := by
    obtain ⟨s0, h0, head⟩ := h
    exact (copied_ok s0 z hj ha h0 head).mono fun x hx => ⟨s0, h0, hx⟩
  have selectIn (x : State) {bs : Fin 7 → List Byte} (h : C bs x) : SelectIn g v x := by
    obtain ⟨s0, h0, ready, _, _, _, rest⟩ := h
    have spNow := h0.shared.stack.nowrap
    exact ⟨ready, by rw [rest.rd, rest.wr, rest.sp]; exact h0.shared.stack.read (by decide),
      by rw [rest.sp]; omega_using [spNow]⟩
  rw [r2Copy]
  exact crt_seq_ct (r2CopyHead_ct hj) (fun s h => headWP s h) (fun s h => headWP s h)
    (crt_seq_ct copyCT (fun z h => copyWP z h) (fun z h => copyWP z h)
      (selectPart_ct.mono (fun _ _ h => ⟨selectIn _ h.1, selectIn _ h.2.1, h.2.2⟩) (fun _ _ _ => trivial))).assoc

/-- Before `r2Given`. -/
def GivenIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧
    ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ) g.words) s ∧
    (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1

theorem r2Given_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => GivenIn g bs1 j s ∧ GivenIn g bs2 j t ∧ s.sp = t.sp)
      (r2Given (56 + 8 * j.val)) (fun _ _ => True) := by
  let v := narrowWords (g.sourceLength j.succ) g.words
  let T := fun (bs : Fin 7 → List Byte) (u : State) =>
    GivenIn g bs j u ∧ u.z = decide (v = (g.sourceLength j.succ + 7) / 8)
  have testWP (s : State) {bs : Fin 7 → List Byte} (h : GivenIn g bs j s) :
      WP isa (.block (r2WidthTest (56 + 8 * j.val + 4))) s (T bs) := by
    refine (r2WidthTest_ok s h.1 h.2.1).mono ?_
    rintro u ⟨z, mem, rest⟩
    exact ⟨⟨h.1.of_mem mem rest, h.2.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.2.1.ptr),
      by rw [mem, rest.sp]; exact h.2.2⟩, z⟩
  have test : RelCT isa (fun s t => GivenIn g bs1 j s ∧ GivenIn g bs2 j t ∧ s.sp = t.sp)
      (.block (r2WidthTest (56 + 8 * j.val + 4))) (fun _ _ => True) := by
    refine (r0Block_keep_ct _ ?_).mono (fun _ _ h => ⟨h.2.2, h.1.2.1.ptr.trans h.2.1.2.1.ptr.symm⟩)
      (fun _ _ _ => trivial)
    rcases hj with rfl | rfl <;> decide
  rw [r2Given]
  refine crt_seq_ct test (fun s h => testWP s h) (fun s h => testWP s h)
    (crt_ite_ct (cond := decide (v = (g.sourceLength j.succ + 7) / 8))
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2]) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun hc => ?_) (fun _ => ?_))
  · have same := of_decide_eq_true hc
    have copyIn (s : State) {bs : Fin 7 → List Byte} (h : T bs s) : CopyIn g bs j v s := by
      have hv : 2 ≤ v := by have := h.1.2.1.layout.1; rw [h.1.2.1.width] at this; exact this
      refine ⟨h.1.1, h.1.2.1, ?_, h.1.2.2⟩
      unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega_using [same, hv]
    exact (r2Copy_ct hj ha).mono (fun _ _ h => ⟨copyIn _ h.1, copyIn _ h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  · exact relCT_of_pre fun s _ h => (r2_ct (by
      obtain ⟨_, le, _, _, _, _, _⟩ := h.1.1.1.narrow_fits j hj
      have : g.words ≤ 128 := (crt_width_valid h.1.1.1.buffers.lengthValid).2.1
      omega_using [le, this])).mono (fun _ _ h => ⟨h.1.1.2.1, h.2.1.1.2.1, h.2.2⟩) (fun _ _ _ => trivial)

theorem crt_narrowPrimeGiven_ct {bs1 bs2 : Fin 7 → List Byte} (hj : j = 1 ∨ j = 2) (ha : g.r2 = some a) :
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (narrowPrimeGiven (56 + 8 * j.val)) (fun _ _ => True) := by
  have invWP (s : State) {bs : Fin 7 → List Byte} (h : CrtPrimeIn g bs j s) :
      WP isa (narrowPrimeInv (56 + 8 * j.val)) s (GivenIn g bs j) := by
    refine (crt_narrowPrimeInv_ok s h.2).mono ?_
    rintro u ⟨readyU, _, _, flagU, frameU, restU⟩
    exact ⟨h.1.after_narrow (frameU.mono (by simp)) restU, readyU, by rw [flagU]; exact h.2.bit⟩
  rw [narrowPrimeGiven]
  exact crt_seq_ct (crt_narrowPrimeInv_ct.mono (fun _ _ h => ⟨h.1.2, h.2.1.2, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => invWP s h) (fun s h => invWP s h) (r2Given_ct hj ha)

end

end VG.Proof.Bignum.Arm
