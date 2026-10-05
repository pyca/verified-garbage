import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Impl.Ed25519.X86.PointTable
import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Impl.Ed25519.X86.Field
import VerifiedGarbage.Impl.Ed25519.X86.PointLoop
import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory
import VerifiedGarbage.Impl.Ed25519.X86.Power
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Impl.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.PointSelect
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Impl.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Impl.Ed25519.X86.BitsExpand
import VerifiedGarbage.Impl.Ed25519.X86.InputBits
import VerifiedGarbage.Impl.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Ed25519.X86.FieldCheck
import VerifiedGarbage.Impl.Ed25519.X86.RecoverSign
import VerifiedGarbage.Impl.Ed25519.X86.Verify

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Workspace`. -/
section

/-!
# Ed25519 on x86 (32-bit): the field arithmetic

Ed25519's field operations are X25519's code (`Impl.X25519.X86`), so their
proofs are X25519's, for Ed25519's working space of 8192 bytes, whose slots
start at offset 64.
-/

namespace VG.Proof.Ed25519.X86

/-- The code's view of the working space of 8192 bytes. -/
abbrev Ctx (x : BitVec 32) (s : VG.X86.State) : Prop := X25519.X86.Ctx 8192 x s

export VG.Proof.X25519.X86 (v wd wv num fe sub scR addr_zero sub_contains sub_disj scR_eq scR_contains
  wd_write_ne wd_write_self wd_frame wd_frame1 frame_write1 sub_sub frameWiden Keep Keep.refl num_succ
  num_congr num_add num_mul fe_lt fe_frame fe_frame1 acc tval treads colv toNat_zero32 updKeep cols_ok
  wp_mul prod_identity num_16 colv_le_len wv_lt wv_mul_le zeroAcc_ok Below F isSlot slot_below slot_ne
  frame_wide mask cswap_ok opOut opIns opValid opVal run op_ok shr31_toNat low31_toNat setAcc_ok
  selects_ok fold_top colv_addM freeze_ok)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Field`. -/
section

/-! Merged from `Proof.Ed25519.X86.FieldMemory`. -/
section
/-! Full-width constants and field-slot copies. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86 VG.Spec.X25519
open VG.Proof.X25519

theorem slot_valid (o : Slot) : VG.Proof.X25519.X86.isSlot 64 (offset o) = true := (by decide : ∀ i : Slot, isSlot 64 (offset i) = true) o

theorem fill_step {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o n : Nat} (ho : VG.Proof.X25519.X86.Below o) (hn : n < 8)
    (f : Nat → BitVec 32) (hk : VG.Proof.X25519.X86.Keep s₀ s) (hf : Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (o + 4 * j) = f j) :
    WP isa (.block [.mov .eax (.imm (f n)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      VG.Proof.X25519.X86.Keep s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = f j := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((VG.Proof.X25519.X86.updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self, u₁.gpr]
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem fill_ok {x : BitVec 32} {s₀ : State} (hc₀ : VG.Proof.Ed25519.X86.Ctx x s₀) {o : Nat} (ho : VG.Proof.X25519.X86.Below o) (f : Nat → BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (f k)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      VG.Proof.X25519.X86.Keep s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = f j
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.Ed25519.X86.fill_ok hc₀ ho f n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      VG.Proof.Ed25519.X86.fill_step (k₁.ctx hc₀) ho (by omega_using [hn]) f k₁ f₁ w₁)

theorem num_digits (v n : Nat) :
    VG.Proof.X25519.X86.num (fun k => v / (2 ^ 32) ^ k % 2 ^ 32) n = v % (2 ^ 32) ^ n := by
  induction n with
  | zero => simp only [VG.Proof.X25519.X86.num, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ, ih, Nat.pow_succ (2 ^ 32) n]
    exact Nat.mod_mul.symm

theorem constField_op {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o : Slot) (v : Fe) :
    WP isa (.block (constField o v)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x (offset o) 32] s.mem t.mem ∧ VG.Proof.X25519.X86.F t.mem x (offset o) = v := by
  refine WP.mono (VG.Proof.Ed25519.X86.fill_ok hc (VG.Proof.X25519.X86.slot_below (VG.Proof.Ed25519.X86.slot_valid o))
    (fun k => BitVec.ofNat 32 (v.val / (2 ^ 32) ^ k)) 8 (Nat.le_refl _)) fun t ⟨hk, hf, hv⟩ => ?_
  refine ⟨hk, hf, ?_⟩
  have he : VG.Proof.X25519.X86.fe t.mem x (offset o) = v.val := by
    unfold VG.Proof.X25519.X86.fe
    rw [VG.Proof.X25519.X86.num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k h => by
      rw [VG.Proof.X25519.X86.wv, hv k h, BitVec.toNat_ofNat]), VG.Proof.Ed25519.X86.num_digits]
    exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [P] at h; omega)
  rw [VG.Proof.X25519.X86.F, he, toFe_self]

end VG.Proof.Ed25519.X86
end

/-! Field programs and exact Edwards-coordinate formulas. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : BitVec 32) : VG.Proof.Ed25519.X86.Env := fun i => VG.Proof.X25519.X86.F m base (offset i)

def evalOp (op : FieldOp) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : VG.Proof.Ed25519.X86.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86.evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [VG.Proof.Ed25519.X86.evalOp, Function.update_apply]

theorem evalOp_add_apply (e : VG.Proof.Ed25519.X86.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86.evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [VG.Proof.Ed25519.X86.evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : VG.Proof.Ed25519.X86.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86.evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [VG.Proof.Ed25519.X86.evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env := ops.foldl (fun e op => VG.Proof.Ed25519.X86.evalOp op e) e

structure FieldKeep (x : BitVec 32) (s t : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s t
  frame : Frame [VG.Proof.X25519.X86.sub x 64 864] s.mem t.mem

theorem FieldKeep.refl (x : BitVec 32) (s : State) : VG.Proof.Ed25519.X86.FieldKeep x s s :=
  ⟨Keep.refl _, Frame.refl _ _⟩

theorem FieldKeep.trans {x : BitVec 32} {s t u : State}
    (h : VG.Proof.Ed25519.X86.FieldKeep x s t) (k : VG.Proof.Ed25519.X86.FieldKeep x t u) : VG.Proof.Ed25519.X86.FieldKeep x s u :=
  ⟨h.keep.trans k.keep, h.frame.trans k.frame⟩

theorem FieldKeep.ctx {x : BitVec 32} {s t : State}
    (h : VG.Proof.Ed25519.X86.FieldKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t := h.keep.ctx hc

theorem offset_inj {a b : Slot} (h : offset a = offset b) : a = b := by
  apply Fin.ext
  simp only [offset] at h
  omega

theorem restrict_update (e : Nat → Spec.X25519.Fe) (o : Slot) (v : Spec.X25519.Fe) :
    (fun i : Slot => Function.update e (offset o) v (offset i)) =
      Function.update (fun i : Slot => e (offset i)) o v := by
  funext i
  by_cases hi : i = o
  · subst i; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (VG.Proof.Ed25519.X86.offset_inj h))]

theorem const_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32) (o : Slot)
    (hf : Frame [VG.Proof.X25519.X86.sub x (offset o) 32] m m') :
    VG.Proof.Ed25519.X86.env m' x = Function.update (VG.Proof.Ed25519.X86.env m x) o (VG.Proof.X25519.X86.F m' x (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst i; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne hi]
    apply congrArg VG.Proof.X25519.toFe
    exact VG.Proof.X25519.X86.fe_frame1 hf hx (by simp only [offset]; omega)
      (by simp only [offset]; omega) (VG.Proof.X25519.X86.slot_ne (VG.Proof.Ed25519.X86.slot_valid o) (VG.Proof.Ed25519.X86.slot_valid i) (fun h => hi (VG.Proof.Ed25519.X86.offset_inj h)))

theorem raw_field_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) (op : Op)
    (hv : VG.Proof.X25519.X86.opValid 64 op = true) (o : Slot) (ho : VG.Proof.X25519.X86.opOut op = offset o) :
    WP isa (.block op.code) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.env t.mem x = Function.update (VG.Proof.Ed25519.X86.env s.mem x) o (VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x)) := by
  refine WP.mono (VG.Proof.X25519.X86.op_ok hc op hv) fun t ⟨hk, hf, he⟩ => ?_
  refine ⟨⟨hk, hf⟩, ?_⟩
  have hr := VG.Proof.Ed25519.X86.restrict_update (VG.Proof.X25519.X86.F s.mem x) o (VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x))
  funext i
  change VG.Proof.X25519.X86.F t.mem x (offset i) = Function.update (fun j => VG.Proof.X25519.X86.F s.mem x (offset j)) o (VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x)) i
  rw [← congrFun hr i]
  exact (he (offset i) (VG.Proof.Ed25519.X86.slot_valid i)).trans (by rw [ho])

theorem fieldOp_ok {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) (op : FieldOp) :
    WP isa (.block op.code) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧ VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.evalOp op (VG.Proof.Ed25519.X86.env s.mem x) := by
  cases op with
  | const o v =>
    refine WP.mono (VG.Proof.Ed25519.X86.constField_op hc o v) fun t ⟨hk, hf, hv⟩ => ?_
    refine ⟨⟨hk, VG.Proof.X25519.X86.frameWiden hf hc.fit (by simp only [offset]; omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega)⟩, ?_⟩
    rw [VG.Proof.Ed25519.X86.const_env hc.fit o hf, hv]; rfl
  | copy o a =>
    exact VG.Proof.Ed25519.X86.raw_field_ok hc (.copy (offset o) (offset a))
      (by simp only [VG.Proof.X25519.X86.opValid, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opIns, List.all_cons, List.all_nil, VG.Proof.Ed25519.X86.slot_valid]; rfl) o rfl
  | mul o a b =>
    exact VG.Proof.Ed25519.X86.raw_field_ok hc (.mul (offset o) (offset a) (offset b))
      (by simp only [VG.Proof.X25519.X86.opValid, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opIns, List.all_cons, List.all_nil, VG.Proof.Ed25519.X86.slot_valid]; rfl) o rfl
  | add o a b =>
    exact VG.Proof.Ed25519.X86.raw_field_ok hc (.add (offset o) (offset a) (offset b))
      (by simp only [VG.Proof.X25519.X86.opValid, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opIns, List.all_cons, List.all_nil, VG.Proof.Ed25519.X86.slot_valid]; rfl) o rfl
  | sub o a b =>
    exact VG.Proof.Ed25519.X86.raw_field_ok hc (.sub (offset o) (offset a) (offset b))
      (by simp only [VG.Proof.X25519.X86.opValid, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opIns, List.all_cons, List.all_nil, VG.Proof.Ed25519.X86.slot_valid]; rfl) o rfl

theorem fieldCode_ok (ops : List FieldOp) {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block (fieldCode ops)) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep x s t ∧ VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.evalOps ops (VG.Proof.Ed25519.X86.env s.mem x) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86.fieldOp_ok hc op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : VG.Proof.Ed25519.X86.Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : VG.Proof.Ed25519.X86.Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps pointAddOps e) 0 1 2 3 = VG.Proof.Ed25519.X86.addResult e 4 (by decide) := by
  rfl

theorem pointDouble_formula (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps pointDoubleOps e) 0 1 2 3 = VG.Proof.Ed25519.X86.addResult e 0 (by decide) := by
  rfl

theorem addResult_eq (e : VG.Proof.Ed25519.X86.Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86.addResult e q hq = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point e 0 1 2 3)
      (VG.Proof.Ed25519.X86.point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [VG.Proof.Ed25519.X86.addResult, VG.Proof.Ed25519.X86.point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : VG.Proof.Ed25519.X86.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point e 0 1 2 3) (VG.Proof.Ed25519.X86.point e 4 5 6 7) :=
  (VG.Proof.Ed25519.X86.pointAdd_formula e).trans (VG.Proof.Ed25519.X86.addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : VG.Proof.Ed25519.X86.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point e 0 1 2 3) (VG.Proof.Ed25519.X86.point e 0 1 2 3) :=
  (VG.Proof.Ed25519.X86.pointDouble_formula e).trans (VG.Proof.Ed25519.X86.addResult_eq e 0 (by decide) hd)

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CopyWords`. -/
section

/-! Bounded word copies between disjoint scratch ranges. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem addr_plus (x : BitVec 32) (a b : Nat) :
    VG.X86.addr (x + BitVec.ofNat 32 a) b = VG.X86.addr x (a + b) := by
  simp only [VG.X86.addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

structure CopyKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [VG.Proof.X25519.X86.sub x o n] s.mem t.mem

theorem CopyKeep.ctx {x : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86.CopyKeep x o n s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t :=
  hc.keep (h.gpr _ (by decide)) h.wr

theorem CopyKeep.refl (x : BitVec 32) (o n : Nat) (s : State) : VG.Proof.Ed25519.X86.CopyKeep x o n s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem CopyKeep.trans {x : BitVec 32} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.X86.CopyKeep x o n s t) (k : VG.Proof.Ed25519.X86.CopyKeep x o n t u) : VG.Proof.Ed25519.X86.CopyKeep x o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans k.frame⟩

theorem copyWorkspaceWord_ok {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (src dst : Reg) (hs : src ≠ .eax) (hd : dst ≠ .eax) (sa da a o n total : Nat)
    (hsa : s₀.gpr src = x + BitVec.ofNat 32 sa) (hda : s₀.gpr dst = x + BitVec.ofNat 32 da)
    (ha : sa + a + 4 * total ≤ 8192) (ho : da + o + 4 * total ≤ 8192)
    (hn : n < total) (hsep : sa + a + 4 * total ≤ da + o ∨ da + o + 4 * total ≤ sa + a)
    (hk : VG.Proof.Ed25519.X86.CopyKeep x (da + o) (4 * n) s₀ s)
    (hv : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (da + o + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (sa + a + 4 * j)) :
    WP isa (.block (workspaceCopyWord src dst a o n)) s fun t =>
      VG.Proof.Ed25519.X86.CopyKeep x (da + o) (4 * (n + 1)) s₀ t ∧
      ∀ j < n + 1, VG.Proof.X25519.X86.wd t.mem x (da + o + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (sa + a + 4 * j) := by
  have ps : s.gpr src = x + BitVec.ofNat 32 sa := (hk.gpr src hs).trans hsa
  have pd : s.gpr dst = x + BitVec.ofNat 32 da := (hk.gpr dst hd).trans hda
  refine Wp.wp_ldm ps (by rw [VG.Proof.Ed25519.X86.addr_plus, ← Nat.add_assoc]; exact hc.inRW (by omega_using [ha, hn]) (by decide))
    fun t ht => ?_
  have pt : t.gpr dst = x + BitVec.ofNat 32 da := (ht.other dst hd).trans pd
  have ct := (VG.Proof.X25519.X86.updKeep ht).ctx hc
  refine Wp.wp_stm pt (by rw [VG.Proof.Ed25519.X86.addr_plus, ← Nat.add_assoc]; exact ct.inW (by omega_using [ho, hn]) (by decide))
    fun u hu => WP.block_nil ?_
  have hvn : VG.Proof.X25519.X86.wd s.mem x (sa + a + 4 * n) = VG.Proof.X25519.X86.wd s₀.mem x (sa + a + 4 * n) :=
    VG.Proof.X25519.X86.wd_frame1 hk.frame hc.fit (by omega_using [ho, hn]) (by omega_using [ha, hn])
      (by omega_using [hsep, hn])
  have hm : u.mem = s.mem.writeW (VG.X86.addr x (da + o + 4 * n)) (VG.Proof.X25519.X86.wd s₀.mem x (sa + a + 4 * n)) := by
    rw [hu.mem, ht.mem, ht.gpr, VG.Proof.Ed25519.X86.addr_plus, VG.Proof.Ed25519.X86.addr_plus, ← Nat.add_assoc, ← Nat.add_assoc]
    exact congrArg (s.mem.writeW (VG.X86.addr x (da + o + 4 * n))) hvn
  refine ⟨⟨fun r hr => by rw [hu.gpr, ht.other r hr, hk.gpr r hr],
    by rw [hu.rd, ht.rd, hk.rd], by rw [hu.wr, ht.wr, hk.wr], ?_⟩, fun j hj => ?_⟩
  · rw [hm]
    exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden hk.frame hc.fit (Nat.le_refl _) (by omega) (by omega_using [ho, hn]))
      hc.fit (by omega_using [ho, hn]) (by omega) (by omega) _
  · rw [hm]
    by_cases he : j = n
    · subst j; exact VG.Proof.X25519.X86.wd_write_self _ _ _ _
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hc.fit, ho, hn, hj])
        (by omega_using [hc.fit, ho, hn]) (by omega_using [he])]
      exact hv j (by omega_using [hj, he])

theorem copyWorkspaceWords_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (src dst : Reg) (hs : src ≠ .eax) (hd : dst ≠ .eax) (sa da a o total : Nat)
    (hsa : s.gpr src = x + BitVec.ofNat 32 sa) (hda : s.gpr dst = x + BitVec.ofNat 32 da)
    (ha : sa + a + 4 * total ≤ 8192) (ho : da + o + 4 * total ≤ 8192)
    (hsep : sa + a + 4 * total ≤ da + o ∨ da + o + 4 * total ≤ sa + a) :
    ∀ n ≤ total, WP isa (.block (workspaceCopyWords src dst a o n)) s fun t =>
      VG.Proof.Ed25519.X86.CopyKeep x (da + o) (4 * n) s t ∧
      ∀ j < n, VG.Proof.X25519.X86.wd t.mem x (da + o + 4 * j) = VG.Proof.X25519.X86.wd s.mem x (sa + a + 4 * j)
  | 0, _ => WP.block_nil ⟨CopyKeep.refl _ _ _ _, fun j hj => by omega⟩
  | n + 1, hn => by
    rw [workspaceCopyWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86.copyWorkspaceWords_ok hc src dst hs hd sa da a o total hsa hda ha ho hsep n (by omega))
      fun t ⟨hk, hv⟩ => ?_
    exact VG.Proof.Ed25519.X86.copyWorkspaceWord_ok (hk.ctx hc) src dst hs hd sa da a o n total hsa hda ha ho (by omega) hsep hk hv

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointTable`. -/
section

/-! Saving and loading four consecutive field coordinates. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def tablePoint (m : Mem) (x : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨VG.Proof.X25519.X86.F m x o, VG.Proof.X25519.X86.F m x (o + 32), VG.Proof.X25519.X86.F m x (o + 64), VG.Proof.X25519.X86.F m x (o + 96)⟩

theorem fields_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, VG.Proof.X25519.X86.wd m' x (o + 4 * k) = VG.Proof.X25519.X86.wd m x (a + 4 * k))
    (j : Nat) (hj : j < 4) : VG.Proof.X25519.X86.F m' x (o + 32 * j) = VG.Proof.X25519.X86.F m x (a + 32 * j) := by
  apply congrArg VG.Proof.X25519.toFe
  apply VG.Proof.X25519.X86.num_congr
  intro k hk
  have hv := h (8 * j + k) (by omega)
  have he : o + 32 * j + 4 * k = o + 4 * (8 * j + k) := by omega
  have he' : a + 32 * j + 4 * k = a + 4 * (8 * j + k) := by omega
  exact congrArg BitVec.toNat (he.symm ▸ he'.symm ▸ hv)

theorem point_mk_congr {a b c d a' b' c' d' : Spec.X25519.Fe}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    Spec.Ed25519.Point.mk a b c d = Spec.Ed25519.Point.mk a' b' c' d' := by
  cases ha; cases hb; cases hc; cases hd; rfl

theorem table_point_of_words {m m' : Mem} {x : BitVec 32} {a o : Nat}
    (h : ∀ k < 32, VG.Proof.X25519.X86.wd m' x (o + 4 * k) = VG.Proof.X25519.X86.wd m x (a + 4 * k)) :
    VG.Proof.Ed25519.X86.tablePoint m' x o = VG.Proof.Ed25519.X86.tablePoint m x a := by
  have h0 := VG.Proof.Ed25519.X86.fields_of_words h 0 (by decide)
  have h1 := VG.Proof.Ed25519.X86.fields_of_words h 1 (by decide)
  have h2 := VG.Proof.Ed25519.X86.fields_of_words h 2 (by decide)
  have h3 := VG.Proof.Ed25519.X86.fields_of_words h 3 (by decide)
  exact VG.Proof.Ed25519.X86.point_mk_congr h0 h1 h2 h3

theorem pointToTable_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      VG.Proof.Ed25519.X86.CopyKeep x o 128 s t ∧ VG.Proof.Ed25519.X86.tablePoint t.mem x o = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (VG.Proof.Ed25519.X86.copyWorkspaceWords_ok hc .edi .edx (by decide) (by decide) 0 o 64 0 32
    hb hp (by decide) (by omega) (Or.inl hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  refine ⟨hk, ?_⟩
  exact VG.Proof.Ed25519.X86.table_point_of_words hv

theorem pointFromTable_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat}
    (hp : s.gpr .edx = x + BitVec.ofNat 32 o) (hlo : 192 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      VG.Proof.Ed25519.X86.CopyKeep x 64 128 s t ∧ VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = VG.Proof.Ed25519.X86.tablePoint s.mem x o := by
  have hb : s.gpr .edi = x + BitVec.ofNat 32 0 := by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hc.edi
  refine WP.mono (VG.Proof.Ed25519.X86.copyWorkspaceWords_ok hc .edx .edi (by decide) (by decide) o 0 0 64 32
    hp hb (by omega) (by decide) (Or.inr hlo) 32 (Nat.le_refl _)) fun t ⟨hk, hv⟩ => ?_
  exact ⟨hk, VG.Proof.Ed25519.X86.table_point_of_words hv⟩

theorem table_env {x : BitVec 32} {o n : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (ho : 768 ≤ o) (hn : o + n ≤ 8192) : VG.Proof.Ed25519.X86.env m' x = VG.Proof.Ed25519.X86.env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact VG.Proof.X25519.X86.fe_frame1 h hx hn (by simp only [offset]; omega)
    (Or.inl (by simp only [offset]; omega))

theorem tablePoint_frame {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (h : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hsep : a + 128 ≤ o ∨ o + n ≤ a) :
    VG.Proof.Ed25519.X86.tablePoint m' x a = VG.Proof.Ed25519.X86.tablePoint m x a := by
  apply VG.Proof.Ed25519.X86.table_point_of_words
  intro k hk
  exact VG.Proof.X25519.X86.wd_frame1 h hx ho (by omega) (by omega)

theorem CopyKeep.high {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.CopyKeep x 64 128 s t)
    (hc : VG.Proof.Ed25519.X86.Ctx x s) (i : Slot) (hi : 4 ≤ i.val) : VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  apply congrArg VG.Proof.X25519.toFe
  exact VG.Proof.X25519.X86.fe_frame1 h.frame hc.fit (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Points`. -/
section

/-! Exact extended-coordinate operations and the slots they preserve. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .add o _ _ | .sub o _ _ => o

theorem evalOp_unchanged (op : FieldOp) (e : VG.Proof.Ed25519.X86.Env) (i : Slot) (hi : i ≠ VG.Proof.Ed25519.X86.fieldDest op) :
    VG.Proof.Ed25519.X86.evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : VG.Proof.Ed25519.X86.Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ VG.Proof.Ed25519.X86.fieldDest op) : VG.Proof.Ed25519.X86.evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change VG.Proof.Ed25519.X86.evalOps ops (VG.Proof.Ed25519.X86.evalOp op e) i = e i
    rw [ih (VG.Proof.Ed25519.X86.evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), VG.Proof.Ed25519.X86.evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (VG.Proof.Ed25519.X86.fieldDest op).val < 16)
    (e : VG.Proof.Ed25519.X86.Env) (i : Slot) (hi : 16 ≤ i.val) : VG.Proof.Ed25519.X86.evalOps ops e i = e i := by
  apply VG.Proof.Ed25519.X86.evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem pointAdd_high (e : VG.Proof.Ed25519.X86.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.X86.evalOps pointAddOps e i = e i :=
  VG.Proof.Ed25519.X86.point_ops_high _ (by decide) e i hi

theorem pointDouble_high (e : VG.Proof.Ed25519.X86.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.X86.evalOps pointDoubleOps e i = e i :=
  VG.Proof.Ed25519.X86.point_ops_high _ (by decide) e i hi

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

theorem savePoint_eval (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps savePointOps e) 17 18 19 20 = VG.Proof.Ed25519.X86.point e 0 1 2 3 := rfl

theorem restorePoint_eval (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps restorePointOps e) 0 1 2 3 = VG.Proof.Ed25519.X86.point e 17 18 19 20 := rfl

theorem copyPointToQ_eval (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps copyPointToQOps e) 4 5 6 7 = VG.Proof.Ed25519.X86.point e 0 1 2 3 := rfl

theorem pointDouble_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (hd : VG.Proof.Ed25519.X86.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointDouble) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep base s t ∧ VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem base) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem base i = VG.Proof.Ed25519.X86.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok pointDoubleOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, VG.Proof.Ed25519.X86.pointDouble_eval _ hd, VG.Proof.Ed25519.X86.pointDouble_high _⟩

theorem pointAdd_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s)
    (hd : VG.Proof.Ed25519.X86.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointAdd) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep base s t ∧ VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem base i = VG.Proof.Ed25519.X86.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok pointAddOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, VG.Proof.Ed25519.X86.pointAdd_eval _ hd, VG.Proof.Ed25519.X86.pointAdd_high _⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PowerEnv`. -/
section

/-! Fixed-count squaring and compositional field exponentiation. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (mul)
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env := Function.update e o (e a * e b)
def opSqn (o a : Slot) (n : Nat) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env := Function.update e o (sqn (e a) n)

structure IKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [VG.Proof.X25519.X86.sub x 64 864] s.mem t.mem

theorem IKeep.refl (x : BitVec 32) (s : State) : VG.Proof.Ed25519.X86.IKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem IKeep.trans {x : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (k : VG.Proof.Ed25519.X86.IKeep x t u) :
    VG.Proof.Ed25519.X86.IKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem IKeep.ctx {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t :=
  hc.keep h.edi h.wr

theorem IKeep.of_field {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.FieldKeep x s t) : VG.Proof.Ed25519.X86.IKeep x s t :=
  ⟨h.keep.edi, h.keep.esp, h.keep.rd, h.keep.wr, h.frame⟩

theorem IKeep.of_counter {x : BitVec 32} {s t : State} {v : BitVec 32}
    (h : Wp.Upd s t .esi v) : VG.Proof.Ed25519.X86.IKeep x s t :=
  ⟨h.other _ (by decide), h.other _ (by decide), h.rd, h.wr,
    by rw [h.mem]; exact Frame.refl _ _⟩

def ISpec (x : BitVec 32) (c : Prog isa) (f : VG.Proof.Ed25519.X86.Env → VG.Proof.Ed25519.X86.Env) : Prop :=
  ∀ s, VG.Proof.Ed25519.X86.Ctx x s → WP isa c s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧ VG.Proof.Ed25519.X86.env t.mem x = f (VG.Proof.Ed25519.X86.env s.mem x)

theorem ISpec.seq {x : BitVec 32} {c d : Prog isa} {f g : VG.Proof.Ed25519.X86.Env → VG.Proof.Ed25519.X86.Env}
    (h : VG.Proof.Ed25519.X86.ISpec x c f) (k : VG.Proof.Ed25519.X86.ISpec x d g) : VG.Proof.Ed25519.X86.ISpec x (.seq c d) (fun e => g (f e)) :=
  fun s hc => WP.seq (WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩)

theorem ISpec.append {x : BitVec 32} {c d : List Instr} {f g : VG.Proof.Ed25519.X86.Env → VG.Proof.Ed25519.X86.Env}
    (h : VG.Proof.Ed25519.X86.ISpec x (.block c) f) (k : VG.Proof.Ed25519.X86.ISpec x (.block d) g) :
    VG.Proof.Ed25519.X86.ISpec x (.block (c ++ d)) (fun e => g (f e)) := fun s hc => by
  rw [WP.block_append_iff]
  exact WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩

abbrev ISlot (o : Slot) : Prop := 14 ≤ o.val ∧ o.val < 18

theorem mulI (x : BitVec 32) (o a b : Slot) (_ho : VG.Proof.Ed25519.X86.ISlot o) :
    VG.Proof.Ed25519.X86.ISpec x (.block (VG.Impl.X25519.X86.mul (offset o) (offset a) (offset b))) (VG.Proof.Ed25519.X86.opMul o a b) := fun _ hc =>
  WP.mono (VG.Proof.Ed25519.X86.fieldOp_ok hc (.mul o a b)) fun _ ⟨hk, he⟩ => ⟨IKeep.of_field hk, he⟩

theorem opMul_update (o : Slot) (e : VG.Proof.Ed25519.X86.Env) (v : Spec.X25519.Fe) :
    VG.Proof.Ed25519.X86.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.Ed25519.X86.opMul, Function.update_self, Function.update_idem]

theorem sqLoop_ok {x : BitVec 32} {s₀ : State} (hc₀ : VG.Proof.Ed25519.X86.Ctx x s₀) (o : Slot)
    (v : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → VG.Proof.Ed25519.X86.IKeep x s₀ s → s.gpr .esi = BitVec.ofNat 32 m →
      VG.Proof.Ed25519.X86.env s.mem x = Function.update (VG.Proof.Ed25519.X86.env s₀.mem x) o (sqn v (n - m)) →
      WP isa (.loop (.block (VG.Impl.X25519.X86.mul (offset o) (offset o) (offset o) ++
        ([.alu .sub .esi (.imm 1)] : List Instr))) .ne) s fun t =>
        VG.Proof.Ed25519.X86.IKeep x s₀ t ∧ VG.Proof.Ed25519.X86.env t.mem x = Function.update (VG.Proof.Ed25519.X86.env s₀.mem x) o (sqn v n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ VG.Proof.Ed25519.X86.IKeep x s₀ s ∧
    s.gpr .esi = BitVec.ofNat 32 m ∧
    VG.Proof.Ed25519.X86.env s.mem x = Function.update (VG.Proof.Ed25519.X86.env s₀.mem x) o (sqn v (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldOp_ok (hk.ctx hc₀) (.mul o o o)) fun t ⟨ht, et⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  have ku := hk.trans ((IKeep.of_field ht).trans (IKeep.of_counter hu))
  have bu : u.gpr .esi = BitVec.ofNat 32 (m - 1) := by
    rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred h1
  have eu : VG.Proof.Ed25519.X86.env u.mem x = Function.update (VG.Proof.Ed25519.X86.env s₀.mem x) o (sqn v (n - (m - 1))) := by
    rw [hu.mem, et, he]
    change VG.Proof.Ed25519.X86.opMul o o o (Function.update _ o _) = _
    rw [VG.Proof.Ed25519.X86.opMul_update, show n - (m - 1) = (n - m) + 1 by omega]
    rfl
  have ev : isa.eval .ne u = some (!decide (m - 1 = 0)) := by
    show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2, hn])]
    rfl
  by_cases hm : m = 1
  · subst m
    exact .inl ⟨by rw [ev]; rfl, ku, by simpa only [Nat.sub_self, Nat.sub_zero] using eu⟩
  · exact .inr ⟨by rw [ev]; simp only [show m - 1 ≠ 0 by omega, decide_false]; rfl,
      m - 1, by omega, by omega, by omega, ku, bu, eu⟩

theorem sqnI (x : BitVec 32) (o a : Slot) (_ho : VG.Proof.Ed25519.X86.ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    VG.Proof.Ed25519.X86.ISpec x (Impl.Ed25519.X86.sqn (offset o) (offset a) n) (VG.Proof.Ed25519.X86.opSqn o a n) := by
  intro s hc
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldOp_ok hc (.mul o a a)) fun t ⟨ht, et⟩ => ?_
  refine Wp.wp_movi fun u hu => WP.block_nil ?_
  refine VG.Proof.Ed25519.X86.sqLoop_ok hc o (VG.Proof.Ed25519.X86.env s.mem x a) n hn' (n - 1) u (by omega) (by omega)
    ((IKeep.of_field ht).trans (IKeep.of_counter hu)) hu.gpr ?_
  rw [hu.mem, et, show n - (n - 1) = 1 by omega]
  rfl

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointPowers`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointPowersFrame`. -/
section
/-! Merged from `Proof.Ed25519.X86.PointTableAddr`. -/
section
/-! A public table index is multiplied by the point's 128 bytes. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tableAddr_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (off j : Nat)
    (hj : j < 2 ^ 25) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr off)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (off + 128 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => VG.Proof.X25519.X86.wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : VG.Proof.X25519.X86.Keep s s₆ := (VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans (h₃.keep.trans
    ((VG.Proof.X25519.X86.updKeep h₄).trans ((VG.Proof.X25519.X86.updKeep h₅).trans (VG.Proof.X25519.X86.updKeep h₆)))))
  have hv : s₃.gpr .eax = BitVec.ofNat 32 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    change VG.Proof.X25519.X86.v s₃ .eax = _
    rw [h₃.eax]
    simp only [VG.Proof.X25519.X86.v, h₂.other .eax (by decide), h₁.gpr, hb, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm j 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * j)) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * j) off]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointLoop`. -/
section
/-! Fixed-size batches of powers use exactly the specified point formula. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem doubleBody_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {n : Nat}
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 n)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      VG.Proof.Ed25519.X86.IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne t = some (!decide (n - 1 = 0)) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointDouble_ok hc hd) fun t ⟨ht, pt, high⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  refine ⟨(IKeep.of_field ht).trans (IKeep.of_counter hu), ?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred hn
  · show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred hn, Wp.ofNat_beq_zero (by omega_using [hn'])]
    rfl
  · rw [hu.mem]; exact pt
  · rw [hu.mem]; exact high

structure DoubleInv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 16
  keep : VG.Proof.Ed25519.X86.IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env s.mem x i = VG.Proof.Ed25519.X86.env s₀.mem x i

theorem double16_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) 16 ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := VG.Proof.Ed25519.X86.DoubleInv x s) ?_ 16 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    have du : VG.Proof.Ed25519.X86.env u.mem x 16 = Spec.Ed25519.d := (h.high 16 (by decide)).trans hd
    refine WP.mono (VG.Proof.Ed25519.X86.doubleBody_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter du)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    have kk := h.keep.trans kv
    have pp : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env v.mem x) 0 1 2 3 =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (16 - (n - 1)) := by
      exact pv.trans ((congrArg₂ Spec.Ed25519.pointAdd h.value h.value).trans
        (by rw [show 16 - (n - 1) = (16 - n) + 1 by omega_using [h.lo, h.hi]]; rfl))
    have hh : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env v.mem x i = VG.Proof.Ed25519.X86.env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem]; rfl
  · rw [ht.mem]; exact fun _ _ => rfl

end VG.Proof.Ed25519.X86
end

/-! Frames for public counters, arithmetic and point tables. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def PowersFrame (x : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [VG.Proof.X25519.X86.sub x 24 4, VG.Proof.X25519.X86.sub x 64 864, VG.Proof.X25519.X86.sub x o n] m m'

structure PowersKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : VG.Proof.Ed25519.X86.PowersFrame x o n s.mem t.mem

theorem PowersKeep.refl (x : BitVec 32) (o n : Nat) (s : State) : VG.Proof.Ed25519.X86.PowersKeep x o n s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem PowersKeep.ctx {x : BitVec 32} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86.PowersKeep x o n s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t := hc.keep h.edi h.wr

theorem PowersKeep.trans {x : BitVec 32} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.X86.PowersKeep x o n s t) (k : VG.Proof.Ed25519.X86.PowersKeep x o n t u) : VG.Proof.Ed25519.X86.PowersKeep x o n s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem PowersFrame.mono {x : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86.PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : VG.Proof.Ed25519.X86.PowersFrame x o' n' m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.X25519.X86.sub x 24 4, by simp, fun _ ha => ha⟩
  · exact ⟨VG.Proof.X25519.X86.sub x 64 864, by simp, fun _ ha => ha⟩
  · exact ⟨VG.Proof.X25519.X86.sub x o' n', by simp, VG.Proof.X25519.X86.sub_sub hx ho hn hob⟩

theorem PowersKeep.mono {x : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86.PowersKeep x o n s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : VG.Proof.Ed25519.X86.PowersKeep x o' n' s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono hc.fit ho hn hob⟩

theorem PowersKeep.of_ikeep {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (o n : Nat) :
    VG.Proof.Ed25519.X86.PowersKeep x o n s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono (fun _r hr => List.mem_cons_of_mem _
    (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))⟩

theorem PowersKeep.of_copy {x : BitVec 32} {o n : Nat} {s t : State} (h : VG.Proof.Ed25519.X86.CopyKeep x o n s t) :
    VG.Proof.Ed25519.X86.PowersKeep x o n s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr,
    h.frame.mono (fun _r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩

theorem PowersKeep.of_counter {x : BitVec 32} {s t : State} (o n : Nat)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [VG.Proof.X25519.X86.sub x 24 4] s.mem t.mem) :
    VG.Proof.Ed25519.X86.PowersKeep x o n s t :=
  ⟨he, hs, hr, hw, hf.mono (fun _r h => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))⟩

theorem workspace_counter {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    VG.Proof.X25519.X86.wd t.mem x 24 = VG.Proof.X25519.X86.wd s.mem x 24 :=
  VG.Proof.X25519.X86.wd_frame1 h.frame hc.fit (by decide) (by decide) (Or.inl (by decide))

theorem workspace_table {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (o : Nat) (hlo : 928 ≤ o) (ho : o + 128 ≤ 8192) :
    VG.Proof.Ed25519.X86.tablePoint t.mem x o = VG.Proof.Ed25519.X86.tablePoint s.mem x o :=
  VG.Proof.Ed25519.X86.tablePoint_frame hc.fit h.frame (by decide) ho (Or.inr hlo)

theorem PowersFrame.table {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86.PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hlo : 928 ≤ a)
    (hsep : a + 128 ≤ o ∨ o + n ≤ a) : VG.Proof.Ed25519.X86.tablePoint m' x a = VG.Proof.Ed25519.X86.tablePoint m x a := by
  apply VG.Proof.Ed25519.X86.table_point_of_words
  intro k hk
  apply VG.Proof.X25519.X86.wd_frame h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact VG.Proof.X25519.X86.sub_disj (by omega) (by omega) (by omega)

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointPowersCounter`. -/
section
/-! The public checkpoint counter occupies bytes24 through27. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc)

theorem word_sub_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  rw [show (0 : BitVec 32) + BitVec.ofNat 32 b = BitVec.ofNat 32 b from BitVec.zero_add _]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using ht
  · exact congrArg (BitVec.ofNat 32)

theorem powersLoad_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block [.mov .esi (.mem (sc 24))]) s fun t =>
      VG.Proof.Ed25519.X86.IKeep x s t ∧ t.mem = s.mem ∧ t.gpr .esi = VG.Proof.X25519.X86.wd s.mem x 24 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  exact ⟨IKeep.of_counter ht, ht.mem, ht.gpr⟩

theorem powersNext_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (j count o n : Nat)
    (hj : j + 1 < 2 ^ 32) (hcount : count < 2 ^ 32) (hv : VG.Proof.X25519.X86.wd s.mem x 24 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      VG.Proof.Ed25519.X86.PowersKeep x o n s t ∧ VG.Proof.X25519.X86.wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      Frame [VG.Proof.X25519.X86.sub x 24 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => ?_
  refine Wp.wp_addi fun u hu => ?_
  have eu : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by
    rw [hu.gpr, ht.gpr]
    change VG.Proof.X25519.X86.wd s.mem x 24 + 1 = _
    rw [hv, BitVec.ofNat_add]; rfl
  have cu := (IKeep.of_counter ht).trans (IKeep.of_counter hu) |>.ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun v hv' => ?_
  refine Wp.wp_cmpi fun w hw _ hz => WP.block_nil ?_
  have hm : w.mem = s.mem.writeW (VG.X86.addr x 24) (BitVec.ofNat 32 (j + 1)) := by
    rw [hw.mem, hv'.mem, hu.mem, ht.mem, eu]
  have fr : Frame [VG.Proof.X25519.X86.sub x 24 4] s.mem w.mem := by
    rw [hm]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ fr, ?_, ?_, fr⟩
  · rw [hw.gpr, hv'.gpr, hu.other .edi (by decide), ht.other .edi (by decide)]
  · rw [hw.gpr, hv'.gpr, hu.other .esp (by decide), ht.other .esp (by decide)]
  · rw [hw.rd, hv'.rd, hu.rd, ht.rd]
  · rw [hw.wr, hv'.wr, hu.wr, ht.wr]
  · rw [hm, VG.Proof.X25519.X86.wd_write_self]
  · show w.zf.map (!·) = _
    rw [hz, hv'.gpr, eu, VG.Proof.Ed25519.X86.word_sub_eq hj hcount]; rfl

theorem powersInit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (o n : Nat) :
    WP isa (.block [.mov .eax (.imm 0), .store (sc 24) .eax]) s fun t =>
      VG.Proof.Ed25519.X86.PowersKeep x o n s t ∧ VG.Proof.X25519.X86.wd t.mem x 24 = 0 ∧ Frame [VG.Proof.X25519.X86.sub x 24 4] s.mem t.mem := by
  refine Wp.wp_movi fun t ht => ?_
  have ct := (VG.Proof.X25519.X86.updKeep ht).ctx hc
  refine Wp.wp_stm ct.edi (ct.inW (by decide) (by decide)) fun u hu => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (VG.X86.addr x 24) (0 : BitVec 32) := by rw [hu.mem, ht.mem, ht.gpr]
  have hf : Frame [VG.Proof.X25519.X86.sub x 24 4] s.mem u.mem := by
    rw [hm]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ hf, ?_, hf⟩
  · rw [hu.gpr, ht.other .edi (by decide)]
  · rw [hu.gpr, ht.other .esp (by decide)]
  · rw [hu.rd, ht.rd]
  · rw [hu.wr, ht.wr]
  · rw [hm, VG.Proof.X25519.X86.wd_write_self]

theorem counter_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [VG.Proof.X25519.X86.sub x 24 4] m m') : VG.Proof.Ed25519.X86.env m' x = VG.Proof.Ed25519.X86.env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact VG.Proof.X25519.X86.fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86
end

/-! Write the current point, then advance one or sixteen doublings. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem IKeep.of_mem {x : BitVec 32} {s t : State} (h : VG.Proof.X25519.X86.Keep s t) (hm : t.mem = s.mem) :
    VG.Proof.Ed25519.X86.IKeep x s t := ⟨h.edi, h.esp, h.rd, h.wr, by rw [hm]; exact Frame.refl _ _⟩

theorem powerBatch_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (powerStride batch) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  cases batch with
  | true => exact VG.Proof.Ed25519.X86.double16_ok hc hd
  | false => exact WP.mono (VG.Proof.Ed25519.X86.pointDouble_ok hc hd) fun _ ⟨hk, hp, hh⟩ => ⟨IKeep.of_field hk, hp, hh⟩

theorem powersBody_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (start count j : Nat) (batch : Bool) (hj : j < count) (hc' : count ≤ 32)
    (hlo : 928 ≤ start) (hfit : start + 128 * count ≤ 8192)
    (hindex : VG.Proof.X25519.X86.wd s.mem x 24 = BitVec.ofNat 32 j) (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (powersBody start count batch) s fun t =>
      VG.Proof.Ed25519.X86.PowersKeep x (start + 128 * j) 128 s t ∧ VG.Proof.X25519.X86.wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (powerStride batch) ∧
      VG.Proof.Ed25519.X86.tablePoint t.mem x (start + 128 * j) = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.powersLoad_ok hc) fun s₁ ⟨k₁, m₁, b₁⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.tableAddr_ok (k₁.ctx hc) start j (by omega) (b₁.trans hindex)) fun s₂ ⟨k₂, m₂, p₂⟩ => ?_
  have c₂ := k₂.ctx (k₁.ctx hc)
  refine WP.mono (VG.Proof.Ed25519.X86.pointToTable_ok c₂ p₂ (by omega) (by omega)) fun s₃ ⟨k₃, p₃⟩ => ?_
  have c₃ := k₃.ctx c₂
  have e₃ : VG.Proof.Ed25519.X86.env s₃.mem x = VG.Proof.Ed25519.X86.env s.mem x := by
    rw [VG.Proof.Ed25519.X86.table_env hc.fit k₃.frame (by omega) (by omega), m₂, m₁]
  have i₃ : VG.Proof.X25519.X86.wd s₃.mem x 24 = BitVec.ofNat 32 j := by
    rw [VG.Proof.X25519.X86.wd_frame1 k₃.frame hc.fit (by omega) (by decide) (Or.inl (by omega)), m₂, m₁]
    exact hindex
  have pk₃ : VG.Proof.Ed25519.X86.PowersKeep x (start + 128 * j) 128 s s₃ :=
    ((PowersKeep.of_ikeep k₁ _ _).trans
      (PowersKeep.of_ikeep (IKeep.of_mem k₂ m₂) _ _)).trans (PowersKeep.of_copy k₃)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.powerBatch_ok c₃ (by rw [e₃]; exact hd) batch) fun s₄ ⟨k₄, p₄, h₄⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.powersNext_ok (k₄.ctx c₃) j count (start + 128 * j) 128 (by omega) (by omega)
    ((VG.Proof.Ed25519.X86.workspace_counter k₄ c₃).trans i₃)) fun s₅ ⟨k₅, i₅, z₅, f₅⟩ => ?_
  have e₅ : VG.Proof.Ed25519.X86.env s₅.mem x = VG.Proof.Ed25519.X86.env s₄.mem x := VG.Proof.Ed25519.X86.counter_env hc.fit f₅
  refine ⟨(pk₃.trans (PowersKeep.of_ikeep k₄ _ _)).trans k₅, i₅, z₅, ?_, ?_, ?_⟩
  · rw [e₅, p₄, e₃]
  · rw [VG.Proof.Ed25519.X86.tablePoint_frame hc.fit f₅ (by decide) (by omega) (Or.inr (by omega)),
      VG.Proof.Ed25519.X86.workspace_table k₄ c₃ _ (by omega) (by omega), p₃, m₂, m₁]
  · intro i hi
    rw [e₅, h₄ i hi, e₃]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd`. -/
section

/-! Load a table point while preserving the accumulator for selection. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.of_mem {x : BitVec 32} {s t : State} (h : VG.Proof.X25519.X86.Keep s t) (hm : t.mem = s.mem) :
    VG.Proof.Ed25519.X86.FieldKeep x s t := ⟨h, by rw [hm]; exact Frame.refl _ _⟩

theorem FieldKeep.of_copy {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.CopyKeep x 64 128 s t)
    (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.FieldKeep x s t :=
  ⟨⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr⟩,
    VG.Proof.X25519.X86.frameWiden h.frame hc.fit (by decide) (by decide) (by decide)⟩

theorem point_congr {e f : VG.Proof.Ed25519.X86.Env} (x y z t : Slot) (hx : e x = f x) (hy : e y = f y)
    (hz : e z = f z) (ht : e t = f t) : VG.Proof.Ed25519.X86.point e x y z t = VG.Proof.Ed25519.X86.point f x y z t :=
  VG.Proof.Ed25519.X86.point_mk_congr hx hy hz ht

theorem savePoint_d (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.evalOps savePointOps e 16 = e 16 := rfl
theorem copyPointToQ_d (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.evalOps copyPointToQOps e 16 = e 16 := rfl
theorem restorePoint_d (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.evalOps restorePointOps e 16 = e 16 := rfl
theorem copyPointToQ_saved (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps copyPointToQOps e) 17 18 19 20 = VG.Proof.Ed25519.X86.point e 17 18 19 20 := rfl
theorem restorePoint_saved (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps restorePointOps e) 17 18 19 20 = VG.Proof.Ed25519.X86.point e 17 18 19 20 := rfl
theorem restorePoint_q (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.evalOps restorePointOps e) 4 5 6 7 = VG.Proof.Ed25519.X86.point e 4 5 6 7 := rfl

theorem prepareAdd_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (j : Nat) (hj : j < 16) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block prepareAdd) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 4 5 6 7 = VG.Proof.Ed25519.X86.tablePoint s.mem x (5120 + 128 * j) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 17 18 19 20 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = VG.Proof.Ed25519.X86.env s.mem x 16 := by
  simp only [prepareAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok savePointOps hc) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.tableAddr_ok (ka.ctx hc) 5120 j (by omega) (ka.keep.esi.trans hb))
    fun b ⟨kb, mb, pb⟩ => ?_
  have cb := kb.ctx (ka.ctx hc)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointFromTable_ok cb pb (by omega) (by omega)) fun c ⟨kc, pc⟩ => ?_
  have ks : VG.Proof.Ed25519.X86.FieldKeep x s c := ka.trans ((FieldKeep.of_mem kb mb).trans (FieldKeep.of_copy kc cb))
  have savec : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env c.mem x) 17 18 19 20 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 := by
    rw [VG.Proof.Ed25519.X86.point_congr _ _ _ _ (kc.high cb 17 (by decide)) (kc.high cb 18 (by decide))
      (kc.high cb 19 (by decide)) (kc.high cb 20 (by decide)), mb, ea, VG.Proof.Ed25519.X86.savePoint_eval]
  have dc : VG.Proof.Ed25519.X86.env c.mem x 16 = VG.Proof.Ed25519.X86.env s.mem x 16 := by rw [kc.high cb 16 (by decide), mb, ea, VG.Proof.Ed25519.X86.savePoint_d]
  have tc : VG.Proof.Ed25519.X86.tablePoint b.mem x (5120 + 128 * j) = VG.Proof.Ed25519.X86.tablePoint s.mem x (5120 + 128 * j) := by
    rw [mb]
    exact VG.Proof.Ed25519.X86.workspace_table (IKeep.of_field ka) hc _ (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok copyPointToQOps (ks.ctx hc)) fun d ⟨kd, ed⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok restorePointOps (kd.ctx (ks.ctx hc))) fun t ⟨kt, et⟩ => ?_
  refine ⟨ks.trans (kd.trans kt), ?_, ?_, ?_, ?_⟩
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_eval, ed, VG.Proof.Ed25519.X86.copyPointToQ_saved, savec]
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_q, ed, VG.Proof.Ed25519.X86.copyPointToQ_eval, pc, tc]
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_saved, ed, VG.Proof.Ed25519.X86.copyPointToQ_saved, savec]
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_d, ed, VG.Proof.Ed25519.X86.copyPointToQ_d, dc]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarStep`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

theorem scalarK_num : VG.Proof.X25519.X86.num (fun k => (scalarK k).toNat) 8 = 2 ^ 256 - L := by decide

theorem scalarDouble_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) (hb : VG.Proof.X25519.X86.acc s < 2) :
    WP isa (.block scalarDouble) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x VG.Impl.Ed25519.X86.scalarR 32] s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = 2 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + VG.Proof.X25519.X86.acc s := by
  have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x [.mulI (VG.Impl.Ed25519.X86.scalarR + 4 * k) 2]) 8 =
      2 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR := by
    rw [VG.Proof.X25519.X86.fe, ← VG.Proof.X25519.X86.num_mul]
    refine VG.Proof.X25519.X86.num_congr fun k _ => ?_
    simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    change VG.Proof.X25519.X86.wv s.mem x (VG.Impl.Ed25519.X86.scalarR + 4 * k) * 2 = 2 * VG.Proof.X25519.X86.wv s.mem x (VG.Impl.Ed25519.X86.scalarR + 4 * k)
    exact Nat.mul_comm _ _
  refine WP.mono (VG.Proof.X25519.X86.cols_ok hc _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by omega_using [hb])) fun t ⟨keep, frame, eq, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact ⟨by simp only [VG.Impl.Ed25519.X86.scalarR]; omega_using [hk], Or.inr (Nat.le_refl _)⟩
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := VG.Proof.X25519.X86.wv_lt s.mem x (VG.Impl.Ed25519.X86.scalarR + 4 * k)
    change VG.Proof.X25519.X86.wv s.mem x (VG.Impl.Ed25519.X86.scalarR + 4 * k) * 2 < 2 ^ 68
    omega_using [hw]
  · rw [hs] at eq
    change VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR + 2 ^ 256 * VG.Proof.X25519.X86.acc t = _ at eq
    have hL := order_bound
    have hz : VG.Proof.X25519.X86.acc t = 0 := by omega_using [eq, hr, hb, hL]
    exact ⟨keep, frame, by rw [hz, Nat.mul_zero, Nat.add_zero] at eq; omega_using [eq]⟩

theorem scalarSubtract_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block scalarSubtract) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.X25519.X86.T + 2 ^ 256 * VG.Proof.X25519.X86.acc t = VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + (2 ^ 256 - L) := by
  refine WP.block_append (WP.mono VG.Proof.X25519.X86.zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv u.mem x [.addM (VG.Impl.Ed25519.X86.scalarR + 4 * k), .addI (scalarK k)]) 8 =
      VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + (2 ^ 256 - L) := by
    rw [← VG.Proof.Ed25519.X86.scalarK_num, VG.Proof.X25519.X86.fe, ← VG.Proof.X25519.X86.num_add, mu]
    exact VG.Proof.X25519.X86.num_congr fun k _ => by
      simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  refine WP.mono (VG.Proof.X25519.X86.cols_ok (ku.ctx hc) _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
      exact ⟨by simp only [VG.Impl.Ed25519.X86.scalarR]; omega_using [hk], Or.inl (by simp only [VG.Impl.Ed25519.X86.scalarR, VG.Impl.X25519.X86.T]; omega_using [hk])⟩
    · simp only [VG.Proof.X25519.X86.treads, List.not_mem_nil] at hd
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := VG.Proof.X25519.X86.wv_lt u.mem x (VG.Impl.Ed25519.X86.scalarR + 4 * k)
    have hk := (scalarK k).isLt
    omega_using [hw, hk]
  · rw [au, Nat.zero_add, hs] at et
    rw [mu] at ft
    exact ⟨ku.trans kt, ft, et⟩

/-- The carry is the comparison with L; the low limbs are the subtraction. -/
theorem scalar_subtract_value {r t c : Nat} (hr : r < 2 * L) (ht : t < 2 ^ 256)
    (h : t + 2 ^ 256 * c = r + (2 ^ 256 - L)) :
    c ≤ 1 ∧ (if c = 1 then t else r) = r % L := by
  have hl := order_bound
  have hp := order_pos
  constructor
  · omega_using [hr, ht, h, hl]
  · by_cases hc : c = 1
    · rw [ite_eq_left hc, Nat.mod_eq_sub_mod (by omega_using [h, hc, hp, hl]),
        Nat.mod_eq_of_lt (by omega_using [hr, h, hc, hl])]
      omega_using [h, hc, hl]
    · have hz : c = 0 := by omega_using [hr, h, hc, hl]
      rw [ite_eq_right hc, Nat.mod_eq_of_lt (by omega_using [ht, h, hz, hl])]

theorem scalarMask_ok {s : State} (ha : VG.Proof.X25519.X86.acc s ≤ 1) :
    WP isa (.block scalarMask) s fun t => VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧
      t.gpr .ecx = VG.Proof.X25519.X86.mask (VG.Proof.X25519.X86.acc s) := by
  refine Wp.wp_movi fun u hu => Wp.wp_sub fun t ht _ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep hu).trans (VG.Proof.X25519.X86.updKeep ht), ht.mem.trans hu.mem, ?_⟩
  rw [ht.gpr, hu.gpr, hu.other .ebx (by decide)]
  have hb : (s.gpr .ebx).toNat = VG.Proof.X25519.X86.acc s := by
    have he := (s.gpr .ebx).isLt
    change _ ≤ 1 at ha
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at ha ⊢
    omega_using [ha, he]
  have hw : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.X25519.X86.acc s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hb, Nat.mod_eq_of_lt (by omega_using [ha])]
  rw [hw]; rfl

theorem scalarRound_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) (hb : VG.Proof.X25519.X86.acc s < 2) :
    WP isa (.block scalarRound) s fun t => VG.Proof.X25519.X86.Keep s t ∧
      Frame [VG.Proof.X25519.X86.sub x VG.Impl.Ed25519.X86.scalarR 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = (2 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + VG.Proof.X25519.X86.acc s) % L := by
  simp only [scalarRound, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarDouble_ok hc hr hb) fun u ⟨ku, fu, eu⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarSubtract_ok (ku.ctx hc)) fun v ⟨kv, fv, ev⟩ => ?_)
  have hv := VG.Proof.Ed25519.X86.scalar_subtract_value (by rw [eu]; omega_using [hr, hb]) (VG.Proof.X25519.X86.fe_lt v.mem x VG.Impl.X25519.X86.T) ev
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarMask_ok hv.1) fun w ⟨kw, mw, ew⟩ => ?_)
  have ewR : VG.Proof.X25519.X86.fe w.mem x VG.Impl.Ed25519.X86.scalarR = VG.Proof.X25519.X86.fe u.mem x VG.Impl.Ed25519.X86.scalarR := by
    rw [mw]; exact VG.Proof.X25519.X86.fe_frame1 fv hc.fit (by decide) (by decide) (Or.inl (by decide))
  refine WP.mono (VG.Proof.X25519.X86.selects_ok (kw.ctx (kv.ctx (ku.ctx hc))) (o := VG.Impl.Ed25519.X86.scalarR)
    (g := VG.Proof.X25519.X86.acc v) (by decide) hv.1 ew 8 (by decide) w
    ⟨Keep.refl _, rfl, Frame.refl _ _, fun _ h => by omega_using [h]⟩)
    fun t ht => ⟨ku.trans (kv.trans (kw.trans ht.keep)), ?_, ?_⟩
  · have fm : Frame [VG.Proof.X25519.X86.sub x VG.Impl.Ed25519.X86.scalarR 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] u.mem w.mem := by
      rw [mw]; exact fv.mono fun r h => List.mem_cons_of_mem _ h
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]).trans
      (fm.trans (ht.frame.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]))
  · have es : VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = if VG.Proof.X25519.X86.acc v = 1 then VG.Proof.X25519.X86.fe w.mem x VG.Impl.X25519.X86.T else VG.Proof.X25519.X86.fe w.mem x VG.Impl.Ed25519.X86.scalarR := by
      split
      · exact VG.Proof.X25519.X86.num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_left ‹_›))
      · exact VG.Proof.X25519.X86.num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_right ‹_›))
    rw [es, ewR, mw, hv.2, eu]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarBody`. -/
section

/-! Merged from `Proof.Ed25519.X86.ScalarByte`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

def scalarFrame (x : BitVec 32) : List Region := [VG.Proof.X25519.X86.sub x VG.Impl.Ed25519.X86.scalarR 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32]

theorem scalarFrame_word {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hf : Frame (VG.Proof.Ed25519.X86.scalarFrame x) m m') : VG.Proof.X25519.X86.wd m' x 32 = VG.Proof.X25519.X86.wd m x 32 := by
  apply VG.Proof.X25519.X86.wd_frame hf
  intro r hr
  simp only [VG.Proof.Ed25519.X86.scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx]) (by simp only [VG.Impl.Ed25519.X86.scalarR]; omega_using [hx]) (Or.inl (by decide))
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx]) (by simp only [VG.Impl.X25519.X86.T]; omega_using [hx]) (Or.inl (by decide))

theorem scalarBitLoad_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {j : Nat} (hj : j < 8) :
    WP isa (.block (scalarBitLoad j)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧
      VG.Proof.X25519.X86.acc t = (VG.Proof.X25519.X86.wv s.mem x 32 / 2 ^ (j + 1)) % 2 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u₁ h₁ => ?_
  refine Wp.wp_shr (by omega_using [hj]) fun u₂ h₂ _ => ?_
  refine Wp.wp_andi fun u₃ h₃ => Wp.wp_movi fun u₄ h₄ => Wp.wp_movi fun t h₅ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans ((VG.Proof.X25519.X86.updKeep h₃).trans ((VG.Proof.X25519.X86.updKeep h₄).trans (VG.Proof.X25519.X86.updKeep h₅)))),
    by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, h₅.gpr, h₅.other .ebx (by decide), h₅.other .ecx (by decide),
    h₄.gpr, h₄.other .ebx (by decide), VG.Proof.X25519.X86.toNat_zero32, Nat.mul_zero, Nat.add_zero]
  rw [h₃.gpr, h₂.gpr, h₁.gpr, BitVec.toNat_and]
  change (VG.Proof.X25519.X86.wd s.mem x 32 >>> (j + 1)).toNat &&& (2 ^ 1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem scalarBit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {j : Nat} (hj : j < 8)
    (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) :
    WP isa (.block (VG.Impl.Ed25519.X86.scalarBit j)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame (VG.Proof.Ed25519.X86.scalarFrame x) s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = (2 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + (VG.Proof.X25519.X86.wv s.mem x 32 / 2 ^ (j + 1)) % 2) % L := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarBitLoad_ok hc hj) fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.scalarRound_ok (ku.ctx hc) (by rw [mu]; exact hr)
    (by rw [au]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, ft, et⟩ => ?_
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, by rw [et, mu, au]⟩

/-- Pure bit recurrence, kept independent from machine states. -/
def scalarConsume (b : Nat) : Nat → Nat → Nat
  | 0, r => r
  | n + 1, r => VG.Proof.Ed25519.X86.scalarConsume b n ((2 * r + b / 2 ^ n % 2) % L)

theorem scalarConsume_eq (b n r : Nat) (hr : r < L) :
    VG.Proof.Ed25519.X86.scalarConsume b n r = (2 ^ n * r + b % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [VG.Proof.Ed25519.X86.scalarConsume, Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero,
      Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [VG.Proof.Ed25519.X86.scalarConsume, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a y z : Nat) : (a * (y % L) + z) % L = (a * y + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul, Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega_using []

theorem scalarBits_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {n : Nat} (hn : n ≤ 8)
    (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) :
    WP isa (.block (scalarBits n)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame (VG.Proof.Ed25519.X86.scalarFrame x) s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = VG.Proof.Ed25519.X86.scalarConsume (VG.Proof.X25519.X86.wv s.mem x 32 / 2) n (VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨Keep.refl _, Frame.refl _ _, rfl⟩
  | succ n ih =>
    have ec : scalarBits (n + 1) = VG.Impl.Ed25519.X86.scalarBit n ++ scalarBits n := by
      simp only [scalarBits, List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.flatMap_append, List.flatMap_singleton]
    rw [ec]
    refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarBit_ok hc (by omega_using [hn]) hr)
      fun u ⟨ku, fu, eu⟩ => ?_)
    refine WP.mono (ih (ku.ctx hc) (by omega_using [hn])
      (by rw [eu]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, ft, et⟩ => ?_
    refine ⟨ku.trans kt, fu.trans ft, ?_⟩
    rw [et, VG.Proof.X25519.X86.wv, VG.Proof.Ed25519.X86.scalarFrame_word hc.fit fu, VG.Proof.Ed25519.X86.scalarConsume, eu]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ n)]

theorem scalarEight_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) (hb : VG.Proof.X25519.X86.wv s.mem x 32 / 2 < 256) :
    WP isa (.block (scalarBits 8)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame (VG.Proof.Ed25519.X86.scalarFrame x) s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = (256 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + VG.Proof.X25519.X86.wv s.mem x 32 / 2) % L := by
  refine WP.mono (VG.Proof.Ed25519.X86.scalarBits_ok hc (by decide) hr) fun t ⟨kt, ft, et⟩ => ⟨kt, ft, ?_⟩
  rw [et, VG.Proof.Ed25519.X86.scalarConsume_eq _ _ _ hr, show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hb]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

structure ScalarKeep (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem ScalarKeep.refl (s : State) : VG.Proof.Ed25519.X86.ScalarKeep s s := ⟨rfl, rfl, rfl, rfl⟩
theorem ScalarKeep.trans {s t u : State} (h : VG.Proof.Ed25519.X86.ScalarKeep s t) (k : VG.Proof.Ed25519.X86.ScalarKeep t u) : VG.Proof.Ed25519.X86.ScalarKeep s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr⟩
theorem ScalarKeep.ctx {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.ScalarKeep s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t :=
  hc.keep h.edi h.wr

theorem Keep.scalar {s t : State} (h : VG.Proof.X25519.X86.Keep s t) : VG.Proof.Ed25519.X86.ScalarKeep s t := ⟨h.edi, h.esp, h.rd, h.wr⟩
theorem scalarUpd {s t : State} {r : Reg} {v : BitVec 32} (h : Wp.Upd s t r v)
    (hr : r ≠ .edi ∧ r ≠ .esp := by decide) : VG.Proof.Ed25519.X86.ScalarKeep s t :=
  ⟨h.other _ hr.1.symm, h.other _ hr.2.symm, h.rd, h.wr⟩

theorem scalar_ld8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : VG.X86.addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Wp.Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  change Option.map _ (if InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr b) o) 1 then
    some (s.mem (VG.X86.addr (s.gpr b) o)) else none) = _
  simp only [ha, hin, ite_true, Option.map_some]

theorem scalarRead_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block scalarRead) s fun t => VG.Proof.Ed25519.X86.ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      Frame [VG.Proof.X25519.X86.sub x 32 4] s.mem t.mem ∧ VG.Proof.X25519.X86.wv t.mem x 32 = 2 * (s.mem (VG.X86.addr x (128 + n))).toNat := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_mov fun s₂ h₂ => Wp.wp_add fun s₃ h₃ _ => ?_
  have e₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [h₁.gpr, hs]
    exact (Wp.ofNat_pred (by omega_using [])).trans (congrArg (BitVec.ofNat 32) (by omega_using []))
  have k₃ := (VG.Proof.Ed25519.X86.scalarUpd h₁).trans ((VG.Proof.Ed25519.X86.scalarUpd h₂).trans (VG.Proof.Ed25519.X86.scalarUpd h₃))
  have c₃ := k₃.ctx hc
  have a₃ : VG.X86.addr (s₃.gpr .eax) 128 = VG.X86.addr x (128 + n) := by
    rw [h₃.gpr, h₂.gpr, h₂.other .esi (by decide), e₁, h₁.other .edi (by decide), hc.edi]
    simp only [VG.X86.addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n 128]
  refine VG.Proof.Ed25519.X86.scalar_ld8 a₃ (c₃.inRW (by omega_using [hn]) (by decide)) fun s₄ h₄ => ?_
  refine Wp.wp_add fun s₅ h₅ _ => ?_
  have c₅ := ((VG.Proof.Ed25519.X86.scalarUpd h₄).trans (VG.Proof.Ed25519.X86.scalarUpd h₅)).ctx c₃
  refine Wp.wp_stm c₅.edi (c₅.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₃.trans ((VG.Proof.Ed25519.X86.scalarUpd h₄).trans ((VG.Proof.Ed25519.X86.scalarUpd h₅).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)), ?_, ?_, ?_⟩
  · rw [ht.gpr, h₅.other .esi (by decide), h₄.other .esi (by decide), h₃.other .esi (by decide),
      h₂.other .esi (by decide), e₁]
  · rw [ht.mem, m₅]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd_write_self, h₅.gpr, h₄.gpr, h₃.mem, h₂.mem, h₁.mem,
      BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
    have hb := (s.mem (VG.X86.addr x (128 + n))).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [hb])]
    omega_using []

def scalarBodyFrame (x : BitVec 32) : List Region := VG.Proof.X25519.X86.sub x 32 4 :: VG.Proof.Ed25519.X86.scalarFrame x

theorem scalarTest_ok (s : State) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (s.gpr .esi == 0) := by
  refine Wp.wp_test fun t ht hz => WP.block_nil ?_
  exact ⟨ht.gpr, ht.mem, ht.rd, ht.wr, by rw [hz, BitVec.and_self]⟩

theorem scalarByte_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) (hr : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < L) :
    WP isa (.block scalarByte) s fun t => VG.Proof.Ed25519.X86.ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.zf = some (decide (n = 0)) ∧ Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = (256 * VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + (s.mem (VG.X86.addr x (128 + n))).toNat) % L := by
  simp only [scalarByte, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarRead_ok hc hn hs) fun u ⟨ku, su, fu, eu⟩ => ?_)
  have vu : VG.Proof.X25519.X86.fe u.mem x VG.Impl.Ed25519.X86.scalarR = VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR :=
    VG.Proof.X25519.X86.fe_frame1 fu hc.fit (by decide) (by decide) (Or.inr (by decide))
  have bu : VG.Proof.X25519.X86.wv u.mem x 32 / 2 = (s.mem (VG.X86.addr x (128 + n))).toNat := by rw [eu]; omega_using []
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarEight_ok (ku.ctx hc) (vu ▸ hr)
    (by rw [bu]; exact BitVec.isLt _)) fun v ⟨kv, fv, ev⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.scalarTest_ok v) fun t ⟨gt, mt, rt, wt, zt⟩ => ?_
  have st : t.gpr .esi = BitVec.ofNat 32 n := by rw [gt, kv.esi, su]
  refine ⟨ku.trans ((Keep.scalar kv).trans ⟨by rw [gt], by rw [gt], rt, wt⟩), st, ?_, ?_, ?_⟩
  · rw [zt, kv.esi, su, Wp.ofNat_beq_zero (by omega_using [hn])]
  · rw [mt]
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self).trans
      (fv.mono fun r h => List.mem_cons_of_mem _ h)
  · rw [mt, ev, vu, bu]
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointAccumulate`. -/
section
/-! Merged from `Proof.Ed25519.X86.BitMask`. -/
section
/-! Only public counters determine the address of a secret scalar bit. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.word {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.FieldKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : VG.Proof.X25519.X86.wd t.mem x o = VG.Proof.X25519.X86.wd s.mem x o :=
  VG.Proof.X25519.X86.wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem FieldKeep.bit {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.FieldKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (VG.X86.addr x (7168 + i)) = s.mem (VG.X86.addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (VG.Proof.X25519.X86.sub x (7168 + i) 1).Disjoint (VG.Proof.X25519.X86.sub x 64 864)) _ (Region.contains_self _ _)

theorem scalarBitMask_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (VG.X86.addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .ecx = VG.Proof.X25519.X86.mask (!bit).toNat := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_movi fun b hb' => VG.Proof.X25519.X86.wp_mul fun c hmul => ?_
  refine Wp.wp_add fun d hd _ => Wp.wp_add fun e he _ => ?_
  have pk : VG.Proof.X25519.X86.Keep s e := (VG.Proof.X25519.X86.updKeep ha).trans ((VG.Proof.X25519.X86.updKeep hb').trans (hmul.keep.trans
    ((VG.Proof.X25519.X86.updKeep hd).trans (VG.Proof.X25519.X86.updKeep he))))
  have pc : c.gpr .eax = BitVec.ofNat 32 (16 * batch) := by
    apply BitVec.eq_of_toNat_eq
    change VG.Proof.X25519.X86.v c .eax = _
    rw [hmul.eax]
    simp only [VG.Proof.X25519.X86.v, hb'.other .eax (by decide), ha.gpr, hb'.gpr]
    change (VG.Proof.X25519.X86.wd s.mem x 28).toNat * 16 % 2 ^ 32 = _
    rw [hbv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show batch < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm batch 16)
  have pe : VG.X86.addr (e.gpr .eax) 7168 = VG.X86.addr x (7168 + (16 * batch + j)) := by
    rw [he.gpr, hd.gpr, pc, hmul.other .esi (by decide) (by decide),
      hb'.other .esi (by decide), ha.other .esi (by decide), hjv,
      hd.other .edi (by decide), hmul.other .edi (by decide) (by decide),
      hb'.other .edi (by decide), ha.other .edi (by decide), hc.edi]
    rw [← BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 32 (16 * batch + j)) x, VG.Proof.Ed25519.X86.addr_plus,
      Nat.add_comm (16 * batch + j) 7168]
  refine VG.Proof.Ed25519.X86.scalar_ld8 pe ((pk.ctx hc).inRW (by omega) (by decide)) fun f hf =>
    Wp.wp_subi fun g hg _ _ => WP.block_nil ?_
  have km : g.mem = s.mem := by rw [hg.mem, hf.mem, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem (pk.trans ((VG.Proof.X25519.X86.updKeep hf).trans (VG.Proof.X25519.X86.updKeep hg))) km, km, ?_⟩
  rw [hg.gpr, hf.gpr, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointSelect`. -/
section
/-! Field and point selection by a fixed sequence of masked swaps. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def swapEnv (a b : Slot) (sw : Bool) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapsEnv (pairs : List (Slot × Slot)) (sw : Bool) (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env :=
  pairs.foldl (fun e (a, b) => VG.Proof.Ed25519.X86.swapEnv a b sw e) e

theorem swapField_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (a b : Slot) (hab : a ≠ b)
    (sw : Bool) (hm : s.gpr .ecx = VG.Proof.X25519.X86.mask sw.toNat) :
    WP isa (.block (VG.Impl.X25519.X86.cswap (offset a) (offset b))) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.swapEnv a b sw (VG.Proof.Ed25519.X86.env s.mem x) := by
  have sep := VG.Proof.X25519.X86.slot_ne (VG.Proof.Ed25519.X86.slot_valid b) (VG.Proof.Ed25519.X86.slot_valid a) (fun h => hab (VG.Proof.Ed25519.X86.offset_inj h))
  refine WP.mono (VG.Proof.X25519.X86.cswap_ok hc (VG.Proof.X25519.X86.slot_below (VG.Proof.Ed25519.X86.slot_valid a)) (VG.Proof.X25519.X86.slot_below (VG.Proof.Ed25519.X86.slot_valid b)) sep
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ⟨hk, hm', hf, ha, hb⟩ => ?_
  have wide : Frame [VG.Proof.X25519.X86.sub x 64 864] s.mem t.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨VG.Proof.X25519.X86.sub x 64 864, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
    · exact VG.Proof.X25519.X86.sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
  refine ⟨⟨hk, wide⟩, hm', ?_⟩
  have hfit := hc.fit
  funext i
  by_cases hia : i = a
  · subst i
    rw [VG.Proof.Ed25519.X86.swapEnv, Function.update_of_ne hab, Function.update_self]
    change VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe t.mem x (offset a)) = _
    rw [ha]
    cases sw <;> rfl
  · by_cases hib : i = b
    · subst i
      rw [VG.Proof.Ed25519.X86.swapEnv, Function.update_self]
      change VG.Proof.X25519.toFe (VG.Proof.X25519.X86.fe t.mem x (offset b)) = _
      rw [hb]
      cases sw <;> rfl
    · rw [VG.Proof.Ed25519.X86.swapEnv, Function.update_of_ne hib, Function.update_of_ne hia]
      apply congrArg VG.Proof.X25519.toFe
      apply VG.Proof.X25519.X86.fe_frame
      intro k hk'
      apply VG.Proof.X25519.X86.wd_frame hf
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hs := VG.Proof.X25519.X86.slot_ne (VG.Proof.Ed25519.X86.slot_valid a) (VG.Proof.Ed25519.X86.slot_valid i) (fun h => hia (VG.Proof.Ed25519.X86.offset_inj h))
        exact VG.Proof.X25519.X86.sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])
      · have hs := VG.Proof.X25519.X86.slot_ne (VG.Proof.Ed25519.X86.slot_valid b) (VG.Proof.Ed25519.X86.slot_valid i) (fun h => hib (VG.Proof.Ed25519.X86.offset_inj h))
        exact VG.Proof.X25519.X86.sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])

theorem swapsEnv_step (pairs : List (Slot × Slot)) (a b : Slot) (sw : Bool)
    {e f g : VG.Proof.Ed25519.X86.Env} (h : f = VG.Proof.Ed25519.X86.swapEnv a b sw e) (k : g = VG.Proof.Ed25519.X86.swapsEnv pairs sw f) :
    g = VG.Proof.Ed25519.X86.swapsEnv ((a, b) :: pairs) sw e := by
  rw [k, h]; rfl

theorem swapFields_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (pairs : List (Slot × Slot)) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    (sw : Bool) (hm : s.gpr .ecx = VG.Proof.X25519.X86.mask sw.toNat) :
    WP isa (.block (swapFields pairs)) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.swapsEnv pairs sw (VG.Proof.Ed25519.X86.env s.mem x) := by
  induction pairs generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl, rfl⟩
  | cons pair pairs ih =>
    rcases pair with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86.swapField_ok hc a b (hpairs _ List.mem_cons_self) sw hm) fun t ⟨kt, mt, et⟩ => ?_
    refine WP.mono (ih (kt.ctx hc) (fun p hp => hpairs p (List.mem_cons_of_mem _ hp)) (mt.trans hm))
      fun u ⟨ku, mu, eu⟩ => ?_
    exact ⟨kt.trans ku, mu.trans mt, VG.Proof.Ed25519.X86.swapsEnv_step pairs a b sw et eu⟩

theorem pointSelect_eval (e : VG.Proof.Ed25519.X86.Env) (sw : Bool) :
    VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e) 0 1 2 3 =
      if sw then VG.Proof.Ed25519.X86.point e 17 18 19 20 else VG.Proof.Ed25519.X86.point e 0 1 2 3 := by
  cases sw <;> rfl

theorem pointSelect_high (e : VG.Proof.Ed25519.X86.Env) (sw : Bool) :
    VG.Proof.Ed25519.X86.swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e 16 = e 16 := rfl

theorem pointSelect_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (sw : Bool)
    (hm : s.gpr .ecx = VG.Proof.X25519.X86.mask sw.toNat) :
    WP isa (.block pointSelect) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        (if sw then VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 17 18 19 20 else VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = VG.Proof.Ed25519.X86.env s.mem x 16 := by
  refine WP.mono (VG.Proof.Ed25519.X86.swapFields_ok hc _ (by decide) sw hm) fun t ⟨hk, _, he⟩ => ?_
  rw [he]
  exact ⟨hk, VG.Proof.Ed25519.X86.pointSelect_eval _ _, VG.Proof.Ed25519.X86.pointSelect_high _ _⟩

end VG.Proof.Ed25519.X86
end

/-! One exact scalar-multiplication bit, including masked selection. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem select_flip {α : Sort _} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) :
    c = if bit then b else a := by
  cases bit <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hd, he] using hc

theorem pointAccumulate_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (VG.X86.addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block pointAccumulate) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3)
          (VG.Proof.Ed25519.X86.tablePoint s.mem x (5120 + 128 * j)) else VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = Spec.Ed25519.d := by
  simp only [pointAccumulate, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.prepareAdd_ok hc j hj hjv) fun u ⟨ku, pu, qu, su, du⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointAdd_ok (ku.ctx hc) (du.trans hd)) fun v ⟨kv, pv, hv⟩ => ?_
  have kp := ku.trans kv
  have va := pv.trans (congrArg₂ Spec.Ed25519.pointAdd pu qu)
  have vs : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env v.mem x) 17 18 19 20 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 :=
    (VG.Proof.Ed25519.X86.point_congr _ _ _ _ (hv 17 (by decide)) (hv 18 (by decide))
      (hv 19 (by decide)) (hv 20 (by decide))).trans su
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.scalarBitMask_ok (kp.ctx hc) batch j hb hj
    ((kp.word hc 28 (by decide)).trans hbv) (kp.keep.esi.trans hjv) bit
    ((kp.bit hc _ (by omega)).trans hbit)) fun w ⟨kw, mw, bw⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86.pointSelect_ok (kw.ctx (kp.ctx hc)) (!bit) bw) fun t ⟨kt, pt, dt⟩ => ?_
  refine ⟨kp.trans (kw.trans kt), ?_, ?_⟩
  · exact VG.Proof.Ed25519.X86.select_flip bit pt (by rw [mw]; exact vs) (by rw [mw]; exact va)
  · rw [dt, mw, hv 16 (by decide), du, hd]

end VG.Proof.Ed25519.X86
end

/-! Descending bits follow the exact pointMul recursion. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (VG.Proof.Ed25519.X86.scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [VG.Proof.Ed25519.X86.scalarBit, h] <;> decide

theorem choose_after (s n : Nat) (p x y : Spec.Ed25519.Point)
    (hx : x = after s p (n + 1)) (hy : y = powerPoint p n) :
    (if VG.Proof.Ed25519.X86.scalarBit s n then Spec.Ed25519.pointAdd x y else x) = after s p n := by
  rw [hx, hy]
  have h := (after_step s p n).symm
  by_cases hz : (s / 2 ^ n) % 2 = 0
  · simpa only [VG.Proof.Ed25519.X86.scalarBit, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, ite_true] using h
  · simpa only [VG.Proof.Ed25519.X86.scalarBit, hz, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] using h

theorem IKeep.word {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : VG.Proof.X25519.X86.wd t.mem x o = VG.Proof.X25519.X86.wd s.mem x o :=
  VG.Proof.X25519.X86.wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem IKeep.bit {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.IKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (VG.X86.addr x (7168 + i)) = s.mem (VG.X86.addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (VG.Proof.X25519.X86.sub x (7168 + i) 1).Disjoint (VG.Proof.X25519.X86.sub x 64 864)) _ (Region.contains_self _ _)

theorem accumulateBody_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (n batch scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hb : batch < 32)
    (hindex : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s.gpr .esi = BitVec.ofNat 32 (n + 1))
    (hbit : s.mem (VG.X86.addr x (7168 + (16 * batch + n))) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.X86.scalarBit scalar (16 * batch + n)).toNat)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n + 1))
    (ht : VG.Proof.Ed25519.X86.tablePoint s.mem x (5120 + 128 * n) = powerPoint p (16 * batch + n)) :
    WP isa (.block accumulateBody) s fun t =>
      VG.Proof.Ed25519.X86.IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      isa.eval .ne t = some (!decide (n = 0)) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = after scalar p (16 * batch + n) ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = Spec.Ed25519.d := by
  simp only [accumulateBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine Wp.wp_subi fun u hu _ _ => WP.block_nil ?_
  have ku : VG.Proof.Ed25519.X86.IKeep x s u := IKeep.of_counter hu
  have bu : u.gpr .esi = BitVec.ofNat 32 n := by
    rw [hu.gpr, hcounter]
    exact (Wp.ofNat_pred (by omega)).trans (congrArg (BitVec.ofNat 32) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.pointAccumulate_ok (ku.ctx hc) batch n hb hn
    (by rw [hu.mem]; exact hindex) bu (VG.Proof.Ed25519.X86.scalarBit scalar (16 * batch + n))
    (by rw [hu.mem]; exact hbit) (by rw [hu.mem]; exact hd)) fun v ⟨kv, pv, dv⟩ => ?_
  have bv := kv.keep.esi.trans bu
  have vp : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env v.mem x) 0 1 2 3 = after scalar p (16 * batch + n) :=
    pv.trans (VG.Proof.Ed25519.X86.choose_after scalar (16 * batch + n) p _ _
      ((congrArg (fun m => VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env m x) 0 1 2 3) hu.mem).trans hp)
      ((congrArg (fun m => VG.Proof.Ed25519.X86.tablePoint m x (5120 + 128 * n)) hu.mem).trans ht))
  refine Wp.wp_test fun t kt zt => WP.block_nil ?_
  have keep : VG.Proof.X25519.X86.Keep v t := ⟨by rw [kt.gpr], by rw [kt.gpr], by rw [kt.gpr], kt.rd, kt.wr⟩
  refine ⟨ku.trans ((IKeep.of_field kv).trans (IKeep.of_mem keep kt.mem)),
    (congrFun kt.gpr .esi).trans bv, ?_, ?_, ?_⟩
  · show t.zf.map (!·) = _
    rw [zt, BitVec.and_self, bv, Wp.ofNat_beq_zero (by omega)]; rfl
  · rw [kt.mem]; exact vp
  · rw [kt.mem]; exact dv

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CommonContract`. -/
section

/-! Untrusted cdecl facts shared by the Ed25519 primitives. No particular
argument list or output is assumed by scratch setup and register saving. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

structure ScratchPre (s₀ : State) (scidx argc : Nat) : Prop where
  index : scidx < argc
  wr : VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx) ∈ s₀.wr
  fit : (arg s₀ scidx).toNat + 8192 ≤ 2 ^ 32
  args : (⟨argAddr s₀ 0, 4 * argc⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * argc⟩ : Region).Disjoint (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx))
  ret_sc : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx))

theorem ScratchPre.arg_contains {s : State} {scidx argc i : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s scidx argc)
    (hi : i < argc) : (⟨argAddr s 0, 4 * argc⟩ : Region).Contains
      (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 4 * argc) hp.sp_fit
    (by omega_using []) (by omega_using [hi]) (by decide)

theorem ScratchPre.argIn {s : State} {scidx argc i : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s scidx argc)
    (hi : i < argc) : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨_, hp.args, hp.arg_contains hi⟩

theorem ScratchPre.arg_same {s : State} {scidx argc i : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s scidx argc)
    {m : Mem} (hf : Frame [VG.Proof.X25519.X86.scR 8192 (arg s scidx)] s.mem m) (hi : i < argc) :
    m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i :=
  hf.readW (hp.arg_contains hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

/-- The callee-saved registers and their slots in the scratch space. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ VG.Proof.Ed25519.X86.savedSlots, p.2 + 4 ≤ 16 := by decide

structure Saved (s₀ : State) (x : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = x
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.X25519.X86.scR 8192 x] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr VG.Proof.Ed25519.X86.savedSlots

theorem Saved.ctx {s₀ s : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hfit : x.toNat + 8192 ≤ 2 ^ 32) (hw : VG.Proof.X25519.X86.scR 8192 x ∈ s₀.wr) : VG.Proof.Ed25519.X86.Ctx x s :=
  ⟨h.edi, hfit, h.wr ▸ hw, by decide⟩

/-- A component writing above the saved words preserves the common ABI invariant. -/
theorem Saved.of_frame {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hk : VG.Proof.Ed25519.X86.ScalarKeep s t) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀ r ∈ rs, r.Sub (VG.Proof.X25519.X86.scR 8192 x))
    (hsep : ∀ p ∈ VG.Proof.Ed25519.X86.savedSlots, ∀ r ∈ rs, (VG.Proof.X25519.X86.sub x p.2 4).Disjoint r) : VG.Proof.Ed25519.X86.Saved s₀ x t :=
  ⟨hk.edi.trans h.edi, hk.esp.trans h.esp, hk.rd.trans h.rd, hk.wr.trans h.wr,
    h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hsub r hr⟩),
    h.saved.of_readW fun p hp => VG.Proof.X25519.X86.wd_frame hf (hsep p hp)⟩

theorem Saved.of_offset {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : VG.Proof.Ed25519.X86.ScalarKeep s t) {o n : Nat}
    (hf : Frame [VG.Proof.X25519.X86.sub x o n] s.mem t.mem) (ho : 16 ≤ o) (hn : o + n ≤ 8192)
    (ho' : o < 8192) : VG.Proof.Ed25519.X86.Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr; rw [List.mem_singleton.mp hr, VG.Proof.X25519.X86.scR_eq]
    exact VG.Proof.X25519.X86.sub_sub hx (Nat.zero_le _) hn ho'
  · intro p hp r hr; rw [List.mem_singleton.mp hr]
    have := VG.Proof.Ed25519.X86.savedSlots_bound p hp
    exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx, this]) (by omega_using [hx, hn]) (Or.inl (by omega_using [this, ho]))

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CommonMemory`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem abiSave_ok {s₀ : State} {scidx argc : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) :
    WP isa (.block (abiSave scidx)) s₀ (VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx)) := by
  have hfit := hp.fit
  rw [show abiSave scidx = .mov .eax (.mem (at_ .esp (4 + 4 * scidx))) :: (Spill.saveCode .eax VG.Proof.Ed25519.X86.savedSlots ++
    ([.mov .edi (.reg .eax)] : List Instr)) from rfl]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * scidx) rfl (hp.argIn hp.index) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ scidx := u₁.gpr
  refine Spill.save_ok VG.Proof.Ed25519.X86.savedSlots (fun p h => by
    rw [ea, u₁.wr]; exact ⟨_, hp.wr, VG.Proof.X25519.X86.scR_contains hfit (by have := VG.Proof.Ed25519.X86.savedSlots_bound p h; omega_using [this])
      (by decide)⟩) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = Spill.saveMem s₀.mem (addr (arg s₀ scidx)) s₀.gpr VG.Proof.Ed25519.X86.savedSlots := by
    rw [u₆.mem, u₅.mem, ea, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  refine ⟨by rw [u₆.gpr, u₅.gpr, ea], by rw [u₆.other _ (by decide), u₅.gpr, u₁.other _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₁.wr], ?_, ?_⟩
  · rw [hm]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      VG.Proof.X25519.X86.scR_contains hfit (by have := VG.Proof.Ed25519.X86.savedSlots_bound p h; omega_using [this]) (by decide)
  · rw [hm]; exact Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by omega_using [hfit])


structure CopyInv (x p : BitVec 32) (dst : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s₀ s
  frame : Frame [VG.Proof.X25519.X86.sub x dst (4 * n)] s₀.mem s.mem
  words : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (dst + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem p (4 * j)

theorem copyWords_ok {x p : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (hp : s₀.gpr .esi = p) {dst N : Nat} (hd : dst + 4 * N ≤ 8192)
    (hi : ∀ j < N, InRegions (s₀.rd ++ s₀.wr) (addr p (4 * j)) 4)
    (hs : ∀ j < N, (VG.Proof.X25519.X86.sub p (4 * j) 4).Disjoint (VG.Proof.X25519.X86.sub x dst (4 * N))) :
    ∀ n ≤ N, WP isa (.block (copyWords dst n)) s₀ (VG.Proof.Ed25519.X86.CopyInv x p dst s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    have he : copyWords dst (n + 1) = copyWords dst n ++
        ([.mov .eax (.mem (at_ .esi (4 * n))), .store (sc (dst + 4 * n)) .eax] : List Instr) := by
      simp only [copyWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [he]
    refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.copyWords_ok hc hp hd hi hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    refine Wp.wp_ldm (hu.keep.esi.trans hp) (by rw [hu.keep.rd, hu.keep.wr]; exact hi n (by omega_using [hn]))
      fun v hv => ?_
    have cv := (VG.Proof.X25519.X86.updKeep hv).ctx cu
    refine Wp.wp_stm cv.edi (cv.inW (by omega_using [hd, hn]) (by decide)) fun t ht => WP.block_nil ?_
    have et : t.mem = u.mem.writeW (addr x (dst + 4 * n)) (VG.Proof.X25519.X86.wd s₀.mem p (4 * n)) := by
      rw [ht.mem, hv.mem, hv.gpr]
      have hw : VG.Proof.X25519.X86.wd u.mem p (4 * n) = VG.Proof.X25519.X86.wd s₀.mem p (4 * n) :=
        VG.Proof.X25519.X86.wd_frame hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact (hs n (by omega_using [hn])).sub_right
            (VG.Proof.X25519.X86.sub_sub hc.fit (Nat.le_refl _) (by omega_using [hn]) (by omega_using [hd, hn]))
      exact congrArg (u.mem.writeW (addr x (dst + 4 * n))) hw
    refine ⟨hu.keep.trans ((VG.Proof.X25519.X86.updKeep hv).trans
      ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩), ?_, fun j hj => ?_⟩
    · rw [et]
      exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden hu.frame hc.fit (Nat.le_refl _) (by omega_using [])
        (by omega_using [hd, hn])) hc.fit (by omega_using [hd, hn]) (by omega_using []) (by omega_using []) _
    · rw [et]
      by_cases e : j = n
      · subst e; exact VG.Proof.X25519.X86.wd_write_self _ _ _ _
      · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by have := hc.fit; omega_using [this, hd, hn, hj])
          (by have := hc.fit; omega_using [this, hd, hn]) (by omega_using [hj, e])]
        exact hu.words j (by omega_using [hj, e])

theorem restore_eq : restore =
    .mov .eax (.reg .edi) :: (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) := rfl

/-- The saved registers restored. -/
theorem abiRestore_ok {x : BitVec 32} {s : State} {g : Reg → BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hs : Spill.Saved s.mem (addr x) g VG.Proof.Ed25519.X86.savedSlots) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = g r) ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .edx = s.gpr .edx ∧ s'.mem = s.mem := by
  rw [VG.Proof.Ed25519.X86.restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  refine Spill.restore_ok (g := g) [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] (by decide)
    (fun p h => by
      rw [ea, u₁.rd, u₁.wr]
      exact hc.inRW (by have := VG.Proof.Ed25519.X86.savedSlots_bound p (by revert p h; decide); omega_using [this]) (by decide))
    (by rw [ea, u₁.mem]; exact hs.sub (by decide)) fun s' r => WP.block_nil
      ⟨fun q hq hsp => r.regs q (by revert hsp; revert hq; revert q; decide),
        by rw [r.other _ (by decide), u₁.other _ (by decide)],
        by rw [r.other _ (by decide), u₁.other _ (by decide)], by rw [r.mem, u₁.mem]⟩

theorem loadArg_ok {s₀ s : State} {scidx argc i : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc)
    (h : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hi : i < argc) :
    WP isa (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))]) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧ t.gpr .esi = arg s₀ i ∧ t.mem = s.mem := by
  refine Wp.wp_ldm h.esp (by rw [h.rd, h.wr]; exact hp.argIn hi) fun t ht => WP.block_nil ?_
  refine ⟨⟨(ht.other _ (by decide)).trans h.edi, (ht.other _ (by decide)).trans h.esp,
    ht.rd.trans h.rd, ht.wr.trans h.wr, by rw [ht.mem]; exact h.frame,
    by rw [ht.mem]; exact h.saved⟩, ?_, ht.mem⟩
  rw [ht.gpr]; exact hp.arg_same h.frame hi

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarLoop`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L decodeLE)

def scalarInput (m : Mem) (x : BitVec 32) : List Byte :=
  (List.range 64).map fun i => m (VG.X86.addr x (128 + i))

theorem scalarInput_length (m : Mem) (x : BitVec 32) : (VG.Proof.Ed25519.X86.scalarInput m x).length = 64 := by
  simp only [VG.Proof.Ed25519.X86.scalarInput, List.length_map, List.length_range]

theorem scalar_suffix (m : Mem) (x : BitVec 32) {n : Nat} (hn : n < 64) :
    decodeLE ((VG.Proof.Ed25519.X86.scalarInput m x).drop n) % L =
      (256 * (decodeLE ((VG.Proof.Ed25519.X86.scalarInput m x).drop (n + 1)) % L) + (m (VG.X86.addr x (128 + n))).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed25519.X86.scalarInput_length]; exact hn), reduce_cons]
  simp only [VG.Proof.Ed25519.X86.scalarInput, List.getElem_map, List.getElem_range]

theorem scalarInput_byte {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hf : Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) m m') {n : Nat} (hn : n < 64) :
    m' (VG.X86.addr x (128 + n)) = m (VG.X86.addr x (128 + n)) := by
  apply hf
  intro r hr
  simp only [VG.Proof.Ed25519.X86.scalarBodyFrame, VG.Proof.Ed25519.X86.scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : (VG.Proof.X25519.X86.sub x (128 + n) 1).Contains (VG.X86.addr x (128 + n)) 1 := Region.contains_self _ _
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hn]) (by omega_using [hx])
      (Or.inr (by omega_using []))) _ hb
  · exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hn]) (by simp only [VG.Impl.Ed25519.X86.scalarR]; omega_using [hx])
      (Or.inr (by simp only [VG.Impl.Ed25519.X86.scalarR]; omega_using []))) _ hb
  · exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hn]) (by simp only [VG.Impl.X25519.X86.T]; omega_using [hx])
      (Or.inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hn]))) _ hb

structure ScalarInv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR = decodeLE ((VG.Proof.Ed25519.X86.scalarInput s₀.mem x).drop n) % L
  keeps : VG.Proof.Ed25519.X86.ScalarKeep s₀ s
  frame : Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s₀.mem s.mem

theorem scalarLoop_ok {x : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (hs : s₀.gpr .esi = 64) (hz : VG.Proof.X25519.X86.fe s₀.mem x VG.Impl.Ed25519.X86.scalarR = 0) :
    WP isa (.loop (.block scalarByte) .ne) s₀ fun t => VG.Proof.Ed25519.X86.ScalarKeep s₀ t ∧
      Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s₀.mem t.mem ∧ VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = decodeLE (VG.Proof.Ed25519.X86.scalarInput s₀.mem x) % L := by
  apply WP.loop (VG.Proof.Ed25519.X86.ScalarInv x s₀) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega_using [this] : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega_using [this]
    refine WP.mono (VG.Proof.Ed25519.X86.scalarByte_ok (hi.keeps.ctx hc) hk hi.counter
      (by rw [hi.value]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, st, zt, ft, vt⟩ => ?_
    have v : VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = decodeLE ((VG.Proof.Ed25519.X86.scalarInput s₀.mem x).drop k) % L := by
      rw [vt, hi.value, VG.Proof.Ed25519.X86.scalarInput_byte hc.fit hi.frame hk, VG.Proof.Ed25519.X86.scalar_suffix _ _ hk]
    have keep := hi.keeps.trans kt
    have frame := hi.frame.trans ft
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true],
        keep, frame, by simpa only [List.drop_zero] using v⟩
    · exact Or.inr ⟨by simp only [eval, zt, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega_using [], ⟨by omega_using [hk0], by omega_using [hk], st, v, keep, frame⟩⟩
  · refine ⟨by decide, by decide, hs, ?_, ScalarKeep.refl _, Frame.refl _ _⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [VG.Proof.Ed25519.X86.scalarInput_length])]
    rfl
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519 (leNum leBytes)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = leBytes n x := by
  unfold Spec.Ed25519.encodeLE leBytes
  congr 1
  funext i
  rw [Nat.shiftRight_eq_div_pow, show 256 ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem addr_offset {x : BitVec 32} {o d : Nat} (hx : x.toNat + o + d < 2 ^ 32) :
    VG.X86.addr x (o + d) = VG.X86.addr x o + BitVec.ofNat 64 d := by
  rw [addr_eq (by omega_using [hx]), addr_eq (by omega_using [hx]), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-- Little-endian decoding of any number of scratch words. -/
theorem decode_words {x : BitVec 32} {o : Nat} (m : Mem) : ∀ n,
    x.toNat + o + 4 * n ≤ 2 ^ 32 →
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (VG.X86.addr x o) (4 * n)) =
      VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv m x (o + 4 * k)) n
  | 0, _ => rfl
  | n + 1, hx => by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega_using []]
    rw [decodeLE_eq]
    change leNum (Spec.X25519.bytesAt m (VG.X86.addr x o) (4 * n + 4)) = _
    rw [Proof.X25519.bytesAt_add, Proof.X25519.leNum_append, Proof.X25519.length_bytesAt,
      Proof.X25519.leNum_bytesAt_32bit]
    have hn := VG.Proof.Ed25519.X86.decode_words (x := x) (o := o) m n (by omega_using [hx])
    rw [decodeLE_eq] at hn
    change leNum (Spec.X25519.bytesAt m (VG.X86.addr x o) (4 * n)) = _ at hn
    rw [hn, VG.Proof.X25519.X86.num_succ, ← VG.Proof.Ed25519.X86.addr_offset (by omega_using [hx])]
    have hp : 256 ^ (4 * n) = (2 ^ 32) ^ n := by
      rw [Nat.pow_mul]
    rw [hp]

theorem scalarInput_bytes {x : BitVec 32} (m : Mem) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    VG.Proof.Ed25519.X86.scalarInput m x = Spec.Ed25519.bytesAt m (VG.X86.addr x 128) 64 := by
  apply List.map_congr_left
  intro i hi
  have hi' : i < 64 := List.mem_range.mp hi
  rw [VG.Proof.Ed25519.X86.addr_offset (by omega_using [hx, hi'])]

theorem scalarInput_num {x : BitVec 32} (m : Mem) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    Spec.Ed25519.decodeLE (VG.Proof.Ed25519.X86.scalarInput m x) = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv m x (128 + 4 * k)) 16 := by
  rw [VG.Proof.Ed25519.X86.scalarInput_bytes m hx]
  exact VG.Proof.Ed25519.X86.decode_words m 16 (by omega_using [hx])

theorem num_shift (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num f (n + 1) = f 0 + 2 ^ 32 * VG.Proof.X25519.X86.num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [VG.Proof.X25519.X86.num]
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ, ih, VG.Proof.X25519.X86.num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

theorem num_digit : ∀ (j : Nat) {f : Nat → Nat} {n : Nat}, (∀ k < n, f k < 2 ^ 32) → j < n →
    VG.Proof.X25519.X86.num f n / (2 ^ 32) ^ j % 2 ^ 32 = f j
  | 0, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [VG.Proof.Ed25519.X86.num_shift, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 hj)]
  | j + 1, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [VG.Proof.Ed25519.X86.num_shift, Nat.pow_succ (2 ^ 32) j, Nat.mul_comm ((2 ^ 32) ^ j) (2 ^ 32), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (h 0 (by omega_using [])), Nat.zero_add]
    exact VG.Proof.Ed25519.X86.num_digit j (fun k hk => h (k + 1) (by omega_using [hk])) (by omega_using [hj])
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CommonFinish`. -/
section

/-! Merged from `Proof.Ed25519.X86.CommonOutput`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure OutputInv (x p : BitVec 32) (src : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s₀ s
  frame : Frame [VG.Proof.X25519.X86.sub p 0 (4 * n)] s₀.mem s.mem
  words : ∀ j < n, VG.Proof.X25519.X86.wd s.mem p (4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (src + 4 * j)

theorem outputWords_ok {x p : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (hp : s₀.gpr .esi = p) {src : Nat} (hd : src + 32 ≤ 8192)
    (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hi : ∀ j < 8, InRegions s₀.wr (addr p (4 * j)) 4)
    (hs : (VG.Proof.X25519.X86.scR 8192 x).Disjoint (VG.Proof.X25519.X86.sub p 0 32)) :
    ∀ n ≤ 8, WP isa (.block (outputWords src n)) s₀ (VG.Proof.Ed25519.X86.OutputInv x p src s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    have he : outputWords src (n + 1) = outputWords src n ++
        ([.mov .eax (.mem (sc (src + 4 * n))), .store (at_ .esi (4 * n)) .eax] : List Instr) := by
      simp only [outputWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [he]
    refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.outputWords_ok hc hp hd hfit hi hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    refine Wp.wp_ldm cu.edi (cu.inRW (by omega_using [hd, hn]) (by decide)) fun v hv => ?_
    refine Wp.wp_stm ((VG.Proof.X25519.X86.updKeep hv).esi.trans (hu.keep.esi.trans hp))
      (by rw [hv.wr, hu.keep.wr]; exact hi n (by omega_using [hn])) fun t ht => WP.block_nil ?_
    have et : t.mem = u.mem.writeW (addr p (4 * n)) (VG.Proof.X25519.X86.wd s₀.mem x (src + 4 * n)) := by
      rw [ht.mem, hv.mem, hv.gpr]
      have hw : VG.Proof.X25519.X86.wd u.mem x (src + 4 * n) = VG.Proof.X25519.X86.wd s₀.mem x (src + 4 * n) :=
        VG.Proof.X25519.X86.wd_frame hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          refine (hs.sub_left ?_).sub_right ?_
          · rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hc.fit (Nat.zero_le _) (by omega_using [hd, hn]) (by omega_using [hd, hn])
          · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]
            exact Region.sub_prefix (by omega_using [hn])
      exact congrArg (u.mem.writeW (addr p (4 * n))) hw
    refine ⟨hu.keep.trans ((VG.Proof.X25519.X86.updKeep hv).trans
      ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩), ?_, fun j hj => ?_⟩
    · rw [et]
      have hf : Frame [VG.Proof.X25519.X86.sub p 0 (4 * (n + 1))] s₀.mem u.mem := hu.frame.sub fun r hr =>
        ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩
      exact hf.writeW (List.mem_singleton_self _) _
        (VG.Proof.X25519.X86.sub_contains (by omega_using [hfit, hn]) (Nat.zero_le _) (by omega_using []) (by decide))
    · rw [et]
      by_cases e : j = n
      · subst e; exact VG.Proof.X25519.X86.wd_write_self _ _ _ _
      · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, hn, hj]) (by omega_using [hfit, hn])
          (by omega_using [hj, e])]
        exact hu.words j (by omega_using [hj, e])

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure OutputPre (s₀ : State) (scidx : Nat) : Prop where
  wr : (⟨(arg s₀ 0).setWidth 64, 32⟩ : Region) ∈ s₀.wr
  fit : (arg s₀ 0).toNat + 32 ≤ 2 ^ 32
  sep : (⟨(arg s₀ 0).setWidth 64, 32⟩ : Region).Disjoint (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx))
  ret : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 0).setWidth 64, 32⟩

theorem finishWords_ok {s₀ s : State} {scidx argc src : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (ho : VG.Proof.Ed25519.X86.OutputPre s₀ scidx)
    (h : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hsrc : src + 32 ≤ 8192) :
    WP isa (.block (finishWords src)) s fun t => abiPreserved s₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((arg s₀ 0).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (VG.Proof.X25519.X86.fe s.mem (arg s₀ scidx) src) := by
  simp only [finishWords, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.loadArg_ok (i := 0) hp h (by have := hp.index; omega_using [this]))
    fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hwr : ∀ j < 8, InRegions u.wr (addr (arg s₀ 0) (4 * j)) 4 := by
    intro j hj
    refine ⟨_, hu.wr ▸ ho.wr, ?_⟩
    have hc := VG.Proof.X25519.X86.sub_contains (x := arg s₀ 0) (a := 0) (k := 32) (d := 4 * j) (n := 4)
      (by have := ho.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hj]) (by decide)
    rwa [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero] at hc
  have hsep : (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx)).Disjoint (VG.Proof.X25519.X86.sub (arg s₀ 0) 0 32) := by
    rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]; exact ho.sep.symm
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.outputWords_ok cu eu hsrc ho.fit hwr hsep 8 (by decide)) fun v hv => ?_)
  have cv := hv.keep.ctx cu
  have saved : Spill.Saved v.mem (addr (arg s₀ scidx)) s₀.gpr VG.Proof.Ed25519.X86.savedSlots := hu.saved.of_readW fun p hp' => by
    have := VG.Proof.Ed25519.X86.savedSlots_bound p hp'
    refine VG.Proof.X25519.X86.wd_frame hv.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine hsep.sub_left ?_
    rw [VG.Proof.X25519.X86.scR_eq]
    exact VG.Proof.X25519.X86.sub_sub hp.fit (Nat.zero_le _) (by omega_using [this]) (by omega_using [this])
  refine WP.mono (VG.Proof.Ed25519.X86.abiRestore_ok cv saved) fun t ⟨gt, st, _, mt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h : r = .esp
    · subst h; exact st.trans (hv.keep.esp.trans hu.esp)
    · exact gt r hr h
  · rw [mt]
    have hvret : v.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = u.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
      hv.frame.readW (Region.contains_self _ _) (by
        simp only [List.mem_singleton]; rintro r rfl
        rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]; exact ho.ret) (by decide)
    rw [hvret]
    exact hu.frame.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc) (by decide)
  · rw [mt, VG.Proof.Ed25519.X86.encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    have eaddr := addr_eq (x := arg s₀ 0) (k := 4 * j) (by have := ho.fit; omega_using [this, hj])
    rw [← eaddr]
    change (VG.Proof.X25519.X86.wd v.mem (arg s₀ 0) (4 * j)).toNat = _
    rw [hv.words j hj, mu, Nat.pow_mul]
    exact (VG.Proof.Ed25519.X86.num_digit j (f := fun k => VG.Proof.X25519.X86.wv s.mem (arg s₀ scidx) (src + 4 * k))
      (fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _) hj).symm
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CommonCT`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {scidx argc : Nat} (hp : VG.Proof.Ed25519.X86.ScratchPre s scidx argc)
    (ho : VG.Proof.Ed25519.X86.OutputPre s scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 32⟩, VG.Proof.X25519.X86.scR 8192 (arg s scidx)])
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 32⟩) :
    VG.X86.Taint.Wf (VG.Proof.Ed25519.X86.scalarTaint scidx argc) s := by
  have hf := hp.fit; have ofit := ho.fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, VG.Proof.Ed25519.X86.scalarTaint], by simpa [hw] using ho.sep, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, ofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) ho.ret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [VG.Proof.Ed25519.X86.scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [VG.Proof.Ed25519.X86.scalarTaint]; have := hp.index; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [VG.Proof.Ed25519.X86.scalarTaint]; have := hp.index; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (VG.Proof.Ed25519.X86.scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (VG.Proof.Ed25519.X86.scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 32⟩, VG.Proof.X25519.X86.scR 8192 (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 32⟩, VG.Proof.X25519.X86.scR 8192 (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (VG.Proof.Ed25519.X86.scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Ed25519.X86.scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [VG.Proof.Ed25519.X86.scalarTaint] at hk
    rw [show VG.X86.Taint.depth (VG.Proof.Ed25519.X86.scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.CommonInput`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure InputPre (s₀ : State) (scidx i n : Nat) : Prop where
  rd : (VG.Proof.X25519.X86.sub (arg s₀ i) 0 (4 * n)) ∈ s₀.rd ++ s₀.wr
  fit : (arg s₀ i).toNat + 4 * n ≤ 2 ^ 32
  sep : (VG.Proof.X25519.X86.sub (arg s₀ i) 0 (4 * n)).Disjoint (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx))

theorem inputWord_contains {s₀ : State} {scidx i n : Nat} (hp : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    {k : Nat} (hk : k < n) : (VG.Proof.X25519.X86.sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) (4 * k)) 4 :=
  VG.Proof.X25519.X86.sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputWord_same {s₀ s : State} {scidx i n : Nat} (hp : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) {k : Nat} (hk : k < n) :
    VG.Proof.X25519.X86.wd s.mem (arg s₀ i) (4 * k) = VG.Proof.X25519.X86.wd s₀.mem (arg s₀ i) (4 * k) :=
  hs.frame.readW (VG.Proof.Ed25519.X86.inputWord_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.sep) (by decide)

theorem loadInput_ok {s₀ s : State} {scidx argc i n dst : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (hi : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hia : i < argc)
    (hd0 : 16 ≤ dst) (hd : dst + 4 * n ≤ 8192) (hd' : dst < 8192) :
    WP isa (.block (([.mov .esi (.mem (at_ .esp (4 + 4 * i)))] : List Instr) ++ copyWords dst n)) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < n, VG.Proof.X25519.X86.wd t.mem (arg s₀ scidx) (dst + 4 * k) = VG.Proof.X25519.X86.wd s₀.mem (arg s₀ i) (4 * k)) ∧
      Frame [VG.Proof.X25519.X86.sub (arg s₀ scidx) dst (4 * n)] s.mem t.mem := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.loadArg_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hread : ∀ k < n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) (4 * k)) 4 := by
    intro k hk; refine ⟨_, ?_, VG.Proof.Ed25519.X86.inputWord_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < n, (VG.Proof.X25519.X86.sub (arg s₀ i) (4 * k) 4).Disjoint (VG.Proof.X25519.X86.sub (arg s₀ scidx) dst (4 * n)) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.sub, addr_eq (by have := hi.fit; omega_using [this, hk]), VG.Proof.X25519.X86.addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hp.fit (Nat.zero_le _) hd hd'
  refine WP.mono (VG.Proof.Ed25519.X86.copyWords_ok cu eu hd hread hsep n (Nat.le_refl _)) fun t ht => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar ht.keep) ht.frame hd0 hd hd', fun k hk => ?_, ?_⟩
  · rw [ht.words k hk]; exact VG.Proof.Ed25519.X86.inputWord_same hi hu hk
  · have hf := ht.frame; rw [mu] at hf; exact hf
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.FreezeField`. -/
section

/-! Canonical reduction preserves the field environment. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (freeze T)
open VG.Proof.X25519 (toFe toFe_mod)

theorem freezeField_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.env s.mem x ∧ VG.Proof.X25519.X86.fe t.mem x (offset a) = (VG.Proof.Ed25519.X86.env s.mem x a).val := by
  refine WP.mono (VG.Proof.X25519.X86.freeze_ok hc (VG.Proof.Ed25519.X86.slot_valid a)) fun t ⟨hk, hf, hv⟩ => ?_
  have fit := hc.fit
  refine ⟨⟨hk, VG.Proof.X25519.X86.frame_wide hc.fit4 (VG.Proof.Ed25519.X86.slot_valid a) (by decide) hf⟩, ?_, hv⟩
  funext i
  by_cases hi : i = a
  · subst i
    change toFe (VG.Proof.X25519.X86.fe t.mem x (offset a)) = _
    rw [hv]; exact toFe_mod _
  · apply congrArg toFe
    apply VG.Proof.X25519.X86.fe_frame
    intro k hk'
    apply VG.Proof.X25519.X86.wd_frame hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs := VG.Proof.X25519.X86.slot_ne (VG.Proof.Ed25519.X86.slot_valid a) (VG.Proof.Ed25519.X86.slot_valid i) (fun h => hi (VG.Proof.Ed25519.X86.offset_inj h))
      exact VG.Proof.X25519.X86.sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [offset]; omega_using [fit, a.isLt]) (by omega_using [hs, hk'])
    · exact VG.Proof.X25519.X86.sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [VG.Impl.X25519.X86.T]; omega_using [fit]) (Or.inl (by simp only [offset, VG.Impl.X25519.X86.T]; omega))

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.InputBits`. -/
section

/-! Merged from `Proof.Ed25519.X86.BitsExpand`. -/
section
/-! Merged from `Proof.Ed25519.X86.BitsExpandStep`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalar_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ t, Wp.Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  change (s.gpr b + BitVec.ofNat 32 o).setWidth 64 = a at ha
  simp only [exec, State.store8, State.ea, ha, hout, ite_true]

theorem doubled_byte_bit (b : Byte) (j : Nat) :
    ((((b.setWidth 32 + b.setWidth 32) >>> (j + 1)) &&& 1).setWidth 8) =
      BitVec.ofNat 8 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  change (((b.setWidth 32 + b.setWidth 32) >>> (j + 1)).toNat &&& (2 ^ 1 - 1)) % 2 ^ 8 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat + b.toNat) (b := 2 ^ 32) (by omega_using [hb]),
    show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ'], ← Nat.div_div_eq_div_mul,
    show (b.toNat + b.toNat) / 2 = b.toNat by omega_using []]
  rfl

theorem expandScalarBit_ok {x p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (hp : s.gpr .esi = p)
    {k : Nat} (hk : k < 512) (hr : InRegions (s.rd ++ s.wr) (addr p (k / 8)) 1) :
    WP isa (.block (expandScalarBit k)) s fun t => VG.Proof.X25519.X86.Keep s t ∧
      t.mem = s.mem.writeW (addr x (7168 + k))
        (BitVec.ofNat 8 ((s.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)) := by
  refine VG.Proof.Ed25519.X86.scalar_ld8 (by rw [hp]) hr fun u₁ h₁ => ?_
  refine Wp.wp_add fun u₂ h₂ _ => Wp.wp_shr
    (by have h := Nat.mod_lt k (by decide : 0 < 8); omega_using [h]) fun u₃ h₃ _ => ?_
  refine Wp.wp_andi fun u₄ h₄ => ?_
  have k₄ := (VG.Proof.X25519.X86.updKeep h₁).trans ((VG.Proof.X25519.X86.updKeep h₂).trans ((VG.Proof.X25519.X86.updKeep h₃).trans (VG.Proof.X25519.X86.updKeep h₄)))
  have c₄ := k₄.ctx hc
  refine VG.Proof.Ed25519.X86.scalar_store8 (by rw [c₄.edi]) (c₄.inW (by omega_using [hk]) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨k₄.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩
  rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  change s.mem.writeW _ ((u₄.gpr .eax).setWidth 8) = _
  rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, VG.Proof.Ed25519.X86.doubled_byte_bit]

theorem bits_byte_write_self (m : Mem) (a : Addr) (v : Byte) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem bits_byte_write_ne (m : Mem) {x : BitVec 32} (v : Byte) {d e : Nat}
    (hd : x.toNat + d + 1 ≤ 2 ^ 32) (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) :
    (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := VG.Proof.X25519.X86.sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure ExpandedBits (x p : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s₀ s
  frame : Frame [VG.Proof.X25519.X86.sub x 7168 n] s₀.mem s.mem
  bits : ∀ k < n, s.mem (addr x (7168 + k)) =
    BitVec.ofNat 8 ((s₀.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)

theorem expandPrefix_ok {x p : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (hp : s₀.gpr .esi = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hr : ∀ i < bytes, InRegions (s₀.rd ++ s₀.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (VG.Proof.X25519.X86.sub p i 1).Disjoint (VG.Proof.X25519.X86.sub x 7168 (8 * bytes))) :
    ∀ n ≤ 8 * bytes, WP isa (.block ((List.range n).flatMap expandScalarBit)) s₀ (VG.Proof.Ed25519.X86.ExpandedBits x p s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.expandPrefix_ok hc hp hb hr hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    have hnb : n / 8 < bytes := by omega_using [hn]
    have input : u.mem (addr p (n / 8)) = s₀.mem (addr p (n / 8)) := by
      apply hu.frame
      intro r hmem; rw [List.mem_singleton.mp hmem]
      have hd := (hs (n / 8) hnb).sub_right
        (VG.Proof.X25519.X86.sub_sub (o := 7168) (n := n) (o' := 7168) (n' := 8 * bytes)
          hc.fit (Nat.le_refl _) (by omega_using [hn]) (by decide))
      exact hd _ (Region.contains_self _ _)
    refine WP.mono (VG.Proof.Ed25519.X86.expandScalarBit_ok cu (hu.keep.esi.trans hp) (by omega_using [hn, hb])
      (by rw [hu.keep.rd, hu.keep.wr]; exact hr _ hnb)) fun t ⟨kt, mt⟩ => ?_
    rw [input] at mt
    refine ⟨hu.keep.trans kt, ?_, fun k hk => ?_⟩
    · rw [mt]
      have hf := VG.Proof.X25519.X86.frameWiden hu.frame hc.fit (Nat.le_refl _) (by omega_using []) (by decide)
        (n' := n + 1)
      exact hf.writeW (List.mem_singleton_self _) _
        (VG.Proof.X25519.X86.sub_contains (by omega_using [hc.fit, hn, hb]) (by omega_using []) (by omega_using []) (by decide))
    · rw [mt]
      by_cases he : k = n
      · subst he; exact VG.Proof.Ed25519.X86.bits_byte_write_self _ _ _
      · rw [VG.Proof.Ed25519.X86.bits_byte_write_ne _ _ (by omega_using [hc.fit, hb, hn, hk])
          (by omega_using [hc.fit, hb, hn]) (by omega_using [he])]
        exact hu.bits k (by omega_using [hk, he])

theorem expanded_scalar_bit {p : BitVec 32} (m : Mem) {bytes k : Nat}
    (hp : p.toNat + bytes ≤ 2 ^ 32) (hk : k < 8 * bytes) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) / 2 ^ k % 2 =
      (m (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2 := by
  rw [decodeLE_eq]
  have he := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) k
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at he
  rw [he]
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega_using [hk] : k / 8 < bytes), Option.map_some, Option.getD_some]
  rw [addr_eq (by omega_using [hp, hk])]

theorem expandScalarBits_ok {x p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hp : s.gpr .esi = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hfit : p.toNat + bytes ≤ 2 ^ 32)
    (hr : ∀ i < bytes, InRegions (s.rd ++ s.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (VG.Proof.X25519.X86.sub p i 1).Disjoint (VG.Proof.X25519.X86.sub x 7168 (8 * bytes))) :
    WP isa (.block (expandScalarBits bytes)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x 7168 (8 * bytes)] s.mem t.mem ∧
      ∀ k < 8 * bytes, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (p.setWidth 64) bytes) / 2 ^ k % 2) := by
  refine WP.mono (VG.Proof.Ed25519.X86.expandPrefix_ok hc hp hb hr hs (8 * bytes) (Nat.le_refl _)) fun t ht =>
    ⟨ht.keep, ht.frame, fun k hk => ?_⟩
  rw [ht.bits k hk, VG.Proof.Ed25519.X86.expanded_scalar_bit s.mem hfit hk]
theorem loadScalarBits_ok {x p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (hp : VG.Proof.X25519.X86.wd s.mem x 20 = p) {bytes : Nat} (hb : bytes ≤ 64)
    (hfit : p.toNat + bytes ≤ 2 ^ 32)
    (hr : ∀ i < bytes, InRegions (s.rd ++ s.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (VG.Proof.X25519.X86.sub p i 1).Disjoint (VG.Proof.X25519.X86.sub x 7168 (8 * bytes))) :
    WP isa (.block (loadScalarBits bytes)) s fun t => VG.Proof.Ed25519.X86.ScalarKeep s t ∧
      Frame [VG.Proof.X25519.X86.sub x 7168 (8 * bytes)] s.mem t.mem ∧
      ∀ k < 8 * bytes, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (p.setWidth 64) bytes) / 2 ^ k % 2) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  have ku := VG.Proof.Ed25519.X86.scalarUpd hu
  refine WP.mono (VG.Proof.Ed25519.X86.expandScalarBits_ok (ku.ctx hc) (hu.gpr.trans hp) hb hfit
    (by intro i hi; rw [hu.rd, hu.wr]; exact hr i hi) hs) fun t ⟨kt, ft, bt⟩ => ?_
  rw [hu.mem] at ft bt
  exact ⟨ku.trans (Keep.scalar kt), ft, bt⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem inputByte_contains {s₀ : State} {scidx i n : Nat} (hp : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    {k : Nat} (hk : k < 4 * n) : (VG.Proof.X25519.X86.sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) k) 1 :=
  VG.Proof.X25519.X86.sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputBytes_same {s₀ s : State} {scidx i n : Nat} (hp : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem ((arg s₀ i).setWidth 64) (4 * n) =
      Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n) := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hp.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hp.sep _ (VG.Proof.Ed25519.X86.inputByte_contains hp hk')

theorem inputBits_ok {s₀ s : State} {scidx argc i n : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (hi : VG.Proof.Ed25519.X86.InputPre s₀ scidx i n)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : n ≤ 16) :
    WP isa (.block (inputBits i (4 * n))) s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 32 * n, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n)) / 2 ^ k % 2)) := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.loadArg_ok hp hs hia) fun u ⟨hu, eu, _⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < 4 * n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) k) 1 := by
    intro k hk; refine ⟨_, ?_, VG.Proof.Ed25519.X86.inputByte_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < 4 * n, (VG.Proof.X25519.X86.sub (arg s₀ i) k 1).Disjoint (VG.Proof.X25519.X86.sub (arg s₀ scidx) 7168 (8 * (4 * n))) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.sub, addr_eq (by have := hi.fit; omega_using [this, hk]), VG.Proof.X25519.X86.addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (VG.Proof.Ed25519.X86.expandScalarBits_ok cu eu (by omega_using [hn]) hi.fit hr hsep)
    fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar kt) ft (by decide) (by omega_using [hn]) (by decide), fun k hk => ?_⟩
  rw [bt k (by omega_using [hk]), VG.Proof.Ed25519.X86.inputBytes_same hi hu]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.InputSlice`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure SlicePre (s₀ : State) (scidx : Nat) (p : BitVec 32) (bytes : Nat) : Prop where
  rd : ∀ k len, 0 < len → k + len ≤ bytes → InRegions (s₀.rd ++ s₀.wr) (addr p k) len
  fit : p.toNat + bytes ≤ 2 ^ 32
  sep : (VG.Proof.X25519.X86.sub p 0 bytes).Disjoint (VG.Proof.X25519.X86.scR 8192 (arg s₀ scidx))

theorem slice_contains {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : VG.Proof.Ed25519.X86.SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    (VG.Proof.X25519.X86.sub p 0 n).Contains (addr p k) len :=
  VG.Proof.X25519.X86.sub_contains (by have := h.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) hlen

theorem slice_read {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : VG.Proof.Ed25519.X86.SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    InRegions (s₀.rd ++ s₀.wr) (addr p k) len := h.rd k len hlen hk

theorem slice_sub {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : VG.Proof.Ed25519.X86.SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    (VG.Proof.X25519.X86.sub p k len).Sub (VG.Proof.X25519.X86.sub p 0 n) := by
  rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.sub, addr_eq (by have := h.fit; omega_using [this, hk, hlen]), VG.Proof.X25519.X86.addr_zero]
  exact Offset.sub_base _ hk

theorem sliceBytes_same {s₀ s : State} {scidx n : Nat} {p : BitVec 32} (hi : VG.Proof.Ed25519.X86.SlicePre s₀ scidx p n)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n = Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) n := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hi.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hi.sep _ (VG.Proof.Ed25519.X86.slice_contains hi (by omega_using [hk']) (by have := hi.fit; omega_using [this, hk']))

theorem loadSlicePointer_ok {s₀ s : State} {scidx argc i skip : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hi : i < argc) :
    WP isa (.block (loadSlicePointer i skip)) s fun t =>
      VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧ t.gpr .esi = arg s₀ i + BitVec.ofNat 32 skip ∧ t.mem = s.mem := by
  have h := VG.Proof.Ed25519.X86.loadArg_ok hp hs hi
  refine WP.block_append (M := isa) (l₁ := ([.mov .esi (.mem (at_ .esp (4 + 4 * i)))] : List Instr))
    (WP.mono h fun u ⟨hu, eu, mu⟩ => ?_)
  refine Wp.wp_addi fun t ht => WP.block_nil ?_
  refine ⟨⟨(ht.other _ (by decide)).trans hu.edi, (ht.other _ (by decide)).trans hu.esp,
    ht.rd.trans hu.rd, ht.wr.trans hu.wr, by rw [ht.mem]; exact hu.frame,
    by rw [ht.mem]; exact hu.saved⟩, ?_, ht.mem.trans mu⟩
  rw [ht.gpr, eu]

theorem inputSliceWords_ok {s₀ s : State} {scidx argc i skip n dst : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (hi : VG.Proof.Ed25519.X86.SlicePre s₀ scidx (arg s₀ i + BitVec.ofNat 32 skip) (4 * n))
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hia : i < argc)
    (hd0 : 16 ≤ dst) (hd : dst + 4 * n ≤ 8192) (hd' : dst < 8192) :
    WP isa (.block (inputSliceWords i skip dst n)) s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < n, VG.Proof.X25519.X86.wd t.mem (arg s₀ scidx) (dst + 4 * k) =
        VG.Proof.X25519.X86.wd s₀.mem (arg s₀ i + BitVec.ofNat 32 skip) (4 * k)) ∧
      Frame [VG.Proof.X25519.X86.sub (arg s₀ scidx) dst (4 * n)] s.mem t.mem := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.loadSlicePointer_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i + BitVec.ofNat 32 skip) (4 * k)) 4 := by
    intro k hk; rw [hu.rd, hu.wr]
    exact VG.Proof.Ed25519.X86.slice_read hi (by omega_using [hk]) (by decide)
  have hsep : ∀ k < n, (VG.Proof.X25519.X86.sub (arg s₀ i + BitVec.ofNat 32 skip) (4 * k) 4).Disjoint (VG.Proof.X25519.X86.sub (arg s₀ scidx) dst (4 * n)) := by
    intro k hk
    refine (hi.sep.sub_left (VG.Proof.Ed25519.X86.slice_sub hi (by omega_using [hk]) (by decide))).sub_right ?_
    rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hp.fit (Nat.zero_le _) hd hd'
  refine WP.mono (VG.Proof.Ed25519.X86.copyWords_ok cu eu hd hr hsep n (Nat.le_refl _)) fun t ht => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar ht.keep) ht.frame hd0 hd hd', ?_, by rw [← mu]; exact ht.frame⟩
  intro k hk
  rw [ht.words k hk]
  exact hu.frame.readW (VG.Proof.Ed25519.X86.slice_contains hi (by omega_using [hk]) (by decide))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hi.sep) (by decide)

theorem inputSliceBits_ok {s₀ s : State} {scidx argc i skip bytes : Nat}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ scidx argc) (hi : VG.Proof.Ed25519.X86.SlicePre s₀ scidx (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : bytes ≤ 64) :
    WP isa (.block (inputSliceBits i skip bytes)) s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 8 * bytes, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem
          ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes) / 2 ^ k % 2)) ∧
      Frame [VG.Proof.X25519.X86.sub (arg s₀ scidx) 7168 (8 * bytes)] s.mem t.mem := by
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.loadSlicePointer_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < bytes, InRegions (u.rd ++ u.wr) (addr (arg s₀ i + BitVec.ofNat 32 skip) k) 1 := by
    intro k hk; rw [hu.rd, hu.wr]
    exact VG.Proof.Ed25519.X86.slice_read hi (by omega_using [hk]) (by decide)
  have hsep : ∀ k < bytes, (VG.Proof.X25519.X86.sub (arg s₀ i + BitVec.ofNat 32 skip) k 1).Disjoint (VG.Proof.X25519.X86.sub (arg s₀ scidx) 7168 (8 * bytes)) := by
    intro k hk
    refine (hi.sep.sub_left (VG.Proof.Ed25519.X86.slice_sub hi (by omega_using [hk]) (by decide))).sub_right ?_
    rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (VG.Proof.Ed25519.X86.expandScalarBits_ok cu eu hn hi.fit hr hsep) fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar kt) ft (by decide) (by omega_using [hn]) (by decide), ?_, by rw [← mu]; exact ft⟩
  intro k hk
  rw [bt k hk, VG.Proof.Ed25519.X86.sliceBytes_same hi hu]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.MulAddLit`. -/
section

namespace VG.Impl.Ed25519.X86
materialize_code scalarMulAdd
end VG.Impl.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarContract`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def scalarReduceLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem scalarReduce_pre {s : State} (h : scalarReduceLocal.pre s) :
    VG.Proof.Ed25519.X86.ScratchPre s 2 3 ∧ VG.Proof.Ed25519.X86.InputPre s 2 1 16 ∧ VG.Proof.Ed25519.X86.OutputPre s 2 := by
  obtain ⟨rd, wr, os, ins, _, ars, ro, rs, ofit, ifit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rs⟩,
    ⟨?_, ifit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero, rd]; simp
  · rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]; exact ins
  · rw [wr]; simp
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarInit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block scalarInit) s fun t => VG.Proof.Ed25519.X86.ScalarKeep s t ∧ t.gpr .esi = 64 ∧
      Frame [VG.Proof.X25519.X86.sub x VG.Impl.Ed25519.X86.scalarR 32] s.mem t.mem ∧ VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = 0 := by
  simp only [scalarInit, List.append_assoc]
  refine WP.block_append (WP.mono VG.Proof.X25519.X86.zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cols_ok (ku.ctx hc) (fun _ => []) 8 (by decide)
    (fun _ _ _ h => by simp only [List.not_mem_nil] at h)
    (fun _ _ => by change 0 < 2 ^ 68; decide) (by rw [au]; decide)) fun v ⟨kv, fv, ev, _⟩ => ?_)
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  have hz : VG.Proof.X25519.X86.fe v.mem x VG.Impl.Ed25519.X86.scalarR = 0 := by
    change VG.Proof.X25519.X86.fe v.mem x VG.Impl.Ed25519.X86.scalarR + _ * _ = VG.Proof.X25519.X86.acc u + 0 at ev
    rw [au] at ev
    omega_using [ev]
  refine ⟨(Keep.scalar ku).trans ((Keep.scalar kv).trans (VG.Proof.Ed25519.X86.scalarUpd ht)), ht.gpr, ?_, ?_⟩
  · rw [ht.mem, mu] at *; exact fv
  · rw [ht.mem]; exact hz

theorem scalarEngine_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa VG.Impl.Ed25519.X86.scalarEngine s fun t => VG.Proof.Ed25519.X86.ScalarKeep s t ∧ Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s.mem t.mem ∧
      VG.Proof.X25519.X86.fe t.mem x VG.Impl.Ed25519.X86.scalarR = Spec.Ed25519.decodeLE (VG.Proof.Ed25519.X86.scalarInput s.mem x) % Spec.Ed25519.L := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.scalarInit_ok hc) fun u ⟨ku, su, fu, vu⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.scalarLoop_ok (ku.ctx hc) su vu) fun t ⟨kt, ft, vt⟩ => ?_
  have fm : Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s.mem u.mem := fu.mono fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have input : VG.Proof.Ed25519.X86.scalarInput u.mem x = VG.Proof.Ed25519.X86.scalarInput s.mem x := List.map_congr_left fun i hi =>
    VG.Proof.Ed25519.X86.scalarInput_byte hc.fit fm (List.mem_range.mp hi)
  exact ⟨ku.trans kt, fm.trans ft, by rw [vt, input]⟩

theorem Saved.scalarEngine {s₀ s t : State} {x : BitVec 32} (h : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : VG.Proof.Ed25519.X86.ScalarKeep s t)
    (hf : Frame (VG.Proof.Ed25519.X86.scalarBodyFrame x) s.mem t.mem) : VG.Proof.Ed25519.X86.Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [VG.Proof.Ed25519.X86.scalarBodyFrame, VG.Proof.Ed25519.X86.scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [VG.Proof.X25519.X86.scR_eq] <;>
      exact VG.Proof.X25519.X86.sub_sub hx (by decide) (by decide) (by decide)
  · have hR : VG.Impl.Ed25519.X86.scalarR = 64 := rfl
    have hT : VG.Impl.X25519.X86.T = 864 := rfl
    intro p hp r hr
    have hj := VG.Proof.Ed25519.X86.savedSlots_bound p hp
    simp only [VG.Proof.Ed25519.X86.scalarBodyFrame, VG.Proof.Ed25519.X86.scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hj]) (by omega_using [hx, hR, hT])
        (Or.inl (by omega_using [hj, hR, hT]))
end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified`. -/
section

/-! Merged from `Proof.Ed25519.X86.MulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.X86.MulAddContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

theorem scalarMulAdd_pre {s : State} (h : scalarMulAddLocal.pre s) :
    ScratchPre s 4 5 ∧ InputPre s 4 2 8 ∧ InputPre s 4 3 8 ∧ InputPre s 4 1 8 ∧ OutputPre s 4 := by
  obtain ⟨rd, wr, os, rs, ks, ss, _, ars, ro, rsc, ofit, rfit, kfit, afit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rsc⟩,
    ⟨?_, kfit, ?_⟩, ⟨?_, afit, ?_⟩, ⟨?_, rfit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ks
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ss
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact rs
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.MulAddSetup`. -/
section
/-! Merged from `Proof.Ed25519.X86.MulAddWide`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulTerms_value (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) = colv m x (prodTerms 256 288 k) +
      (if k < 8 then wv m x (320 + 4 * k) else 0) := by
  simp only [scalarMulTerms, colv, List.map_append, List.sum_append]
  split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, tval]

theorem num_extend8 (f : Nat → Nat) : num (fun k => if k < 8 then f k else 0) 16 = num f 8 := by
  rw [num_16]
  have h0 : num (fun k => if 8 + k < 8 then f (8 + k) else 0) 8 = 0 := by
    have he : (fun k => if 8 + k < 8 then f (8 + k) else 0) = (fun _ => 0) := by
      funext k; rw [ite_eq_right (by omega_using [])]
    rw [he]; rfl
  rw [h0, Nat.mul_zero, Nat.add_zero]
  exact num_congr fun k hk => ite_eq_left hk

theorem scalarMulTerms_num (m : Mem) (x : BitVec 32) :
    num (fun k => colv m x (scalarMulTerms k)) 16 = fe m x 256 * fe m x 288 + fe m x 320 := by
  simp only [scalarMulTerms_value]
  rw [num_add, num_extend8]
  have hp : num (fun k => colv m x (prodTerms 256 288 k)) 16 = fe m x 256 * fe m x 288 := by
    simp only [colv, prodTerms, List.map_map]
    exact prod_identity (fun i => wv m x (256 + 4 * i)) (fun i => wv m x (288 + 4 * i))
  rw [hp]; rfl

theorem scalarMulTerms_bound (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) < 2 ^ 68 := by
  rw [scalarMulTerms_value]
  have hl : (prodTerms 256 288 k).length ≤ 8 := by
    simp only [prodTerms, List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hp := colv_le_len (m := m) (x := x) (B := 2 ^ 64) (ts := prodTerms 256 288 k) fun t ht => by
    simp only [prodTerms, List.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact wv_mul_le _ _ _ _
  have hm := Nat.mul_le_mul_right (2 ^ 64) hl
  have hw := wv_lt m x (320 + 4 * k)
  split <;> omega_using [hp, hm, hw]

theorem scalarMulTerms_reads {k : Nat} (hk : k < 16) {t : Term} (ht : t ∈ scalarMulTerms k)
    {d : Nat} (hd : d ∈ treads t) : d + 4 ≤ 4096 ∧ 128 + 4 * k ≤ d := by
  simp only [scalarMulTerms, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    obtain ⟨i, ⟨hi, _, hki⟩, rfl⟩ := ht
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> constructor <;> omega_using [hk, hi, hki]
  · split at ht
    · simp only [List.mem_singleton] at ht; subst ht
      simp only [treads, List.mem_singleton] at hd; subst hd
      constructor <;> omega_using [hk]
    · simp only [List.not_mem_nil] at ht

theorem scalarWideMul_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarWideMul) s fun t => Keep s t ∧ Frame [sub x 128 64] s.mem t.mem ∧
      num (fun k => wv t.mem x (128 + 4 * k)) 16 = fe s.mem x 256 * fe s.mem x 288 + fe s.mem x 320 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (cols_ok (ku.ctx hc) scalarMulTerms 16 (by decide)
    (fun k hk t ht d hd => let h := scalarMulTerms_reads hk ht hd; ⟨h.1, Or.inr h.2⟩)
    (fun k _ => scalarMulTerms_bound _ _ k) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  rw [au, Nat.zero_add, scalarMulTerms_num, mu] at et
  have hA := fe_lt s.mem x 256
  have hB := fe_lt s.mem x 288
  have hC := fe_lt s.mem x 320
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt hA) (Nat.le_pred_of_lt hB)
  change fe s.mem x 256 * fe s.mem x 288 ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) at hab
  have hz : acc t = 0 := by
    change _ + (2 ^ 256 * 2 ^ 256) * acc t = _ at et
    omega_using [et, hab, hC]
  rw [hz, Nat.mul_zero, Nat.add_zero] at et
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, et⟩
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem copied_fe {s₀ t : State} {p x : BitVec 32} {dst : Nat}
    (hp : p.toNat + 32 ≤ 2 ^ 32)
    (hw : ∀ k < 8, wd t.mem x (dst + 4 * k) = wd s₀.mem p (4 * k)) :
    fe t.mem x dst = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) 32) := by
  have ew : fe t.mem x dst = num (fun k => wv s₀.mem p (0 + 4 * k)) 8 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (hw k hk)
  rw [ew, ← decode_words s₀.mem 8 (by omega_using [hp]), addr_zero]

theorem scalarMulInputs_ok {s₀ s : State} (hp : ScratchPre s₀ 4 5)
    (hA : InputPre s₀ 4 2 8) (hB : InputPre s₀ 4 3 8) (hC : InputPre s₀ 4 1 8)
    (hs : Saved s₀ (arg s₀ 4) s) :
    WP isa (.block scalarMulInputs) s fun t => Saved s₀ (arg s₀ 4) t ∧
      fe t.mem (arg s₀ 4) 256 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 288 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 320 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) := by
  have he : scalarMulInputs =
      (([.mov .esi (.mem (at_ .esp 12))] : List Instr) ++ copyWords 256 8) ++
      ((([.mov .esi (.mem (at_ .esp 16))] : List Instr) ++ copyWords 288 8) ++
      (([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 320 8)) := by
    simp only [scalarMulInputs, List.append_assoc]
  rw [he]
  refine WP.block_append (WP.mono (loadInput_ok hp hA hs (by decide) (dst := 256)
    (by decide) (by decide) (by decide)) fun u ⟨hu, wu, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadInput_ok hp hB hu (by decide) (dst := 288)
    (by decide) (by decide) (by decide)) fun v ⟨hv, wv, fv⟩ => ?_)
  refine WP.mono (loadInput_ok hp hC hv (by decide) (dst := 320)
    (by decide) (by decide) (by decide)) fun t ⟨ht, wt, ft⟩ => ?_
  refine ⟨ht, ?_, ?_, copied_fe hC.fit wt⟩
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide)),
      fe_frame1 fv hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hA.fit wu
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hB.fit wv
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_correct {s : State} (h : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hp, hA, hB, hC, ho⟩ := scalarMulAdd_pre h
  simp only [scalarMulAdd, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.block_append (WP.mono (scalarMulInputs_ok hp hA hB hC hu) fun v ⟨hv, evA, evB, evC⟩ => ?_)
  refine WP.mono (scalarWideMul_ok (hv.ctx hp.fit hp.wr)) fun w ⟨kw, fw, ew⟩ => ?_
  have hw := hv.of_offset hp.fit (Keep.scalar kw) fw (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (scalarEngine_ok (hw.ctx hp.fit hp.wr)) fun z ⟨kz, fz, ez⟩ => ?_)
  have hz := hw.scalarEngine hp.fit kz fz
  refine WP.mono (finishWords_ok hp ho hz (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ez, scalarInput_num w.mem hp.fit, ew, evA, evB, evC, Spec.Ed25519.scalarMulAdd]
  rw [Nat.add_comm]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  obtain ⟨hp, _, _, _, ho⟩ := scalarMulAdd_pre h
  obtain ⟨_, wr, _, _, _, _, ao, _⟩ := h
  exact scalarTaint_wf hp ho wr ao

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := (scalarMulAdd_pre hs).1
  have pt := (scalarMulAdd_pre ht).1
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

def mulAddSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x38 else if a = 0x8015 then 0x40 else 0

def mulAddSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := mulAddSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x3800, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct h

def scalarMulAddWide : Contract isa :=
  { scalarMulAddLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def scalarMulAddRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 32⟩, ⟨argAddr s 0, 20⟩]
def scalarMulAddWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem scalarMulAddWide_pre (s : State) (h : scalarMulAddWide.pre s) :
    scalarMulAddLocal.pre (s.withRegions (scalarMulAddRd s) (scalarMulAddWr s)) := by
  simp only [scalarMulAddLocal, scalarMulAddRd, scalarMulAddWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarMulAddWide_implies : scalarMulAddWide.Implies (Spec.Ed25519.scalarMulAddContract X86.abi) := by
    have a0 : arg mulAddSatState 0 = 0x1000 := by decide
    have a1 : arg mulAddSatState 1 = 0x2000 := by decide
    have a2 : arg mulAddSatState 2 = 0x3000 := by decide
    have a3 : arg mulAddSatState 3 = 0x3800 := by decide
    have a4 : arg mulAddSatState 4 = 0x4000 := by decide
    have e : argAddr mulAddSatState 0 = 0x8004 := by decide
    have esp : mulAddSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, scalarMulAddWide, scalarMulAddLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, e, esp] using mulAddSatState

theorem scalarMulAdd_verified : Verified X86.target scalarMulAdd (Spec.Ed25519.scalarMulAddContract X86.abi) := by
  have hsat := scalarMulAddWide_implies.sat_left
  have satLocal : ∃ s, scalarMulAddLocal.pre s := hsat.elim fun s h => ⟨_, scalarMulAddWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarMulAdd scalarMulAddLocal :=
    Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarMulAddRd scalarMulAddWr scalarMulAddWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarMulAddWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarMulAddRd, scalarMulAddWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarMulAddWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarMulAddWide, scalarMulAddLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Power`. -/
section

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def power250Env (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env :=
  VG.Proof.Ed25519.X86.opMul 15 16 15 (VG.Proof.Ed25519.X86.opSqn 16 16 50 (VG.Proof.Ed25519.X86.opMul 16 17 16 (VG.Proof.Ed25519.X86.opSqn 17 16 100
    (VG.Proof.Ed25519.X86.opMul 16 16 15 (VG.Proof.Ed25519.X86.opSqn 16 15 50 (VG.Proof.Ed25519.X86.opMul 15 16 15 (VG.Proof.Ed25519.X86.opSqn 16 16 10 (VG.Proof.Ed25519.X86.opMul 16 17 16 (VG.Proof.Ed25519.X86.opSqn 17 16 20
    (VG.Proof.Ed25519.X86.opMul 16 16 15 (VG.Proof.Ed25519.X86.opSqn 16 15 10 (VG.Proof.Ed25519.X86.opMul 15 16 15 (VG.Proof.Ed25519.X86.opSqn 16 15 5 (VG.Proof.Ed25519.X86.opMul 15 15 16
    (VG.Proof.Ed25519.X86.opMul 16 14 14 (VG.Proof.Ed25519.X86.opMul 14 14 15 (VG.Proof.Ed25519.X86.opMul 15 2 15 (VG.Proof.Ed25519.X86.opMul 15 15 15 (VG.Proof.Ed25519.X86.opMul 15 14 14
    (VG.Proof.Ed25519.X86.opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : BitVec 32) : VG.Proof.Ed25519.X86.ISpec base power250 VG.Proof.Ed25519.X86.power250Env := by
  have h : VG.Proof.Ed25519.X86.ISpec base _ _ :=
    (VG.Proof.Ed25519.X86.mulI base 14 2 2 ⟨by decide, by decide⟩).seq <|
    ((VG.Proof.Ed25519.X86.mulI base 15 14 14 ⟨by decide, by decide⟩).append
      (VG.Proof.Ed25519.X86.mulI base 15 15 15 ⟨by decide, by decide⟩)).seq <|
    ((((VG.Proof.Ed25519.X86.mulI base 15 2 15 ⟨by decide, by decide⟩).append
      (VG.Proof.Ed25519.X86.mulI base 14 14 15 ⟨by decide, by decide⟩)).append
      (VG.Proof.Ed25519.X86.mulI base 16 14 14 ⟨by decide, by decide⟩)).append
      (VG.Proof.Ed25519.X86.mulI base 15 15 16 ⟨by decide, by decide⟩)).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 16 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 16 15 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 17 16 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 16 16 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 16 15 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 17 16 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.X86.sqnI base 16 16 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.X86.mulI base 15 16 15 ⟨by decide, by decide⟩)
  exact h

def invEnv (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env := VG.Proof.Ed25519.X86.opMul 15 15 14 (VG.Proof.Ed25519.X86.opSqn 15 15 5 (VG.Proof.Ed25519.X86.power250Env e))
def rootEnv (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.Env := VG.Proof.Ed25519.X86.opMul 15 15 2 (VG.Proof.Ed25519.X86.opSqn 15 15 2 (VG.Proof.Ed25519.X86.power250Env e))

theorem invert_spec (base : BitVec 32) : VG.Proof.Ed25519.X86.ISpec base invert VG.Proof.Ed25519.X86.invEnv := by
  have h : VG.Proof.Ed25519.X86.ISpec base _ _ := (VG.Proof.Ed25519.X86.power250_spec base).seq ((VG.Proof.Ed25519.X86.sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.X86.mulI base 15 15 14 ⟨by decide, by decide⟩))
  exact h

theorem rootPower_spec (base : BitVec 32) : VG.Proof.Ed25519.X86.ISpec base Impl.Ed25519.X86.rootPower VG.Proof.Ed25519.X86.rootEnv := by
  have h : VG.Proof.Ed25519.X86.ISpec base _ _ := (VG.Proof.Ed25519.X86.power250_spec base).seq ((VG.Proof.Ed25519.X86.sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.X86.mulI base 15 15 2 ⟨by decide, by decide⟩))
  exact h

theorem invEnv_eval (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.X86.invEnv, VG.Proof.Ed25519.X86.power250Env, VG.Proof.Ed25519.X86.opMul, VG.Proof.Ed25519.X86.opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.X86.rootEnv, VG.Proof.Ed25519.X86.power250Env, VG.Proof.Ed25519.X86.opMul, VG.Proof.Ed25519.X86.opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s) :
    WP isa invert s fun t => VG.Proof.Ed25519.X86.IKeep base s t ∧
      VG.Proof.Ed25519.X86.env t.mem base 15 = VG.Proof.X25519.invert (VG.Proof.Ed25519.X86.env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.X86.invert_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, VG.Proof.Ed25519.X86.invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : VG.Proof.Ed25519.X86.Ctx base s) :
    WP isa Impl.Ed25519.X86.rootPower s fun t => VG.Proof.Ed25519.X86.IKeep base s t ∧
      VG.Proof.Ed25519.X86.env t.mem base 15 = VG.Proof.Ed25519.rootPower (VG.Proof.Ed25519.X86.env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.X86.rootPower_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, VG.Proof.Ed25519.X86.rootEnv_eval]⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointAffine`. -/
section
/-! Convert extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem affine_eval (e : VG.Proof.Ed25519.X86.Env) :
    VG.Proof.Ed25519.X86.evalOps affineOps e 0 = e 0 * e 15 ∧ VG.Proof.Ed25519.X86.evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩
theorem invEnv_x (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.invEnv e 0 = e 0 := rfl
theorem invEnv_y (e : VG.Proof.Ed25519.X86.Env) : VG.Proof.Ed25519.X86.invEnv e 1 = e 1 := rfl

theorem pointAffine_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa pointAffine s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧
      VG.Proof.Ed25519.X86.env t.mem x 0 = VG.Proof.Ed25519.X86.env s.mem x 0 * Spec.X25519.pow (VG.Proof.Ed25519.X86.env s.mem x 2) (Spec.X25519.P - 2) ∧
      VG.Proof.Ed25519.X86.env t.mem x 1 = VG.Proof.Ed25519.X86.env s.mem x 1 * Spec.X25519.pow (VG.Proof.Ed25519.X86.env s.mem x 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.invert_spec x s hc) fun u ⟨ku, eu⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok affineOps (ku.ctx hc)) fun t ⟨kt, et⟩ => ?_
  refine ⟨ku.trans (IKeep.of_field kt), ?_, ?_⟩
  · rw [et, (VG.Proof.Ed25519.X86.affine_eval _).1, eu, VG.Proof.Ed25519.X86.invEnv_x, VG.Proof.Ed25519.X86.invEnv_eval, VG.Proof.X25519.invert_eq]
  · rw [et, (VG.Proof.Ed25519.X86.affine_eval _).2, eu, VG.Proof.Ed25519.X86.invEnv_y, VG.Proof.Ed25519.X86.invEnv_eval, VG.Proof.X25519.invert_eq]

end VG.Proof.Ed25519.X86
end

/-! Place the affine x parity in the high bit of the canonical y encoding. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem sign_word (w : BitVec 32) :
    (w &&& 1).rotateRight 1 = BitVec.ofNat 32 ((w.toNat % 2) * 2 ^ 31) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega)]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> decide

theorem field_parity (m : Mem) (x : BitVec 32) (o : Nat) : VG.Proof.X25519.X86.fe m x o % 2 = VG.Proof.X25519.X86.wv m x o % 2 := by
  rw [VG.Proof.X25519.X86.fe, VG.Proof.Ed25519.X86.num_shift]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.add_mod, Nat.mul_mod,
    show 2 ^ 32 % 2 = 0 from by decide, Nat.zero_mul, Nat.mod_mod]

theorem pointSign_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) :
    WP isa (.block pointSign) s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧ t.mem = s.mem ∧
      t.gpr .esi = BitVec.ofNat 32 ((VG.Proof.X25519.X86.fe s.mem x 64 % 2) * 2 ^ 31) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_andi fun b hb => Wp.wp_ror (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(IKeep.of_counter ha).trans ((IKeep.of_counter hb).trans (IKeep.of_counter ht)),
    by rw [ht.mem, hb.mem, ha.mem], ?_⟩
  rw [ht.gpr, hb.gpr, ha.gpr, VG.Proof.Ed25519.X86.field_parity]
  exact VG.Proof.Ed25519.X86.sign_word _

theorem fe_last_write {x : BitVec 32} (m : Mem) (w : BitVec 32) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    VG.Proof.X25519.X86.fe (m.writeW (VG.X86.addr x 124) w) x 96 =
      VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv m x (96 + 4 * k)) 7 + 2 ^ 224 * w.toNat := by
  rw [VG.Proof.X25519.X86.fe, VG.Proof.X25519.X86.num_succ]
  have h : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv (m.writeW (VG.X86.addr x 124) w) x (96 + 4 * k)) 7 =
      VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv m x (96 + 4 * k)) 7 := VG.Proof.X25519.X86.num_congr fun k hk => by
    apply congrArg BitVec.toNat
    exact VG.Proof.X25519.X86.wd_write_ne _ _ (by omega) (by omega) (Or.inl (by omega))
  rw [h]
  change _ + 2 ^ 224 * (VG.Proof.X25519.X86.wd (m.writeW (VG.X86.addr x 124) w) x 124).toNat = _
  rw [VG.Proof.X25519.X86.wd_write_self]

theorem encodeSign_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (parity y : Nat) (hp : parity ≤ 1) (hy : y < 2 ^ 255) (hv : VG.Proof.X25519.X86.fe s.mem x 96 = y)
    (hs : s.gpr .esi = BitVec.ofNat 32 (parity * 2 ^ 31)) :
    WP isa (.block encodeSign) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧ VG.Proof.X25519.X86.fe t.mem x 96 = y + parity * 2 ^ 255 := by
  have top : VG.Proof.X25519.X86.wv s.mem x 124 < 2 ^ 31 := by
    have h := VG.Proof.Ed25519.X86.num_digit 7 (f := fun k => VG.Proof.X25519.X86.wv s.mem x (96 + 4 * k)) (n := 8)
      (fun k _ => BitVec.isLt _) (by decide)
    change VG.Proof.X25519.X86.fe s.mem x 96 / 2 ^ 224 % 2 ^ 32 = VG.Proof.X25519.X86.wv s.mem x 124 at h
    rw [hv] at h
    omega
  change (s.mem.readW (VG.X86.addr x 124) 32).toNat < 2 ^ 31 at top
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_add fun b hb _ => ?_
  have kb := (VG.Proof.X25519.X86.updKeep ha).trans (VG.Proof.X25519.X86.updKeep hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have val : (b.gpr .eax).toNat = VG.Proof.X25519.X86.wv s.mem x 124 + parity * 2 ^ 31 := by
    rw [hb.gpr, ha.gpr, ha.other .esi (by decide), hs, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show parity * 2 ^ 31 < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨kb.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩, ?_⟩
  · rw [ht.mem, hb.mem, ha.mem]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, hb.mem, ha.mem, VG.Proof.Ed25519.X86.fe_last_write _ _ hc.fit, val]
    have hsum : VG.Proof.X25519.X86.fe s.mem x 96 = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s.mem x (96 + 4 * k)) 7 + 2 ^ 224 * VG.Proof.X25519.X86.wv s.mem x 124 := rfl
    rw [hsum] at hv
    omega

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointPowersLoop`. -/
section

/-! Checkpoint-loop termination and the exact contents of every entry. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure PowersInv (s₀ : State) (x : BitVec 32) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : VG.Proof.Ed25519.X86.Ctx x s
  counter : VG.Proof.X25519.X86.wd s.mem x 24 = BitVec.ofNat 32 (count - n)
  value : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 =
    powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, VG.Proof.Ed25519.X86.tablePoint s.mem x (o + 128 * j) =
    powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env s.mem x i = VG.Proof.Ed25519.X86.env s₀.mem x i
  keep : VG.Proof.Ed25519.X86.PowersKeep x o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (o count : Nat) (hlo : 928 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hcounter : VG.Proof.X25519.X86.wd s₀.mem x 24 = 0)
    (hd : VG.Proof.Ed25519.X86.env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody o count batch) .ne) s₀ fun t =>
      VG.Proof.Ed25519.X86.PowersKeep x o (128 * count) s₀ t ∧
      (∀ j < count, VG.Proof.Ed25519.X86.tablePoint t.mem x (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * j)) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s₀.mem x i := by
  apply WP.loop (fun n => VG.Proof.Ed25519.X86.PowersInv s₀ x o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86.powersBody_ok hi.scratch o count (count - (k + 1)) batch (by omega) hn hlo hbound
      hi.counter ((hi.high 16 (by decide)).trans hd)) fun t ⟨kt, it, zt, pt, tt, ht⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have pv : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [pt, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by rw [← hstep, Nat.mul_add, Nat.mul_one])
    have tv : ∀ j < count - k, VG.Proof.Ed25519.X86.tablePoint t.mem x (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases hj' : j < count - (k + 1)
      · rw [kt.frame.table hc.fit (by omega) (by omega) (by omega) (Or.inl (by omega)), hi.table j hj']
      · have he : j = count - (k + 1) := by omega
        rw [he, tt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s₀.mem x i :=
      fun i h => (ht i h).trans (hi.high i h)
    have kk := hi.keep.trans (kt.mono hi.scratch (by omega) (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst k
      exact .inl ⟨by rw [zt, show count - (0 + 1) + 1 = count by omega]; simp, kk, tv, pv, hh⟩
    · exact .inr ⟨by rw [zt]; simp only [show count - (k + 1) + 1 ≠ count by omega, decide_false]; rfl,
        k, by omega, ⟨by omega, by omega, kt.ctx hi.scratch, hstep ▸ it, pv, tv, hh, kk⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hc, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact hcounter
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem pointPowers_ok (batch : Bool) {s : State} {x : BitVec 32} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (o count : Nat) (hlo : 928 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointPowers o count batch) s fun t =>
      VG.Proof.Ed25519.X86.PowersKeep x o (128 * count) s t ∧
      (∀ j < count, VG.Proof.Ed25519.X86.tablePoint t.mem x (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (powerStride batch * j)) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 =
        powerPoint (VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.powersInit_ok hc o (128 * count)) fun t ⟨kt, it, ft⟩ => ?_)
  have et := VG.Proof.Ed25519.X86.counter_env hc.fit ft
  refine WP.mono (VG.Proof.Ed25519.X86.powersLoop_ok batch (kt.ctx hc) o count hlo hbound hn0 hn it
    (by rw [et]; exact hd)) fun u ⟨ku, tu, pu, hu⟩ => ?_
  rw [et] at tu pu hu
  exact ⟨kt.trans ku, tu, pu, hu⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PointMulCounter`. -/
section

/-! Merged from `Proof.Ed25519.X86.PointMulFrame`. -/
section
/-! Merged from `Proof.Ed25519.X86.AccumulateLoop`. -/
section
/-! Consume one sixteen-bit batch from most significant bit to least. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure AccumulateInv (x : BitVec 32) (s₀ : State) (scalar batch : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  keep : VG.Proof.Ed25519.X86.IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n)
  d : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d

theorem accumulateLoop_ok {x : BitVec 32} {s₀ : State} (hc : VG.Proof.Ed25519.X86.Ctx x s₀)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : VG.Proof.X25519.X86.wd s₀.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s₀.gpr .esi = BitVec.ofNat 32 16)
    (hbits : ∀ j < 16, s₀.mem (VG.X86.addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.X86.scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, VG.Proof.Ed25519.X86.tablePoint s₀.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s₀.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : VG.Proof.Ed25519.X86.env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block accumulateBody) .ne) s₀ fun t => VG.Proof.Ed25519.X86.IKeep x s₀ t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ VG.Proof.Ed25519.X86.env t.mem x 16 = Spec.Ed25519.d := by
  apply WP.loop (fun n => VG.Proof.Ed25519.X86.AccumulateInv x s₀ scalar batch p n) (n := 16)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < 16 := by have := h.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86.accumulateBody_ok (h.keep.ctx hc) j batch scalar p hj hb
      ((h.keep.word hc 28 (by decide)).trans hindex) h.counter
      ((h.keep.bit hc _ (by omega)).trans (hbits j hj)) h.d
      (by simpa only [Nat.add_assoc] using h.value)
      ((VG.Proof.Ed25519.X86.workspace_table h.keep hc _ (by omega) (by omega)).trans (htable j hj)))
      fun t ⟨kt, bt, zt, pt, dt⟩ => ?_
    have keep := h.keep.trans kt
    by_cases hz : j = 0
    · subst j
      exact .inl ⟨by rw [zt]; rfl, keep, by simpa only [Nat.add_zero] using pt, dt⟩
    · exact .inr ⟨by rw [zt]; simp only [decide_eq_false hz]; rfl,
        j, by omega, ⟨by omega, by omega, keep, bt, pt, dt⟩⟩
  · exact ⟨by decide, by decide, IKeep.refl _ _, hcounter, hp, hd⟩

theorem accumulate16_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hbits : ∀ j < 16, s.mem (VG.X86.addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (VG.Proof.Ed25519.X86.scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, VG.Proof.Ed25519.X86.tablePoint s.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa accumulate16 s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ VG.Proof.Ed25519.X86.env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (Wp.wp_movi fun u hu => WP.block_nil ?_)
  have ku : VG.Proof.Ed25519.X86.IKeep x s u := IKeep.of_counter hu
  refine WP.mono (VG.Proof.Ed25519.X86.accumulateLoop_ok (ku.ctx hc) scalar batch p hb
    (by rw [hu.mem]; exact hindex) hu.gpr (by rw [hu.mem]; exact hbits)
    (by rw [hu.mem]; exact htable) (by rw [hu.mem]; exact hp) (by rw [hu.mem]; exact hd))
    fun t ⟨kt, pt, dt⟩ => ?_
  exact ⟨ku.trans kt, pt, dt⟩

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointBatch`. -/
section
/-! Each batch contains sixteen consecutive exact powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem loadCheckpoint_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block loadCheckpoint) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = VG.Proof.Ed25519.X86.tablePoint s.mem x (1024 + 128 * j) ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 17 18 19 20 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = VG.Proof.Ed25519.X86.env s.mem x 16 := by
  simp only [loadCheckpoint, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok savePointOps hc) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.tableAddr_ok (ka.ctx hc) 1024 j (by omega) (ka.keep.esi.trans hb))
    fun b ⟨kb, mb, pb⟩ => ?_
  have cb := kb.ctx (ka.ctx hc)
  refine WP.mono (VG.Proof.Ed25519.X86.pointFromTable_ok cb pb (by omega) (by omega)) fun c ⟨kc, pc⟩ => ?_
  refine ⟨ka.trans ((FieldKeep.of_mem kb mb).trans (FieldKeep.of_copy kc cb)), ?_, ?_, ?_⟩
  · rw [pc, mb]
    exact VG.Proof.Ed25519.X86.workspace_table (IKeep.of_field ka) hc _ (by omega) (by omega)
  · rw [VG.Proof.Ed25519.X86.point_congr _ _ _ _ (kc.high cb 17 (by decide)) (kc.high cb 18 (by decide))
      (kc.high cb 19 (by decide)) (kc.high cb 20 (by decide)), mb, ea, VG.Proof.Ed25519.X86.savePoint_eval]
  · rw [kc.high cb 16 (by decide), mb, ea, VG.Proof.Ed25519.X86.savePoint_d]

theorem prepareBatch_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (hd : VG.Proof.Ed25519.X86.env s.mem x 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => VG.Proof.Ed25519.X86.PowersKeep x 5120 2048 s t ∧
      VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env t.mem x) 0 1 2 3 = VG.Proof.Ed25519.X86.point (VG.Proof.Ed25519.X86.env s.mem x) 0 1 2 3 ∧
      (∀ i < 16, VG.Proof.Ed25519.X86.tablePoint t.mem x (5120 + 128 * i) =
        powerPoint (VG.Proof.Ed25519.X86.tablePoint s.mem x (1024 + 128 * j)) i) ∧
      VG.Proof.Ed25519.X86.env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.loadCheckpoint_ok hc j hj hb) fun a ⟨ka, pa, sa, da⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.pointPowers_ok false (ka.ctx hc) 5120 16 (by decide) (by decide)
    (by decide) (by decide) (da.trans hd)) fun b ⟨kb, tb, _, high⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc))) fun t ⟨kt, et⟩ => ?_
  refine ⟨((PowersKeep.of_ikeep (IKeep.of_field ka) _ _).trans kb).trans
    (PowersKeep.of_ikeep (IKeep.of_field kt) _ _), ?_, ?_, ?_⟩
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_eval, VG.Proof.Ed25519.X86.point_congr _ _ _ _ (high 17 (by decide)) (high 18 (by decide))
      (high 19 (by decide)) (high 20 (by decide)), sa]
  · intro i hi
    rw [VG.Proof.Ed25519.X86.workspace_table (IKeep.of_field kt) (kb.ctx (ka.ctx hc)) _ (by omega) (by omega), tb i hi, pa]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [et, VG.Proof.Ed25519.X86.restorePoint_d, high 16 (by decide), da, hd]

end VG.Proof.Ed25519.X86
end

/-! One scalar batch preserves checkpoints, bits and saved API pointers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure BatchKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [VG.Proof.X25519.X86.sub x 24 904, VG.Proof.X25519.X86.sub x 5120 2048] s.mem t.mem

theorem BatchKeep.ctx {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.BatchKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s) : VG.Proof.Ed25519.X86.Ctx x t :=
  hc.keep h.edi h.wr
theorem BatchKeep.trans {x : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.X86.BatchKeep x s t) (k : VG.Proof.Ed25519.X86.BatchKeep x t u) :
    VG.Proof.Ed25519.X86.BatchKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem BatchKeep.of_powers {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (h : VG.Proof.Ed25519.X86.PowersKeep x 5120 2048 s t) : VG.Proof.Ed25519.X86.BatchKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.X25519.X86.sub x 24 904, by simp, VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨VG.Proof.X25519.X86.sub x 24 904, by simp, VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨VG.Proof.X25519.X86.sub x 5120 2048, by simp, fun _ ha => ha⟩

theorem BatchKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (h : VG.Proof.Ed25519.X86.IKeep x s t) :
    VG.Proof.Ed25519.X86.BatchKeep x s t := BatchKeep.of_powers hc (PowersKeep.of_ikeep h _ _)

theorem BatchKeep.of_counter {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [VG.Proof.X25519.X86.sub x 28 4] s.mem t.mem) : VG.Proof.Ed25519.X86.BatchKeep x s t :=
  ⟨he, hs, hr, hw, hf.sub fun r h => ⟨VG.Proof.X25519.X86.sub x 24 904, by simp, by
    rw [List.mem_singleton.mp h]; exact VG.Proof.X25519.X86.sub_sub hc.fit (by decide) (by decide) (by decide)⟩⟩

theorem BatchKeep.checkpoint {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.BatchKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (j : Nat) (hj : j < 32) : VG.Proof.Ed25519.X86.tablePoint t.mem x (1024 + 128 * j) = VG.Proof.Ed25519.X86.tablePoint s.mem x (1024 + 128 * j) := by
  apply VG.Proof.Ed25519.X86.table_point_of_words
  intro k hk
  apply VG.Proof.X25519.X86.wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inr (by omega))
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inl (by omega))

theorem BatchKeep.bit {x : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.X86.BatchKeep x s t) (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (VG.X86.addr x (7168 + i)) = s.mem (VG.X86.addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : (VG.Proof.X25519.X86.sub x (7168 + i) 1).Contains (VG.X86.addr x (7168 + i)) 1 := Region.contains_self _ _
  rcases hr with rfl | rfl
  · exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb
  · exact (VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb

theorem PowersKeep.batch_index {x : BitVec 32} {s t : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (h : VG.Proof.Ed25519.X86.PowersKeep x 5120 2048 s t) : VG.Proof.X25519.X86.wd t.mem x 28 = VG.Proof.X25519.X86.wd s.mem x 28 := by
  apply VG.Proof.X25519.X86.wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inr (by decide))
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))

end VG.Proof.Ed25519.X86
end

/-! Public batch countdown, leaving all coordinate values unchanged. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem counter28_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [VG.Proof.X25519.X86.sub x 28 4] m m') : VG.Proof.Ed25519.X86.env m' x = VG.Proof.Ed25519.X86.env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact VG.Proof.X25519.X86.fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

theorem batchBegin_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (n : Nat)
    (hb : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block batchBegin) s fun t => VG.Proof.Ed25519.X86.BatchKeep x s t ∧
      t.gpr .esi = BitVec.ofNat 32 n ∧ VG.Proof.X25519.X86.wd t.mem x 28 = BitVec.ofNat 32 n ∧
      Frame [VG.Proof.X25519.X86.sub x 28 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_subi fun v hv _ _ => ?_
  have bv : v.gpr .esi = BitVec.ofNat 32 n := by
    rw [hv.gpr, hu.gpr]
    change VG.Proof.X25519.X86.wd s.mem x 28 - 1 = _
    rw [hb, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have cv := ((IKeep.of_counter hu).trans (IKeep.of_counter hv)).ctx hc
  refine Wp.wp_stm cv.edi (cv.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have mt : t.mem = s.mem.writeW (VG.X86.addr x 28) (BitVec.ofNat 32 n) := by rw [ht.mem, hv.mem, hu.mem, bv]
  have ft : Frame [VG.Proof.X25519.X86.sub x 28 4] s.mem t.mem := by
    rw [mt]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨BatchKeep.of_counter hc ?_ ?_ ?_ ?_ ft, ?_, ?_, ft⟩
  · rw [ht.gpr, hv.other .edi (by decide), hu.other .edi (by decide)]
  · rw [ht.gpr, hv.other .esp (by decide), hu.other .esp (by decide)]
  · rw [ht.rd, hv.rd, hu.rd]
  · rw [ht.wr, hv.wr, hu.wr]
  · rw [ht.gpr]; exact bv
  · rw [mt, VG.Proof.X25519.X86.wd_write_self]

theorem batchTest_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (n : Nat) (hn : n < 32)
    (hb : VG.Proof.X25519.X86.wd s.mem x 28 = BitVec.ofNat 32 n) :
    WP isa (.block batchTest) s fun t => VG.Proof.Ed25519.X86.IKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some (!decide (n = 0)) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨(IKeep.of_counter hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩, by rw [ht.mem, hu.mem], ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hu.gpr]
  change some (!(VG.Proof.X25519.X86.wd s.mem x 28 == 0)) = _
  rw [hb, Wp.ofNat_beq_zero (by omega)]

theorem mulCounterInit_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ Frame [VG.Proof.X25519.X86.sub x 28 4] s.mem t.mem ∧ VG.Proof.X25519.X86.wd t.mem x 28 = BitVec.ofNat 32 count := by
  refine Wp.wp_movi fun u hu => ?_
  have cu := (VG.Proof.X25519.X86.updKeep hu).ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_, ?_⟩
  · rw [ht.mem, hu.mem]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, VG.Proof.X25519.X86.wd_write_self, hu.gpr]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.RecoverParity`. -/
section

/-! Merged from `Proof.Ed25519.X86.FieldCheck`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

def orWords (m : Mem) (x : BitVec 32) (o : Nat) : Nat → BitVec 32
  | 0 => 0
  | n + 1 => VG.Proof.Ed25519.X86.orWords m x o n ||| wd m x (o + 4 * n)

theorem orWords_zero (m : Mem) (x : BitVec 32) (o n : Nat) :
    VG.Proof.Ed25519.X86.orWords m x o n = 0#32 ↔ VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv m x (o + 4 * j)) n = 0 := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    change (VG.Proof.Ed25519.X86.orWords m x o n ||| wd m x (o + 4 * n) = 0#32) ↔ _
    rw [BitVec.or_eq_zero_iff, ih, VG.Proof.X25519.X86.num_succ]
    have hp : 0 < (2 ^ 32) ^ n := Nat.pow_pos (by decide)
    have hw : VG.Proof.X25519.X86.wd m x (o + 4 * n) = 0#32 ↔ VG.Proof.X25519.X86.wv m x (o + 4 * n) = 0 :=
      ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · rintro ⟨h, w⟩; rw [h, w]; rfl
    · intro h
      have hw' : VG.Proof.X25519.X86.wv m x (o + 4 * n) = 0 := by
        have := Nat.le_mul_of_pos_left (VG.Proof.X25519.X86.wv m x (o + 4 * n)) hp
        omega_using [h, this]
      exact ⟨by omega_using [h], hw'⟩

theorem wordOr_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o j : Nat}
    (ho : o + 4 * j + 4 ≤ 8192) :
    WP isa (.block (wordOr o j)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧
      t.gpr .eax = s.gpr .eax ||| wd s.mem x (o + 4 * j) := by
  refine Wp.wp_ldm hc.edi (hc.inRW ho (by decide)) fun a ha => ?_
  refine Wp.wp_or fun t ht => WP.block_nil ?_
  exact ⟨(VG.Proof.X25519.X86.updKeep ha).trans (VG.Proof.X25519.X86.updKeep ht), ht.mem.trans ha.mem,
    by rw [ht.gpr, ha.gpr, ha.other .eax (by decide)]⟩

theorem orPrefix_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat}
    (ho : o + 32 ≤ 8192) (hz : s.gpr .eax = 0) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (wordOr o))) s fun t =>
      VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧ t.gpr .eax = VG.Proof.Ed25519.X86.orWords s.mem x o n
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, hz⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.orPrefix_ok hc ho hz n (by omega_using [hn])) fun u ⟨ku, mu, vu⟩ => ?_)
    refine WP.mono (VG.Proof.Ed25519.X86.wordOr_ok (ku.ctx hc) (by omega_using [ho, hn])) fun t ⟨kt, mt, vt⟩ => ?_
    exact ⟨ku.trans kt, mt.trans mu, by rw [vt, mu, vu]; rfl⟩

theorem wordsZero_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (wordsZero o)) s fun t => VG.Proof.X25519.X86.Keep s t ∧ t.mem = s.mem ∧
      t.zf = some (decide (VG.Proof.X25519.X86.fe s.mem x o = 0)) := by
  rw [wordsZero, List.append_assoc, WP.block_append_iff]
  refine Wp.wp_movi fun a ha => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.orPrefix_ok ((VG.Proof.X25519.X86.updKeep ha).ctx hc) ho ha.gpr 8 (Nat.le_refl _)) fun b ⟨kb, mb, vb⟩ => ?_
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨((VG.Proof.X25519.X86.updKeep ha).trans kb).trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩,
    ht.mem.trans (mb.trans ha.mem), ?_⟩
  rw [zt, BitVec.and_self, vb, ha.mem]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  change (VG.Proof.Ed25519.X86.orWords s.mem x o 8 == 0) = true ↔ decide (VG.Proof.X25519.X86.fe s.mem x o = 0) = true
  rw [beq_iff_eq, decide_eq_true_eq]
  exact VG.Proof.Ed25519.X86.orWords_zero s.mem x o 8

theorem fieldZero_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧ VG.Proof.Ed25519.X86.env t.mem x = VG.Proof.Ed25519.X86.env s.mem x ∧
      t.zf = some (decide (VG.Proof.Ed25519.X86.env s.mem x a = 0)) := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.freezeField_ok hc a) fun u ⟨ku, eu, vu⟩ => ?_
  have ho : offset a + 32 ≤ 8192 := by have ha := a.isLt; simp only [offset]; omega_using [ha]
  refine WP.mono (VG.Proof.Ed25519.X86.wordsZero_ok (ku.ctx hc) ho) fun t ⟨kt, mt, zt⟩ => ?_
  refine ⟨ku.trans (FieldKeep.of_mem kt mt), by rw [mt, eu], ?_⟩
  rw [zt, vu]
  have he : (VG.Proof.Ed25519.X86.env s.mem x a).val = 0 ↔ VG.Proof.Ed25519.X86.env s.mem x a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s) (a b : Slot) :
    WP isa (.block (fieldEqual a b)) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧
      (∀ i : Slot, i ≠ 21 → VG.Proof.Ed25519.X86.env t.mem x i = VG.Proof.Ed25519.X86.env s.mem x i) ∧
      t.zf = some (decide (VG.Proof.Ed25519.X86.env s.mem x a = VG.Proof.Ed25519.X86.env s.mem x b)) := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86.fieldCode_ok [.sub 21 a b] hc) fun u ⟨ku, eu⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86.fieldZero_ok (ku.ctx hc) 21) fun t ⟨kt, et, zt⟩ => ?_
  refine ⟨ku.trans kt, ?_, ?_⟩
  · intro i hi
    rw [et, eu]
    exact Function.update_of_ne hi _ _
  · rw [zt, eu]
    change some (decide (VG.Proof.Ed25519.X86.env s.mem x a - VG.Proof.Ed25519.X86.env s.mem x b = 0)) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def signWord (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

theorem parity_eq (w : BitVec 32) (b : Bool) :
    ((w &&& 1) ^^^ VG.Proof.Ed25519.X86.signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega)]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {x : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.X86.Ctx x s)
    (b : Bool) (hb : s.gpr .esi = VG.Proof.Ed25519.X86.signWord b) :
    WP isa (.block recoverParity) s fun t => VG.Proof.Ed25519.X86.FieldKeep x s t ∧ t.mem = s.mem ∧
      t.zf = some ((VG.Proof.X25519.X86.fe s.mem x 64 % 2 == 1) == b) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_andi fun c hc' => Wp.wp_xor fun d hd => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kk := (VG.Proof.X25519.X86.updKeep ha).trans ((VG.Proof.X25519.X86.updKeep hc').trans (VG.Proof.X25519.X86.updKeep hd))
  have kt : VG.Proof.X25519.X86.Keep s t := kk.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = s.mem := by rw [ht.mem, hd.mem, hc'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem kt mt, mt, ?_⟩
  rw [zt, BitVec.and_self, hd.gpr, hc'.gpr, hc'.other .esi (by decide), ha.other .esi (by decide), hb, ha.gpr]
  rw [VG.Proof.Ed25519.X86.field_parity]
  exact congrArg some (VG.Proof.Ed25519.X86.parity_eq _ b)

theorem returnFlag_ok (s : State) (x : BitVec 32) (b : Bool) :
    WP isa (.block [.mov .eax (.imm (VG.Proof.Ed25519.X86.signWord b))]) s fun t =>
      VG.Proof.Ed25519.X86.FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .eax = VG.Proof.Ed25519.X86.signWord b := by
  refine Wp.wp_movi fun t ht => WP.block_nil ⟨FieldKeep.of_mem (VG.Proof.X25519.X86.updKeep ht) ht.mem, ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyContract`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

def verifyLocal : Contract isa where
  pre s :=
    let pk := VG.Proof.X25519.X86.sub (arg s 0) 0 32
    let sig := VG.Proof.X25519.X86.sub (arg s 1) 0 64
    let challenge := VG.Proof.X25519.X86.sub (arg s 2) 0 64
    let scratch := VG.Proof.X25519.X86.scR 8192 (arg s 3)
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge, args] ∧ s.wr = [VG.Proof.X25519.X86.sub (arg s 3) 0 0, scratch] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s t := t.gpr .eax = VG.Proof.Ed25519.X86.signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) 64 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 2).setWidth 64) 64

theorem input_slice {s : State} {scidx i n skip bytes : Nat} (h : VG.Proof.Ed25519.X86.InputPre s scidx i n)
    (hn : skip + bytes ≤ 4 * n) (hb : 0 < bytes) :
    VG.Proof.Ed25519.X86.SlicePre s scidx (arg s i + BitVec.ofNat 32 skip) bytes := by
  have hf := h.fit
  have hs : skip < 2 ^ 32 := by omega_using [hn, hb, hf]
  refine ⟨?_, ?_, ?_⟩
  · intro k len hl hk
    rw [VG.Proof.Ed25519.X86.addr_plus]
    exact ⟨_, h.rd, VG.Proof.X25519.X86.sub_contains (by omega_using [hf]) (Nat.zero_le _)
      (by omega_using [hn, hk]) hl⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt (by omega_using [hn, hb, hf])]
    omega_using [hn, hf]
  · apply h.sep.sub_left
    rw [VG.Proof.X25519.X86.sub, VG.Proof.Ed25519.X86.addr_plus, Nat.add_zero, VG.Proof.X25519.X86.sub, addr_eq (by omega_using [hn, hb, hf]), VG.Proof.X25519.X86.addr_zero]
    exact Offset.sub_base _ hn

structure VerifyPre (s : State) : Prop where
  scratch : VG.Proof.Ed25519.X86.ScratchPre s 3 4
  pk : VG.Proof.Ed25519.X86.SlicePre s 3 (arg s 0 + BitVec.ofNat 32 0) 32
  r : VG.Proof.Ed25519.X86.SlicePre s 3 (arg s 1 + BitVec.ofNat 32 0) 32
  scalar : VG.Proof.Ed25519.X86.SlicePre s 3 (arg s 1 + BitVec.ofNat 32 32) 32
  challenge : VG.Proof.Ed25519.X86.SlicePre s 3 (arg s 2 + BitVec.ofNat 32 0) 64
  signature_fit : (arg s 1).toNat + 64 ≤ 2 ^ 32

theorem verify_pre {s : State} (h : verifyLocal.pre s) : VG.Proof.Ed25519.X86.VerifyPre s := by
  obtain ⟨rd, wr, ps, ss, cs, ars, rs, pf, sf, cf, scf, spf⟩ := h
  have hp : VG.Proof.Ed25519.X86.ScratchPre s 3 4 := ⟨by decide, by rw [wr]; simp, scf,
    by rw [rd]; simp, by omega_using [spf], ars, rs⟩
  have p : VG.Proof.Ed25519.X86.InputPre s 3 0 8 := ⟨by rw [rd]; simp, pf, ps⟩
  have sg : VG.Proof.Ed25519.X86.InputPre s 3 1 16 := ⟨by rw [rd]; simp, sf, ss⟩
  have ch : VG.Proof.Ed25519.X86.InputPre s 3 2 16 := ⟨by rw [rd]; simp, cf, cs⟩
  exact ⟨hp, VG.Proof.Ed25519.X86.input_slice p (by decide) (by decide), VG.Proof.Ed25519.X86.input_slice sg (by decide) (by decide),
    VG.Proof.Ed25519.X86.input_slice sg (by decide) (by decide), VG.Proof.Ed25519.X86.input_slice ch (by decide) (by decide), sf⟩

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyFinish_ok {s₀ s : State} (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ 3 4)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) :
    WP isa (.block verifyFinish) s fun t => abiPreserved s₀ t ∧ t.gpr .eax = s.gpr .eax ∧ t.mem = s.mem := by
  simp only [verifyFinish, List.append_assoc]
  refine WP.block_append (Wp.wp_mov fun a ka => WP.block_nil ?_)
  have ca := (VG.Proof.X25519.X86.updKeep ka).ctx (hs.ctx hp.fit hp.wr)
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.abiRestore_ok (g := s₀.gpr) ca (by rw [ka.mem]; exact hs.saved))
    fun b ⟨gb, sb, eb, mb⟩ => ?_)
  refine Wp.wp_mov fun t kt => WP.block_nil ?_
  have mt : t.mem = s.mem := kt.mem.trans (mb.trans ka.mem)
  refine ⟨⟨?_, ?_⟩, ?_, mt⟩
  · intro r hr
    rw [kt.other r fun e => absurd (e ▸ hr) (by decide)]
    by_cases h : r = .esp
    · subst h; rw [sb, ka.other _ (by decide)]; exact hs.esp
    · exact gb r hr h
  · rw [mt]
    exact hs.frame.readW (Region.contains_self _ _)
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc) (by decide)
  · rw [kt.gpr, eb, ka.gpr]

end VG.Proof.Ed25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar`. -/
section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (T)

theorem scalarCarry_compare {x : BitVec 32} {s t : State}
    (hv : VG.Proof.X25519.X86.fe t.mem x VG.Impl.X25519.X86.T + 2 ^ 256 * VG.Proof.X25519.X86.acc t = VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR + (2 ^ 256 - Spec.Ed25519.L)) :
    (t.gpr .ebx == 0) = decide (VG.Proof.X25519.X86.fe s.mem x VG.Impl.Ed25519.X86.scalarR < Spec.Ed25519.L) := by
  have hr := VG.Proof.X25519.X86.fe_lt s.mem x VG.Impl.Ed25519.X86.scalarR
  have ht := VG.Proof.X25519.X86.fe_lt t.mem x VG.Impl.X25519.X86.T
  have hL := order_bound
  have hc : VG.Proof.X25519.X86.acc t ≤ 1 := by omega_using [hv, hr, hL]
  have he : (t.gpr .ebx).toNat = VG.Proof.X25519.X86.acc t := by
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at hc ⊢
    omega_using [hc]
  have hz : t.gpr .ebx = 0 ↔ (t.gpr .ebx).toNat = 0 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, hz, he]
  omega_using [hv, ht, hL]

theorem verifyScalar_ok {s₀ s : State}
    (hp : VG.Proof.Ed25519.X86.ScratchPre s₀ 3 4) (hi : VG.Proof.Ed25519.X86.SlicePre s₀ 3 (arg s₀ 1 + 32) 32)
    (hs : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) s) :
    WP isa (.block verifyScalar) s fun t => VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 3) t ∧
      t.zf = some (decide (VG.Proof.X25519.X86.fe s₀.mem (arg s₀ 1 + 32) 0 < Spec.Ed25519.L)) := by
  simp only [verifyScalar, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.inputSliceWords_ok hp hi hs (by decide)
    (dst := 64) (by decide) (by decide) (by decide)) fun a ⟨ha, wa, _⟩ => ?_)
  have fa : VG.Proof.X25519.X86.fe a.mem (arg s₀ 3) VG.Impl.Ed25519.X86.scalarR = VG.Proof.X25519.X86.fe s₀.mem (arg s₀ 1 + 32) 0 := by
    apply VG.Proof.X25519.X86.num_congr
    intro k hk
    change (VG.Proof.X25519.X86.wd a.mem (arg s₀ 3) (64 + 4 * k)).toNat =
      (VG.Proof.X25519.X86.wd s₀.mem (arg s₀ 1 + BitVec.ofNat 32 32) (0 + 4 * k)).toNat
    rw [Nat.zero_add]
    exact congrArg BitVec.toNat (wa k hk)
  refine WP.block_append (WP.mono (VG.Proof.Ed25519.X86.scalarSubtract_ok (ha.ctx hp.fit hp.wr)) fun b ⟨kb, fb, vb⟩ => ?_)
  have hb := ha.of_offset hp.fit (Keep.scalar kb) fb (by decide) (by decide) (by decide)
  refine Wp.wp_test fun t kt zt => WP.block_nil ?_
  refine ⟨⟨(congrFun kt.gpr .edi).trans hb.edi, (congrFun kt.gpr .esp).trans hb.esp,
    kt.rd.trans hb.rd, kt.wr.trans hb.wr, by rw [kt.mem]; exact hb.frame,
    by rw [kt.mem]; exact hb.saved⟩, ?_⟩
  rw [zt, BitVec.and_self, VG.Proof.Ed25519.X86.scalarCarry_compare vb, fa]

end VG.Proof.Ed25519.X86

end
