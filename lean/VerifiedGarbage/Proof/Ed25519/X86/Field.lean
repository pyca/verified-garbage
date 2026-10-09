import VerifiedGarbage.Proof.Ed25519.X86.Workspace
import VerifiedGarbage.Proof.X25519.X86.Field32.Call
import VerifiedGarbage.Impl.Ed25519.X86.Field

/-! Merged from `Proof.Ed25519.X86.FieldMemory`. -/
section
/-! Full-width constants and field-slot copies. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86 VG.Spec.X25519
open VG.Proof.X25519

theorem slot_valid (o : Slot) : isSlot 64 (offset o) = true := (by decide : ∀ i : Slot, isSlot 64 (offset i) = true) o

theorem fill_step {x : BitVec 32} {s₀ s : State} (hc : Ctx x s) {o n : Nat} (ho : Below o) (hn : n < 8)
    (f : Nat → BitVec 32) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = f j) :
    WP isa (.block [.mov .eax (.imm (f n)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = f j := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self, u₁.gpr]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem fill_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx x s₀) {o : Nat} (ho : Below o) (f : Nat → BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (f k)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = f j
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (fill_ok hc₀ ho f n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      fill_step (k₁.ctx hc₀) ho (by omega_using [hn]) f k₁ f₁ w₁)

theorem num_digits (v n : Nat) :
    num (fun k => v / (2 ^ 32) ^ k % 2 ^ 32) n = v % (2 ^ 32) ^ n := by
  induction n with
  | zero => simp only [num, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [num_succ, ih, Nat.pow_succ (2 ^ 32) n]
    exact Nat.mod_mul.symm

theorem constField_op {s : State} {x : BitVec 32} (hc : Ctx x s) (o : Slot) (v : Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Keep s t ∧ Frame [sub x (offset o) 32] s.mem t.mem ∧ F t.mem x (offset o) = v := by
  refine WP.mono (fill_ok hc (slot_below (slot_valid o))
    (fun k => BitVec.ofNat 32 (v.val / (2 ^ 32) ^ k)) 8 (Nat.le_refl _)) fun t ⟨hk, hf, hv⟩ => ?_
  refine ⟨hk, hf, ?_⟩
  have he : fe t.mem x (offset o) = v.val := by
    unfold fe
    rw [num_congr (g := fun k => v.val / (2 ^ 32) ^ k % 2 ^ 32) (fun k h => by
      rw [wv, hv k h, BitVec.toNat_ofNat]), num_digits]
    exact Nat.mod_eq_of_lt (by have h := v.isLt; simp only [P] at h; omega)
  rw [F, he, toFe_self]

end VG.Proof.Ed25519.X86
end

/-! Field programs and exact Edwards-coordinate formulas. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : BitVec 32) : Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : Env) (o a b i : Slot) :
    evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_add_apply (e : Env) (o a b i : Slot) :
    evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : Env) (o a b i : Slot) :
    evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure FieldKeep (x : BitVec 32) (s t : State) : Prop where
  keep : Keep s t
  frame : Frame [sub x 64 864] s.mem t.mem

theorem FieldKeep.refl (x : BitVec 32) (s : State) : FieldKeep x s s :=
  ⟨Keep.refl _, Frame.refl _ _⟩

theorem FieldKeep.trans {x : BitVec 32} {s t u : State}
    (h : FieldKeep x s t) (k : FieldKeep x t u) : FieldKeep x s u :=
  ⟨h.keep.trans k.keep, h.frame.trans k.frame⟩

theorem FieldKeep.ctx {x : BitVec 32} {s t : State}
    (h : FieldKeep x s t) (hc : Ctx x s) : Ctx x t := h.keep.ctx hc

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
  · rw [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (offset_inj h))]

theorem const_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32) (o : Slot)
    (hf : Frame [sub x (offset o) 32] m m') :
    env m' x = Function.update (env m x) o (F m' x (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst i; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne hi]
    apply congrArg VG.Proof.X25519.toFe
    exact fe_frame1 hf hx (by simp only [offset]; omega)
      (by simp only [offset]; omega) (slot_ne (slot_valid o) (slot_valid i) (fun h => hi (offset_inj h)))

theorem raw_field_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (op : Op)
    (hv : opValid 64 op = true) (o : Slot) (ho : opOut op = offset o) :
    WP isa (.block op.code) s fun t => FieldKeep x s t ∧
      env t.mem x = Function.update (env s.mem x) o (opVal op (F s.mem x)) := by
  refine WP.mono (op_ok hc op hv) fun t ⟨hk, hf, he⟩ => ?_
  refine ⟨⟨hk, hf⟩, ?_⟩
  have hr := restrict_update (F s.mem x) o (opVal op (F s.mem x))
  funext i
  change F t.mem x (offset i) = Function.update (fun j => F s.mem x (offset j)) o (opVal op (F s.mem x)) i
  rw [← congrFun hr i]
  exact (he (offset i) (slot_valid i)).trans (by rw [ho])

theorem fieldOp_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (op : FieldOp) :
    WP isa (.block op.code) s fun t => FieldKeep x s t ∧ env t.mem x = evalOp op (env s.mem x) := by
  cases op with
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hk, hf, hv⟩ => ?_
    refine ⟨⟨hk, frameWiden hf hc.fit (by simp only [offset]; omega)
      (by simp only [offset]; omega) (by simp only [offset]; omega)⟩, ?_⟩
    rw [const_env hc.fit o hf, hv]; rfl
  | copy o a =>
    exact raw_field_ok hc (.copy (offset o) (offset a))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | mul o a b =>
    exact raw_field_ok hc (.mul (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | add o a b =>
    exact raw_field_ok hc (.add (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl
  | sub o a b =>
    exact raw_field_ok hc (.sub (offset o) (offset a) (offset b))
      (by simp only [opValid, opOut, opIns, List.all_cons, List.all_nil, slot_valid]; rfl) o rfl

theorem fieldCode_ok (ops : List FieldOp) {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block (fieldCode ops)) s fun t =>
      FieldKeep x s t ∧ env t.mem x = evalOps ops (env s.mem x) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOp_ok hc op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-! ## Field programs with calls

A product of `fieldProg` is a call of `vg_gf25519_r32_mul`
(`Proof/X25519/X86/Field32/Call.lean`), which also changes the function's own
working space (bytes 768 to 1023) and the 20 bytes of stack below `esp` that
the call uses (`CallKeep`). -/

/-- What field programs with calls keep: the registers `Keep` keeps, and the
memory but the slots, the field function's own working space and the stack a
call uses. -/
structure CallKeep (x : BitVec 32) (s t : State) : Prop where
  keep : Keep s t
  frame : Frame [sub x 64 960, VG.Proof.X25519.X86.callStk s] s.mem t.mem

theorem CallKeep.refl (x : BitVec 32) (s : State) : CallKeep x s s :=
  ⟨Keep.refl _, Frame.refl _ _⟩

theorem CallKeep.trans {x : BitVec 32} {s t u : State}
    (h : CallKeep x s t) (k : CallKeep x t u) : CallKeep x s u :=
  ⟨h.keep.trans k.keep, h.frame.trans (by rw [VG.Proof.X25519.X86.callStk, ← h.keep.esp]; exact k.frame)⟩

theorem CallKeep.ctx {x : BitVec 32} {s t : State}
    (h : CallKeep x s t) (hc : Ctx x s) : Ctx x t := h.keep.ctx hc

/-- Field code without calls keeps what field code with calls does. -/
theorem FieldKeep.call {x : BitVec 32} {s t : State} (h : FieldKeep x s t) : CallKeep x s t :=
  ⟨h.keep, h.frame.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩⟩

/-- Bytes of the working space lie apart from the stack a call uses. -/
theorem stk_apart {x : BitVec 32} {s : State} (hc : Ctx x s) {d n : Nat} (hd : d + n ≤ 8192) (hn : 0 < n) :
    (sub x d n).Disjoint (callStk s) :=
  (hc.stk rfl (Nat.le_refl _)).2.sub_left (by
    rw [scR_eq]; exact sub_sub hc.fit (Nat.zero_le _) (by omega) (by omega))

/-- A word of the working space apart from regions `rs`, through a frame of them and of the
stack a call uses. -/
theorem wd_frameS {x : BitVec 32} {s : State} (hc : Ctx x s) {rs : List Region} {m m' : Mem}
    (hf : Frame (rs ++ [callStk s]) m m') {d : Nat} (hd : d + 4 ≤ 8192)
    (h : ∀ r ∈ rs, (sub x d 4).Disjoint r) : wd m' x d = wd m x d :=
  wd_frame hf fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact h r hr
    · rw [List.mem_singleton.mp hr]; exact stk_apart hc hd (by decide)

/-- `wd_frame1` with the stack a call uses. -/
theorem wd_frame1s {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem} {o n d : Nat}
    (hf : Frame [sub x o n, callStk s] m m') (ho : o + n ≤ 8192) (hd : d + 4 ≤ 8192)
    (h : d + 4 ≤ o ∨ o + n ≤ d) : wd m' x d = wd m x d :=
  wd_frameS hc (rs := [sub x o n]) hf hd fun r hr => by
    rw [List.mem_singleton.mp hr]; exact sub_disj (by have := hc.fit; omega) (by have := hc.fit; omega) h

/-- `fe_frame1` with the stack a call uses. -/
theorem fe_frame1s {x : BitVec 32} {s : State} (hc : Ctx x s) {m m' : Mem} {o n q : Nat}
    (hf : Frame [sub x o n, callStk s] m m') (ho : o + n ≤ 8192) (hq : q + 32 ≤ 8192)
    (h : q + 32 ≤ o ∨ o + n ≤ q) : fe m' x q = fe m x q :=
  fe_frame fun k hk => wd_frame1s hc hf ho (by omega) (by omega)

/-- A frame of a region and the stack is one of any region containing it, and the stack. -/
theorem frameWidenS {x : BitVec 32} {s : State} {m m' : Mem} {o n o' n' : Nat}
    (hf : Frame [sub x o n, callStk s] m m') (hx : x.toNat + 8192 ≤ 2 ^ 32) (h₁ : o' ≤ o)
    (h₂ : o + n ≤ o' + n') (hn : o < 8192) : Frame [sub x o' n', callStk s] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_sub hx h₁ h₂ hn⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- A frame of a region is one of it and the stack. -/
theorem Frame.withStk {x : BitVec 32} {s : State} {m m' : Mem} {o n : Nat}
    (hf : Frame [sub x o n] m m') : Frame [sub x o n, callStk s] m m' :=
  hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

theorem mulProg_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (o a b : Slot) :
    WP isa (FieldOp.mul o a b).prog s fun t => CallKeep x s t ∧ env t.mem x = evalOp (.mul o a b) (env s.mem x) := by
  have hfit := hc.fit
  have sl : ∀ q : Slot, offset q + 32 ≤ 768 := fun q => by simp only [offset]; omega
  refine WP.mono (VG.Proof.X25519.X86.Field32.mulCall_ok hc (sl o) (sl a) (sl b)) fun t ⟨hk, hf, hv⟩ => ⟨⟨hk, ?_⟩, ?_⟩
  · refine hf.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (by simp only [offset]; omega)
        (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (by decide) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · funext i
    by_cases hi : i = o
    · subst i
      rw [evalOp_mul_apply, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      exact VG.Proof.X25519.toFe_mul hv
    · rw [evalOp_mul_apply, ite_eq_right_iff.mpr (fun h => absurd h hi)]
      apply congrArg VG.Proof.X25519.toFe
      refine fe_frame fun k hk => wd_frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj (by simp only [offset]; omega) (by simp only [offset]; omega)
          (by have := slot_ne (slot_valid o) (slot_valid i) (fun h => hi (offset_inj h)); simp only [offset] at this ⊢; omega)
      · exact sub_disj (by simp only [offset]; omega) (by simp only [VG.Impl.X25519.X86.Field32.opA]; omega)
          (.inl (by simp only [offset, VG.Impl.X25519.X86.Field32.opA]; omega))
      · exact (hc.stk rfl (Nat.le_refl _)).2.sub_left (by
          rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [offset]; omega)
            (by simp only [offset]; omega))

theorem fieldProgOp_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (op : FieldOp) :
    WP isa op.prog s fun t => CallKeep x s t ∧ env t.mem x = evalOp op (env s.mem x) := by
  cases op with
  | mul o a b => exact mulProg_ok hc o a b
  | _ => exact WP.mono (fieldOp_ok hc _) fun t ⟨hk, he⟩ => ⟨hk.call, he⟩

theorem fieldProg_ok (ops : List FieldOp) {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (fieldProg ops) s fun t => CallKeep x s t ∧ env t.mem x = evalOps ops (env s.mem x) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨CallKeep.refl _ _, rfl⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (fieldProgOp_ok hc op) fun t ⟨ht, et⟩ => ?_)
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) :
    point (evalOps pointAddOps e) 0 1 2 3 = addResult e 4 (by decide) := by
  rfl

theorem pointDouble_formula (e : Env) :
    point (evalOps pointDoubleOps e) 0 1 2 3 = addResult e 0 (by decide) := by
  rfl

theorem addResult_eq (e : Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    addResult e q hq = Spec.Ed25519.pointAdd (point e 0 1 2 3)
      (point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) :=
  (pointAdd_formula e).trans (addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 0 1 2 3) :=
  (pointDouble_formula e).trans (addResult_eq e 0 (by decide) hd)

end VG.Proof.Ed25519.X86
