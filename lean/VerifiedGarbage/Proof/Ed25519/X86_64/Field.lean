import VerifiedGarbage.Impl.Ed25519.X86_64.Field
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 field programs: correctness of the lowering

Each arithmetic operation uses X25519's existing proof. An induction composes
these into a proof for any list of field operations.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F fe ofs)

/-- The field multiplications the code may be emitted with: the baseline's, or BMI2 and
ADX's. The proofs hold for any multiplications that are correct (`ok`); the constant-time
proofs evaluate the code, so they consider each of these (`known`). -/
class EdArith (fld : Arith) : Prop where
  ok : Proof.X25519.X86_64.FieldOk fld
  known : fld = Impl.X25519.X86_64.baseline ∨ fld = Impl.X25519.X86_64.adx

instance : EdArith Impl.X25519.X86_64.baseline := ⟨Proof.X25519.X86_64.baseline_ok, .inl rfl⟩
instance : EdArith Impl.X25519.X86_64.adx := ⟨Proof.X25519.X86_64.adx_ok, .inr rfl⟩

variable {fld : Arith} [EdArith fld]

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : Addr) : Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .sqr o a => Function.update e o (e a * e a)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)
  | .mul2 o a b => Function.update e o (e a * e b + e a * e b)
  | .sqr2 o a => Function.update e o (e a * e a + e a * e a)

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

structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 64 704 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (k : Keep base t u) :
    Keep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem env_update {base : Addr} {m m' : Mem} (o : Slot)
    (h : Outside base (offset o) 32 m m') :
    env m' base = Function.update (env m base) o (F m' base (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [env]
  · rw [Function.update_of_ne hi]
    simp only [env, F]
    have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem op_keep {base : Addr} {o : Slot} {s t : State} (h : Op base (offset o) s t) :
    Keep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by simp only [offset]; omega)
    (by simp only [offset]; omega)⟩

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base) (op : FieldOp) :
    WP isa (.block (op.code fld)) s fun t => Keep base s t ∧ env t.mem base = evalOp op (env s.mem base) := by
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | const o v =>
    refine WP.mono (constField_op hs o v) fun t ⟨h, e, _⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | mul o a b =>
    refine WP.mono ((EdArith.ok (fld := fld)).mul hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | sqr o a =>
    refine WP.mono ((EdArith.ok (fld := fld)).sqr hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | add o a b =>
    refine WP.mono (Proof.X25519.X86_64.add_ok hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | sub o a b =>
    refine WP.mono (Proof.X25519.X86_64.sub_ok hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | mul2 o a b =>
    refine WP.mono ((EdArith.ok (fld := fld)).mul2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩
  | sqr2 o a =>
    refine WP.mono ((EdArith.ok (fld := fld)).sqr2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl⟩

/-- Slot `i` holds at most `2p`. -/
def Bnd (m : Mem) (base : Addr) (i : Slot) : Prop :=
  fe m base (offset i) ≤ 2 * Spec.X25519.P

/-- A product of `fld` is at most `2p`. -/
theorem EdArith.mulBnd {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Proof.X25519.X86_64.Slot o) (ha : Proof.X25519.X86_64.Slot a)
    (hb : Proof.X25519.X86_64.Slot b) :
    WP isa (.block (fld.mul o a b)) s fun t => Op base o s t ∧
      F t.mem base o = F s.mem base a * F s.mem base b ∧ fe t.mem base o ≤ 2 * Spec.X25519.P := by
  rcases EdArith.known (fld := fld) with rfl | rfl
  · exact Proof.X25519.X86_64.mulBnd_ok hs ho ha hb
  · exact Proof.X25519.X86_64.mulXBnd_ok hs ho ha hb

/-- A square of `fld` is at most `2p`. -/
theorem EdArith.sqrBnd {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Proof.X25519.X86_64.Slot o) (ha : Proof.X25519.X86_64.Slot a) :
    WP isa (.block (fld.sqr o a)) s fun t => Op base o s t ∧
      F t.mem base o = F s.mem base a * F s.mem base a ∧ fe t.mem base o ≤ 2 * Spec.X25519.P := by
  rcases EdArith.known (fld := fld) with rfl | rfl
  · exact Proof.X25519.X86_64.sqrBnd_ok hs ho ha
  · exact Proof.X25519.X86_64.sqrXBnd_ok hs ho ha

/-- The bounds after an operation into `op.out`: the other slots keep theirs. -/
theorem bnd_after {op : FieldOp} {B : Slot → Bool} {base : Addr} {s t : State}
    (h : Op base (offset op.out) s t) (hB : ∀ i, B i = true → Bnd s.mem base i)
    (hp : op.bnd = true → Bnd t.mem base op.out) :
    ∀ i, bndStep op B i = true → Bnd t.mem base i := by
  intro i hi
  by_cases e : i = op.out
  · subst e
    simp only [bndStep, ↓reduceIte] at hi
    exact hp hi
  · simp only [bndStep, e, ↓reduceIte] at hi
    have hne : i.val ≠ op.out.val := fun h' => e (Fin.ext h')
    unfold Bnd
    rw [h.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
    exact hB i hi

/-- `fieldOpB_ok`, with the operation's frame: memory changes only at its result. -/
theorem fieldOpB_op {s : State} {base : Addr} (hs : Scr s base) (lazy : Bool) (op : FieldOp)
    {B : Slot → Bool} (hok : opOk lazy op B = true) (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (op.codeB fld lazy)) s fun t => Op base (offset op.out) s t ∧
      env t.mem base = evalOp op (env s.mem base) ∧ ∀ i, bndStep op B i = true → Bnd t.mem base i := by
  cases op with
  | mul o a b =>
    refine WP.mono (EdArith.mulBnd (fld := fld) hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e, hb⟩ => ?_
    exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => hb⟩
  | sqr o a =>
    refine WP.mono (EdArith.sqrBnd (fld := fld) hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e, hb⟩ => ?_
    exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => hb⟩
  | add o a b =>
    cases lazy with
    | false =>
      refine WP.mono (Proof.X25519.X86_64.add_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
    | true =>
      have hab : Bnd s.mem base a ∨ Bnd s.mem base b := by
        simp only [opOk, Bool.or_eq_true] at hok
        exact hok.imp (hB a) (hB b)
      refine WP.mono (Proof.X25519.X86_64.addL_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega) hab) fun t ⟨h, e⟩ => ?_
      exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | sub o a b =>
    cases lazy with
    | false =>
      refine WP.mono (Proof.X25519.X86_64.sub_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
    | true =>
      refine WP.mono (Proof.X25519.X86_64.subL_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega) (hB b hok)) fun t ⟨h, e⟩ => ?_
      exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | copy o a =>
    refine WP.mono (copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | const o v =>
    refine WP.mono (constField_op hs o v) fun t ⟨h, e, r⟩ => ?_
    refine ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => ?_⟩
    show fe t.mem base (offset o) ≤ _
    rw [r]; have := v.isLt; omega
  | mul2 o a b =>
    refine WP.mono ((EdArith.ok (fld := fld)).mul2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | sqr2 o a =>
    refine WP.mono ((EdArith.ok (fld := fld)).sqr2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩

theorem fieldOpB_ok {s : State} {base : Addr} (hs : Scr s base) (lazy : Bool) (op : FieldOp)
    {B : Slot → Bool} (hok : opOk lazy op B = true) (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (op.codeB fld lazy)) s fun t => Keep base s t ∧
      env t.mem base = evalOp op (env s.mem base) ∧ ∀ i, bndStep op B i = true → Bnd t.mem base i :=
  WP.mono (fieldOpB_op hs lazy op hok hB) fun _ ⟨h, e, b⟩ => ⟨op_keep h, e, b⟩

theorem opOk_self (op : FieldOp) (B : Slot → Bool) : opOk (opOk true op B) op B = true := by
  cases h : opOk true op B
  · cases op <;> rfl
  · exact h

theorem fieldCodeFrom_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base)
    {B : Slot → Bool} (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (fieldCodeFrom fld B ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ i, bndOut ops B i = true → Bnd t.mem base i := by
  induction ops generalizing s B with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, hB⟩
  | cons op ops ih =>
    rw [fieldCodeFrom, WP.block_append_iff]
    refine WP.mono (fieldOpB_ok hs _ op (opOk_self op B) hB) fun t ⟨ht, et, bt⟩ => ?_
    refine WP.mono (ih (ht.scr hs) bt) fun u ⟨hu, eu, bu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl, bu⟩

theorem fieldCode_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) :=
  WP.mono (fieldCodeFrom_ok ops hs (B := fun _ => false) nofun) fun _ ⟨k, e, _⟩ => ⟨k, e⟩

/-- The bytes at `x` are in no result of `ops`. -/
def Outs (ops : List FieldOp) (base x : Addr) : Prop :=
  ∀ op ∈ ops, ofs base x < offset op.out ∨ offset op.out + 32 ≤ ofs base x

/-- `fieldCodeFrom_ok`, with the program's frame: memory changes only at the results of its
operations. -/
theorem fieldCodeFrom_frame (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base)
    {B : Slot → Bool} (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (fieldCodeFrom fld B ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Outs ops base x → t.mem x = s.mem x := by
  induction ops generalizing s B with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ => rfl⟩
  | cons op ops ih =>
    rw [fieldCodeFrom, WP.block_append_iff]
    refine WP.mono (fieldOpB_op hs _ op (opOk_self op B) hB) fun t ⟨ht, et, bt⟩ => ?_
    refine WP.mono (ih ((op_keep ht).scr hs) bt) fun u ⟨hu, eu, fu⟩ => ?_
    refine ⟨(op_keep ht).trans hu, by rw [eu, et]; rfl, fun x hx => ?_⟩
    rw [fu x fun o ho => hx o (List.mem_cons_of_mem _ ho)]
    exact ht.mem x (hx op List.mem_cons_self)

theorem fieldCode_frame (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Outs ops base x → t.mem x = s.mem x :=
  fieldCodeFrom_frame ops hs (B := fun _ => false) nofun

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

end VG.Proof.Ed25519.X86_64
