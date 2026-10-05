import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86_64.Bits
import VerifiedGarbage.Impl.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Impl.Ed25519.X86_64.PointTable
import VerifiedGarbage.Impl.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Impl.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Impl.Ed25519.X86_64.Field
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Cached
import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulate
import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect
import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86_64.PointBatch
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
import VerifiedGarbage.Impl.Ed25519.X86_64.RecoverSign
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Impl.Ed25519.X86_64.RootPower
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory`. -/
section

/-! Field constants and copies, with the surrounding memory preserved. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (loads store4)
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F Keeps val4 fe ea_sc readSrc_sc store4_ok fe_st4 st4_outside)

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = v.val ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [constWords, runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed25519.X86_64.limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega),
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem constField_op {s : State} {base : Addr} (hs : Scr s base) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v := by
  rw [constField, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (o := offset o)
    (by simp only [offset]; omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  have op : Op base (offset o) s u :=
    ⟨fun r hr => (hg r).trans ((hk.mono (by decide)).1 r hr), hrd.trans hk.2.2.1,
      hwr.trans hk.2.2.2, by rw [hm, hk.2.1]; exact st4_outside _ _ (by simp only [offset]; omega) _ _ _ _⟩
  refine ⟨op, ?_⟩
  rw [F, hm, fe_st4 _ _ (by simp only [offset]; omega), hv, Proof.X25519.toFe_self]

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (loads (offset a) .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (offset a) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have hr (d : Nat) (hd : d + 8 ≤ 4096) : InRegions (s.rd ++ s.wr) (Proof.X25519.X86_64.off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Proof.X25519.X86_64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr (offset a) (by simp only [offset]; omega),
    hr (offset a + 8) (by simp only [offset]; omega),
    hr (offset a + 16) (by simp only [offset]; omega),
    hr (offset a + 24) (by simp only [offset]; omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) := by
  rw [copyField, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (o := offset o)
    (by simp only [offset]; omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  have op : Op base (offset o) s u :=
    ⟨fun r hr => (hg r).trans ((hk.mono (by decide)).1 r hr), hrd.trans hk.2.2.1,
      hwr.trans hk.2.2.2, by rw [hm, hk.2.1]; exact st4_outside _ _ (by simp only [offset]; omega) _ _ _ _⟩
  refine ⟨op, ?_⟩
  rw [F, hm, fe_st4 _ _ (by simp only [offset]; omega), hv]

theorem Outside_F {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 32 < 2 ^ 64)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : F m' base d = F m base d := by
  unfold F
  rw [h.fe hsep hd]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.Field`. -/
section

/-!
# Ed25519 field programs: correctness of the lowering

Each arithmetic operation uses X25519's existing proof. An induction composes
these into a proof for any list of field operations.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F)

/-- The field multiplications the code may be emitted with: the baseline's, or BMI2 and
ADX's. The proofs hold for any multiplications that are correct (`ok`); the constant-time
proofs evaluate the code, so they consider each of these (`known`). -/
class EdArith (fld : Arith) : Prop where
  ok : Proof.X25519.X86_64.FieldOk fld
  known : fld = Impl.X25519.X86_64.baseline ∨ fld = Impl.X25519.X86_64.adx

instance : VG.Proof.Ed25519.X86_64.EdArith Impl.X25519.X86_64.baseline := ⟨Proof.X25519.X86_64.baseline_ok, .inl rfl⟩
instance : VG.Proof.Ed25519.X86_64.EdArith Impl.X25519.X86_64.adx := ⟨Proof.X25519.X86_64.adx_ok, .inr rfl⟩

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : Addr) : VG.Proof.Ed25519.X86_64.Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .sqr o a => Function.update e o (e a * e a)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : VG.Proof.Ed25519.X86_64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86_64.evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [VG.Proof.Ed25519.X86_64.evalOp, Function.update_apply]

theorem evalOp_add_apply (e : VG.Proof.Ed25519.X86_64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86_64.evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [VG.Proof.Ed25519.X86_64.evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : VG.Proof.Ed25519.X86_64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.X86_64.evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [VG.Proof.Ed25519.X86_64.evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.Env := ops.foldl (fun e op => VG.Proof.Ed25519.X86_64.evalOp op e) e

structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 64 704 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.Ed25519.X86_64.Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed25519.X86_64.Keep base s t) (k : VG.Proof.Ed25519.X86_64.Keep base t u) :
    VG.Proof.Ed25519.X86_64.Keep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.Keep base s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem env_update {base : Addr} {m m' : Mem} (o : Slot)
    (h : Outside base (offset o) 32 m m') :
    VG.Proof.Ed25519.X86_64.env m' base = Function.update (VG.Proof.Ed25519.X86_64.env m base) o (F m' base (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [VG.Proof.Ed25519.X86_64.env]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.Ed25519.X86_64.env, F]
    have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem op_keep {base : Addr} {o : Slot} {s t : State} (h : Op base (offset o) s t) :
    VG.Proof.Ed25519.X86_64.Keep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by simp only [offset]; omega)
    (by simp only [offset]; omega)⟩

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base) (op : FieldOp) :
    WP isa (.block (op.code fld)) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.evalOp op (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  cases op with
  | copy o a =>
    refine WP.mono (VG.Proof.Ed25519.X86_64.copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩
  | const o v =>
    refine WP.mono (VG.Proof.Ed25519.X86_64.constField_op hs o v) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩
  | mul o a b =>
    refine WP.mono ((EdArith.ok (fld := fld)).mul hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩
  | sqr o a =>
    refine WP.mono ((EdArith.ok (fld := fld)).sqr hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩
  | add o a b =>
    refine WP.mono (Proof.X25519.X86_64.add_ok hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩
  | sub o a b =>
    refine WP.mono (Proof.X25519.X86_64.sub_ok hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep h, by rw [VG.Proof.Ed25519.X86_64.env_update o h.mem, e]; rfl⟩

theorem fieldCode_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.evalOps ops (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86_64.fieldOp_ok hs op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.scr hs)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : VG.Proof.Ed25519.X86_64.Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : VG.Proof.Ed25519.X86_64.Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointAddOps e) 0 1 2 3 = VG.Proof.Ed25519.X86_64.addResult e 4 (by decide) := by
  rfl

theorem pointDouble_formula (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointDoubleOps e) 0 1 2 3 = VG.Proof.Ed25519.X86_64.addResult e 0 (by decide) := by
  rfl

theorem addResult_eq (e : VG.Proof.Ed25519.X86_64.Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86_64.addResult e q hq = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point e 0 1 2 3)
      (VG.Proof.Ed25519.X86_64.point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [VG.Proof.Ed25519.X86_64.addResult, VG.Proof.Ed25519.X86_64.point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : VG.Proof.Ed25519.X86_64.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point e 0 1 2 3) (VG.Proof.Ed25519.X86_64.point e 4 5 6 7) :=
  (VG.Proof.Ed25519.X86_64.pointAdd_formula e).trans (VG.Proof.Ed25519.X86_64.addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : VG.Proof.Ed25519.X86_64.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point e 0 1 2 3) (VG.Proof.Ed25519.X86_64.point e 0 1 2 3) :=
  (VG.Proof.Ed25519.X86_64.pointDouble_formula e).trans (VG.Proof.Ed25519.X86_64.addResult_eq e 0 (by decide) hd)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide`. -/
section

/-! Run the field workspace inside Ed25519's eight-KiB scratch argument. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Keeps clob Outside)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

structure Scratch (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

theorem Scratch.of_keep {s t : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (hk : VG.Proof.Ed25519.X86_64.Keep base s t) :
    VG.Proof.Ed25519.X86_64.Scratch t base := ⟨(hk.gpr _ (by decide)).trans hs.rdi, hk.wr ▸ hs.wr, hs.nowrap⟩

theorem Scratch.of_keeps {s t : State} {base : Addr} {rs : List Reg} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (hk : Keeps rs s t) (hr : .rdi ∉ rs) : VG.Proof.Ed25519.X86_64.Scratch t base :=
  ⟨(hk.1 _ hr).trans hs.rdi, hk.2.2.2 ▸ hs.wr, hs.nowrap⟩

theorem field_lift {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (code : List Instr)
    (f : VG.Proof.Ed25519.X86_64.Env → VG.Proof.Ed25519.X86_64.Env)
    (correct : ∀ t, Scr t base → WP isa (.block code) t fun u =>
      VG.Proof.Ed25519.X86_64.Keep base t u ∧ VG.Proof.Ed25519.X86_64.env u.mem base = f (VG.Proof.Ed25519.X86_64.env t.mem base)) :
    WP isa (.block code) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = f (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv⟩ := correct narrow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem fieldCodeWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (ops : List FieldOp) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.evalOps ops (VG.Proof.Ed25519.X86_64.env s.mem base) :=
  VG.Proof.Ed25519.X86_64.field_lift hs (fieldCode fld ops) (VG.Proof.Ed25519.X86_64.evalOps ops) (fun _ h => VG.Proof.Ed25519.X86_64.fieldCode_ok ops h)

theorem constFieldWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = Function.update (VG.Proof.Ed25519.X86_64.env s.mem base) o v :=
  VG.Proof.Ed25519.X86_64.field_lift hs (constField o v) (fun e => Function.update e o v) (fun _ h => by
    refine WP.mono (VG.Proof.Ed25519.X86_64.constField_op h o v) fun t ⟨hk, hv⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep hk, by rw [VG.Proof.Ed25519.X86_64.env_update o hk.mem, hv]⟩)

theorem copyFieldWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.env t.mem base = Function.update (VG.Proof.Ed25519.X86_64.env s.mem base) o (VG.Proof.Ed25519.X86_64.env s.mem base a) :=
  VG.Proof.Ed25519.X86_64.field_lift hs (copyField o a) (fun e => Function.update e o (e a)) (fun _ h => by
    refine WP.mono (VG.Proof.Ed25519.X86_64.copyField_op h o a) fun t ⟨hk, hv⟩ => ?_
    exact ⟨VG.Proof.Ed25519.X86_64.op_keep hk, by rw [VG.Proof.Ed25519.X86_64.env_update o hk.mem, hv]; rfl⟩)

structure RbxKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem RbxKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.RbxKeep base s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    VG.Proof.Ed25519.X86_64.Scratch t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem RbxKeep.trans {base : Addr} {s t u : State}
    (h : VG.Proof.Ed25519.X86_64.RbxKeep base s t) (k : VG.Proof.Ed25519.X86_64.RbxKeep base t u) : VG.Proof.Ed25519.X86_64.RbxKeep base s u :=
  ⟨fun r hr hb => (k.gpr r hr hb).trans (h.gpr r hr hb), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem RbxKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .rbx ∨ r ∈ Proof.X25519.X86_64.clob) : VG.Proof.Ed25519.X86_64.RbxKeep base s t := by
  refine ⟨fun r hr hb => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h
    · exact hb h
    · exact hr h
  · rw [h.2.1]; exact Proof.X25519.X86_64.Outside.refl _ _ _ _

theorem Keep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob) : VG.Proof.Ed25519.X86_64.Keep base s t :=
  ⟨fun r hr => h.1 r (fun hm => hr (hrs r hm)), h.2.2.1, h.2.2.2,
    by rw [h.2.1]; exact Proof.X25519.X86_64.Outside.refl _ _ _ _⟩

theorem RbxKeep.of_keep {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.Keep base s t) : VG.Proof.Ed25519.X86_64.RbxKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.mem⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.Points`. -/
section

/-! Exact extended-coordinate operations and the slots they preserve. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

theorem evalOp_unchanged (op : FieldOp) (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot) (hi : i ≠ VG.Proof.Ed25519.X86_64.fieldDest op) :
    VG.Proof.Ed25519.X86_64.evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ VG.Proof.Ed25519.X86_64.fieldDest op) : VG.Proof.Ed25519.X86_64.evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change VG.Proof.Ed25519.X86_64.evalOps ops (VG.Proof.Ed25519.X86_64.evalOp op e) i = e i
    rw [ih (VG.Proof.Ed25519.X86_64.evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), VG.Proof.Ed25519.X86_64.evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (VG.Proof.Ed25519.X86_64.fieldDest op).val < 16)
    (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot) (hi : 16 ≤ i.val) : VG.Proof.Ed25519.X86_64.evalOps ops e i = e i := by
  apply VG.Proof.Ed25519.X86_64.evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem pointAdd_high (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.X86_64.evalOps pointAddOps e i = e i :=
  VG.Proof.Ed25519.X86_64.point_ops_high _ (by decide) e i hi

theorem pointDouble_high (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.X86_64.evalOps pointDoubleOps e i = e i :=
  VG.Proof.Ed25519.X86_64.point_ops_high _ (by decide) e i hi

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

theorem savePoint_eval (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps savePointOps e) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point e 0 1 2 3 := rfl

theorem restorePoint_eval (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps restorePointOps e) 0 1 2 3 = VG.Proof.Ed25519.X86_64.point e 17 18 19 20 := rfl

theorem copyPointToQ_eval (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps copyPointToQOps e) 4 5 6 7 = VG.Proof.Ed25519.X86_64.point e 0 1 2 3 := rfl

theorem pointDoubleWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (pointDouble fld)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs pointDoubleOps) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, VG.Proof.Ed25519.X86_64.pointDouble_eval _ hd, VG.Proof.Ed25519.X86_64.pointDouble_high _⟩

theorem pointAddWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (pointAdd fld)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs pointAddOps) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, VG.Proof.Ed25519.X86_64.pointAdd_eval _ hd, VG.Proof.Ed25519.X86_64.pointAdd_high _⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop`. -/
section

/-! Sixteen exact doublings, preserving the saved accumulator. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob Outside Keeps)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rsi → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.refl (base : Addr) (s : State) : VG.Proof.Ed25519.X86_64.DoubleKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed25519.X86_64.DoubleKeep base s t)
    (k : VG.Proof.Ed25519.X86_64.DoubleKeep base t u) : VG.Proof.Ed25519.X86_64.DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.DoubleKeep base s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    VG.Proof.Ed25519.X86_64.Scratch t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_zero : ∀ n < 16,
    (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem doubleDec_ok (s : State) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rsi (.imm 1)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧ Keeps [.rsi] s t := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    hc, VG.Proof.Ed25519.X86_64.point_counter_zero n hn, e, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem doubleBody_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (doubleBody fld)) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i) ∧ VG.Proof.Ed25519.X86_64.DoubleKeep base s t := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointDoubleWide_ok hs hd) fun t ⟨hk, hv, hi⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.doubleDec_ok t n hn ((hk.gpr _ (by decide)).trans hc)) fun u ⟨hcu, hzu, ku⟩ => ?_
  refine ⟨hcu, hzu, ?_, ?_, ?_⟩
  · rw [ku.2.1]; exact hv
  · rw [ku.2.1]; exact hi
  · exact ⟨fun r hr hc => (ku.1 r (by simpa using hr)).trans (hk.gpr r hc),
      ku.2.2.1.trans hk.rd, ku.2.2.2.trans hk.wr, by rw [ku.2.1]; exact hk.mem⟩

structure DoubleInv (s₀ : State) (base : Addr) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : VG.Proof.Ed25519.X86_64.Scratch s base
  counter : s.gpr .rsi = BitVec.ofNat 64 n
  value : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 =
    powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env s.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i
  keep : VG.Proof.Ed25519.X86_64.DoubleKeep base s₀ s

theorem doubleLoop_ok {s₀ : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s₀ base)
    (hc : s₀.gpr .rsi = 16) (hd : VG.Proof.Ed25519.X86_64.env s₀.mem base 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block (doubleBody fld)) .ne) s₀ fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i) ∧ VG.Proof.Ed25519.X86_64.DoubleKeep base s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.X86_64.DoubleInv s₀ base) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86_64.doubleBody_ok hi.scratch k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htv, hthi, htk⟩ => ?_
    have hv : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, htz, decide_true, Option.map_some, Bool.not_true], hv, hh, hkeep⟩
    · exact Or.inr ⟨by simp only [eval, htz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hs, hc, rfl, fun _ _ => rfl, DoubleKeep.refl _ _⟩

theorem doubleInit_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.imm 16)]) s fun t => t.gpr .rsi = 16 ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem double16_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (double16 fld) s fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i) ∧ VG.Proof.Ed25519.X86_64.DoubleKeep base s t := by
  rw [double16]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.doubleInit_ok s) fun t ⟨hc, hk⟩ => ?_)
  have hs' : VG.Proof.Ed25519.X86_64.Scratch t base := ⟨(hk.1 _ (by decide)).trans hs.rdi, hk.2.2.2 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.Ed25519.X86_64.doubleLoop_ok hs' hc (by rw [hk.2.1]; exact hd)) fun u ⟨hv, hh, hu⟩ => ?_
  have hkeep : VG.Proof.Ed25519.X86_64.DoubleKeep base s t := ⟨fun r hr _ => hk.1 r (by simpa using hr),
    hk.2.2.1, hk.2.2.2, by rw [hk.2.1]; exact Outside.refl _ _ _ _⟩
  rw [hk.2.1] at hv hh
  exact ⟨hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PointTable`. -/
section
/-! Point table accesses remain within the caller's scratch argument. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off fe val4 st4 ea_at ea_sc Keeps Outside F fe_st4 st4_outside)
open VG.Impl.X25519.X86_64 (loads)

theorem tableWords_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (dst : Nat) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (tableWords dst)) s fun t =>
      t.mem = st4 s.mem base (o + dst) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [tableWords, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hp,
    Offset.add_add, State.store64, w (o + dst) (by omega), w (o + (dst + 8)) (by omega),
    w (o + (dst + 16)) (by omega), w (o + (dst + 24)) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial⟩
  simp only [st4, Nat.add_assoc]

theorem fromTableWords_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (src : Nat) (ho : o + src + 32 ≤ 8192) :
    WP isa (.block (fromTableWords src)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (o + src) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have r : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [fromTableWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hp, Offset.add_add, r (o + src) (by omega), r (o + (src + 8)) (by omega),
    r (o + (src + 16)) (by omega), r (o + (src + 24)) (by omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [fe, Proof.X25519.X86_64.word, Nat.add_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem loadsFieldWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (a : Slot) :
    WP isa (.block (loads (offset a) .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (offset a) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have hr (d : Nat) (hd : d + 8 ≤ 8192) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr (offset a) (by simp only [offset]; omega),
    hr (offset a + 8) (by simp only [offset]; omega),
    hr (offset a + 16) (by simp only [offset]; omega),
    hr (offset a + 24) (by simp only [offset]; omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

structure TableKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base o n s.mem t.mem

theorem TableKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.X86_64.TableKeep base o n s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) : VG.Proof.Ed25519.X86_64.Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem TableKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.X86_64.TableKeep base o n s t) (k : VG.Proof.Ed25519.X86_64.TableKeep base o n t u) : VG.Proof.Ed25519.X86_64.TableKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem TableKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : VG.Proof.Ed25519.X86_64.TableKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.X86_64.TableKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono ho hn⟩

theorem table_env {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (ho : 768 ≤ o) : VG.Proof.Ed25519.X86_64.env m' base = VG.Proof.Ed25519.X86_64.env m base := by
  funext i
  simp only [VG.Proof.Ed25519.X86_64.env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem toTableQuarter_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (loads (64 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      F t.mem base (o + 32 * j) = VG.Proof.Ed25519.X86_64.env s.mem base ⟨j, by omega⟩ ∧ VG.Proof.Ed25519.X86_64.TableKeep base (o + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.loadsFieldWide_ok hs ⟨j, by omega⟩) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableWords_ok (hs.of_keeps hk (by decide))
    ((hk.1 _ (by decide)).trans hp) (32 * j) (by omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv]
    rfl
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem toTablePrefix_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      loads (64 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      (∀ j (hj : j < n), F t.mem base (o + 32 * j) = VG.Proof.Ed25519.X86_64.env s.mem base ⟨j, by omega⟩) ∧
      VG.Proof.Ed25519.X86_64.TableKeep base o (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.X86_64.toTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · rw [VG.Proof.Ed25519.X86_64.Outside_F ku.mem (by omega) (Or.inl (by omega)), hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, VG.Proof.Ed25519.X86_64.table_env hk.mem hlo]

def tablePoint (m : Mem) (base : Addr) (o : Nat) : Spec.Ed25519.Point :=
  ⟨F m base o, F m base (o + 32), F m base (o + 64), F m base (o + 96)⟩

theorem pointToTable_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      VG.Proof.Ed25519.X86_64.tablePoint t.mem base o = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧ VG.Proof.Ed25519.X86_64.TableKeep base o 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.toTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  simp only [VG.Proof.Ed25519.X86_64.tablePoint, VG.Proof.Ed25519.X86_64.point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.PointTableLoad`. -/
section
/-! Copying point tables back into the arithmetic workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F fe_st4 st4_outside Outside)
open VG.Impl.X25519.X86_64 (stores)

theorem fromTableQuarter_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (64 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      VG.Proof.Ed25519.X86_64.env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      VG.Proof.Ed25519.X86_64.TableKeep base (64 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fromTableWords_ok hs hp (32 * j) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega : 64 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * j) = _
    rw [F, hm, fe_st4 _ _ (by omega), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefix_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (64 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), VG.Proof.Ed25519.X86_64.env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      VG.Proof.Ed25519.X86_64.TableKeep base 64 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.X86_64.fromTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : VG.Proof.Ed25519.X86_64.env u.mem base ⟨j, by omega⟩ = VG.Proof.Ed25519.X86_64.env t.mem base ⟨j, by omega⟩ :=
        VG.Proof.Ed25519.X86_64.Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, VG.Proof.Ed25519.X86_64.Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTable_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.X86_64.tablePoint s.mem base o ∧ VG.Proof.Ed25519.X86_64.TableKeep base 64 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.fromTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change VG.Proof.Ed25519.X86_64.env t.mem base 0 = _ at h0
  change VG.Proof.Ed25519.X86_64.env t.mem base 1 = _ at h1
  change VG.Proof.Ed25519.X86_64.env t.mem base 2 = _ at h2
  change VG.Proof.Ed25519.X86_64.env t.mem base 3 = _ at h3
  simp only [VG.Proof.Ed25519.X86_64.tablePoint, VG.Proof.Ed25519.X86_64.point, h0, h1, h2, h3]

end VG.Proof.Ed25519.X86_64
end

/-! Public point-table address arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps)

theorem tableAddr_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (o j : Nat) (hj : j < 64) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (tableAddr o)) s fun t =>
      t.gpr .rax = off base (o + 128 * j) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have hval : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [tableAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hc, hp, hval,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change BitVec.ofNat 64 (j * 128) + base + BitVec.ofNat 64 o = _
    rw [BitVec.add_comm (BitVec.ofNat 64 (j * 128)), BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun n => off base n) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers`. -/
section

/-! Constructing bounded tables of exact point doublings. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

/-- Only the field workspace and the specified table can change. -/
def TableFrame (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < 64 ∨ 768 ≤ ofs base p) →
    (ofs base p < o ∨ o + n ≤ ofs base p) → m' p = m p

theorem TableFrame.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.Ed25519.X86_64.TableFrame base o n m m :=
  fun _ _ _ => rfl

theorem TableFrame.trans {base : Addr} {o n : Nat} {m m' m'' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') (k : VG.Proof.Ed25519.X86_64.TableFrame base o n m' m'') : VG.Proof.Ed25519.X86_64.TableFrame base o n m m'' :=
  fun p hp hq => (k p hp hq).trans (h p hp hq)

theorem TableFrame.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    VG.Proof.Ed25519.X86_64.TableFrame base o' n' m m' := fun p hp hq => h p hp (by omega)

theorem TableFrame.workspace {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base 64 704 m m') : VG.Proof.Ed25519.X86_64.TableFrame base o n m m' := fun p hp _ => h p hp

theorem TableFrame.table {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') : VG.Proof.Ed25519.X86_64.TableFrame base o n m m' := fun p _ hp => h p hp

theorem TableFrame.word {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 8 ≤ o ∨ o + n ≤ d) (hb : d + 8 < 2 ^ 64) :
    Proof.X25519.X86_64.word m' base d = Proof.X25519.X86_64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [Proof.X25519.X86_64.ofs_off base (by omega)]; omega)
    (by rw [Proof.X25519.X86_64.ofs_off base (by omega)]; omega)).symm).symm

theorem TableFrame.field {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) (hb : d + 32 < 2 ^ 64) :
    Proof.X25519.X86_64.F m' base d = Proof.X25519.X86_64.F m base d := by
  simp only [Proof.X25519.X86_64.F, Proof.X25519.X86_64.fe]
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

theorem TableFrame.point {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 < 2 ^ 64) :
    VG.Proof.Ed25519.X86_64.tablePoint m' base d = VG.Proof.Ed25519.X86_64.tablePoint m base d := by
  simp only [VG.Proof.Ed25519.X86_64.tablePoint]
  rw [h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega),
    h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega)]

theorem workspace_tablePoint {base : Addr} {m m' : Mem}
    (h : Outside base 64 704 m m') {d : Nat} (hd : 768 ≤ d) (hb : d + 128 < 2 ^ 64) :
    VG.Proof.Ed25519.X86_64.tablePoint m' base d = VG.Proof.Ed25519.X86_64.tablePoint m base d := by
  simp only [VG.Proof.Ed25519.X86_64.tablePoint]
  rw [VG.Proof.Ed25519.X86_64.Outside_F h (by omega) (Or.inr (by omega)), VG.Proof.Ed25519.X86_64.Outside_F h (by omega) (Or.inr (by omega)),
    VG.Proof.Ed25519.X86_64.Outside_F h (by omega) (Or.inr (by omega)), VG.Proof.Ed25519.X86_64.Outside_F h (by omega) (Or.inr (by omega))]

structure PowersKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : VG.Proof.Ed25519.X86_64.TableFrame base o n s.mem t.mem

theorem PowersKeep.refl (base : Addr) (o n : Nat) (s : State) : VG.Proof.Ed25519.X86_64.PowersKeep base o n s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, TableFrame.refl _ _ _ _⟩

theorem PowersKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.X86_64.PowersKeep base o n s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) : VG.Proof.Ed25519.X86_64.Scratch t base :=
  ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem PowersKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : VG.Proof.Ed25519.X86_64.PowersKeep base o n s t) (k : VG.Proof.Ed25519.X86_64.PowersKeep base o n t u) : VG.Proof.Ed25519.X86_64.PowersKeep base o n s u :=
  ⟨fun r hb hs hc => (k.gpr r hb hs hc).trans (h.gpr r hb hs hc), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem PowersKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : VG.Proof.Ed25519.X86_64.PowersKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    VG.Proof.Ed25519.X86_64.PowersKeep base o' n' s t := ⟨h.gpr, h.rd, h.wr, h.mem.mono ho hn⟩

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (j + 1) ∧ t.zf = some (decide (j + 1 = count)) ∧
      Keeps [.rax, .rbx] s t := by
  have ha : BitVec.ofNat 64 j + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (j + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 count == 0) = decide (j + 1 = count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hn]
  apply WP.of_runBlock
  simp only [powersNext, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem powerBatch_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch fld batch) s fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i) ∧ VG.Proof.Ed25519.X86_64.DoubleKeep base s t := by
  cases batch with
  | true => exact VG.Proof.Ed25519.X86_64.double16_ok hs hd
  | false =>
    refine WP.mono (VG.Proof.Ed25519.X86_64.pointDoubleWide_ok hs hd) fun t ⟨hk, hv, hh⟩ => ?_
    exact ⟨hv, hh, ⟨fun r _ hr => hk.gpr r hr, hk.rd, hk.wr, hk.mem⟩⟩

theorem powersBody_ok (batch : Bool) {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (o j count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (powersBody fld o count batch) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (j + 1) ∧ t.zf = some (decide (j + 1 = count)) ∧
      VG.Proof.Ed25519.X86_64.tablePoint t.mem base (o + 128 * j) = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i) ∧
      VG.Proof.Ed25519.X86_64.PowersKeep base (o + 128 * j) 128 s t := by
  rw [powersBody]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableAddr_ok hs.rdi o j (by omega) hc) fun t ⟨htp, htk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointToTable_ok (hs.of_keeps htk (by decide)) htp (by omega) (by omega))
    fun u ⟨hut, huk⟩ => ?_
  have heu : VG.Proof.Ed25519.X86_64.env u.mem base = VG.Proof.Ed25519.X86_64.env s.mem base := (VG.Proof.Ed25519.X86_64.table_env huk.mem (by omega)).trans
    (congrArg (fun m => VG.Proof.Ed25519.X86_64.env m base) htk.2.1)
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.X86_64.powerBatch_ok (huk.scratch (hs.of_keeps htk (by decide)))
    (by rw [heu]; exact hd) batch) fun v ⟨hvp, hvhi, hvk⟩ => ?_
  have hvc : v.gpr .rbx = BitVec.ofNat 64 j := (hvk.gpr _ (by decide) (by decide)).trans
    ((huk.gpr _ (by decide)).trans ((htk.1 _ (by decide)).trans hc))
  refine WP.mono (VG.Proof.Ed25519.X86_64.powersNext_ok v j count hj (by omega) hvc) fun w ⟨hwc, hwz, hwk⟩ => ?_
  refine ⟨hwc, hwz, ?_, ?_, ?_, ?_⟩
  · rw [hwk.2.1, VG.Proof.Ed25519.X86_64.workspace_tablePoint hvk.mem (by omega) (by omega), hut, htk.2.1]
  · rw [hwk.2.1, hvp, heu]
  · intro i hi
    rw [hwk.2.1, hvhi i hi, heu]
  · refine ⟨fun r hb hr hc => ?_, hwk.2.2.1.trans (hvk.rd.trans (huk.rd.trans htk.2.2.1)),
      hwk.2.2.2.trans (hvk.wr.trans (huk.wr.trans htk.2.2.2)), ?_⟩
    · have ha : r ≠ .rax := by simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc; exact hc.1
      have ht : r ∉ [Reg.rax, .rcx, .rdx] := by
        simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc ⊢
        exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
      have hu : r ∉ [Reg.r8, .r9, .r10, .r11] := by
        simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc ⊢
        exact ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1⟩
      exact (hwk.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ha, hb⟩)).trans
        ((hvk.gpr r hr hc).trans ((huk.gpr r hu).trans (htk.1 r ht)))
    · rw [hwk.2.1, ← htk.2.1]
      exact (TableFrame.table huk.mem).trans (TableFrame.workspace hvk.mem)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop`. -/
section

/-! Termination and table contents for the checkpoint loop. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

structure PowersInv (s₀ : State) (base : Addr) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : VG.Proof.Ed25519.X86_64.Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 (count - n)
  value : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, VG.Proof.Ed25519.X86_64.tablePoint s.mem base (o + 128 * j) =
    powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env s.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i
  keep : VG.Proof.Ed25519.X86_64.PowersKeep base o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s₀ base)
    (o count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hc : s₀.gpr .rbx = 0)
    (hd : VG.Proof.Ed25519.X86_64.env s₀.mem base 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody fld o count batch) .ne) s₀ fun t =>
      (∀ j < count, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * j)) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i) ∧
      VG.Proof.Ed25519.X86_64.PowersKeep base o (128 * count) s₀ t := by
  apply WP.loop (fun n => VG.Proof.Ed25519.X86_64.PowersInv s₀ base o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86_64.powersBody_ok batch hi.scratch o (count - (k + 1)) count hlo hbound (by omega) hn
      hi.counter ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htt, htv, hthi, htk⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have hv : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [htv, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by cases batch <;> simp only [powerStride, Bool.false_eq_true, ite_true, ite_false] <;> omega)
    have ht : ∀ j < count - k, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases h : j < count - (k + 1)
      · rw [htk.mem.point (by omega) (Or.inl (by omega)) (by omega), hi.table j h]
      · have he : j = count - (k + 1) := by omega
        rw [he, htt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s₀.mem base i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans (htk.mono (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, htz, show count - (0 + 1) + 1 = count by omega,
        decide_true, Option.map_some, Bool.not_true], ht, hv, hh, hkeep⟩
    · exact Or.inr ⟨by simp only [eval, htz,
        decide_eq_false (show count - (k + 1) + 1 ≠ count by omega), Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, hstep ▸ htc, hv, ht, hh, hkeep⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hs, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact hc
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem powersInit_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 0)]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem pointPowers_ok (batch : Bool) {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (o count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (pointPowers fld o count batch) s fun t =>
      (∀ j < count, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (o + 128 * j) =
        powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (powerStride batch * j)) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i) ∧
      VG.Proof.Ed25519.X86_64.PowersKeep base o (128 * count) s t := by
  rw [pointPowers]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.powersInit_ok s) fun t ⟨hc, hk⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86_64.powersLoop_ok batch (hs.of_keeps hk (by decide)) o count hlo hbound hn0 hn hc
    (by rw [hk.2.1]; exact hd)) fun u ⟨ht, hv, hh, hu⟩ => ?_
  have hkeep : VG.Proof.Ed25519.X86_64.PowersKeep base o (128 * count) s t := ⟨fun r hr _ _ => hk.1 r (by simpa using hr),
    hk.2.2.1, hk.2.2.2, by rw [hk.2.1]; exact TableFrame.refl _ _ _ _⟩
  rw [hk.2.1] at ht hv hh
  exact ⟨ht, hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.Bits`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.BitByte`. -/
section
/-! Expanding each input byte uses the existing verified bit stores. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr off ofs Outside)

theorem scalarBitWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (i j : Nat) (hi : i < 64) (hj : j < 8) (hc : s.gpr .rbx = BitVec.ofNat 64 i)
    (b : BitVec 8) (hb : s.gpr .rax = b.setWidth 64) :
    WP isa (.block (expandScalarBit j)) s fun t =>
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = s.mem.writeW (off base (768 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hg, hr, hw, hm⟩ := Proof.X25519.X86_64.bitJ_ok hn hi hc hb hj
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hg, rfl, rfl, hm⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  change Exec isa (.block (expandScalarBit j)) _ _ _ at e
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

structure BitKeep (base : Addr) (i n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rdx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base (768 + 8 * i) n s.mem t.mem

theorem BitKeep.scratch {base : Addr} {i n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.BitKeep base i n s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) : VG.Proof.Ed25519.X86_64.Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scalarBitPrefix_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (i n : Nat) (hi : i < 64) (hn : n ≤ 8) (hc : s.gpr .rbx = BitVec.ofNat 64 i)
    (b : BitVec 8) (hb : s.gpr .rax = b.setWidth 64) :
    WP isa (.block ((List.range n).flatMap expandScalarBit)) s fun t => VG.Proof.Ed25519.X86_64.BitKeep base i n s t ∧
      ∀ j < n, t.mem (off base (768 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩, fun _ h => by omega⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega) hc hb) fun t ⟨hk, hv⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBitWide_ok (hk.scratch hs) i n hi (by omega)
      ((hk.gpr _ (by decide)).trans hc) b ((hk.gpr _ (by decide)).trans hb))
      fun u ⟨ug, ur, uw, um⟩ => ?_
    refine ⟨⟨fun r hr => (ug r hr).trans (hk.gpr r hr), ur.trans hk.rd, uw.trans hk.wr, ?_⟩, ?_⟩
    · intro p hp
      rw [um, Proof.X25519.X86_64.writeW8_outside _ _ _ (by omega) (by omega), hk.mem p (by omega)]
    · intro j hj
      rw [um, Proof.X25519.X86_64.writeW8_apply]
      by_cases h : j = n
      · subst j; rw [ite_eq_left rfl]
      · rw [ite_eq_right (fun he => h (by
          have hh := (Proof.X25519.X86_64.off_eq_iff base (by omega) (by omega)).mp he
          omega))]
        exact hv j (by omega)

end VG.Proof.Ed25519.X86_64
end

/-! Expand all scalar bits, without X25519's clamping. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps Outside ea_scalar)

structure BitsKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base o n s.mem t.mem

theorem BitsKeep.scratch {base : Addr} {o n : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.BitsKeep base o n s t) (hs : VG.Proof.Ed25519.X86_64.Scratch s base) : VG.Proof.Ed25519.X86_64.Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BitsKeep.trans {base : Addr} {o n : Nat} {s t u : State}
    (h : VG.Proof.Ed25519.X86_64.BitsKeep base o n s t) (k : VG.Proof.Ed25519.X86_64.BitsKeep base o n t u) : VG.Proof.Ed25519.X86_64.BitsKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem BitsKeep.mono {base : Addr} {o n o' n' : Nat} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.BitsKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : VG.Proof.Ed25519.X86_64.BitsKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono ho hn⟩

theorem scalarByteBits_ok {s : State} {base k : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (i count : Nat) (hi : i < count) (hn : count ≤ 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 i) (hp : s.gpr .rsi = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block (scalarByteBits count)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t.zf = some (decide (i + 1 = count)) ∧
      VG.Proof.Ed25519.X86_64.BitsKeep base (768 + 8 * i) 8 s t ∧
      ∀ j < 8, t.mem (off base (768 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1) := by
  rw [scalarByteBits, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun t => t.gpr .rax = (s.mem (off k i)).setWidth 64 ∧ Keeps [.rax] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_scalar s hp hc,
      State.load8, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBitPrefix_ok (hs.of_keeps ka (by decide)) i 8 (by omega) (by decide)
    ((ka.1 _ (by decide)).trans hc) _ av) fun b ⟨kb, bv⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.powersNext_ok b i count hi hn
    ((kb.gpr _ (by decide)).trans ((ka.1 _ (by decide)).trans hc))) fun t ⟨tc, tz, kt⟩ => ?_
  refine ⟨tc, tz, ⟨fun r hr => ?_, kt.2.2.1.trans (kb.rd.trans ka.2.2.1),
    kt.2.2.2.trans (kb.wr.trans ka.2.2.2), ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact (kt.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.2⟩)).trans
      ((kb.gpr r hr.2.1).trans (ka.1 r (by simpa using hr.1)))
  · rw [kt.2.1, ← ka.2.1]; exact kb.mem
  · rw [kt.2.1]; exact bv

structure BitsInv (s₀ : State) (base k : Addr) (count i : Nat) (s : State) : Prop where
  scratch : VG.Proof.Ed25519.X86_64.Scratch s base
  ptr : s.gpr .rsi = k
  counter : s.gpr .rbx = BitVec.ofNat 64 i
  keep : VG.Proof.Ed25519.X86_64.BitsKeep base 768 (8 * count) s₀ s
  bits : ∀ t < 8 * i, s.mem (off base (768 + t)) =
    BitVec.ofNat 8 (((s₀.mem (off k (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem scalarBitsLoop_ok {s₀ : State} {base k : Addr} (count : Nat) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s₀.rd ++ s₀.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    ∀ i s, i < count → VG.Proof.Ed25519.X86_64.BitsInv s₀ base k count i s →
      WP isa (.loop (.block (scalarByteBits count)) .ne) s fun t => VG.Proof.Ed25519.X86_64.BitsInv s₀ base k count count t := by
  intro i s hi h
  refine WP.loop (M := isa) (body := .block (scalarByteBits count)) (c := .ne)
    (Q := fun t => VG.Proof.Ed25519.X86_64.BitsInv s₀ base k count count t)
    (fun n s => ∃ i, n = count - i ∧ i < count ∧ VG.Proof.Ed25519.X86_64.BitsInv s₀ base k count i s) ?_
    (count - i) s ⟨i, rfl, hi, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarByteBits_ok h.scratch i count hi hn h.counter h.ptr
    (by rw [h.keep.rd, h.keep.wr]; exact hr i hi)) fun t ⟨tc, tz, tk, tb⟩ => ?_
  have hbyte : s.mem (off k i) = s₀.mem (off k i) := h.keep.mem _ (by have := hd i hi; omega)
  have inv : VG.Proof.Ed25519.X86_64.BitsInv s₀ base k count (i + 1) t := by
    refine ⟨tk.scratch h.scratch, (tk.gpr _ (by decide)).trans h.ptr, tc,
      h.keep.trans (tk.mono (by omega) (by omega)), fun j hj => ?_⟩
    by_cases hp : j < 8 * i
    · rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits j hp]
    · have e := tb (j - 8 * i) (by omega)
      rw [show 8 * i + (j - 8 * i) = j by omega, hbyte] at e
      rw [e, show j / 8 = i by omega, show j % 8 = j - 8 * i by omega]
  by_cases he : i + 1 = count
  · exact Or.inl ⟨by simp only [eval, tz, he, decide_true, Option.map_some, Bool.not_true], he ▸ inv⟩
  · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false he, Option.map_some, Bool.not_false],
      count - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem input_byte (m : Mem) (k : Addr) (count j : Nat) (hj : j < count) :
    (Spec.Ed25519.bytesAt m k count).getD j 0 = m (off k j) := by
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem expandScalarBits_ok {s : State} {base k : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (hp : s.gpr .rsi = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBits count) s fun t => VG.Proof.Ed25519.X86_64.BitsKeep base 768 (8 * count) s t ∧
      ∀ j < 8 * count, t.mem (off base (768 + j)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k count) / 2 ^ j) % 2) := by
  rw [scalarBits]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.powersInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  have init : VG.Proof.Ed25519.X86_64.BitsInv s base k count 0 a := by
    refine ⟨hs.of_keeps ka (by decide), (ka.1 _ (by decide)).trans hp, ac,
      ⟨fun r hr => ka.1 r (fun hm => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))), ka.2.2.1, ka.2.2.2, ?_⟩, fun j hj => by omega⟩
    rw [ka.2.1]; exact Outside.refl _ _ _ _
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBitsLoop_ok count hn hr hd 0 a hn0 init) fun t h => ?_
  refine ⟨h.keep, fun j hj => ?_⟩
  rw [h.bits j hj]
  have hb := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt s.mem k count) j
  rw [← decodeLE_eq, VG.Proof.Ed25519.X86_64.input_byte _ _ _ _ (by omega)] at hb
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb ⊢
  exact congrArg (BitVec.ofNat 8) hb.symm

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport`. -/
section

/-! Retain separate functional postconditions for two secret inputs. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64

set_option hygiene false in
/-- `taint_decide` for the code emitted with `fld`, for each field arithmetic it may be. -/
macro "fld_taint_decide" : tactic =>
  `(tactic| first
    | (rcases (EdArith.known (fld := fld)) with h | h <;> (rw [h]; exact ⟨_, by taint_decide⟩))
    | exact ⟨_, by taint_decide⟩)

set_option hygiene false in
/-- `lit_decide` for the code emitted with `fld`, for each field arithmetic it may be. -/
macro "fld_lit_decide" : tactic =>
  `(tactic| first
    | (rcases (EdArith.known (fld := fld)) with h | h <;> (rw [h]; lit_decide))
    | lit_decide)

/-- `RelCT.taint`, with the hint found by `fld_taint_decide` for each field arithmetic. -/
theorem taintFld {P : State → State → Prop} {c : Prog isa} (τ : VG.X86_64.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.Agree τ s₁ s₂)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T, (VG.X86_64.taint.check τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  let ⟨_, h⟩ := h; VG.RelCT.taint (A := VG.X86_64.taint) τ hp h

/-- `RelCT.taintRegs`, with the hint found by `fld_taint_decide`. -/
theorem taintRegsFld {τ : VG.X86_64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → VG.X86_64.Taint.Agree τ s₁ s₂) (rs : List Reg)
    (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      ((VG.X86_64.taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c fun s₁ s₂ => ∀ r ∈ rs, s₁.gpr r = s₂.gpr r :=
  let ⟨_, h⟩ := h; VG.X86_64.RelCT.taintRegs hp rs h

theorem execBlock_append_seq {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem blockAppend_ct {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => VG.RelCT.seq hx hy _ _ _ _ _ _ hp
    (VG.Proof.Ed25519.X86_64.execBlock_append_seq ex) (VG.Proof.Ed25519.X86_64.execBlock_append_seq ey)

theorem withRuns {P Q F₁ F₂ : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c Q)
    (hw : ∀ x y, P x y → WP isa c x (F₁ x) ∧ WP isa c y (F₂ y)) :
    RelCT isa P c fun x' y' => Q x' y' ∧ ∃ x y, P x y ∧ F₁ x x' ∧ F₂ y y' := by
  intro x y tx ty x' y' hp ex ey
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp ex ey
  obtain ⟨⟨_, u, eu, hu⟩, ⟨_, v, ev, hv⟩⟩ := hw x y hp
  obtain ⟨-, rfl⟩ := Exec.det ex eu
  obtain ⟨-, rfl⟩ := Exec.det ey ev
  exact ⟨ht, hq, x, y, hp, hu, hv⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect`. -/
section

/-! Point selection reuses the verified constant-time field swaps. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr mask F cswap_ok)

def swapEnv (a b : Slot) (sw : Bool) (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.Env :=
  ops.foldl (fun e (a, b) => VG.Proof.Ed25519.X86_64.swapEnv a b sw e) e

theorem swapField_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (VG.Impl.X25519.X86_64.cswap (offset a) (offset b))) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.swapEnv a b sw (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok hs (by simp only [offset]; omega) (by simp only [offset]; omega)
    (by simp only [offset]; omega) hm) fun t ⟨hg, hc, hr, hw, ⟨m, h₁, h₂, f₁⟩, _, f₂⟩ => ?_
  refine ⟨⟨hg, hr, hw, (h₁.mono (by simp only [offset]; omega) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp only [offset]; omega) (by simp only [offset]; omega))⟩, hc, ?_⟩
  rw [VG.Proof.Ed25519.X86_64.env_update b h₂, VG.Proof.Ed25519.X86_64.env_update a h₁]
  simp only [F, f₁, f₂]
  cases sw <;> rfl

theorem swapFieldWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (VG.Impl.X25519.X86_64.cswap (offset a) (offset b))) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.swapEnv a b sw (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hc, hv⟩ := VG.Proof.Ed25519.X86_64.swapField_ok hn a b hab hm
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hc, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem swapFieldsWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (ops : List (Slot × Slot))
    (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (swapFields ops)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ VG.Proof.Ed25519.X86_64.env t.mem base = VG.Proof.Ed25519.X86_64.swapEnvs ops sw (VG.Proof.Ed25519.X86_64.env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, rfl⟩
  | cons ab ops ih =>
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86_64.swapFieldWide_ok hs ab.1 ab.2 (hops ab (by simp)) hm) fun t ⟨hk, hc, hv⟩ => ?_
    refine WP.mono (ih (hs.of_keep hk) (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (hc.trans hm))
      fun u ⟨ku, cu, vu⟩ => ?_
    refine ⟨hk.trans ku, cu.trans hc, ?_⟩
    rw [vu, hv]; rfl

theorem pointSelect_eval (e : VG.Proof.Ed25519.X86_64.Env) (sw : Bool) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then VG.Proof.Ed25519.X86_64.point e 17 18 19 20 else VG.Proof.Ed25519.X86_64.point e 0 1 2 3 := by
  cases sw <;> rfl

theorem pointSelect_d (e : VG.Proof.Ed25519.X86_64.Env) (sw : Bool) : VG.Proof.Ed25519.X86_64.swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {sw : Bool}
    (hm : s.gpr .rcx = mask sw) :
    WP isa (.block pointSelect) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        (if sw then VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 17 18 19 20 else VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = VG.Proof.Ed25519.X86_64.env s.mem base 16 := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.swapFieldsWide_ok hs pointSelectPairs (by decide) hm) fun t ⟨hk, _, hv⟩ => ?_
  exact ⟨hk, by rw [hv, VG.Proof.Ed25519.X86_64.pointSelect_eval], by rw [hv, VG.Proof.Ed25519.X86_64.pointSelect_d]⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PointAccumulate`. -/
section
/-! One masked point addition, with all memory indices public. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off mask Keeps clob)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem scalarBitMask_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitMask) s fun t =>
      t.gpr .rcx = mask (decide (bit = 0)) ∧ Keeps [.rax, .rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) * 1#64 + BitVec.ofInt 64 768 =
      off base (768 + (start + j)) := by
    rw [BitVec.mul_one, ← BitVec.ofNat_add, show BitVec.ofInt 64 768 = BitVec.ofNat 64 768 from rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hm : (BitVec.ofNat 8 bit).setWidth 64 - (1 : BitVec 32).signExtend 64 = mask (decide (bit = 0)) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, State.ea, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hj, hstart, hs.rdi, he, hr, hb, hm,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem Keep.of_table {base : Addr} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.TableKeep base 64 128 s t) : VG.Proof.Ed25519.X86_64.Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : VG.Proof.Ed25519.X86_64.TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i :=
  VG.Proof.Ed25519.X86_64.Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem savedPoint_congr (e f : VG.Proof.Ed25519.X86_64.Env) (h : ∀ i : Slot, 16 ≤ i.val → e i = f i) :
    VG.Proof.Ed25519.X86_64.point e 17 18 19 20 = VG.Proof.Ed25519.X86_64.point f 17 18 19 20 := by
  simp only [VG.Proof.Ed25519.X86_64.point, h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide)]

theorem copyPointToQ_saved (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps copyPointToQOps e) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point e 17 18 19 20 := rfl

theorem restorePoint_saved (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps restorePointOps e) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point e 17 18 19 20 := rfl

theorem restorePoint_q (e : VG.Proof.Ed25519.X86_64.Env) : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps restorePointOps e) 4 5 6 7 = VG.Proof.Ed25519.X86_64.point e 4 5 6 7 := rfl

theorem prepareAdd_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (prepareAdd fld)) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 4 5 6 7 = VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * j) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = VG.Proof.Ed25519.X86_64.env s.mem base 16 := by
  rw [prepareAdd, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs savePointOps) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableAddr_ok (hs.of_keep ka).rdi 5376 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : VG.Proof.Ed25519.X86_64.Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointFromTable_ok (hs.of_keep (ka.trans kbe)) pb (by omega) (by omega))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_table kc
  have cs : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env c.mem base) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 := by
    rw [VG.Proof.Ed25519.X86_64.savedPoint_congr _ _ (fun i hi => VG.Proof.Ed25519.X86_64.tableLoad_high kc i (by omega)), kb.2.1, va, VG.Proof.Ed25519.X86_64.savePoint_eval]
  have cd : VG.Proof.Ed25519.X86_64.env c.mem base 16 = VG.Proof.Ed25519.X86_64.env s.mem base 16 := by
    rw [VG.Proof.Ed25519.X86_64.tableLoad_high kc 16 (by decide), kb.2.1, va]; rfl
  have cq : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env c.mem base) 0 1 2 3 = VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * j) := by
    rw [pc, kb.2.1]
    exact VG.Proof.Ed25519.X86_64.workspace_tablePoint ka.mem (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok (hs.of_keep ((ka.trans kbe).trans kce)) copyPointToQOps)
    fun d ⟨kd, vd⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok (hs.of_keep (((ka.trans kbe).trans kce).trans kd)) restorePointOps)
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans kbe).trans kce).trans kd).trans kt, ?_, ?_, ?_, ?_⟩
  · rw [vt, VG.Proof.Ed25519.X86_64.restorePoint_eval, vd, VG.Proof.Ed25519.X86_64.copyPointToQ_saved, cs]
  · rw [vt, VG.Proof.Ed25519.X86_64.restorePoint_q, vd, VG.Proof.Ed25519.X86_64.copyPointToQ_eval, cq]
  · rw [vt, VG.Proof.Ed25519.X86_64.restorePoint_saved, vd, VG.Proof.Ed25519.X86_64.copyPointToQ_saved, cs]
  · rw [vt, vd]
    exact cd

theorem Keep.bit {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.Keep base s t) (i : Nat) (hi : i < 512) :
    t.mem (off base (768 + i)) = s.mem (off base (768 + i)) :=
  h.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)

theorem pointAccumulate_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j start bit : Nat) (hj : j < 16) (hi : start + j < 512) (hbit : bit < 2)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (pointAccumulate fld)) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        (if bit = 0 then VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 else
          Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * j))) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d := by
  rw [pointAccumulate, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.prepareAdd_ok hs j hj hc) fun a ⟨ka, ap, aq, av, ad⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointAddWide_ok (hs.of_keep ka) (ad.trans hd)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBitMask_ok (hs.of_keep kab) j start bit hi hbit
    ((kab.gpr _ (by decide)).trans hc) ((kab.gpr _ (by decide)).trans hstart)
    ((kab.bit _ hi).trans hb)) fun c ⟨cm, kc⟩ => ?_
  have kce : VG.Proof.Ed25519.X86_64.Keep base b c := Keep.of_keeps kc (by decide)
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointSelect_ok (hs.of_keep (kab.trans kce)) cm) fun t ⟨kt, tv, td⟩ => ?_
  refine ⟨(kab.trans kce).trans kt, ?_, ?_⟩
  · rw [tv, kc.2.1, VG.Proof.Ed25519.X86_64.savedPoint_congr _ _ bh, av, bp, ap, aq]
    simp only [decide_eq_true_eq]
  · rw [td, kc.2.1, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.X86_64
end

/-! The descending-bit loop follows the specification exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hc, e, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem accumulateTest_ok (s : State) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, BitVec.and_self, VG.Proof.Ed25519.X86_64.point_counter_zero n hn,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem accumulateBody_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * n) = powerPoint p (start + n)) :
    WP isa (.block (accumulateBody fld)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.X86_64.RbxKeep base s t := by
  rw [accumulateBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointAccumulate_ok (hs.of_keeps ka (by decide)) n start ((scalar / 2 ^ (start + n)) % 2) hn hi (by omega) ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb) (by rw [ka.2.1]; exact hd))
    fun b ⟨kb, bp, bd⟩ => ?_
  have bc : b.gpr .rbx = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine WP.mono (VG.Proof.Ed25519.X86_64.accumulateTest_ok b n hn bc) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kt.1 _ (by simp)).trans bc, tz, ?_, ?_, ?_⟩
  · rw [kt.2.1, bp, ka.2.1, hp, ht, ← after_step]
  · rw [kt.2.1]; exact bd
  · exact ((RbxKeep.of_keeps ka (by decide)).trans (RbxKeep.of_keep kb)).trans
      (RbxKeep.of_keeps kt (by decide))

structure AccumulateInv (s₀ : State) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : VG.Proof.Ed25519.X86_64.Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  startReg : s.gpr .rsi = BitVec.ofNat 64 start
  d : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d
  value : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)
  keep : VG.Proof.Ed25519.X86_64.RbxKeep base s₀ s

theorem RbxKeep.refl (base : Addr) (s : State) : VG.Proof.Ed25519.X86_64.RbxKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem accumulateLoop_ok {s₀ : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s₀ base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hc : s₀.gpr .rbx = 16) (hstart : s₀.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s₀.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : VG.Proof.Ed25519.X86_64.env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint s₀.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop (.block (accumulateBody fld)) .ne) s₀ fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = after scalar p start ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.X86_64.RbxKeep base s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.X86_64.AccumulateInv s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86_64.accumulateBody_ok h.scratch k start scalar p hk (by omega) h.counter h.startReg
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (off base (768 + (start + i))) =
        BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2) := by
      intro i hi'
      rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi']
    have ht' : ∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (5376 + 128 * i) = powerPoint p (start + i) := by
      intro i hi'
      rw [VG.Proof.Ed25519.X86_64.workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, td, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc,
          (tk.gpr _ (by decide) (by decide)).trans h.startReg, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hs, hc, hstart, hd, hp, hb, ht, RbxKeep.refl _ _⟩

theorem accumulateInit_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 16)]) s fun t => t.gpr .rbx = 16 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem accumulate16_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa (accumulate16 fld) s fun t => VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = after scalar p start ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.X86_64.RbxKeep base s t := by
  rw [accumulate16]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86_64.accumulateLoop_ok (hs.of_keeps ka (by decide)) start scalar p hi ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb)
    (by rw [ka.2.1]; exact hd) (by rw [ka.2.1]; exact hp) (by rw [ka.2.1]; exact ht))
    fun t ⟨tv, td, tk⟩ => ?_
  exact ⟨tv, td, (RbxKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint`. -/
section

/-!
# Cached points

The cached addition is the specification's `pointAdd` (`grind`); each constant
field of a cached point is four immediate words stored through `rax`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F Keeps Outside fe_st4 st4_outside)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

def addCachedResult (e : VG.Proof.Ed25519.X86_64.Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointAddCachedOps e) 0 1 2 3 = VG.Proof.Ed25519.X86_64.addCachedResult e := rfl

theorem pointAddCached_eval (e : VG.Proof.Ed25519.X86_64.Env) (q : Spec.Ed25519.Point) (hq : VG.Proof.Ed25519.X86_64.point e 4 5 6 7 = cache q) :
    VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [VG.Proof.Ed25519.X86_64.pointAddCached_formula]
  simp only [VG.Proof.Ed25519.X86_64.addCachedResult, VG.Proof.Ed25519.X86_64.point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> grind

theorem pointAddCached_high (e : VG.Proof.Ed25519.X86_64.Env) (i : Slot) (hi : 16 ≤ i.val) :
    VG.Proof.Ed25519.X86_64.evalOps pointAddCachedOps e i = e i :=
  VG.Proof.Ed25519.X86_64.point_ops_high _ (by decide) e i hi

theorem pointAddCachedWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (q : Spec.Ed25519.Point) (hq : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 4 5 6 7 = cache q) :
    WP isa (.block (pointAddCached fld)) s fun t =>
      VG.Proof.Ed25519.X86_64.Keep base s t ∧ VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs pointAddCachedOps) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, VG.Proof.Ed25519.X86_64.pointAddCached_eval _ q hq, VG.Proof.Ed25519.X86_64.pointAddCached_high _⟩

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (v : Spec.X25519.Fe) (dst : Nat) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base (o + dst) = v ∧ VG.Proof.Ed25519.X86_64.TableKeep base (o + dst) 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableWords_ok (hs.of_keeps hk (by decide)) ((hk.1 _ (by decide)).trans hp) dst ho)
    fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv, Proof.X25519.toFe_self]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (q : Spec.Ed25519.Point) (dst : Nat) (ho : o + dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      VG.Proof.Ed25519.X86_64.tablePoint t.mem base (o + dst) = q ∧ VG.Proof.Ed25519.X86_64.TableKeep base (o + dst) 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.cachedFieldStore_ok hs hp q.X dst (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.cachedFieldStore_ok (ka.scratch hs) ((ka.gpr _ (by decide)).trans hp) q.Y (dst + 32)
    (by omega)) fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.cachedFieldStore_ok (kb.scratch (ka.scratch hs))
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)) q.Z (dst + 64)
    (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs)))
    ((kc.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)))
    q.T (dst + 96) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base (o + dst) = q.X := by
    rw [VG.Proof.Ed25519.X86_64.Outside_F (d := o + dst) kt.mem (by omega) (Or.inl (by omega)),
      VG.Proof.Ed25519.X86_64.Outside_F (d := o + dst) kc.mem (by omega) (Or.inl (by omega)),
      VG.Proof.Ed25519.X86_64.Outside_F (d := o + dst) kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (o + dst + 32) = q.Y := by
    rw [show o + dst + 32 = o + (dst + 32) by omega,
      VG.Proof.Ed25519.X86_64.Outside_F (d := o + (dst + 32)) kt.mem (by omega) (Or.inl (by omega)),
      VG.Proof.Ed25519.X86_64.Outside_F (d := o + (dst + 32)) kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (o + dst + 64) = q.Z := by
    rw [show o + dst + 64 = o + (dst + 64) by omega,
      VG.Proof.Ed25519.X86_64.Outside_F (d := o + (dst + 64)) kt.mem (by omega) (Or.inl (by omega)), cz]
  have et : F t.mem base (o + dst + 96) = q.T := by
    rw [show o + dst + 96 = o + (dst + 96) by omega, tt]
  simp only [VG.Proof.Ed25519.X86_64.tablePoint, ex, ey, ez, et]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine`. -/
section

/-! Normalization reuses X25519's verified exponentiation chain. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr IKeep E F)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem invertWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    WP isa (VG.Impl.X25519.X86_64.invert fld) s fun t => IKeep base s t ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 15 = VG.Proof.X25519.invert (VG.Proof.Ed25519.X86_64.env s.mem base 2) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hg, hr, hw, hm, hv⟩ := Proof.X25519.X86_64.invert_ok (EdArith.ok (fld := fld)) hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hg, rfl, rfl, hm⟩, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem affine_eval (e : VG.Proof.Ed25519.X86_64.Env) :
    VG.Proof.Ed25519.X86_64.evalOps affineOps e 0 = e 0 * e 15 ∧ VG.Proof.Ed25519.X86_64.evalOps affineOps e 1 = e 1 * e 15 := by
  exact ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    WP isa (pointAffine fld) s fun t => VG.Proof.Ed25519.X86_64.RbxKeep base s t ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 0 = VG.Proof.Ed25519.X86_64.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 1 = VG.Proof.Ed25519.X86_64.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.invertWide_ok hs) fun t ⟨hk, hv⟩ => ?_)
  have ht : VG.Proof.Ed25519.X86_64.Scratch t base := ⟨(hk.gpr _ (by decide) (by decide)).trans hs.rdi, hk.wr ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok ht affineOps) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hk.gpr r hr hb), ku.rd.trans hk.rd,
    ku.wr.trans hk.wr, (hk.mem.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (VG.Proof.Ed25519.X86_64.affine_eval _).1, hv]
    have he : VG.Proof.Ed25519.X86_64.env t.mem base 0 = VG.Proof.Ed25519.X86_64.env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]
  · rw [vu, (VG.Proof.Ed25519.X86_64.affine_eval _).2, hv]
    have he : VG.Proof.Ed25519.X86_64.env t.mem base 1 = VG.Proof.Ed25519.X86_64.env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode`. -/
section

/-! Canonical point encoding in four machine words. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Keeps val4 fe)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem freezeWide_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (a : Slot) :
    WP isa (.block (VG.Impl.X25519.X86_64.freeze (offset a))) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = (VG.Proof.Ed25519.X86_64.env s.mem base a).val ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx] s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hv, hk⟩ := Proof.X25519.X86_64.freeze_ok hn (a := offset a) (by simp only [offset]; omega)
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem sign_word (w : BitVec 64) :
    (w &&& (1 : BitVec 32).signExtend 64).rotateRight 1 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2) * 2 ^ 63) ∧
      Keeps [.rbx] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execShift, show 1 ≤ 1 ∧ 1 ≤ 63 from by decide, and_self, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hv]; exact VG.Proof.Ed25519.X86_64.sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = y)
    (hs : s.gpr .rbx = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.alu .add .r11 (.reg .rbx)]) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.r11] s t := by
  have hb : (s.gpr .r11).toNat < 2 ^ 63 := by simp only [val4] at hv; omega
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega
  have ha : (s.gpr .r11 + s.gpr .rbx).toNat = (s.gpr .r11).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [val4, ha] at hv ⊢; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem pointEncode_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    WP isa (pointEncode fld) s fun t => VG.Proof.Ed25519.X86_64.RbxKeep base s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        (VG.Proof.Ed25519.X86_64.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((VG.Proof.Ed25519.X86_64.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.freezeWide_ok (ka.scratch hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : VG.Proof.Ed25519.X86_64.RbxKeep base a b := RbxKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : VG.Proof.Ed25519.X86_64.RbxKeep base b c := RbxKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.freezeWide_ok (kce.scratch (kbe.scratch (ka.scratch hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : VG.Proof.Ed25519.X86_64.RbxKeep base c d := RbxKeep.of_keeps kd (by decide)
  have dx : d.gpr .rbx = BitVec.ofNat 64
      (((VG.Proof.Ed25519.X86_64.env s.mem base 0 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.1 .rbx (by decide), cx, bx, ax]
  rw [kc.2.1, kb.2.1, ay] at dy
  refine WP.mono (VG.Proof.Ed25519.X86_64.encodeSign_ok d _ _ (by
    exact Nat.lt_trans (VG.Proof.Ed25519.X86_64.env s.mem base 1 * Spec.X25519.pow (VG.Proof.Ed25519.X86_64.env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (RbxKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.PointBatch`. -/
section
/-! The local table preserves the accumulator, bits, and checkpoints. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : VG.Proof.Ed25519.X86_64.Keep base s t) :
    VG.Proof.Ed25519.X86_64.PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, TableFrame.workspace h.mem⟩

theorem loadCheckpoint_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (loadCheckpoint fld)) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.X86_64.tablePoint s.mem base (1280 + 128 * j) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 17 18 19 20 = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = VG.Proof.Ed25519.X86_64.env s.mem base 16 := by
  rw [loadCheckpoint, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs savePointOps) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.tableAddr_ok (hs.of_keep ka).rdi 1280 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : VG.Proof.Ed25519.X86_64.Keep base a b := Keep.of_keeps kb (by decide)
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointFromTable_ok (hs.of_keep (ka.trans kbe)) pb (by omega) (by omega))
    fun t ⟨pt, kt⟩ => ?_
  refine ⟨(ka.trans kbe).trans (Keep.of_table kt), ?_, ?_, ?_⟩
  · rw [pt, kb.2.1]; exact VG.Proof.Ed25519.X86_64.workspace_tablePoint ka.mem (by omega) (by omega)
  · rw [VG.Proof.Ed25519.X86_64.savedPoint_congr _ _ (fun i hi => VG.Proof.Ed25519.X86_64.tableLoad_high kt i (by omega)), kb.2.1, va, VG.Proof.Ed25519.X86_64.savePoint_eval]
  · rw [VG.Proof.Ed25519.X86_64.tableLoad_high kt 16 (by decide), kb.2.1, va]; rfl

theorem prepareBatch_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j)
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (prepareBatch fld) s fun t => VG.Proof.Ed25519.X86_64.PowersKeep base 5376 2048 s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (5376 + 128 * i) =
        powerPoint (VG.Proof.Ed25519.X86_64.tablePoint s.mem base (1280 + 128 * j)) i) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d := by
  rw [prepareBatch]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.loadCheckpoint_ok hs j hj hc) fun a ⟨ka, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.pointPowers_ok false (hs.of_keep ka) 5376 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨bt, _, bh, kb⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok (kb.scratch (hs.of_keep ka)) restorePointOps) fun t ⟨kt, vt⟩ => ?_
  refine ⟨((PowersKeep.of_keep ka).trans kb).trans (PowersKeep.of_keep kt), ?_, ?_, ?_⟩
  · rw [vt, VG.Proof.Ed25519.X86_64.restorePoint_eval, VG.Proof.Ed25519.X86_64.savedPoint_congr _ _ bh, av]
  · intro i hi
    rw [VG.Proof.Ed25519.X86_64.workspace_tablePoint kt.mem (by omega) (by omega), bt i hi, ap]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [vt]
    change VG.Proof.Ed25519.X86_64.env b.mem base 16 = _
    rw [bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.X86_64
end

/-! The public batch counter survives field and table operations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps ea_sc)

theorem tableFrame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : VG.Proof.Ed25519.X86_64.TableFrame base o n m m') (ho : 64 ≤ o) (hn : 768 ≤ o + n) :
    Outside base 64 (o + n - 64) m m' := by
  intro p hp
  exact h p (by omega) (by omega)

theorem batchBegin_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 j := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [batchBegin, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, trivial, trivial, ?_⟩
  · exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · intro p hp
    exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide) p hp

theorem batchBitOffset_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchBitOffset) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (16 * j) ∧ Keeps [.rax, .rdx, .rcx, .rsi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hv : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [batchBitOffset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hs.rdi, hr, hc, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change BitVec.ofNat 64 (j * 16) = BitVec.ofNat 64 (16 * j)
    rw [Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem batchTest_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.zf = some (decide (j = 0)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj]
  apply WP.of_runBlock
  simp only [batchTest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, BitVec.and_self, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch`. -/
section

/-! One checkpoint batch advances the exact scalar-multiplication invariant. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem PowersKeep.of_keeps {base : Addr} {o n : Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : VG.Proof.Ed25519.X86_64.PowersKeep base o n s t := by
  refine ⟨fun r hb hs hr => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hb h
    · exact hs h
    · exact hr h
  · rw [h.2.1]; exact TableFrame.refl _ _ _ _

theorem PowersKeep.of_rbx {base : Addr} {o n : Nat} {s t : State} (h : VG.Proof.Ed25519.X86_64.RbxKeep base s t) :
    VG.Proof.Ed25519.X86_64.PowersKeep base o n s t := ⟨fun r hb _ hr => h.gpr r hr hb, h.rd, h.wr, TableFrame.workspace h.mem⟩

theorem header_env {base : Addr} {m m' : Mem} (h : Outside base 56 8 m m') : VG.Proof.Ed25519.X86_64.env m' base = VG.Proof.Ed25519.X86_64.env m base := by
  funext i
  exact VG.Proof.Ed25519.X86_64.Outside_F h (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem TableFrame.bits {base : Addr} {m m' : Mem} (h : VG.Proof.Ed25519.X86_64.TableFrame base 5376 2048 m m')
    (i : Nat) (hi : i < 512) : m' (off base (768 + i)) = m (off base (768 + i)) := by
  apply h
  · rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega
  · rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega

theorem pointMulBatch_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (j count scalar : Nat) (p : Spec.Ed25519.Point) (hj : j < count) (hn : count ≤ 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1))
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2))
    (ht : ∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)) :
    WP isa (pointMulBatch fld) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ t.zf = some (decide (j = 0)) ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = after scalar p (16 * j) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧
      (∀ i < 16 * count, t.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) ∧
      (∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint t.mem base (1280 + 128 * i) = powerPoint p (16 * i)) ∧
      VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s t := by
  rw [pointMulBatch]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.batchBegin_ok hs j hc) fun a ⟨ac, av, ag, ar, aw, am⟩ => ?_)
  have ka : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s a := ⟨fun r hr _ _ => ag r hr, ar, aw,
    (TableFrame.table am).mono (by decide) (by decide)⟩
  have ae := VG.Proof.Ed25519.X86_64.header_env am
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.prepareBatch_ok (ka.scratch hs) j (by omega) ac
    (by rw [ae]; exact hd)) fun b ⟨kb, bp, bt, bd⟩ => ?_)
  have bcounter : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 j := by
    exact ((VG.Proof.Ed25519.X86_64.tableFrame_outside kb.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans av
  have bbits : ∀ i < 16 * count, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.mem.bits i (by omega), am _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hb i hi]
  have bcheck : ∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint b.mem base (1280 + 128 * i) = powerPoint p (16 * i) := by
    intro i hi
    rw [kb.mem.point (by omega) (Or.inl (by omega)) (by omega),
      (TableFrame.table am).point (by omega) (Or.inr (by omega)) (by omega), ht i hi]
  have btable : ∀ i < 16, VG.Proof.Ed25519.X86_64.tablePoint b.mem base (5376 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hi
    rw [bt i hi, (TableFrame.table am).point (by omega) (Or.inr (by omega)) (by omega), ht j hj, powerPoint_add]
  have bpoint : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env b.mem base) 0 1 2 3 = after scalar p (16 * j + 16) := by
    rw [bp, ae, hp, Nat.mul_add, Nat.mul_one]
  have kab : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s b := ka.trans (kb.mono (by decide) (by decide))
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.batchBitOffset_ok (kab.scratch hs) j (by omega) bcounter) fun c ⟨cs, kc⟩ => ?_)
  have kce : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 b c := PowersKeep.of_keeps kc (by decide)
  have kabc := kab.trans kce
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.accumulate16_ok (kabc.scratch hs) (16 * j) scalar p (by omega) cs
    (by intro i hi; rw [kc.2.1]; exact bbits _ (by omega))
    (by rw [kc.2.1]; exact bd) (by rw [kc.2.1]; exact bpoint) (by rw [kc.2.1]; exact btable))
    fun d ⟨dp, dd, kd⟩ => ?_)
  have dcounter : d.mem.readW (off base 56) 64 = BitVec.ofNat 64 j := by
    exact (kd.mem.word (d := 56) (Or.inl (by decide)) (by decide)).trans
      ((congrArg (fun m : Mem => m.readW (off base 56) 64) kc.2.1).trans bcounter)
  have kabcd : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s d := kabc.trans (PowersKeep.of_rbx kd)
  refine WP.mono (VG.Proof.Ed25519.X86_64.batchTest_ok (kabcd.scratch hs) j (by omega) dcounter) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, tz, ?_, ?_, ?_, ?_, kabcd.trans (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact dcounter
  · rw [kt.2.1]; exact dp
  · rw [kt.2.1]; exact dd
  · intro i hi
    rw [kt.2.1, kd.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), kc.2.1]
    exact bbits i hi
  · intro i hi
    rw [kt.2.1, VG.Proof.Ed25519.X86_64.workspace_tablePoint kd.mem (by omega) (by omega), kc.2.1]
    exact bcheck i hi

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMulLoop`. -/
section

/-! Complete descent through the checkpoint table. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

structure PointMulInv (s₀ : State) (base : Addr) (count scalar : Nat) (p : Spec.Ed25519.Point)
    (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : VG.Proof.Ed25519.X86_64.Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 n
  d : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d
  value : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3 = after scalar p (16 * n)
  bits : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  table : ∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)
  keep : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s₀ s

theorem pointMulLoop_ok {s₀ : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s₀ base)
    (count scalar : Nat) (p : Spec.Ed25519.Point) (hn0 : 0 < count) (hn : count ≤ 32)
    (hc : s₀.mem.readW (off base 56) 64 = BitVec.ofNat 64 count)
    (hd : VG.Proof.Ed25519.X86_64.env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s₀.mem base) 0 1 2 3 = after scalar p (16 * count))
    (hb : ∀ i < 16 * count, s₀.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2))
    (ht : ∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint s₀.mem base (1280 + 128 * i) = powerPoint p (16 * i)) :
    WP isa (.loop (pointMulBatch fld) .ne) s₀ fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar p ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.X86_64.PointMulInv s₀ base count scalar p) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    refine WP.mono (VG.Proof.Ed25519.X86_64.pointMulBatch_ok h.scratch j count scalar p hj hn h.counter h.d h.value h.bits h.table)
      fun t ⟨tc, tz, tv, td, tb, tt, tk⟩ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      rw [Nat.mul_zero, after_zero] at tv
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, td, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hj0, Option.map_some, Bool.not_false],
        j, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc, td, tv, tb, tt, h.keep.trans tk⟩⟩
  · exact ⟨hn0, Nat.le_refl _, hs, hc, hd, hp, hb, ht, PowersKeep.refl _ _ _ _⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMul`. -/
section

/-! Checkpoint generation and batch descent implement pointMul. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside ea_sc)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [mulCounterInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hw,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨Mem.readW_writeW_self64 _ _ _, fun r hr => ?_, rfl, trivial, ?_⟩
  · simp only [hr, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)

theorem pointMultiplyInit_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (count scalar : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (pointMultiplyInit fld count) s fun t =>
      VG.Proof.Ed25519.X86_64.PointMulInv s base count scalar (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) count t := by
  rw [pointMultiplyInit]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.pointPowers_ok true hs 1280 count (by decide) (by omega) hn0 hn hd)
    fun a ⟨atab, _, ahigh, ka⟩ => ?_)
  have ad : VG.Proof.Ed25519.X86_64.env a.mem base 16 = Spec.Ed25519.d := (ahigh 16 (by decide)).trans hd
  have abits : ∀ i < 16 * count, a.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [ka.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)
      (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hb i hi]
  have kat : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s a := ka.mono (by decide) (by omega)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok (ka.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun b ⟨kb, vb⟩ => ?_)
  have bd : VG.Proof.Ed25519.X86_64.env b.mem base 16 = Spec.Ed25519.d := by rw [vb]; exact ad
  have bp : VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env b.mem base) 0 1 2 3 =
      after scalar (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (16 * count) := by
    rw [vb, VG.Proof.Ed25519.X86_64.constPoint_eval, after_top _ _ _ hscalar]
  have bbits : ∀ i < 16 * count, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega), abits i hi]
  have btab : ∀ i < count, VG.Proof.Ed25519.X86_64.tablePoint b.mem base (1280 + 128 * i) =
      powerPoint (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) (16 * i) := by
    intro i hi
    rw [VG.Proof.Ed25519.X86_64.workspace_tablePoint kb.mem (by omega) (by omega)]
    exact atab i hi
  have kab := kat.trans (PowersKeep.of_keep kb)
  refine WP.mono (VG.Proof.Ed25519.X86_64.mulCounterInit_ok (kab.scratch hs) count) fun c ⟨cc, cg, cr, cw, cm⟩ => ?_
  have kc : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 b c := ⟨fun r _ _ hr => cg r (by
    intro he; subst r; exact hr (by decide)), cr, cw, (TableFrame.table cm).mono (by decide) (by decide)⟩
  have ce := VG.Proof.Ed25519.X86_64.header_env cm
  exact ⟨hn0, Nat.le_refl _, (kab.trans kc).scratch hs, cc,
    (by rw [ce]; exact bd), (by rw [ce]; exact bp),
    (by intro i hi; rw [cm _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)]; exact bbits i hi),
    (by intro i hi; rw [(TableFrame.table cm).point (by omega) (Or.inr (by omega)) (by omega)]; exact btab i hi),
    kab.trans kc⟩

theorem pointMultiply_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base)
    (count scalar : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hd : VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (pointMultiply fld count) s fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧ VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s t := by
  rw [pointMultiply]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.pointMultiplyInit_ok hs count scalar hn0 hn hscalar hd hb) fun a h => ?_)
  refine WP.mono (VG.Proof.Ed25519.X86_64.pointMulLoop_ok h.scratch count scalar _ hn0 hn h.counter h.d h.value h.bits h.table)
    fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨tv, td, h.keep.trans kt⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.FieldCheck`. -/
section
/-! Compare field elements through canonical representatives. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps clob)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

theorem wordsZero_flag (a b c d : BitVec 64) :
    (((a ||| b) ||| c) ||| d == 0#64) = decide (val4 a b c d = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq, val4]
  constructor
  · rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl
  · intro h
    have ha : a.toNat = 0 := by omega
    have hb : b.toNat = 0 := by omega
    have hc : c.toNat = 0 := by omega
    have hd : d.toNat = 0 := by omega
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq ha, BitVec.eq_of_toNat_eq hb⟩,
      BitVec.eq_of_toNat_eq hc⟩, BitVec.eq_of_toNat_eq hd⟩

theorem wordsZero_ok (s : State) :
    WP isa (.block wordsZero) s fun t =>
      t.zf = some (decide (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = 0)) ∧
      Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [wordsZero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨VG.Proof.Ed25519.X86_64.wordsZero_flag _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem fieldZero_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t =>
      t.zf = some (decide (VG.Proof.Ed25519.X86_64.env s.mem base a = 0)) ∧ VG.Proof.Ed25519.X86_64.Keep base s t ∧ t.mem = s.mem := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.freezeWide_ok hs a) fun u ⟨uv, ku⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.wordsZero_ok u) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, (Keep.of_keeps ku (by decide)).trans (Keep.of_keeps kt (by decide)), kt.2.1.trans ku.2.1⟩
  rw [tz, uv]
  have he : (VG.Proof.Ed25519.X86_64.env s.mem base a).val = 0 ↔ VG.Proof.Ed25519.X86_64.env s.mem base a = 0 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (a b : Slot) :
    WP isa (.block (fieldEqual fld a b)) s fun t =>
      t.zf = some (decide (VG.Proof.Ed25519.X86_64.env s.mem base a = VG.Proof.Ed25519.X86_64.env s.mem base b)) ∧ VG.Proof.Ed25519.X86_64.Keep base s t ∧
      ∀ i : Slot, i ≠ 21 → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok hs [.sub 21 a b]) fun u ⟨ku, vu⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldZero_ok (hs.of_keep ku) 21) fun t ⟨tz, kt, tm⟩ => ?_
  refine ⟨?_, ku.trans kt, ?_⟩
  · rw [tz, vu]
    change some (decide (VG.Proof.Ed25519.X86_64.env s.mem base a - VG.Proof.Ed25519.X86_64.env s.mem base b = 0)) = _
    have e : VG.Proof.Ed25519.X86_64.env s.mem base a - VG.Proof.Ed25519.X86_64.env s.mem base b = 0 ↔ VG.Proof.Ed25519.X86_64.env s.mem base a = VG.Proof.Ed25519.X86_64.env s.mem base b :=
      ⟨fun h => by grind, fun h => by grind⟩
    simp only [e]
  · intro i hi
    rw [tm, vu]
    change Function.update (VG.Proof.Ed25519.X86_64.env s.mem base) 21 (VG.Proof.Ed25519.X86_64.env s.mem base a - VG.Proof.Ed25519.X86_64.env s.mem base b) i = _
    exact Function.update_of_ne hi _ _

end VG.Proof.Ed25519.X86_64
end

/-! The public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps)

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& (1 : BitVec 32).signExtend 64) ^^^ VG.Proof.Ed25519.X86_64.signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .rsi = VG.Proof.Ed25519.X86_64.signWord b) :
    WP isa (.block recoverParity) s fun t =>
      t.zf = some (((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 == 1) == b)) ∧
      Keeps [.rax] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self, hs, VG.Proof.Ed25519.X86_64.parity_flag, hv]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov32 .rax (.imm (if b then 1 else 0))]) s fun t =>
      t.gpr .rax = VG.Proof.Ed25519.X86_64.signWord b ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases b <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem testSign_ok {s : State} (b : Bool) (hs : s.gpr .rsi = VG.Proof.Ed25519.X86_64.signWord b) :
    WP isa (.block [.alu .test .rsi (.reg .rsi)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine`. -/
section

/-! The scalar bits, point multiplication, and canonical encoding compose. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside val4)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (VG.Proof.Ed25519.X86_64.encodedValue p) := rfl

theorem powersKeep_outside {base : Addr} {s t : State} (h : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s t) :
    Outside base 56 7368 s.mem t.mem := fun p hp => h.mem p (by omega) hp

theorem scalarBaseInit_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    WP isa (.block (scalarBaseInit fld)) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = Spec.Ed25519.basePoint ∧ VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d := by
  rw [scalarBaseInit, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.fieldCodeWide_ok (hs.of_keep ka) (constPointOps Spec.Ed25519.basePoint))
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_⟩
  · rw [vt, VG.Proof.Ed25519.X86_64.constPoint_eval]
  · rw [vt, va]; rfl

theorem scalarBasePrepare_ok {s : State} {base k : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBasePrepare fld) s fun t => VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = Spec.Ed25519.basePoint ∧
      VG.Proof.Ed25519.X86_64.env t.mem base 16 = Spec.Ed25519.d ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
  rw [scalarBasePrepare]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.expandScalarBits_ok hs hp 32 (by decide) (by decide) hr hd)
    fun a ⟨ka, abits⟩ => ?_)
  have kap : VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr,
      (TableFrame.table ka.mem).mono (by decide) (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBaseInit_ok (ka.scratch hs)) fun b ⟨kb, bp, bd⟩ => ?_
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at h
    rw [show 256 ^ 32 = 2 ^ (16 * 16) by decide] at h
    exact h
  have bbits : ∀ i < 16 * 16, b.mem (off base (768 + i)) =
      BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega)]; exact abits i hi
  exact ⟨kap.trans (PowersKeep.of_keep kb), bp, bd, bbits, hscalar⟩

def BaseEngineCorrect (engine : Prog isa) : Prop :=
  ∀ {s : State} {base k : Addr}, VG.Proof.Ed25519.X86_64.Scratch s base → s.gpr .rsi = k →
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) →
    (∀ q < 32, 8192 ≤ ofs base (off k q)) →
    WP isa engine s fun t => VG.Proof.Ed25519.X86_64.PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        VG.Proof.Ed25519.X86_64.encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseMemory`. -/
section
/-! Keep the output pointer and saved registers outside the point workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Outside Keeps ea_at ea_sc)

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi ∧ Outside (s.gpr .rdx) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .rdx) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, hw', ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_self _ _ _
  · exact RegUpd.gpr_setReg_of_ne _ _ hr
  · exact Mem.readW_writeW_self64 _ _ _
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .rdx = base ∧ t.gpr .rdi = s.mem.readW (off base 48) 64 ∧ Keeps [.rdx, .rdi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86_64
end

/-! Base-point multiplication satisfies its memory and ABI obligations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved val4 st4 bytesAt_st4)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

def scalarBaseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rsi, 32⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .rsi) 32)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

theorem farScratch {base p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    8192 ≤ ofs base (off p i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  change (off p i - base).toNat + 1 ≤ 8192
  change (off p i - base).toNat < 8192 at h
  omega

theorem scalarBase_correct_of_engine (engine : Prog isa) (engine_ok : VG.Proof.Ed25519.X86_64.BaseEngineCorrect engine)
    {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith engine) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hn⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, ma, sva⟩ => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ => ?_
  rw [ga] at pb ob mb
  have hb : VG.Proof.Ed25519.X86_64.Scratch b (s.gpr .rdx) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .rdx) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .rsi) 32 = bytesAt s.mem (s.gpr .rsi) 32 := VG.Proof.Ed25519.X86_64.bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (engine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .rsi, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => VG.Proof.Ed25519.X86_64.farScratch hd hq (by decide))) fun c ⟨kc, vc⟩ => ?_
  have mc := VG.Proof.Ed25519.X86_64.powersKeep_outside kc
  have svc : Saved (s.gpr .rdx) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.X86_64.scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have rdxd : d.gpr .rdx = s.gpr .rdx := pd
  have rdid : d.gpr .rdi = s.gpr .rdi := od.trans oc
  have wd : d.wr = s.wr := kd.2.2.2.trans wc
  rw [WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) rdxd (wd ▸ hws) (by rw [kd.2.1]; exact svc))
    fun e ⟨re, ge, me, _, we⟩ => ?_
  have rdie : e.gpr .rdi = s.gpr .rdi := (ge _ (by decide)).trans rdid
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ e.wr := by rw [we, wd, hw]; simp
  refine WP.mono (scalarOut_ok rdie hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fme : Frame [⟨s.gpr .rdx, 8192⟩] s.mem e.mem := by
    rw [me, kd.2.1]; exact fm.trans (scratchFrame mc (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.rbx, 0) (by decide)
    · exact re (.rbp, 8) (by decide)
    · rw [ge _ (by decide), kd.1 _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
    · exact re (.r12, 16) (by decide)
    · exact re (.r13, 24) (by decide)
    · exact re (.r14, 32) (by decide)
    · exact re (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have hc : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fme.mono (by simp)).writeW hm _ (hc 0 (by decide))).writeW hm _
        (hc 8 (by decide))).writeW hm _ (hc 16 (by decide))).writeW hm _ (hc 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarBase _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarBase, VG.Proof.Ed25519.X86_64.encodedValue_spec, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ge .r8 (by decide), ge .r9 (by decide), ge .r10 (by decide), ge .r11 (by decide),
      kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide)]
    change val4 (c.gpr .r8) (c.gpr .r9) (c.gpr .r10) (c.gpr .r11) = _
    rw [vc, input]

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry`. -/
section

/-!
# Adding a table entry

An addition `add` adds `q` to the accumulator when slots 4–7 hold `f q`
(`AddSpec`): `pointAdd` with `f = id`, `pointAddCached` with `f = cache`.
`pointFromTableQ` copies a table entry to slots 4–7.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F fe_st4 st4_outside Outside Keeps clob)
open VG.Impl.X25519.X86_64 (stores)

variable {fld : Arith} [VG.Proof.Ed25519.X86_64.EdArith fld]

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), VG.Proof.Ed25519.X86_64.Scratch s base →
    VG.Proof.Ed25519.X86_64.env s.mem base 16 = Spec.Ed25519.d → VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => VG.Proof.Ed25519.X86_64.Keep base s t ∧
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → VG.Proof.Ed25519.X86_64.env t.mem base i = VG.Proof.Ed25519.X86_64.env s.mem base i

theorem pointAdd_spec : VG.Proof.Ed25519.X86_64.AddSpec (pointAdd fld) id := fun _ _ _ hs hd hq =>
  WP.mono (VG.Proof.Ed25519.X86_64.pointAddWide_ok hs hd) fun _ ⟨k, v, h⟩ => ⟨k, v.trans (by rw [hq]; rfl), h⟩

theorem pointAddCached_spec : VG.Proof.Ed25519.X86_64.AddSpec (pointAddCached fld) cache := fun _ _ q hs _ hq =>
  VG.Proof.Ed25519.X86_64.pointAddCachedWide_ok hs q hq

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      VG.Proof.Ed25519.X86_64.env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      VG.Proof.Ed25519.X86_64.TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.fromTableWords_ok hs hp (32 * j) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, hm, fe_st4 _ _ (by omega), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), VG.Proof.Ed25519.X86_64.env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      VG.Proof.Ed25519.X86_64.TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (VG.Proof.Ed25519.X86_64.fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : VG.Proof.Ed25519.X86_64.env u.mem base ⟨4 + j, by omega⟩ = VG.Proof.Ed25519.X86_64.env t.mem base ⟨4 + j, by omega⟩ :=
        VG.Proof.Ed25519.X86_64.Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, VG.Proof.Ed25519.X86_64.Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.X86_64.Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      VG.Proof.Ed25519.X86_64.point (VG.Proof.Ed25519.X86_64.env t.mem base) 4 5 6 7 = VG.Proof.Ed25519.X86_64.tablePoint s.mem base o ∧ VG.Proof.Ed25519.X86_64.TableKeep base 192 128 s t := by
  refine WP.mono (VG.Proof.Ed25519.X86_64.fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change VG.Proof.Ed25519.X86_64.env t.mem base 4 = _ at h0
  change VG.Proof.Ed25519.X86_64.env t.mem base 5 = _ at h1
  change VG.Proof.Ed25519.X86_64.env t.mem base 6 = _ at h2
  change VG.Proof.Ed25519.X86_64.env t.mem base 7 = _ at h3
  simp only [VG.Proof.Ed25519.X86_64.tablePoint, VG.Proof.Ed25519.X86_64.point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : VG.Proof.Ed25519.X86_64.TableKeep base 192 128 s t) : VG.Proof.Ed25519.X86_64.Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

end VG.Proof.Ed25519.X86_64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits`. -/
section

/-! Load the encoded y-coordinate and its separate sign bit. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps ea_at val4)

theorem decodeLE_inputWords (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      val4 (m.readW (off p 0) 64) (m.readW (off p 8) 64)
        (m.readW (off p 16) 64) (m.readW (off p 24) 64) := by
  rw [decodeLE_eq, show off p 0 = p from BitVec.add_zero p, val4]
  exact VG.Proof.X25519.leNum_bytesAt_words64 m p

private theorem encoded_top (m : Mem) (p : Addr) :
    ((m.readW (off p 24) 64) >>> 63).toNat =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) / 2 ^ 255 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decodeLE_inputWords, val4]
  have h0 := (m.readW (off p 0) 64).isLt
  have h1 := (m.readW (off p 8) 64).isLt
  have h2 := (m.readW (off p 16) 64).isLt
  omega

theorem loadSign_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : InRegions (s.rd ++ s.wr) (off p 24) 8) :
    WP isa (.block loadSign) s fun t =>
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      Keeps [.rsi] s t := by
  have hn := decodeLE_lt (Spec.Ed25519.bytesAt s.mem p 32)
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [hl] at hn
  have hv : (s.mem.readW (off p 24) 64) >>> 63 =
      signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) := by
    have h : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 0 ∨
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 1 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [encoded_top]
    rcases h with h | h <;> rw [h] <;> rfl
  apply WP.of_runBlock
  simp only [loadSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift,
    State.load64, ea_at, hp, hr, show 1 ≤ 63 ∧ 63 ≤ 63 by decide, and_self,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

theorem loadY_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block Impl.X25519.X86_64.loadU) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s t := by
  refine WP.mono (Proof.X25519.X86_64.loadU_ok s hp hr) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, kt⟩
  rw [tv, Proof.X25519.decodeUCoordinate_eq (Proof.X25519.length_bytesAt _ _ _), decodeLE_eq]
  rfl

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.RecoverAdjust`. -/
section
/-! Sign selection and the extended coordinates of a decoded point. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩

def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (recoverSuccess fld)) s fun t => Keep base s t ∧ t.gpr .rax = 1 ∧
      VG.Proof.Ed25519.X86_64.point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs recoverSuccessOps) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (returnFlag_ok a true) fun t ⟨tr, kt⟩ => ?_
  refine ⟨ka.trans (Keep.of_keeps kt (by decide)), tr, ?_⟩
  rw [kt.2.1, va]
  rfl

private theorem adjustBranch_ok {s : State} {base : Addr} (hs : Scratch s base) (b : Bool)
    (hz : s.zf = some (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite .e (.block []) (.block (fieldCode fld [.const 5 0, .sub 0 5 0]))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧ env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by exact hz)
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCodeWide_ok hs [.const 5 0, .sub 0 5 0]) fun t ⟨kt, vt⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [vt]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [vt]; rfl

theorem recoverAdjustSign_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (recoverAdjustSign fld) s fun t => Keep base s t ∧ t.gpr .rax = 1 ∧
      VG.Proof.Ed25519.X86_64.point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  rw [recoverAdjustSign]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.1 _ (by decide)).trans hb)) fun c ⟨cz, kc⟩ => ?_
  have kac : Keep base s c := (Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kc (by decide))
  have cm : c.mem = s.mem := kc.2.1.trans ka.2.1
  have ch : c.zf = some (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, ax, cm]
  refine WP.seq (WP.mono (adjustBranch_ok (hs.of_keep kac) b ch) fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok (hs.of_keep (kac.trans kd))) fun t ⟨kt, tr, tv⟩ => ?_
  exact ⟨(kac.trans kd).trans kt, tr, by rw [tv, dx, dy, cm]⟩

end VG.Proof.Ed25519.X86_64
end

/-! Reject the negative encoding of zero and otherwise return the selected sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def DecodeResult (base : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .rax = 0
  | some p => s.gpr .rax = 1 ∧ VG.Proof.Ed25519.X86_64.point (env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : Addr) :
    WP isa recoverInvalid s fun t => Keep base s t ∧ DecodeResult base none t :=
  WP.mono (returnFlag_ok s false) fun _ ⟨tr, kt⟩ => ⟨Keep.of_keeps kt (by decide), tr⟩

theorem recoverSign_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (recoverSign fld) s fun t => Keep base s t ∧
      DecodeResult base (signResult (env s.mem base 0) (env s.mem base 1) b) t := by
  rw [recoverSign]
  refine WP.seq (WP.mono (fieldZero_ok hs 0) fun a ⟨az, ka, am⟩ => ?_)
  apply WP.ite (decide (env s.mem base 0 = 0)) (by exact az)
  · intro hzero
    have hz : env s.mem base 0 = 0 := of_decide_eq_true hzero
    refine WP.seq (WP.mono (testSign_ok b ((ka.gpr _ (by decide)).trans hb)) fun c ⟨cz, kc⟩ => ?_)
    have kac := ka.trans (Keep.of_keeps kc (by decide))
    apply WP.ite b (by simp only [eval, cz, Option.map_some, Bool.not_not])
    · intro ht
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨kac.trans kt, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok (hs.of_keep kac) b ((kac.gpr _ (by decide)).trans hb))
        fun t ⟨kt, tr, tv⟩ => ?_
      refine ⟨kac.trans kt, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨tr, by rw [tv, kc.2.1, am, hf]⟩
  · intro hnonzero
    have hn : env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (hs.of_keep ka) b ((ka.gpr _ (by decide)).trans hb))
      fun t ⟨kt, tr, tv⟩ => ?_
    refine ⟨ka.trans kt, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨tr, by rw [tv, am]⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.RecoverPoint`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.RecoverCandidate`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RootWide`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.RootPower`. -/
section
/-! Decoding reuses the proved field multiplication and squaring loops. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519.X86_64

def rootEnv (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  opMul 17 17 4 (opSqn 17 17 2 (opMul 17 18 17 (opSqn 18 18 50 (opMul 18 19 18 (opSqn 19 18 100
    (opMul 18 18 17 (opSqn 18 17 50 (opMul 17 18 17 (opSqn 18 18 10 (opMul 18 19 18 (opSqn 19 18 20
    (opMul 18 18 17 (opSqn 18 17 10 (opMul 17 18 17 (opSqn 18 17 5 (opMul 17 17 18
    (opMul 18 16 16 (opMul 16 16 17 (opMul 17 4 17 (opMul 17 17 17 (opMul 17 16 16
    (opMul 16 4 4 e))))))))))))))))))))))

theorem rootPower_spec {fld : Impl.Ed25519.X86_64.Arith} [EdArith fld] (base : Addr) : ISpec base (Impl.Ed25519.X86_64.rootPower fld) rootEnv := by
  have h : ISpec base _ _ :=
    (sqrI (EdArith.ok (fld := fld)) base 16 4 ⟨by decide, by decide⟩).seq <|
    ((sqrI (EdArith.ok (fld := fld)) base 17 16 ⟨by decide, by decide⟩).append
      (sqrI (EdArith.ok (fld := fld)) base 17 17 ⟨by decide, by decide⟩)).seq <|
    ((((mulI (EdArith.ok (fld := fld)) base 17 4 17 ⟨by decide, by decide⟩).append
      (mulI (EdArith.ok (fld := fld)) base 16 16 17 ⟨by decide, by decide⟩)).append
      (sqrI (EdArith.ok (fld := fld)) base 18 16 ⟨by decide, by decide⟩)).append
      (mulI (EdArith.ok (fld := fld)) base 17 17 18 ⟨by decide, by decide⟩)).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 19 18 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 18 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 17 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 19 18 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 18 18 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI (EdArith.ok (fld := fld)) base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI (EdArith.ok (fld := fld)) base 17 17 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI (EdArith.ok (fld := fld)) base 17 17 4 ⟨by decide, by decide⟩)
  exact h

theorem rootEnv_eval (e : VG.Proof.X25519.X86_64.Env) : rootEnv e 17 = VG.Proof.Ed25519.rootPower (e 4) := by
  simp only [↓reduceIte, rootEnv, opMul, opSqn, Function.update_apply]
  rfl

end VG.Proof.Ed25519.X86_64
end

/-! Lift the root exponentiation into Ed25519's larger scratch region. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr IKeep)

variable {fld : Arith} [EdArith fld]

theorem rootPowerWide_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (Impl.Ed25519.X86_64.rootPower fld) s fun t => IKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv⟩ := rootPower_spec (fld := fld) base narrow hn
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, ?_⟩
  · have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
    simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e
  · change VG.Proof.X25519.X86_64.E t.mem base 17 = _
    rw [hv, rootEnv_eval, rootPower_eq]
    rfl

end VG.Proof.Ed25519.X86_64
end

/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (recoverCandidate fld) s fun t => RbxKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCodeWide_ok hs recoverInitOps) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPowerWide_ok (hs.of_keep ka)) fun b ⟨kb, vb⟩ => ?_)
  have kbr : RbxKeep base a b := ⟨kb.gpr, kb.rd, kb.wr, kb.mem.mono (by decide) (by decide)⟩
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    exact Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  refine WP.mono (fieldCodeWide_ok (kbr.scratch (hs.of_keep ka)) recoverFinishOps) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, va, au, av3, az]
    rfl
  have kar : RbxKeep base s a := ⟨fun r hr _ => ka.gpr r hr, ka.rd, ka.wr, ka.mem⟩
  have ktr : RbxKeep base b t := ⟨fun r hr _ => kt.gpr r hr, kt.rd, kt.wr, kt.mem⟩
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.X86_64
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa (recoverSign fld) s fun t => RbxKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨RbxKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (recoverPoint fld) s fun t => RbxKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scratch hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (RbxKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by change c.zf = _; rw [cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scratch hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scratch hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (RbxKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by change d.zf = _; rw [dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCodeWide_ok (kacd.scratch hs) [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (RbxKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scratch hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (RbxKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectTable`. -/
section

/-!
The comb's 32 constant-time table selections as literals (`materialize_table`):
the literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read them rather than build the selections
from the tables again.
-/

namespace VG

materialize_table Impl.Ed25519.X86_64.combSelect 32

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit`. -/
section

/-! The point arithmetic and the inversion chains, for each field arithmetic, as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/
namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_value pointAddLit := pointAdd Impl.X25519.X86_64.baseline
materialize_value pointAddAdxLit := pointAdd Impl.X25519.X86_64.adx
materialize_value pointDoubleLit := pointDouble Impl.X25519.X86_64.baseline
materialize_value pointDoubleAdxLit := pointDouble Impl.X25519.X86_64.adx
materialize_value pointAddCachedLit := pointAddCached Impl.X25519.X86_64.baseline
materialize_value pointAddCachedAdxLit := pointAddCached Impl.X25519.X86_64.adx
materialize_code invertLit := Impl.X25519.X86_64.invert Impl.X25519.X86_64.baseline
materialize_code invertAdxLit := Impl.X25519.X86_64.invert Impl.X25519.X86_64.adx
materialize_code rootPowerLit := VG.Impl.Ed25519.X86_64.rootPower Impl.X25519.X86_64.baseline
materialize_code rootPowerAdxLit := VG.Impl.Ed25519.X86_64.rootPower Impl.X25519.X86_64.adx
materialize_code double4Lit := VG.Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.baseline
materialize_code double4AdxLit := VG.Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.adx

end VG.Proof.Ed25519.X86_64

/-! Checked literals for the pieces of the relational constant-time proof. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code prepareBatchLit := (prepareBatch Impl.X25519.X86_64.baseline : Prog isa)
materialize_code prepareBatchAdxLit := (prepareBatch Impl.X25519.X86_64.adx : Prog isa)
materialize_code accumulate16Lit := (accumulate16 Impl.X25519.X86_64.baseline : Prog isa)
materialize_code accumulate16AdxLit := (accumulate16 Impl.X25519.X86_64.adx : Prog isa)
materialize_code pointEncodeLit := (pointEncode Impl.X25519.X86_64.baseline : Prog isa)
materialize_code pointEncodeAdxLit := (pointEncode Impl.X25519.X86_64.adx : Prog isa)
materialize_code scalarBasePrepareLit := (scalarBasePrepare Impl.X25519.X86_64.baseline : Prog isa)
materialize_code scalarBasePrepareAdxLit := (scalarBasePrepare Impl.X25519.X86_64.adx : Prog isa)
materialize_code pointMultiplyInit16 := pointMultiplyInit Impl.X25519.X86_64.baseline 16
materialize_code pointMultiplyInit16Adx := pointMultiplyInit Impl.X25519.X86_64.adx 16
materialize_code baseInit := (.block (scalarBaseInit Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code baseInitAdx := (.block (scalarBaseInit Impl.X25519.X86_64.adx) : Prog isa)
materialize_code identityInit := (.block (constPoint Impl.X25519.X86_64.baseline Spec.Ed25519.identity) : Prog isa)
materialize_code identityInitAdx := (.block (constPoint Impl.X25519.X86_64.adx Spec.Ed25519.identity) : Prog isa)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.CombLit`. -/
section

/-! Checked literals for the comb variant and its constant-time proof. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code combMultiplyLit := (combMultiply Impl.X25519.X86_64.baseline)
materialize_code combMultiplyAdxLit := (combMultiply Impl.X25519.X86_64.adx)
end VG.Proof.Ed25519.X86_64

namespace VG
materialize_code scalarBase_precomputedLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
materialize_code scalarBase_precomputedAdxLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx)
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit`. -/
section

/-! Checked literals for the verifier's fixed control-flow pieces. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code recoverCandidateLit := (recoverCandidate Impl.X25519.X86_64.baseline : Prog isa)
materialize_code recoverCandidateAdxLit := (recoverCandidate Impl.X25519.X86_64.adx : Prog isa)
materialize_code decodeLoadBlock := (.block pointDecodeLoad : Prog isa)
materialize_code parityBlock :=
  (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual Impl.X25519.X86_64.baseline 11 6) : Prog isa)
materialize_code rootCheckBlockAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual Impl.X25519.X86_64.baseline 11 12) : Prog isa)
materialize_code rootCheckMinusBlockAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode Impl.X25519.X86_64.baseline [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code negateBlockAdx := (.block (fieldCode Impl.X25519.X86_64.adx [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock :=
  (.block (fieldCode Impl.X25519.X86_64.baseline [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code rootAdjustBlockAdx :=
  (.block (fieldCode Impl.X25519.X86_64.adx [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block (recoverSuccess Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code successBlockAdx := (.block (recoverSuccess Impl.X25519.X86_64.adx) : Prog isa)
materialize_code pointEqualFirst := (.block (fieldCode Impl.X25519.X86_64.baseline pointEqualOps ++ fieldEqual Impl.X25519.X86_64.baseline 8 9) : Prog isa)
materialize_code pointEqualFirstAdx := (.block (fieldCode Impl.X25519.X86_64.adx pointEqualOps ++ fieldEqual Impl.X25519.X86_64.adx 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual Impl.X25519.X86_64.baseline 10 11) : Prog isa)
materialize_code pointEqualSecondAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 10 11) : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7424) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7552) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyScalarTail := (.block (loadScalarWords ++ scalarSubtract) : Prog isa)
materialize_code verifyFinishBlock :=
  (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore) : Prog isa)
materialize_code windowPrepLit :=
  (.seq (.seq (.seq (.block windowSetup) (aTable Impl.X25519.X86_64.baseline)) (.block bTable)) (.block (windowInit Impl.X25519.X86_64.baseline)) : Prog isa)
materialize_code windowPrepLitAdx :=
  (.seq (.seq (.seq (.block windowSetup) (aTable Impl.X25519.X86_64.adx)) (.block bTable)) (.block (windowInit Impl.X25519.X86_64.adx)) : Prog isa)
materialize_code addDigitA :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd Impl.X25519.X86_64.baseline)) :
    Prog isa)
materialize_code addDigitAAdx :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd Impl.X25519.X86_64.adx)) :
    Prog isa)
materialize_code addDigitB :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
    (pointAddCached Impl.X25519.X86_64.baseline)) : Prog isa)
materialize_code addDigitBAdx :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
    (pointAddCached Impl.X25519.X86_64.adx)) : Prog isa)
materialize_code negRBlock := (.block (negR Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code negRBlockAdx := (.block (negR Impl.X25519.X86_64.adx) : Prog isa)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks`. -/
section

/-! Fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem rdi_agree {base : Addr} {s t : State} (hs : s.gpr .rdi = base) (ht : t.gpr .rdi = base) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t := Taint.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) (recoverCandidate fld) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86_64.rdi_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86_64.rdi_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86_64.rdi_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (fieldCode fld [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86_64.rdi_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base)
      (.block (recoverSuccess fld)) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.X86_64.rdi_agree h.1 h.2

theorem recoverInvalid_ct : RelCT isa (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
  exact fun _ _ _ => Taint.agree_ofRegs (by simp)

end VG.Proof.Ed25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit`. -/
section

/-! A checked literal for the complete verification program. -/

namespace VG

materialize_code verifyEquationLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.baseline
  (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.baseline))
materialize_code verifyEquationAdxLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.adx))
materialize_code verifyEquationIfmaLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  Impl.Ed25519.X86_64.Ifma.double4)

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode`. -/
section

/-!
# Facts about the code of each registered verification

That every load of MXCSR restores it (`ctlOk`, the hypothesis of
`verify_verified`) and that no instruction writes the stack pointer, for each
field multiplication and doubling `vg_ed25519_verify_equation` is registered
with: evaluated once here, from the literals, for both the equation's own
artifacts and the generic verification over SHA-512 that calls it.
-/

namespace VG.Proof.Ed25519.X86_64.VerifyCode

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

theorem baseline_mx : ctlOk (verifyEquation Impl.X25519.X86_64.baseline
    (double4 Impl.X25519.X86_64.baseline)) = true := by lit_decide

theorem baseline_spSafe : (verifyEquation Impl.X25519.X86_64.baseline
    (double4 Impl.X25519.X86_64.baseline)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem adx_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx
    (double4 Impl.X25519.X86_64.adx)) = true := by lit_decide

theorem adx_spSafe : (verifyEquation Impl.X25519.X86_64.adx
    (double4 Impl.X25519.X86_64.adx)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

theorem ifma_mx : ctlOk (verifyEquation Impl.X25519.X86_64.adx Ifma.double4) = true := by
  lit_decide

theorem ifma_spSafe : (verifyEquation Impl.X25519.X86_64.adx Ifma.double4).all
    (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

end VG.Proof.Ed25519.X86_64.VerifyCode

end

end
