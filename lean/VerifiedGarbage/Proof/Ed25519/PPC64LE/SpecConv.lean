module

public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.MulFn
public import VerifiedGarbage.Spec.Ed25519
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub

/-! ### `Ed25519.PPC64LE.Power`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.FieldProg`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: field programs

The slots as residues (`env`), what an operation does to them (`evalOp`),
and the code of a list of operations doing that (`fieldCode_ok`), keeping
every register but `fclob` and every byte outside the field area `FA`
(`Keep`). A call of `vg_gf25519_r32_mul` (`mulCall_ok`) is the inlined
product's equal. The extended Edwards addition of the slots is
`Spec.Ed25519.pointAdd` (`pointAdd_eval`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

abbrev Env := Slot → Spec.X25519.Fe

/-- The slots' elements. -/
def env (m : Mem) (b : Addr) : Env := fun i => FS m b (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b | .mulc o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

/-- The registers field code writes: X25519's, and those of a call of the product. -/
abbrev fclob : List Reg := [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

structure Keep (b : Addr) (s s' : State) : Prop where
  rest : Rest fclob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : Addr) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : Addr} {s t u : State} (h : Keep b s t) (k : Keep b t u) : Keep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : Addr} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

/-- An operation's frame: the result's slot and the product's limbs. -/
abbrev opFrame (b : Addr) (o : Nat) : List Region :=
  [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

theorem slot_frame {b : Addr} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame (opFrame b (offset o)) m m') : FS m' b (offset i) = FS m b (offset i) := by
  have hi := slot_range i
  have ho := slot_range o
  have hA := ACC_eq
  have hsep : offset i + 32 ≤ offset o ∨ offset o + 32 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega_arith
  refine congrArg Proof.X25519.toFe (val32_congr (limb_frame hf fun r hr k hk => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

theorem field_update {b : Addr} {m m' : Mem} (o : Slot) (hf : Frame (opFrame b (offset o)) m m') :
    env m' b = Function.update (env m b) o (FS m' b (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp only [Function.update_self, env]
  · rw [Function.update_of_ne hi]
    exact slot_frame hi hf

theorem frame_FA {b : Addr} {o : Slot} {m m' : Mem} (hf : Frame (opFrame b (offset o)) m m') :
    Frame [FA b] m m' := by
  have ho := slot_range o
  have hA := ACC_eq
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem frame_o {b : Addr} {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m m') :
    Frame (opFrame b o) m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem field_finish {b : Addr} {s t : State} (o : Slot) (hr : Rest fclob s t)
    (hf : Frame (opFrame b (offset o)) s.mem t.mem) {v : Spec.X25519.Fe}
    (hv : FS t.mem b (offset o) = v) :
    Keep b s t ∧ env t.mem b = Function.update (env s.mem b) o v := by
  rw [← hv]
  exact ⟨⟨hr, frame_FA hf⟩, field_update o hf⟩

/-! ## A call of the product -/

/-- What a call of `vg_gf25519_r32_mul` asks of the function: the working space's first 4096
bytes, and the offsets of `o`, `a` and `c` in `r4`–`r6`. -/
def mulK (b : Addr) (o a c : Slot) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨b, 4096⟩] ∧ Ctx3 b t ∧ (t.gpr .r4).toNat % 2 ^ 32 = offset o ∧
    (t.gpr .r5).toNat % 2 ^ 32 = offset a ∧ (t.gpr .r6).toNat % 2 ^ 32 = offset c
  post t t' := Rest mulFnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧
    env t'.mem b = Function.update (env t.mem b) o (env t.mem b a * env t.mem b c)
  pub _ _ := True

/-- `mulFn` keeps the ABI's registers and the link register. -/
theorem mulFn_abi {s s' : State} {t : List Leak} (he : VG.Exec isa mulFn s t s')
    (hr : Rest mulFnClob s s') : abiPreserved s s' :=
  ⟨fun r hr' => hr.gpr r (by revert hr'; cases r <;> decide), hr.sp,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩

theorem mulK_ok {b : Addr} (o a c : Slot) :
    ∀ t, (mulK b o a c).pre t → ∃ tr t', VG.Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧
      (mulK b o a c).post t t' := fun t ⟨_, _, ht, t4, t5, t6⟩ => by
  obtain ⟨tr, t', he, hR, hF, hV⟩ := mulFn_ok (slot_range o).2 (slot_range a).2 (slot_range c).2 ht t4 t5 t6
  refine ⟨tr, t', he, mulFn_abi he hR, hR, frame_FA hF, ?_⟩
  exact (field_update o hF).trans (congrArg _ (Proof.X25519.toFe_mul hV))

theorem offset_word (o : Slot) : (BitVec.ofNat 64 (offset o)).toNat % 2 ^ 32 = offset o := by
  have := slot_range o
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- **A call of `vg_gf25519_r32_mul`**, as the inlined product. -/
theorem mulCall_ok {b : Addr} {s : State} (hc : Ctx b s) (o a c : Slot) :
    WP isa (mulCall (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  obtain ⟨n, hn, hw⟩ := hc.wr
  unfold mulCall
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by omega_arith) fun s2 u2 =>
    wp_li (by omega_arith) fun s3 u3 => wp_li (by omega_arith) fun s4 u4 => WP.block_nil ?_)
  have hr4 : Rest [.r3, .r4, .r5, .r6] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have e3 : s4.gpr .r3 = b := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.r6]
    simp
  have e4 : s4.gpr .r4 = BitVec.ofNat 64 (offset o) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
  have e5 : s4.gpr .r5 = BitVec.ofNat 64 (offset a) := by rw [u4.other _ (by decide), u3.gpr]
  have e6 : s4.gpr .r6 = BitVec.ofNat 64 (offset c) := u4.gpr
  have g : ∀ q, q ∉ linkRegs → (s4.callEntry.withRegions [] [⟨b, 4096⟩]).gpr q = s4.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hsub : ∀ r ∈ ([⟨b, 4096⟩] : List Region), ∃ r' ∈ s4.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton.mp hr, hr4.wr]
    exact ⟨_, hw, 0, by simp, by simp only; omega_arith⟩
  refine WP.seq (WP.call (k := mulK b o a c) (mulK_ok o a c) (rd := []) (wr := [⟨b, 4096⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact e3, 4096, Nat.le_refl _, List.mem_singleton_self _⟩,
      by rw [g _ (by decide), e4]; exact offset_word o, by rw [g _ (by decide), e5]; exact offset_word a,
      by rw [g _ (by decide), e6]; exact offset_word c⟩
    (Covers.of_sub fun r hr => by
      obtain ⟨r', hr', h'⟩ := hsub r (by simpa using hr)
      exact ⟨r', List.mem_append_right _ hr', h'⟩)
    (Covers.of_sub hsub) ?_ (by decide +kernel))
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hV
  rw [hm4] at hF hV
  have hg : ∀ q, q ∉ mulFnClob → t.gpr q = s4.gpr q := fun q hq => by
    have := hR.gpr q hq
    simp only [State.withRegions_gpr] at this
    rw [this, State.callEntry_gpr _ (by revert hq; cases q <;> decide)]
  refine wp_addi (by decide) (by decide) fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · by_cases h6 : q = .r6
    · subst h6
      rw [v1.gpr, hg _ (by decide), e3, hc.r6]; simp
    · rw [v1.other _ h6, hg _ (by revert hq h6; cases q <;> decide), hr4.gpr _ (by revert hq h6; cases q <;> decide)]
  · rw [v1.rd, hrd, hr4.rd]
  · rw [v1.wr, hwr, hr4.wr]
  · rw [v1.sp, hsp, hr4.sp]
  · rw [v1.mem]; exact hF
  · rw [v1.mem]; exact hV

/-! ## Operations and programs -/

theorem fieldOp_ok {b : Addr} {s : State} (hc : Ctx b s) (op : FieldOp) :
    WP isa op.code s fun t => Keep b s t ∧ env t.mem b = evalOp op (env s.mem b) := by
  have hA := ACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) hf (Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : Addr} (hc : Ctx b s) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (fieldOp_ok hc op) fun t ⟨ht, et⟩ => ?_)
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-! ## Inline programs, framed by the slots they write -/

/-- The slot an operation writes. -/
def opOut : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o

/-- An inline operation changes no register but X25519's `clob`, and no memory but its result
and the product's limbs. -/
theorem fieldOpW_ok {b : Addr} {s : State} (hc : Ctx b s) (op : FieldOp) (hi : op.inline = true) :
    WP isa op.code s fun t => Rest clob s t ∧ Frame (opFrame b (offset (opOut op))) s.mem t.mem ∧
      env t.mem b = evalOp op (env s.mem b) := by
  have hA := ACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (frame_o hf), hv]; rfl
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (frame_o hf), hv]; rfl
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ =>
      ⟨hr, hf, ?_⟩
    rw [field_update o hf]; exact congrArg _ (Proof.X25519.toFe_mul hv)
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_sub hv)

/-- Inline field code, framed by any regions `R` that hold the results and the product's limbs. -/
theorem fieldCodeW_ok (ops : List FieldOp) (hi : ops.all FieldOp.inline = true) {b : Addr}
    (R : List Region) (hR : ∀ op ∈ ops, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ R, r.Sub r')
    {s : State} (hc : Ctx b s) :
    WP isa (fieldCode ops) s fun t =>
      Rest clob s t ∧ Frame R s.mem t.mem ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, rfl⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hi
    refine WP.seq (WP.mono (fieldOpW_ok hc op hi.1) fun t ⟨rt, ft, et⟩ => ?_)
    refine WP.mono (ih hi.2 (fun op' h' => hR op' (List.mem_cons_of_mem _ h')) (hc.of_rest rt (by decide)))
      fun u ⟨ru, fu, eu⟩ => ⟨rt.trans ru, (ft.sub (hR op List.mem_cons_self)).trans fu, by rw [eu, et]; rfl⟩

/-! ## The addition formula -/

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

/-- The sum of the points at slots 0–3 and 4–7, as the formula computes it. -/
def addResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 5 - e 4)
  let b := (e 1 + e 0) * (e 5 + e 4)
  let c := (e 3 * e 16 + e 3 * e 16) * e 7
  let dd := (e 2 + e 2) * e 6
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) : point (evalOps pointAddOps e) 0 1 2 3 = addResult e := rfl

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) := by
  rw [pointAdd_formula]
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: the addition chain to `z^(2^250 - 1)` and `z^11`

`chain250` with inlined products (`PSpec`): it changes no register but the
counter `r12` and X25519's `clob`, and no memory but bytes 512 to 1023 of the
working space (`PR`: slots 14 to 17 and the product's limbs), and maps the
slots by `power250Env`, whose slots 15 and 14 are `chainF`'s results.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- What the chain writes: bytes 512 to 1023 of the working space. -/
abbrev PR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 512, 512⟩

/-- `c` maps the slots by `f`, changing no register but `r12` and `clob`
and no memory but `PR`. -/
def PSpec (b : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → WP isa c s fun t =>
    Rest (.r12 :: clob) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = f (env s.mem b)

theorem PSpec.seq {b : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : PSpec b c₁ f) (h₂ : PSpec b c₂ g) : PSpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc => WP.seq (WP.mono (h₁ s hc) fun _ ⟨r₁, f₁, e₁⟩ =>
    WP.mono (h₂ _ (hc.of_rest r₁ (by decide))) fun _ ⟨r₂, f₂, e₂⟩ =>
      ⟨r₁.trans r₂, f₁.trans f₂, by rw [e₂, e₁]⟩)

theorem frame_PR {b : Addr} {o : Slot} (ho : 14 ≤ o.val) {m m' : Mem}
    (hf : Frame (opFrame b (offset o)) m m') : Frame [PR b] m m' := by
  have hs := slot_range o
  have hA := ACC_eq
  have ho' : 512 ≤ offset o := by simp only [offset]; omega_arith
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem mulP_ok {b : Addr} {s : State} (hc : Ctx b s) (o x y : Slot) (ho : 14 ≤ o.val) :
    WP isa (mulP o x y) s fun t =>
      Rest clob s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = opMul o x y (env s.mem b) := by
  have hA := ACC_eq
  have h1 := slot_range o
  have h2 := slot_range x
  have h3 := slot_range y
  have := slot_al o; have := slot_al x; have := slot_al y
  refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ =>
    ⟨hr, frame_PR ho hf, ?_⟩
  rw [field_update o hf]
  exact congrArg _ (Proof.X25519.toFe_mul hv)

theorem mulPS (b : Addr) (o x y : Slot) (ho : 14 ≤ o.val) : PSpec b (mulP o x y) (opMul o x y) :=
  fun _ hc => WP.mono (mulP_ok hc o x y ho) fun _ ⟨r, f, e⟩ => ⟨r.mono (by decide), f, e⟩

theorem sqLoop_ok {s₀ : State} {b : Addr} (hc : Ctx b s₀) (o : Slot) (ho : 14 ≤ o.val)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 15) :
    ∀ m s, 1 ≤ m → m ≤ n → Rest (.r12 :: clob) s₀ s → Frame [PR b] s₀.mem s.mem →
      s.gpr .r12 = BitVec.ofNat 64 m →
      env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subi .r12 .r12 1])) (.nonzero .d .r12)) s fun t =>
        Rest (.r12 :: clob) s₀ t ∧ Frame [PR b] s₀.mem t.mem ∧
        env t.mem b = Function.update (env s₀.mem b) o (sqn x n) := by
  intro m s h1 h2 hr hf hb he
  refine WP.loop (M := isa) (fun m (s : State) =>
    1 ≤ m ∧ m ≤ n ∧ Rest (.r12 :: clob) s₀ s ∧ Frame [PR b] s₀.mem s.mem ∧
    s.gpr .r12 = BitVec.ofNat 64 m ∧
    env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hr, hf, hb, he⟩
  intro m s ⟨h1, h2, hr, hf, hb, he⟩
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.seq (WP.mono (mulP_ok hcs o o o ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine wp_subi (by decide) (by decide) fun s2 u2 => WP.block_nil ?_
  have b2 : s2.gpr .r12 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, r1.gpr _ (by decide), hb, ofNat_sub_one h1 (by omega_arith)]
  have k2 : Rest (.r12 :: clob) s₀ s2 := hr.trans ((r1.mono (by decide)).trans (u2.rest (by decide)))
  have f2 : Frame [PR b] s₀.mem s2.mem := by rw [u2.mem]; exact hf.trans f1
  have e2 : env s2.mem b = Function.update (env s₀.mem b) o (sqn x (n - (m - 1))) := by
    rw [u2.mem, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem b) o)
    rw [show n - (m - 1) = (n - m) + 1 by omega_arith]
    rfl
  have hz : (s2.gpr .r12 != 0) = decide (m - 1 ≠ 0) := by rw [b2, ofNat_ne_zero (by omega_arith)]
  rw [eval_nonzero, hz]
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by simp [hm], k2, f2, by rw [e2, hm, Nat.sub_zero]⟩
  · exact .inr ⟨by simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, k2, f2, b2, e2⟩

theorem sqnS (b : Addr) (o a : Slot) (n : Nat) (ho : 14 ≤ o.val) (hn : 2 ≤ n) (hn' : n < 2 ^ 15) :
    PSpec b (Impl.Ed25519.PPC64LE.sqn o a n) (opSqn o a n) := by
  intro s hc
  refine WP.seq (WP.mono (mulP_ok hc o a a ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine WP.seq (wp_li (by omega_arith) fun s2 u2 => WP.block_nil ?_)
  have k2 : Rest (.r12 :: clob) s s2 := (r1.mono (by decide)).trans (u2.rest (by decide))
  refine sqLoop_ok hc o ho (env s.mem b a) n hn' (n - 1) s2 (by omega_arith) (by omega_arith) k2
    (by rw [u2.mem]; exact f1) u2.gpr ?_
  rw [u2.mem, e1, show n - (n - 1) = 1 by omega_arith]
  rfl

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem chain250S (b : Addr) : PSpec b chain250 power250Env :=
  (mulPS b 14 2 2 (by decide)).seq <|
  (mulPS b 15 14 14 (by decide)).seq <|
  (mulPS b 15 15 15 (by decide)).seq <|
  (mulPS b 15 2 15 (by decide)).seq <|
  (mulPS b 14 14 15 (by decide)).seq <|
  (mulPS b 16 14 14 (by decide)).seq <|
  (mulPS b 15 15 16 (by decide)).seq <|
  (sqnS b 16 15 5 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 20 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 100 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide))

theorem power250Env_eval (e : Env) :
    power250Env e 15 = (Proof.X25519.chainF (e 2)).1 ∧ power250Env e 14 = (Proof.X25519.chainF (e 2)).2 := by
  simp only [power250Env, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

/-- `vg_gf25519_r32_pow250`'s code, from the working space in `r3`. -/
theorem pow250Fn_ok {b : Addr} {s : State} (h3 : s.gpr .r3 = b)
    (hw : ∃ n, 4096 ≤ n ∧ (⟨b, n⟩ : Region) ∈ s.wr) :
    WP isa pow250Fn s fun t =>
      Rest (.r6 :: .r12 :: clob) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = power250Env (env s.mem b) := by
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc : Ctx b s1 := ⟨by rw [u1.gpr, h3]; simp, by rw [u1.wr]; exact hw⟩
  refine WP.mono (chain250S b s1 hc) fun t ⟨hr, hf, he⟩ => ⟨?_, by rw [u1.mem] at hf; exact hf, by rw [he, u1.mem]⟩
  exact (u1.rest (by decide)).trans (hr.mono (by decide))

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: the elements as the contracts read them

An element's 32 bytes, little-endian, are its eight words (`read_V`), so the
contracts' `valAt` and `elemAt` are the proofs' `V` and `FS` (`valAt_eq`,
`elemAt_eq`), and their `Keeps` follow from the frames of the code.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

theorem read_V (m : Mem) (b : Addr) (o : Nat) : (m.read (b + BitVec.ofNat 64 o) 32).toNat = V m b o := by
  have e : ∀ k, b + BitVec.ofNat 64 (o + 4 * k) = b + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) :=
    fun k => by rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [← Proof.X25519.leNum_bytesAt_read, Proof.X25519.leNum_bytesAt_words32]
  simp only [V, val32, limb, wd, e]
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  simp only [Nat.reduceMul, BitVec.add_zero]

theorem valAt_eq (m : Mem) (b : Addr) (o : BitVec 32) : Proof.X25519.Field32.valAt m b o = V m b o.toNat :=
  read_V m b o.toNat

theorem valAt_ofNat (m : Mem) (b : Addr) (i : Slot) :
    Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]

theorem elemAt_eq (m : Mem) (b : Addr) (i : Slot) :
    Proof.Ed25519.Point32.elemAt m b (offset i) = env m b i :=
  congrArg (Fin.ofNat P) (read_V m b (offset i))

theorem pointAt_eq (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.pAt = point (env m b) 0 1 2 3 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

theorem pointAt_q (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.qAt = point (env m b) 4 5 6 7 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

/-- A byte of the working space outside `[e, e + k)` is in no region of a frame there. -/
theorem byte_out {b : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨b + BitVec.ofNat 64 e, k⟩ : Region).Contains (b + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint b (d := i) (n := 1) (e := e) (k := k) (by omega_using [h]) (by omega_using [hi]) (by omega_using [he]) _ (Region.contains_self _ _) hc

/-- `pow250`'s `Keeps₂`, from its frame. -/
theorem keeps_pow {b : Addr} {m m' : Mem} (hf : Frame [PR b] m m') : Proof.X25519.Field32.Keeps₂ b m m' := by
  intro i hi hown
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd] at hi hown
  exact hf _ fun r hr => by rw [List.mem_singleton.mp hr]; exact byte_out (by omega_using [hi]) (by omega_using []) hown

/-- What the point addition writes: the sum, the temporaries and the product's limbs. -/
abbrev addW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 64, 128⟩, ⟨b + BitVec.ofNat 64 320, 256⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

/-- The point addition's `Keeps`, from its frame. -/
theorem keeps_add {b : Addr} {m m' : Mem} (hf : Frame (addW b) m m') : Proof.Ed25519.Point32.Keeps b m m' := by
  intro i hi hp ht ho
  simp only [Proof.Ed25519.Point32.wsBytes, Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes] at hi hp ht ho
  have hA := ACC_eq
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact byte_out (by omega_using [hi]) (by omega_using []) hp
  · exact byte_out (by omega_using [hi]) (by omega_using []) ht
  · exact byte_out (by omega_using [hi]) (by omega_using [hA]) (by omega_using [ho, hA])

/-- A power, as the contract states it. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = Proof.X25519.pw (env m b j) e) :
    V m' b (offset i) % P = V m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, Proof.X25519.toFe_val, Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

end VG.Proof.Ed25519.PPC64LE
