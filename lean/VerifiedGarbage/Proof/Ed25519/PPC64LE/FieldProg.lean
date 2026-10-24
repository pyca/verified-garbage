module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.MulFn
public import VerifiedGarbage.Spec.Ed25519
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

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
    omega
  refine congrArg Proof.X25519.toFe (val32_congr (limb_frame hf fun r hr k hk => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

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
  · exact Offset.sub _ (by omega) (by omega)
  · exact Offset.sub _ (by omega) (by omega)

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
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A call of `vg_gf25519_r32_mul`**, as the inlined product. -/
theorem mulCall_ok {b : Addr} {s : State} (hc : Ctx b s) (o a c : Slot) :
    WP isa (mulCall (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  obtain ⟨n, hn, hw⟩ := hc.wr
  unfold mulCall
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by omega) fun s2 u2 =>
    wp_li (by omega) fun s3 u3 => wp_li (by omega) fun s4 u4 => WP.block_nil ?_)
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
    exact ⟨_, hw, 0, by simp, by simp only; omega⟩
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
    refine WP.mono (mul_ok (by omega) (by omega) (by omega) (by omega) hc) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) hf (Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc)
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
    refine WP.mono (mul_ok (by omega) (by omega) (by omega) (by omega) hc) fun t ⟨hr, hf, hv⟩ =>
      ⟨hr, hf, ?_⟩
    rw [field_update o hf]; exact congrArg _ (Proof.X25519.toFe_mul hv)
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc)
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
