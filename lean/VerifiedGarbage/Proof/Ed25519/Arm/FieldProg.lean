import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFn
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Covers
import Mathlib.Logic.Function.Basic

/-! Compositional field programs and the extended Edwards formulas. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (b : BitVec 32) : Env := fun i => FS m (State.addr b) (offset i)

def AllLim (m : Mem) (b : BitVec 32) : Prop := ∀ i : Slot, Lim m (State.addr b) (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b | .mulc o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure Keep (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest fclob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : BitVec 32) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : BitVec 32} {s t u : State} (h : Keep b s t) (k : Keep b t u) :
    Keep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : BitVec 32} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

theorem limb_slot_frame {b : BitVec 32} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m') :
    ∀ k < 16, limb m' (State.addr b) (offset i) k = limb m (State.addr b) (offset i) k := by
  have hi := slot_range i
  have ho := slot_range o
  have hsep : offset i + 64 ≤ offset o ∨ offset o + 64 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega
  rw [ACC_eq] at hi ho
  refine limb_frame hf fun r hr k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by rw [ACC_eq]; omega)) (by omega) (by rw [ACC_eq]; omega)

theorem field_update {b : BitVec 32} {m m' : Mem} (o : Slot) (hl : AllLim m b)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m')
    (ho : Lim m' (State.addr b) (offset o)) :
    AllLim m' b ∧ env m' b = Function.update (env m b) o (FS m' (State.addr b) (offset o)) := by
  constructor
  · intro i
    by_cases hi : i = o
    · subst hi; exact ho
    · intro k hk
      rw [limb_slot_frame hi hf k hk]
      exact hl i k hk
  · funext i
    by_cases hi : i = o
    · subst hi; simp only [Function.update_self, env]
    · rw [Function.update_of_ne hi]
      exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_slot_frame hi hf))

/-- An operation's frame at `o` and in the product's own working space is
within the field area. -/
theorem frame_FA16 {b : BitVec 32} {o : Slot} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m') : Frame [FA b] m m' := by
  have ho := slot_range o
  have hA := ACC_eq
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega) (by omega)
  · exact Offset.sub _ (by omega) (by omega)

/-- The product's frame, within an operation's. -/
theorem frame_acc16 {b : BitVec 32} {o : Nat} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m' := by
  refine hf.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩

/-- A frame at `o` alone, as an operation's. -/
theorem frame_o16 {b : BitVec 32} {o : Nat} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem field_finish {b : BitVec 32} {s t : State} (o : Slot) (hl : AllLim s.mem b)
    (hr : Rest fclob s t)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem)
    (ho : Lim t.mem (State.addr b) (offset o)) {v : Spec.X25519.Fe}
    (hv : FS t.mem (State.addr b) (offset o) = v) :
    Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = Function.update (env s.mem b) o v := by
  obtain ⟨hlim, he⟩ := field_update o hl hf ho
  rw [hv] at he
  exact ⟨⟨hr, frame_FA16 hf⟩, hlim, he⟩

/-- What a call of `vg_gf25519_r16_mul` asks of the function, as a contract on the working
space: `o`, `a` and `c`'s offsets in `r1`–`r3`. -/
def mulK (b : BitVec 32) (o a c : Slot) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨State.addr b, 8192⟩] ∧ Ctx b t ∧ AllLim t.mem b ∧
    t.gpr .r1 = BitVec.ofNat 32 (offset o) ∧ t.gpr .r2 = BitVec.ofNat 32 (offset a) ∧
    t.gpr .r3 = BitVec.ofNat 32 (offset c)
  post t t' := Rest mulFnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧ AllLim t'.mem b ∧
    env t'.mem b = Function.update (env t.mem b) o (env t.mem b a * env t.mem b c)
  pub _ _ := True

theorem movw_offset (o : Slot) : ((BitVec.ofNat 16 (offset o)).setWidth 32) = BitVec.ofNat 32 (offset o) := by
  have := slot_range o
  rw [ACC_eq] at this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- **A call of `vg_gf25519_r16_mul`**, as the inlined product. -/
theorem mulCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) (o a c : Slot) :
    WP isa (mulCall (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  have hA := ACC_eq
  unfold mulCall
  rw [WP.seq_iff]
  refine wp_movw fun s1 u1 => wp_movw fun s2 u2 => wp_movw fun s3 u3 => WP.block_nil ?_
  have hr3 : Rest [.r1, .r2, .r3] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hl3 : AllLim s3.mem b := by rw [hm3]; exact hl
  have e1 : s3.gpr .r1 = BitVec.ofNat 32 (offset o) := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, movw_offset]
  have e2 : s3.gpr .r2 = BitVec.ofNat 32 (offset a) := by
    rw [u3.other _ (by decide), u2.gpr, movw_offset]
  have e3 : s3.gpr .r3 = BitVec.ofNat 32 (offset c) := by rw [u3.gpr, movw_offset]
  have hv : ∀ t, (mulK b o a c).pre t → ∃ tr t', Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧
      (mulK b o a c).post t t' := fun t ⟨_, _, ht, hlt, t1, t2, t3⟩ => by
    obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := mulFn_ok (by omega) (by omega) (by omega) ht t1 t2 t3
      (hlt a) (hlt c)
    obtain ⟨hlim, henv⟩ := field_update o hlt hF hL
    exact ⟨tr, t', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hR,
      frame_FA16 hF, hlim, henv.trans (congrArg _ (VG.Proof.X25519.toFe_mul hV))⟩
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s3.callEntry.withRegions [] [⟨State.addr b, 8192⟩]).gpr q = s3.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hcov : Covers [⟨State.addr b, 8192⟩] s3.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hc3.wr
  refine WP.call (k := mulK b o a c) hv (rd := []) (wr := [⟨State.addr b, 8192⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact hc3.r0, hc3.fit, List.mem_singleton_self _⟩,
      by rw [State.withRegions_mem, State.callEntry_mem]; exact hl3,
      by rw [g _ (by decide)]; exact e1, by rw [g _ (by decide)]; exact e2,
      by rw [g _ (by decide)]; exact e3⟩
    (Covers.right hcov) hcov ?_ (by decide +kernel)
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hL, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hL hV
  rw [hm3] at hF hV
  refine ⟨⟨⟨fun q hq => ?_, hrd.trans hr3.rd, hwr.trans hr3.wr, hsp.trans hr3.sp⟩, hF⟩, hL, hV⟩
  have h3 : q ∉ ([.r1, .r2, .r3] : List Reg) := by revert hq; cases q <;> decide
  have hR' := hR.gpr q h3
  simp only [State.withRegions_gpr] at hR'
  rw [hR', State.callEntry_gpr _ (by revert hq; cases q <;> decide), hr3.gpr q h3]

theorem fieldOp_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (op : FieldOp) :
    WP isa op.code s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOp op (env s.mem b) := by
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
  | mul o a c =>
    refine WP.mono (mul_ok (by decide) (slot_range o).2 (slot_range a).2 (slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_acc16 hf) ho (VG.Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc hl o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    refine WP.mono (fieldOp_ok hc hl op) fun t ⟨ht, hlt, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc) hlt) fun u ⟨hu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hlu, by rw [eu, et]; rfl⟩

/-- The field area without `SAVE`, `[64, 1600)`: what field code, which calls
nothing, changes. -/
abbrev FA0 (b : BitVec 32) : Region := Proof.X25519.Arm.FA ACC b

/-- `fieldOp_ok`, which also changes no register but X25519's `clob` and no
memory but `FA0`: an operation calls nothing. -/
theorem fieldOpFree_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (op : FieldOp) (hi : op.inline = true) :
    WP isa op.code s fun t => Keep b s t ∧ Rest clob s t ∧ Frame [FA0 b] s.mem t.mem ∧ AllLim t.mem b ∧
      env t.mem b = evalOp op (env s.mem b) := by
  have hs (o : Slot) := slot_range o
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
    exact ⟨k, hr.mono (by decide), frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
    exact ⟨k, hr.mono (by decide), frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | mul o a c =>
    refine WP.mono (mul_ok (by decide) (slot_range o).2 (slot_range a).2 (slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_acc16 hf) ho (VG.Proof.X25519.toFe_mul hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) hf, l, e⟩
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_sub hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) (frame_o hf), l, e⟩

/-- `fieldCode_ok`, which also changes no register but X25519's `clob` and no
memory but `FA0`. -/
theorem fieldCodeFree_ok (ops : List FieldOp) (hi : ops.all FieldOp.inline = true) {s : State}
    {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ Rest clob s t ∧ Frame [FA0 b] s.mem t.mem ∧
      AllLim t.mem b ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, Rest.refl _ _, Frame.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    simp only [List.all_cons, Bool.and_eq_true] at hi
    refine WP.mono (fieldOpFree_ok hc hl op hi.1) fun t ⟨ht, hrt, hft, hlt, et⟩ => ?_
    refine WP.mono (ih hi.2 (ht.ctx hc) hlt) fun u ⟨hu, hru, hfu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hrt.trans hru, hft.trans hfu, hlu, by rw [eu, et]; rfl⟩

theorem constField_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o v := fieldOp_ok hc hl (.const o v)

theorem copyField_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a) := fieldOp_ok hc hl (.copy o a)

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

end VG.Proof.Ed25519.Arm
