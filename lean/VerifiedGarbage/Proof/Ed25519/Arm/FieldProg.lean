module

import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Ed25519.Arm.MulFnRow
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Call
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.X25519.Arm.Slots
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Ed25519.Arm.MulFnFn`, which only this module used -/

section

/-!
# `vg_gf25519_r16_mul` on ARMv7: the function

Untrusted: everything here is checked by Lean. `mulFn_ok`: `mulBody_ok`
between saving the callee-saved registers the body changes (`r4`–`r11`) at
`SAVE` and restoring them (`Spill`): the function changes no register but
`r1`–`r3` and no memory but the result's and its own working space (`ACC`
and `SAVE`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)

theorem SAVE_eq : SAVE = 1600 := rfl

theorem mulSaved_ok : Spill.Slots SAVE (SAVE + 32) mulSaved := by decide

theorem mulSaved_restorable : Spill.Restorable .r0 mulSaved := by decide

/-- The registers `vg_gf25519_r16_mul` changes. -/
abbrev mulFnClob : List Reg := [.r1, .r2, .r3]

theorem mulClob_split : ∀ r, r ∉ mulFnClob → r ∉ mulSaved.map Prod.fst → r ∉ mulClob := by
  intro r; cases r <;> decide

/-- **`vg_gf25519_r16_mul`**: the product of `[x]` and `[y]` into `[o]`, the offsets in
`r1`–`r3`, saving and restoring the registers its body changes. -/
theorem mulFn_ok {e : Nat} {b : BitVec 32} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC)
    (hy : y + 64 ≤ ACC) {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 x) (h3 : s.gpr .r3 = BitVec.ofNat 32 y)
    (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa mulFn s fun t =>
      Rest mulFnClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  have hS := SAVE_eq
  have hA := ACC_eq
  have hB : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  rw [mulFn, WP.seq_iff]
  rw [← List.append_nil (List.map _ mulSaved)]
  refine Spill.save_slots_ok mulSaved_ok (by rw [hc.r0, hS]; omega_using [hfit])
    (fun d hd hd' => by rw [hB]; exact hc.inW (by rw [hS] at hd'; omega_using [hd'])) (WP.block_nil ?_)
  rw [hB]
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, SAVE + 32 - SAVE⟩] s.mem
      (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) :=
    Spill.saveMem_frame_slots mulSaved_ok s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) (State.addr b) s.gpr
      mulSaved :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem mulSaved mulSaved_ok
  generalize Spill.saveMem s.mem (State.addr b) s.gpr mulSaved = M1 at hf1 hsv1 ⊢
  have hlimb : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16, limb M1 (State.addr b) z k = limb s.mem (State.addr b) z k :=
    fun z hz => limb_frame hf1 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by rw [hS]; omega_using [hA, hz, hk])) (by omega_using [hA, hz, hk]) (by omega_using [hS])
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : State, s₁ = { s with mem := M1 } := ⟨_, rfl⟩
  rw [← hs₁]
  have hm₁ : s₁.mem = M1 := by rw [hs₁]
  have hg₁ : s₁.gpr = s.gpr := by rw [hs₁]
  have hc₁ : CtxN e b s₁ := by rw [hs₁]; exact ⟨hc.r0, hc.fit, hc.wr⟩
  have hlx₁ : Lim s₁.mem (State.addr b) x := fun k hk => by rw [hm₁, hlimb x hx k hk]; exact hlx k hk
  have hly₁ : Lim s₁.mem (State.addr b) y := fun k hk => by rw [hm₁, hlimb y hy k hk]; exact hly k hk
  have hV : ∀ z : Nat, z + 64 ≤ ACC → V s₁.mem (State.addr b) z = V s.mem (State.addr b) z :=
    fun z hz => by rw [hm₁]; exact val16_congr (hlimb z hz)
  refine WP.seq (WP.mono (mulBody_ok ho hx hy hc₁ (by rw [hg₁, h1]) (by rw [hg₁, h2])
    (by rw [hg₁, h3]) hlx₁ hly₁) fun t ⟨hrt, hf, hlt, hvt⟩ => ?_)
  rw [hm₁] at hf
  have hct : CtxN e b t := hc₁.of_rest hrt (by decide)
  have hsv : Spill.Saved t.mem (State.addr (t.gpr .r0)) s.gpr mulSaved := by
    rw [hct.r0]
    refine hsv1.frame mulSaved_ok hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega_using [ho, hA])) (by omega_using [hS]) (by omega_using [ho, hA])
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega_using [hA])) (by omega_using [hS]) (by omega_using [hA])
  refine WP.mono (Spill.restore_block_ok mulSaved_ok mulSaved_restorable
    (by rw [hct.r0, hS]; omega_using [hfit]) (fun d _ hd' => by rw [hct.r0]; exact hct.inR (by rw [hS] at hd'; omega_using [hd'])) hsv)
    fun u ⟨hres, hoth, hmu, hrd, hwr, hsp⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hrd, hrt.rd, hs₁], by rw [hwr, hrt.wr, hs₁], by rw [hsp, hrt.sp, hs₁]⟩,
    ?_, by rw [hmu]; exact hlt, ?_⟩
  · by_cases hm : r ∈ mulSaved.map Prod.fst
    · exact Spill.restored_reg hres hm
    · rw [hoth r hm, hrt.gpr r (mulClob_split r hr hm), hg₁]
  · rw [hmu]
    refine (hf1.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by rw [hS]; omega_using [hA]) (by rw [hS]; omega_using [hA])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · rw [hmu, hvt, hV x hx, hV y hy]

end VG.Proof.Ed25519.Arm

end

end


/-! Compositional field programs and the extended Edwards formulas. -/

@[expose] public section

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
    omega_arith
  rw [ACC_eq] at hi ho
  refine limb_frame hf fun r hr k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by rw [ACC_eq]; omega_arith)) (by omega_arith) (by rw [ACC_eq]; omega_arith)

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
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

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
  omega_arith

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
    obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := mulFn_ok (by omega_arith) (by omega_arith) (by omega_arith) ht t1 t2 t3
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
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
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
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
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

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega_arith⟩
  let y := e ⟨q + 1, by omega_arith⟩
  let z := e ⟨q + 2, by omega_arith⟩
  let t := e ⟨q + 3, by omega_arith⟩
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
      (point e ⟨q, by omega_arith⟩ ⟨q + 1, by omega_arith⟩ ⟨q + 2, by omega_arith⟩ ⟨q + 3, hq⟩) := by
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
