module

import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Ed25519.Arm.Point16
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Ed25519.Arm.AsFn`, which this module and modules that import it used -/

section

/-! ### `Ed25519.Arm.FieldOn`, which only this module used -/

section

/-!
# Ed25519 on ARMv7: field code on some of the slots

`fieldCode_ok` asks every slot's limbs to be below `2^16` (`AllLim`), which
the Ed25519 code keeps throughout. A function of point arithmetic may only
assume it of its operands: `LimOn m b S` asks it of the slots of `S`, and
`fieldCodeOn_ok` runs field code whose every operation reads only such slots
(`limsAfter`, decided on the slots), adding each operation's result to them,
and changes no memory but the slots `W` it writes and `ACC` (`wRegions`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- The slots of `S` hold limbs below `2^16`. -/
def LimOn (m : Mem) (b : BitVec 32) (S : List Slot) : Prop := ∀ i ∈ S, Lim m (State.addr b) (offset i)

theorem LimOn.mono {m : Mem} {b : BitVec 32} {S S' : List Slot} (h : LimOn m b S) (hs : ∀ i ∈ S', i ∈ S) :
    LimOn m b S' := fun i hi => h i (hs i hi)

theorem LimOn.of_all {m : Mem} {b : BitVec 32} (h : AllLim m b) (S : List Slot) : LimOn m b S :=
  fun i _ => h i

theorem LimOn.all {m : Mem} {b : BitVec 32} {S : List Slot} (h : LimOn m b S) (hs : ∀ i : Slot, i ∈ S) :
    AllLim m b := fun i => h i (hs i)

/-- The bytes of slot `i`. -/
abbrev slotR (b : BitVec 32) (i : Slot) : Region := ⟨State.addr b + BitVec.ofNat 64 (offset i), 64⟩

/-- The bytes of `ACC`. -/
abbrev accR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩

/-- What field code that writes the slots `W` changes: those slots and `ACC`. -/
def wRegions (b : BitVec 32) (W : List Slot) : List Region := W.map (slotR b) ++ [accR b]

theorem frame_w {b : BitVec 32} {o : Slot} {W : List Slot} (hw : o ∈ W) {m m' : Mem}
    (hf : Frame [slotR b o, accR b] m m') : Frame (wRegions b W) m m' := by
  refine hf.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hw), fun _ h => h⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩

/-- Each region of `wRegions` is bytes `[d, d + n)` of `[64, 1600)`. -/
theorem wRegions_bound {b : BitVec 32} {W : List Slot} {r : Region} (hr : r ∈ wRegions b W) :
    ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ 64 ≤ d ∧ d + n ≤ 1600 := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    have hi := slot_range i
    rw [ACC_eq] at hi
    exact ⟨_, _, rfl, hi.1, by omega_using [hi]⟩
  · exact ⟨ACC, 128, List.mem_singleton.mp hr, by rw [ACC_eq]; omega_using [], by rw [ACC_eq]⟩

/-- The slots an operation reads. -/
def opReads : FieldOp → List Slot
  | .copy _ a => [a]
  | .const _ _ => []
  | .mul _ a c | .mulc _ a c | .add _ a c | .sub _ a c => [a, c]

/-- The slot an operation writes. -/
def opOut : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o

/-- The slots with limbs below `2^16` after `ops`, from those of `S`, if each
operation is inlined and reads only such slots. -/
def limsAfter : List FieldOp → List Slot → Option (List Slot)
  | [], S => some S
  | op :: ops, S =>
    if op.inline && (opReads op).all S.contains then limsAfter ops (opOut op :: S) else none

theorem field_updateOn {b : BitVec 32} {m m' : Mem} (o : Slot) {S : List Slot} (hl : LimOn m b S)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m')
    (ho : Lim m' (State.addr b) (offset o)) :
    LimOn m' b (o :: S) ∧ env m' b = Function.update (env m b) o (FS m' (State.addr b) (offset o)) := by
  constructor
  · intro i hi
    by_cases hio : i = o
    · subst hio; exact ho
    · intro k hk
      rw [limb_slot_frame hio hf k hk]
      exact hl i ((List.mem_cons.mp hi).resolve_left hio) k hk
  · funext i
    by_cases hi : i = o
    · subst hi; simp only [Function.update_self, env]
    · rw [Function.update_of_ne hi]
      exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_slot_frame hi hf))

/-- An operation that reads only slots of `S`: it changes no register but
X25519's `clob` and no memory but `FA0`. -/
theorem fieldOpOn_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {S : List Slot} (hl : LimOn s.mem b S)
    (op : FieldOp) (hin : op.inline = true) (hr : ∀ i ∈ opReads op, i ∈ S) {W : List Slot}
    (hw : opOut op ∈ W) :
    WP isa op.code s fun t => Rest clob s t ∧ Frame (wRegions b W) s.mem t.mem ∧ LimOn t.mem b (opOut op :: S) ∧
      env t.mem b = evalOp op (env s.mem b) := by
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a (hr a List.mem_cons_self))) fun t ⟨hrt, hf, ho, hv⟩ => ?_
    obtain ⟨l, e⟩ := field_updateOn o hl (frame_o16 hf) ho
    rw [hv] at e
    exact ⟨hrt.mono (by decide), frame_w hw (frame_o hf), l, e⟩
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hrt, hf, ho, hv⟩ => ?_
    obtain ⟨l, e⟩ := field_updateOn o hl (frame_o16 hf) ho
    rw [hv] at e
    exact ⟨hrt.mono (by decide), frame_w hw (frame_o hf), l, e⟩
  | mul o a c =>
    refine WP.mono (mul_ok (by decide) (slot_range o).2 (slot_range a).2 (slot_range c).2 hc
      (hl a (hr a List.mem_cons_self)) (hl c (hr c (List.mem_cons_of_mem _ List.mem_cons_self))))
      fun t ⟨hrt, hf, ho, hv⟩ => ?_
    obtain ⟨l, e⟩ := field_updateOn o hl (frame_acc16 hf) ho
    have hv' : FS t.mem (State.addr b) (offset o) = _ := VG.Proof.X25519.toFe_mul hv
    rw [hv'] at e
    exact ⟨hrt, frame_w hw hf, l, e⟩
  | mulc => simp [FieldOp.inline] at hin
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]) (slot_sep o a) (slot_sep o c) hc
      (hl a (hr a List.mem_cons_self)) (hl c (hr c (List.mem_cons_of_mem _ List.mem_cons_self))))
      fun t ⟨hrt, hf, ho, hv⟩ => ?_
    obtain ⟨l, e⟩ := field_updateOn o hl (frame_o16 hf) ho
    have hv' : FS t.mem (State.addr b) (offset o) = _ := VG.Proof.X25519.toFe_add hv
    rw [hv'] at e
    exact ⟨hrt, frame_w hw (frame_o hf), l, e⟩
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]) (slot_sep o a) (slot_sep o c) hc
      (hl a (hr a List.mem_cons_self)) (hl c (hr c (List.mem_cons_of_mem _ List.mem_cons_self))))
      fun t ⟨hrt, hf, ho, hv⟩ => ?_
    obtain ⟨l, e⟩ := field_updateOn o hl (frame_o16 hf) ho
    have hv' : FS t.mem (State.addr b) (offset o) = _ := VG.Proof.X25519.toFe_sub hv
    rw [hv'] at e
    exact ⟨hrt, frame_w hw (frame_o hf), l, e⟩

/-- Field code whose every operation reads only slots with limbs below
`2^16` (`limsAfter ops S = some S'`) and writes a slot of `W`. -/
theorem fieldCodeOn_ok (ops : List FieldOp) {S S' : List Slot} (h : limsAfter ops S = some S')
    {W : List Slot} (hW : ∀ op ∈ ops, opOut op ∈ W)
    {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : LimOn s.mem b S) :
    WP isa (fieldCode ops) s fun t => Rest clob s t ∧ Frame (wRegions b W) s.mem t.mem ∧ LimOn t.mem b S' ∧
      env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s S with
  | nil =>
    cases h
    exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    simp only [limsAfter] at h
    split at h
    · rename_i hrd
      simp only [Bool.and_eq_true] at hrd
      rw [fieldCode, WP.seq_iff]
      refine WP.mono (fieldOpOn_ok hc hl op hrd.1 (fun i hi => by
          simpa using List.all_eq_true.mp hrd.2 i hi) (hW op List.mem_cons_self))
        fun t ⟨hrt, hft, hlt, et⟩ => ?_
      refine WP.mono (ih h (fun op hop => hW op (List.mem_cons_of_mem _ hop)) (hc.of_rest hrt (by decide)) hlt) fun u ⟨hru, hfu, hlu, eu⟩ => ?_
      exact ⟨hrt.trans hru, hft.trans hfu, hlu, by rw [eu, et]; rfl⟩
    · cases h

end VG.Proof.Ed25519.Arm

end

end


/-!
# Ed25519 on ARMv7: field code as a function

`asFn_ok`: field code that changes no memory but the slots it writes and
`ACC` (`wRegions`), from the slots `S` with limbs below `2^16` (`LimOn`), run as a function (`asFn`), between saving the callee-saved registers
it changes at `SAVE` and restoring them (`Spill`), computes what it computed
inline, and changes no register but `r1`–`r3`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem regSlots_ok (c : Bool) : Spill.Slots SAVE (SAVE + 28) (regSlots c) := by
  cases c <;> decide

theorem regSlots_restorable (c : Bool) : Spill.Restorable .r0 (regSlots c) := by
  cases c <;> decide

/-- The bytes of `SAVE` that `asFn` uses. -/
abbrev saveR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 SAVE, 28⟩

/-- The slots, `ACC` and `SAVE` are in `FA`. -/
theorem frameS_FA {b : BitVec 32} {W : List Slot} {m m' : Mem} (hf : Frame (wRegions b W ++ [saveR b]) m m') :
    Frame [FA b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨d, n, rfl, h1, h2⟩ := wRegions_bound hr
    exact Offset.sub _ h1 (by omega_using [h2])
  · rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by rw [SAVE_eq]; omega_using []) (by rw [SAVE_eq]; omega_using [])

/-- The registers a function made by `asFn` changes. -/
abbrev fnClob : List Reg := [.r1, .r2, .r3]

/-- Memory changed only above `ACC`'s 128 bytes keeps the elements. -/
theorem highFrame_limb {b : BitVec 32} {m m' : Mem} {o n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (ho : ACC + 128 ≤ o) (hn : o + n ≤ 8192)
    (i : Slot) :
    ∀ k < 16, limb m' (State.addr b) (offset i) k = limb m (State.addr b) (offset i) k :=
  limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    have hi := slot_range i
    rw [ACC_eq] at hi ho
    exact Offset.disjoint _ (.inl (by omega_using [ho, hk, hi])) (by omega_using [hk, hi]) (by omega_using [hn])

/-- `body` as a function: from the working space at `r0` with the limbs of
the slots of `S` below `2^16`, if `body` changes no register but `R` (each
either `r1`–`r3` or saved) and no memory but the slots `W` and `ACC`, and
maps the elements by `f`, then so does `asFn c body`, which changes no
register but `r1`–`r3` and no memory but those and `SAVE`. -/
theorem asFn_ok {b : BitVec 32} {c : Bool} {body : Prog isa} {R : List Reg} {f : Env → Env}
    {S S' W : List Slot}
    (hR : ∀ r ∈ R, r ∈ fnClob ∨ r ∈ (regSlots c).map Prod.fst)
    (hbody : ∀ s₁ : State, Ctx b s₁ → LimOn s₁.mem b S → WP isa body s₁ fun t =>
      Rest R s₁ t ∧ Frame (wRegions b W) s₁.mem t.mem ∧ LimOn t.mem b S' ∧ env t.mem b = f (env s₁.mem b))
    {s : State} (hc : Ctx b s) (hl : LimOn s.mem b S) :
    WP isa (asFn c body) s fun t =>
      Rest fnClob s t ∧ Frame (wRegions b W ++ [saveR b]) s.mem t.mem ∧ LimOn t.mem b S' ∧
        env t.mem b = f (env s.mem b) := by
  have hfit : b.toNat + 8192 ≤ 2 ^ 32 := hc.fit
  have hS := SAVE_eq
  have hA := ACC_eq
  have hB : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  rw [asFn, WP.seq_iff]
  rw [← List.append_nil (List.map _ (regSlots c))]
  refine Spill.save_slots_ok (regSlots_ok c) (by rw [hc.r0, hS]; omega_using [hfit])
    (fun d hd hd' => by rw [hB]; exact hc.inW (by rw [hS] at hd'; omega_using [hd'])) (WP.block_nil ?_)
  rw [hB]
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, SAVE + 28 - SAVE⟩] s.mem
      (Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c)) :=
    Spill.saveMem_frame_slots (regSlots_ok c) s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved (Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c)) (State.addr b) s.gpr
      (regSlots c) :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem (regSlots c) (regSlots_ok c)
  generalize Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c) = M1 at hf1 hsv1 ⊢
  have hlimb := highFrame_limb hf1 (by rw [hS, hA]) (by rw [hS]; omega_using [])
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : State, s₁ = { s with mem := M1 } := ⟨_, rfl⟩
  rw [← hs₁]
  have hm₁ : s₁.mem = M1 := by rw [hs₁]
  have hr₁ : Rest [] s s₁ := by rw [hs₁]; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have hc₁ : Ctx b s₁ := by rw [hs₁]; exact ⟨hc.r0, hc.fit, hc.wr⟩
  have hl₁ : LimOn s₁.mem b S := fun i hi k hk => by
    rw [hm₁, hlimb i k hk]; exact hl i hi k hk
  have he₁ : env s₁.mem b = env s.mem b := funext fun i => by
    rw [hm₁]; exact congrArg VG.Proof.X25519.toFe (val16_congr (hlimb i))
  refine WP.seq (WP.mono (hbody s₁ hc₁ hl₁) fun t ⟨hrt, hf, hlt, het⟩ => ?_)
  rw [hm₁] at hf
  have hct : Ctx b t := hc₁.of_rest (hrt.mono fun r h => h) (fun h => by
    rcases hR _ h with h | h <;> revert h <;> cases c <;> decide)
  have hsv : Spill.Saved t.mem (State.addr (t.gpr .r0)) s.gpr (regSlots c) := by
    rw [hct.r0]
    refine hsv1.frame (regSlots_ok c) hf fun r hr => ?_
    obtain ⟨d, n, rfl, h1, h2⟩ := wRegions_bound hr
    exact Offset.disjoint _ (.inr (by rw [hS]; omega_using [h2])) (by omega_using [hS]) (by omega_using [h2])
  refine WP.mono (Spill.restore_block_ok (regSlots_ok c) (regSlots_restorable c)
    (by rw [hct.r0, hS]; omega_using [hfit]) (fun d _ hd' => by rw [hct.r0]; exact hct.inR (by rw [hS] at hd'; omega_using [hd'])) hsv)
    fun u ⟨hres, hoth, hmu, hrd, hwr, hsp⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hrd, hrt.rd, hr₁.rd], by rw [hwr, hrt.wr, hr₁.wr], by rw [hsp, hrt.sp, hr₁.sp]⟩,
    ?_, ?_, ?_⟩
  · by_cases hm : r ∈ (regSlots c).map Prod.fst
    · exact Spill.restored_reg hres hm
    · rw [hoth r hm]
      exact (hrt.gpr r fun h => (hR r h).elim hr hm).trans (hr₁.gpr r (List.not_mem_nil))
  · rw [hmu]
    refine (hf1.sub fun r hr => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩).trans
      (hf.sub fun r hr => ⟨_, List.mem_append_left _ hr, fun _ h => h⟩)
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  · rw [hmu]; exact hlt
  · rw [hmu, het]; exact congrArg f he₁

end VG.Proof.Ed25519.Arm

end

end

/-!
# Ed25519 on ARMv7: calls of field code made a function

`fnCall_ok`: a call of a function on the working space at `r0` that, from
any state whose elements' limbs are below `2^16` (`AllLim`), changes no
register but `r1`–`r3` and no memory but `FA`, and maps the elements by `f`
(as `asFn_ok` proves of field code made a function), keeps what field code
keeps (`Keep`: a call also changes `lr`) and maps the elements by `f`. The
call runs on the working space alone (`WP.call`).

`addCall_ok` and `doubleCall_ok`: the calls of point addition and doubling,
as the inlined formulas (`fieldCode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- What `fnCall_ok` asks of the function, as a contract on the working space. -/
def fnK (b : BitVec 32) (f : Env → Env) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨State.addr b, 8192⟩] ∧ Ctx b t ∧ AllLim t.mem b
  post t t' := Rest fnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧ AllLim t'.mem b ∧
    env t'.mem b = f (env t.mem b)
  pub _ _ := True

theorem fnCall_ok {n : String} {c : Prog isa} {b : BitVec 32} {f : Env → Env}
    (hfn : ∀ s, Ctx b s → AllLim s.mem b → WP isa c s fun t => Rest fnClob s t ∧
      Frame [FA b] s.mem t.mem ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b))
    (hn : c.noCalls = true) {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (.call n c) s fun t => Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b) := by
  have hv : ∀ t, (fnK b f).pre t → ∃ tr t', Exec isa c t tr t' ∧ abiPreserved t t' ∧ (fnK b f).post t t' :=
    fun t ⟨_, _, ht, hlt⟩ => by
      obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := hfn t ht hlt
      exact ⟨tr, t', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hR, hF, hL, hV⟩
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s.callEntry.withRegions [] [⟨State.addr b, 8192⟩]).gpr q = s.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hcov : Covers [⟨State.addr b, 8192⟩] s.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hc.wr
  refine WP.call (k := fnK b f) hv (rd := []) (wr := [⟨State.addr b, 8192⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact hc.r0, hc.fit, List.mem_singleton_self _⟩,
      by rw [State.withRegions_mem, State.callEntry_mem]; exact hl⟩
    (Covers.right hcov) hcov ?_ hn
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hL, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hL hV
  refine ⟨⟨⟨fun q hq => ?_, hrd, hwr, hsp⟩, hF⟩, hL, hV⟩
  have hR' := hR.gpr q (by revert hq; cases q <;> decide)
  simp only [State.withRegions_gpr] at hR'
  rw [hR', State.callEntry_gpr _ (by revert hq; cases q <;> decide)]

/-- `limsAfter` keeps the slots it starts from. -/
theorem limsAfter_sup : ∀ {ops : List FieldOp} {S S' : List Slot}, limsAfter ops S = some S' →
    ∀ i ∈ S, i ∈ S'
  | [], _, _, h => by cases h; exact fun _ hi => hi
  | op :: ops, S, S', h => by
    simp only [limsAfter] at h
    split at h
    · exact fun i hi => limsAfter_sup h i (List.mem_cons_of_mem _ hi)
    · cases h

/-- Every slot. -/
def allSlots : List Slot := List.finRange 22

theorem mem_allSlots (i : Slot) : i ∈ allSlots := List.mem_finRange i

/-- `asFn_ok` for field code that every operation of which reads only
slots with limbs below `2^16`, from every slot's. -/
theorem asFnAll_ok {c : Bool} {ops : List FieldOp} {S' : List Slot} (h : limsAfter ops allSlots = some S')
    {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (asFn c (fieldCode ops)) s fun t => Rest fnClob s t ∧ Frame [FA b] s.mem t.mem ∧
      AllLim t.mem b ∧ env t.mem b = evalOps ops (env s.mem b) :=
  WP.mono (asFn_ok (R := clob) (fun r hr => by cases c <;> revert r <;> decide)
      (fun s₁ hc₁ hl₁ => fieldCodeOn_ok ops h (W := allSlots) (fun _ _ => mem_allSlots _) hc₁ hl₁) hc
      (LimOn.of_all hl allSlots))
    fun _ ⟨hr, hf, hl', he⟩ => ⟨hr, frameS_FA hf, hl'.all fun i => limsAfter_sup h i (mem_allSlots i), he⟩

/-- A call of `vg_ed25519_r16_point_add`, as the inlined addition. -/
theorem addCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa Point16.addCall s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps pointAddOps (env s.mem b) :=
  fnCall_ok (fun _ hc hl => asFnAll_ok rfl hc hl) (by decide +kernel) hc hl

/-- A call of `vg_ed25519_r16_point_double`, as the inlined doubling. -/
theorem doubleCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa Point16.doubleCall s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps pointDoubleOps (env s.mem b) :=
  fnCall_ok (fun _ hc hl => asFnAll_ok rfl hc hl) (by decide +kernel) hc hl

end VG.Proof.Ed25519.Arm
