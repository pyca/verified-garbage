import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg

/-!
# Ed25519 on ARMv7: field code on some of the slots

`fieldCode_ok` asks every slot's limbs to be below `2^16` (`AllLim`), which
the Ed25519 code keeps throughout. A function of point arithmetic may only
assume it of its operands: `LimOn m b S` asks it of the slots of `S`, and
`fieldCodeOn_ok` runs field code whose every operation reads only such slots
(`limsAfter`, decided on the slots), adding each operation's result to them,
and changes no memory but the slots `W` it writes and `ACC` (`wRegions`).
-/

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
    exact ⟨_, _, rfl, hi.1, by omega⟩
  · exact ⟨ACC, 128, List.mem_singleton.mp hr, by rw [ACC_eq]; omega, by rw [ACC_eq]⟩

/-- The slots and `ACC` are in `FA0`. -/
theorem wRegions_FA0 {b : BitVec 32} {W : List Slot} {m m' : Mem} (hf : Frame (wRegions b W) m m') :
    Frame [FA0 b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  obtain ⟨d, n, rfl, h1, h2⟩ := wRegions_bound hr
  exact Offset.sub _ h1 (by rw [ACC_eq]; omega)

/-- The slots an operation reads. -/
def opReads : FieldOp → List Slot
  | .copy _ a => [a]
  | .const _ _ => []
  | .mul _ a c | .add _ a c | .sub _ a c => [a, c]

/-- The slot an operation writes. -/
def opOut : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .add o _ _ | .sub o _ _ => o

/-- The slots with limbs below `2^16` after `ops`, from those of `S`, if each
operation reads only such slots. -/
def limsAfter : List FieldOp → List Slot → Option (List Slot)
  | [], S => some S
  | op :: ops, S => if (opReads op).all S.contains then limsAfter ops (opOut op :: S) else none

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
    (op : FieldOp) (hr : ∀ i ∈ opReads op, i ∈ S) {W : List Slot} (hw : opOut op ∈ W) :
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
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc
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
    refine WP.mono (sub_ok (by omega) (by omega) (by omega) (slot_sep o a) (slot_sep o c) hc
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
      rw [fieldCode, WP.seq_iff]
      refine WP.mono (fieldOpOn_ok hc hl op (fun i hi => by
          simpa using List.all_eq_true.mp hrd i hi) (hW op List.mem_cons_self))
        fun t ⟨hrt, hft, hlt, et⟩ => ?_
      refine WP.mono (ih h (fun op hop => hW op (List.mem_cons_of_mem _ hop)) (hc.of_rest hrt (by decide)) hlt) fun u ⟨hru, hfu, hlu, eu⟩ => ?_
      exact ⟨hrt.trans hru, hft.trans hfu, hlu, by rw [eu, et]; rfl⟩
    · cases h

end VG.Proof.Ed25519.Arm
