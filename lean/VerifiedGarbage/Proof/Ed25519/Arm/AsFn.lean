import VerifiedGarbage.Impl.Ed25519.Arm.Point16
import VerifiedGarbage.Proof.Ed25519.Arm.FieldOn
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# Ed25519 on ARMv7: field code as a function

`asFn_ok`: field code that changes no memory but the slots it writes and
`ACC` (`wRegions`), from the slots `S` with limbs below `2^16` (`LimOn`), run as a function (`asFn`), between saving the callee-saved registers
it changes at `SAVE` and restoring them (`Spill`), computes what it computed
inline, and changes no register but `r1`–`r3`.
-/

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
    exact Offset.sub _ h1 (by omega)
  · rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by rw [SAVE_eq]; omega) (by rw [SAVE_eq]; omega)

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
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

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
  refine Spill.save_slots_ok (regSlots_ok c) (by rw [hc.r0, hS]; omega)
    (fun d hd hd' => by rw [hB]; exact hc.inW (by rw [hS] at hd'; omega)) (WP.block_nil ?_)
  rw [hB]
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, SAVE + 28 - SAVE⟩] s.mem
      (Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c)) :=
    Spill.saveMem_frame_slots (regSlots_ok c) s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved (Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c)) (State.addr b) s.gpr
      (regSlots c) :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem (regSlots c) (regSlots_ok c)
  generalize Spill.saveMem s.mem (State.addr b) s.gpr (regSlots c) = M1 at hf1 hsv1 ⊢
  have hlimb := highFrame_limb hf1 (by rw [hS, hA]) (by rw [hS]; omega)
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
    exact Offset.disjoint _ (.inr (by rw [hS]; omega)) (by omega) (by omega)
  refine WP.mono (Spill.restore_block_ok (regSlots_ok c) (regSlots_restorable c)
    (by rw [hct.r0, hS]; omega) (fun d _ hd' => by rw [hct.r0]; exact hct.inR (by rw [hS] at hd'; omega)) hsv)
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
