import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Impl.Ed25519.X86.Point32
import VerifiedGarbage.TCB.X86.Target

/-!
# `vg_ed25519_r32_point_add` on x86 (32-bit): what it computes

From its entry (`Entry`: the working space `ws` at `x`, its argument on the
stack), `entry` saves `ebx`, `ebp` and `edi` at `SAVE` and points `edi` at
the working space (`entry_ok`); the body is the inlined addition
(`fieldCode pointAddOps`), whose values `pointAdd_eval` gives, and which
writes only its outputs, slots 0–3 and 8–15, and X25519's product `T`
(`fieldCode_frame`); `exit` restores the registers (`exit_ok`). `addFn_ok`:
the function keeps the callee-saved registers, changes memory only in slots
0–3 and 8–15 and bytes 864 to 1023, and leaves in slots 0–3 the sum of the
points in slots 0–3 and 4–7, if slot 16 holds `d`.
-/

namespace VG.Proof.Ed25519.X86.Point32

variable {c : Bool}

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.Ed25519.X86.Point32 VG.Proof.Ed25519.X86
open VG.Impl.X25519.X86 (T)

/-- The function's entry: the working space `ws = x` (its argument), writable
for 8192 bytes and within the 32-bit address space; the argument readable,
and the return address apart from the working space. -/
structure Entry (s : State) (x : BitVec 32) : Prop where
  ws : arg s 0 = x
  fit : x.toNat + 8192 ≤ 2 ^ 32
  wr : scR 8192 x ∈ s.wr
  read : InRegions (s.rd ++ s.wr) (argAddr s 0) 4

/-- The registers saved at `SAVE`. -/
structure Saved (x : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop where
  ebx : wd m x SAVE = g .ebx
  ebp : wd m x (SAVE + 4) = g .ebp
  edi : wd m x (SAVE + 8) = g .edi

theorem entry_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (.block entry) s fun t => Ctx x t false ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .esp = s.gpr .esp ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [sub x SAVE 12] s.mem t.mem ∧ Saved x s.gpr t.mem := by
  have hfit := h.fit
  refine Wp.wp_ldm (b := .esp) (o := 4 + 4 * 0) rfl h.read fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = x := by rw [u₁.gpr]; exact h.ws
  refine Wp.wp_stm e₁ ⟨_, by rw [u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact e₁)
    ⟨_, by rw [u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁)
    ⟨_, by rw [u₃.wr, u₂.wr, u₁.wr]; exact h.wr, scR_contains hfit (by decide) (by decide)⟩ fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = ((s.mem.writeW (addr x SAVE) (s.gpr .ebx)).writeW (addr x (SAVE + 4)) (s.gpr .ebp)).writeW
      (addr x (SAVE + 8)) (s.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.other .ebx (by decide)]
  have g₅ : ∀ r, r ≠ .eax → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₅.other _ h2, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ h1]
  refine ⟨⟨by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁, hfit,
      by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr, by decide, nofun⟩,
    g₅ _ (by decide) (by decide), g₅ _ (by decide) (by decide),
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [m₅]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
      |>.writeW (List.mem_singleton_self _) _ ?_ <;>
    exact sub_contains (by simp only [SAVE]; omega_using [hfit]) (by decide) (by decide) (by decide)
  · rw [m₅]
    refine ⟨?_, ?_, ?_⟩
    · rw [wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide),
        wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide), wd_write_self]
    · rw [wd_write_ne _ _ (by simp only [SAVE]; omega_using [hfit]) (by simp only [SAVE]; omega_using [hfit])
        (by decide), wd_write_self]
    · rw [wd_write_self]

/-- A field operation writes only its output and `T`. -/
theorem fieldOp_frame {s : State} {x : BitVec 32} (hc : Ctx x s c) (op : FieldOp) :
    WP isa (.block op.code) s fun t => Frame [sub x (offset (fieldDest op)) 32, sub x T 64] s.mem t.mem := by
  have wide : ∀ {o : Nat} {m m' : Mem}, Frame [sub x o 32] m m' → Frame [sub x o 32, sub x T 64] m m' :=
    fun hf => hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  cases op with
  | const o v => exact WP.mono (constField_op hc o v) fun _ ⟨_, f, _⟩ => wide f
  | copy o a =>
    exact WP.mono (VG.Proof.X25519.X86.copy_ok hc (slot_below (slot_valid o)) (slot_below (slot_valid a))
      (VG.Proof.X25519.X86.slot_apart (slot_valid o) (slot_valid a))) fun _ ⟨_, f, _⟩ => wide f
  | mul o a b =>
    exact WP.mono (VG.Proof.X25519.X86.mul_ok hc (slot_below (slot_valid o)) (slot_below (slot_valid a))
      (slot_below (slot_valid b))) fun _ ⟨_, f, _⟩ => f
  | add o a b =>
    exact WP.mono (VG.Proof.X25519.X86.add_ok hc (slot_below (slot_valid o)) (slot_below (slot_valid a))
      (slot_below (slot_valid b)) (VG.Proof.X25519.X86.slot_apart (slot_valid o) (slot_valid a))
      (VG.Proof.X25519.X86.slot_apart (slot_valid o) (slot_valid b))) fun _ ⟨_, f, _⟩ => wide f
  | sub o a b =>
    exact WP.mono (VG.Proof.X25519.X86.sub_ok hc (slot_below (slot_valid o)) (slot_below (slot_valid a))
      (slot_below (slot_valid b)) (VG.Proof.X25519.X86.slot_apart (slot_valid o) (slot_valid a))
      (VG.Proof.X25519.X86.slot_apart (slot_valid o) (slot_valid b))) fun _ ⟨_, f, _⟩ => wide f

/-- Field operations write only within the regions `R` that contain their
outputs and `T`. -/
theorem fieldCode_frame {x : BitVec 32} (R : List Region) : ∀ (ops : List FieldOp) {s : State}, Ctx x s c →
    (∀ op ∈ ops, ∀ r ∈ [sub x (offset (fieldDest op)) 32, sub x T 64], ∃ r' ∈ R, Region.Sub r r') →
    WP isa (.block (fieldCode ops)) s fun t => Frame R s.mem t.mem
  | [], _, _, _ => WP.block_nil (Frame.refl _ _)
  | op :: ops, s, hc, hR => by
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (WP.and (fieldOp_frame hc op) (fieldOp_ok hc op)) fun t ⟨f, k, _⟩ => ?_
    refine WP.mono (fieldCode_frame R ops (k.ctx hc) fun o ho => hR o (List.mem_cons_of_mem _ ho))
      fun u fu => ?_
    exact (f.sub fun r hr => hR op List.mem_cons_self r hr).trans fu

/-- The regions the addition writes: slots 0–3, slots 8–15, and bytes 864 to 1023. -/
abbrev addW (x : BitVec 32) : List Region := [sub x 64 128, sub x 320 256, sub x T 160]

/-- The regions the body writes: slots 0–3, slots 8–15, and `T`. -/
abbrev bodyW (x : BitVec 32) : List Region := [sub x 64 128, sub x 320 256, sub x T 64]

/-- A function's program writes only slots 0–3 and 8–15. -/
abbrev DestsOk (ops : List FieldOp) : Prop :=
  ∀ op ∈ ops, (64 ≤ offset (fieldDest op) ∧ offset (fieldDest op) + 32 ≤ 192) ∨
    (320 ≤ offset (fieldDest op) ∧ offset (fieldDest op) + 32 ≤ 576)

theorem pointAddOps_dests : DestsOk pointAddOps := by decide

theorem pointAddAffineOps_dests : DestsOk pointAddAffineOps := by decide

theorem pointDoubleRfcOps_dests : DestsOk pointDoubleRfcOps := by decide

theorem ops_frame {ops : List FieldOp} (hd : DestsOk ops) {s : State} {x : BitVec 32} (hc : Ctx x s c) :
    WP isa (.block (fieldCode ops)) s fun t => Frame (bodyW x) s.mem t.mem := by
  have hfit := hc.fit
  refine fieldCode_frame _ ops hc fun op hop r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hd op hop with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit h₁ (by omega_using [h₂]) (by omega_using [h₂])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_sub hfit h₁ (by omega_using [h₂])
        (by omega_using [h₂])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem exit_ok {u : State} {x : BitVec 32} {g : Reg → BitVec 32} (hc : Ctx x u c) (hsv : Saved x g u.mem) :
    WP isa (.block exit) u fun v => v.gpr .ebx = g .ebx ∧ v.gpr .ebp = g .ebp ∧ v.gpr .edi = g .edi ∧
      v.gpr .esi = u.gpr .esi ∧ v.gpr .esp = u.gpr .esp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.mem = u.mem := by
  have hfit := hc.fit
  refine Wp.wp_mov fun u₁ v₁ => ?_
  have edx₁ : u₁.gpr .edx = x := by rw [v₁.gpr, hc.edi]
  have rin : ∀ d, d + 4 ≤ 8192 → InRegions (u₁.rd ++ u₁.wr) (addr x d) 4 := fun d hd =>
    ⟨_, List.mem_append_right _ (by rw [v₁.wr]; exact hc.wr), scR_contains hfit hd (by decide)⟩
  refine Wp.wp_ldm (B := x) (o := SAVE) edx₁ (rin _ (by decide)) fun u₂ v₂ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 4) (by rw [v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₃ v₃ => ?_
  refine Wp.wp_ldm (B := x) (o := SAVE + 8) (by rw [v₃.other _ (by decide), v₂.other _ (by decide)]; exact edx₁)
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr]; exact rin _ (by decide)) fun u₄ v₄ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr],
    by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]⟩
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem]; exact hsv.ebx
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem]; exact hsv.ebp
  · rw [v₄.gpr, v₃.mem, v₂.mem, v₁.mem]; exact hsv.edi
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)]

/-- The body keeps the saved registers. -/
theorem Saved.body {x : BitVec 32} (hfit : x.toNat + 8192 ≤ 2 ^ 32) {g : Reg → BitVec 32} {m m' : Mem}
    (h : Saved x g m) (hf : Frame (bodyW x) m m') : Saved x g m' := by
  have k : ∀ d, SAVE ≤ d → d + 4 ≤ SAVE + 12 → wd m' x d = wd m x d := fun d h₁ h₂ =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [SAVE] at h₁ h₂
      rcases hr with rfl | rfl | rfl
      · exact sub_disj (by omega_using [hfit, h₂]) (by omega_using [hfit]) (.inr (by omega))
      · exact sub_disj (by omega_using [hfit, h₂]) (by omega_using [hfit]) (.inr (by omega))
      · exact sub_disj (by omega_using [hfit, h₂]) (by simp only [T]; omega_using [hfit])
          (.inr (by simp only [T]; omega))
  exact ⟨(k _ (by decide) (by decide)).trans h.ebx, (k _ (by decide) (by decide)).trans h.ebp,
    (k _ (by decide) (by decide)).trans h.edi⟩

/-- The slots, through a frame of `SAVE`. -/
theorem env_save {x : BitVec 32} (hfit : x.toNat + 8192 ≤ 2 ^ 32) {m m' : Mem}
    (hf : Frame [sub x SAVE 12] m m') : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 hf hfit (by decide) (by simp only [offset]; omega)
    (.inl (by simp only [offset, SAVE]; omega))

/-- A function running the field program `ops`: the callee-saved registers kept, memory
changed only in slots 0–3 and 8–15 and bytes 864 to 1023, and the slots' values `evalOps ops`
of theirs. -/
theorem fnOf_ok {ops : List FieldOp} (hd : DestsOk ops) {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa (fnOf ops) s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame (addW x) s.mem t.mem ∧ env t.mem x = evalOps ops (env s.mem x) := by
  have hfit := h.fit
  rw [fnOf, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entry_ok h) fun t ⟨hc, esi, esp, rd, wr, hf, hsv⟩ => ?_
  refine WP.mono (WP.and (ops_frame hd hc) (fieldCode_ok ops hc)) fun u ⟨fu, ku, eu⟩ => ?_
  refine WP.mono (exit_ok (ku.ctx hc) (hsv.body hfit fu)) fun v ⟨rb, rp, ri, rs, re, rr, rw', rm⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [rr, ku.keep.rd, rd], by rw [rw', ku.keep.wr, wr], ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rb
    · rw [rs, ku.keep.esi, esi]
    · exact ri
    · exact rp
    · rw [re, ku.keep.esp, esp]
  · rw [rm]
    refine (hf.sub fun r hr => ?_).trans (fu.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        sub_sub hfit (by simp only [T, SAVE]; decide) (by simp only [T, SAVE]; decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          sub_sub hfit (Nat.le_refl _) (by simp only [T]; decide) (by simp only [T]; decide)⟩
  · rw [rm, eu, env_save hfit hf]

theorem addFn_ok {s : State} {x : BitVec 32} (h : Entry s x) :
    WP isa addFn s fun t => (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame (addW x) s.mem t.mem ∧
      (env s.mem x 16 = Spec.Ed25519.d → point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 4 5 6 7)) :=
  WP.mono (fnOf_ok pointAddOps_dests h) fun _ ⟨hk, hrd, hwr, hf, hv⟩ =>
    ⟨hk, hrd, hwr, hf, fun hd => by rw [hv]; exact pointAdd_eval _ hd⟩

/-! ## The new functions' values -/

/-- What `pointAddAffineOps` computes, from the accumulator's coordinates and the cached
entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffine_formula (e : Env) :
    point (evalOps pointAddAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := rfl

/-- What `pointDoubleRfcOps` computes. -/
def dblResult (e : Env) : Spec.Ed25519.Point :=
  let a := e 0 * e 0
  let b := e 1 * e 1
  let c := e 2 * e 2 + e 2 * e 2
  let ee := e 0 * e 1 + e 0 * e 1
  let g := b - a
  let f := g - c
  let h := g - b - b
  ⟨ee * f, g * h, f * g, ee * h⟩

theorem dbl_formula (e : Env) : point (evalOps pointDoubleRfcOps e) 0 1 2 3 = dblResult e := rfl

/-- `pointDoubleRfcOps` computes RFC 8032's doubling. -/
theorem dbl_eval (e : Env) :
    point (evalOps pointDoubleRfcOps e) 0 1 2 3 = Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3) := by
  rw [dbl_formula]
  simp only [dblResult, Spec.Ed25519.Point64.pointDouble, point]
  congr 1 <;> grind

end VG.Proof.Ed25519.X86.Point32
