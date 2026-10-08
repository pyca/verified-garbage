import VerifiedGarbage.Proof.Blowfish.AArch64.F

/-!
# One round on sixteen blocks

`round_run`: `round sch up L R`, with `x5` at Pᵢ₊₁ in the schedule at `sch`,
leaves `L ^ Pᵢ₊₁` in `L` and `R ^ F(L ^ Pᵢ₊₁)` in `R`, word by word, and
moves `x5` to the next entry (`up`) or the previous one.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- Only the general-purpose registers `gs` and the vector registers `vs` change. -/
structure Only (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with gpr := s'.gpr, v := s'.v }
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem Only.refl (gs : List Reg) (vs : List VReg) (s : State) : Only gs vs s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Only.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : Only gs vs a b) (h₂ : Only gs vs b c) :
    Only gs vs a c := by
  refine ⟨?_, fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem Only.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : Only gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : Only gs' vs' a b :=
  ⟨h.eq, fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h')⟩

theorem Only.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : Only [] vs a b := by
  refine ⟨?_, fun r _ => ?_, h.2⟩
  · rw [h.1]
  · rw [h.1]

theorem Only.mem {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.mem = a.mem := by
  rw [h.eq]
theorem Only.rd {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.rd = a.rd := by
  rw [h.eq]
theorem Only.wr {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.wr = a.wr := by
  rw [h.eq]
theorem Only.sp {gs : List Reg} {vs : List VReg} {a b : State} (h : Only gs vs a b) : b.sp = a.sp := by
  rw [h.eq]

/-- The schedule at `sch` is readable. -/
def SchedIn (s : State) (sch : Reg) : Prop :=
  ∀ off n, off + n ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr sch + BitVec.ofNat 64 off) n

theorem SchedIn.readable {s : State} {sch : Reg} (h : SchedIn s sch) : Readable s sch :=
  fun off hoff => h off 16 (by omega)

/-- The registers of the halves. -/
def halfRegs : List VReg := [.v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11]

/-- What a round writes: `v0` and the registers of `planes` and `f`, and the halves. -/
def roundRegs : List VReg := .v0 :: planesRegs ++ stepRegs ++ halfRegs

/-- Halves `L` and `R`: `A` and `B` (`v4`–`v11`), in either role. -/
structure Halves (L R : Nat → VReg) : Prop where
  inL : ∀ k < 4, L k ∈ halfRegs
  inR : ∀ k < 4, R k ∈ halfRegs
  injL : ∀ k < 4, ∀ k' < 4, k ≠ k' → L k ≠ L k'
  injR : ∀ k < 4, ∀ k' < 4, k ≠ k' → R k ≠ R k'
  ne : ∀ k < 4, ∀ k' < 4, L k ≠ R k'

theorem halves_ab : Halves aReg bReg := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem halves_ba : Halves bReg aReg := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem half_notin : ∀ r ∈ halfRegs, r ∉ planesRegs ∧ r ∉ stepRegs ∧ r ≠ .v0 := by decide

/-- XOR of a register with `v0`, for each of the four registers of a half `H`. -/
def xorHalf (H : Nat → VReg) (S : Nat → VReg) : List Instr :=
  (List.range 4).map fun k => veor (H k) (H k) (S k)

theorem xorHalf_run (s : State) {H S : Nat → VReg} (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → H k ≠ H k')
    (hS : ∀ k < 4, ∀ k' < 4, S k ≠ H k') :
    ∃ s', runBlock isa (xorHalf H S) s = some s' ∧
      (∀ k < 4, s'.v (H k) = s.v (H k) ^^^ s.v (S k)) ∧ Only [] [H 0, H 1, H 2, H 3] s s' := by
  let t (k : Nat) (u : State) := u.setV (H k) (u.v (H k) ^^^ u.v (S k))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  refine ⟨s₄, ?_, ?_, ?_⟩
  · have e : ∀ k (u : State), exec (veor (H k) (H k) (S k)) u = some (t k u) := fun _ _ => rfl
    show runBlock isa [veor (H 0) (H 0) (S 0), veor (H 1) (H 1) (S 1), veor (H 2) (H 2) (S 2),
      veor (H 3) (H 3) (S 3)] s = _
    rw [runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some, runBlock_cons, e, runStep_some,
      runBlock_cons, e, runStep_some, runBlock_nil]
  · have hh : ∀ k < 4, ∀ k' < 4, k ≠ k' → ∀ u : State, (t k' u).v (H k) = u.v (H k) :=
      fun k hk k' hk' hne u => v_setV_of_ne _ _ (hinj k hk k' hk' hne)
    have hs : ∀ k < 4, ∀ k' < 4, ∀ u : State, (t k' u).v (S k) = u.v (S k) :=
      fun k hk k' hk' u => v_setV_of_ne _ _ (hS k hk k' hk')
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [hh 0 (by decide) 3 (by decide) (by decide), hh 0 (by decide) 2 (by decide) (by decide),
        hh 0 (by decide) 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [hh 1 (by decide) 3 (by decide) (by decide), hh 1 (by decide) 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, hh 1 (by decide) 0 (by decide) (by decide), hs 1 (by decide) 0 (by decide)]
    · rw [hh 2 (by decide) 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, hh 2 (by decide) 1 (by decide) (by decide), hh 2 (by decide) 0 (by decide) (by decide),
        hs 2 (by decide) 1 (by decide), hs 2 (by decide) 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, hh 3 (by decide) 2 (by decide) (by decide), hh 3 (by decide) 1 (by decide) (by decide),
        hh 3 (by decide) 0 (by decide) (by decide), hs 3 (by decide) 2 (by decide),
        hs 3 (by decide) 1 (by decide), hs 3 (by decide) 0 (by decide)]
  · exact Only.ofV ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _))

theorem round_eq (sch : Reg) (up : Bool) (L R : Nat → VReg) :
    round sch up L R = loadP ++ xorHalf L (fun _ => .v0) ++ planes L ++ f sch ++ xorHalf R fReg ++
      [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] := rfl

theorem quarter_lane (x : BitVec 128) {n j : Nat} (hj : j < 4) :
    vbyte x (4 * (n % 4) + (3 - j)) = quarter (vword x (n % 4)) j := by
  rw [vbyte_word _ (by omega)]; rfl

theorem fReg_ne_half : ∀ k < 4, ∀ r ∈ halfRegs, fReg k ≠ r := by decide

theorem round_run {s : State} {sch : Reg} (hS : SchedIn s sch) (hc : Consts s) (up : Bool)
    {L R : Nat → VReg} (H : Halves L R) {i : Nat} (hi : i < 18)
    (hx5 : s.gpr .x5 = s.gpr sch + BitVec.ofNat 64 (4 * i)) (hsch : sch ≠ .x5 ∧ sch ≠ .x6) :
    ∃ s', runBlock isa (round sch up L R) s = some s' ∧
      (∀ n < 16, lane s'.v L n = lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i) ∧
      (∀ n < 16, lane s'.v R n = lane s.v R n ^^^
        Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (lane s.v L n ^^^ pEntry (scheduleAt s.mem (s.gpr sch)) i)) ∧
      s'.gpr .x5 = (if up then s.gpr .x5 + 4 else s.gpr .x5 - 4) ∧
      Only [.x5, .x6] roundRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  let p := pEntry K i
  -- the P-array entry
  have hp : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 pOff) 4 := by
    rw [hx5, Offset.add_add]; exact hS _ _ (by simp only [pOff]; omega)
  have hread : s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32 = p := by
    rw [hx5, Offset.add_add, show 4 * i + pOff = 4096 + 4 * i by simp only [pOff]; omega]
    exact (pEntry_read _ _ hi).symm
  let s₁ := s.write .w .x6 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 pOff) 32)
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  have r₂ : runBlock isa loadP s = some s₂ := by
    rw [loadP, runBlock_cons, exec_ldr_w (by simp only [pOff]; decide) hp, runStep_some, runBlock_cons,
      exec_dup4, runStep_some, runBlock_nil]
  have v0₂ : ∀ l < 4, vword (s₂.v .v0) l = p := by
    intro l hl
    simp only [s₂, v_setV_self]
    rw [vword_ofVWords _ _ _ _ hl]
    have : (s₁.gpr .x6).setWidth 32 = p := by
      simp only [s₁, gpr_write_self, ← hread]; exact BitVec.setWidth_setWidth_of_le _ (by omega) |>.trans (by simp)
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> exact this
  have o₂ : Only [.x6] [.v0] s s₂ := by
    refine ⟨rfl, fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr
      simp only [s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
    · simp only [List.mem_singleton] at hr
      exact v_setV_of_ne _ _ hr
  have hL := fun k hk => half_notin _ (H.inL k hk)
  have hR := fun k hk => half_notin _ (H.inR k hk)
  -- L ^= P
  obtain ⟨s₃, r₃, v₃, o₃⟩ := xorHalf_run s₂ H.injL (S := fun _ => .v0) fun k _ k' hk' => (hL k' hk').2.2.symm
  have L₃ : ∀ n < 16, lane s₃.v L n = lane s.v L n ^^^ p := by
    intro n hn
    simp only [lane]
    rw [v₃ _ (by omega), vword_xor, v0₂ _ (by omega), o₂.v _ (by simp; exact (hL _ (by omega)).2.2)]
  -- the planes
  obtain ⟨s₄, r₄, v₄, o₄⟩ := planes_run s₃ L fun k hk => (hL k hk).1
  -- F
  have o₂₄ : Only [.x6] roundRegs s s₄ := (o₂.mono (by simp) (by simp [roundRegs])).trans
    ((o₃.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inL _ (by decide))).trans
      ((Only.ofV o₄).mono (by simp) (fun r hr => by simp [roundRegs, hr])))
  have hS₄ : Readable s₄ sch := fun off hoff => by
    rw [o₂₄.rd, o₂₄.wr, o₂₄.g _ (by simp; exact hsch.2)]; exact hS.readable off hoff
  have hc₄ : Consts s₄ := by
    have n64 : c64 ∉ roundRegs := by decide
    have n128 : c128 ∉ roundRegs := by decide
    exact ⟨fun e he => by rw [o₂₄.v _ n64]; exact hc.1 e he, fun e he => by rw [o₂₄.v _ n128]; exact hc.2 e he⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := f_run hS₄ hc₄ (lane s₃.v L) fun j hj n hn => by
    rw [v₄ j hj n hn, quarter_lane _ hj]; rfl
  have K₅ : scheduleAt s₄.mem (s₄.gpr sch) = K := by
    rw [o₂₄.mem, o₂₄.g _ (by simp; exact hsch.2)]
  -- R ^= F
  obtain ⟨s₆, r₆, v₆, o₆⟩ := xorHalf_run s₅ H.injR (S := fReg) fun k hk k' hk' =>
    fReg_ne_half k hk _ (H.inR k' hk')
  let s₇ := s₆.write .x .x5 (if up then s₆.read .x .x5 + BitVec.ofNat _ 4 else s₆.read .x .x5 - BitVec.ofNat _ 4)
  have r₇ : runBlock isa [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] s₆ = some s₇ := by
    cases up
    · rw [runBlock_cons]; simp only [Bool.false_eq_true, ite_false]
      rw [exec_subImm_x (by decide), runStep_some, runBlock_nil]; rfl
    · rw [runBlock_cons]; simp only [ite_true]
      rw [exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
  have o₂₆ : Only [.x6] roundRegs s s₆ := o₂₄.trans (((Only.ofV o₅).mono (by simp) (fun r hr => by simp [roundRegs, hr])).trans
    (o₆.mono (by simp) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h <;> subst h <;>
          exact List.mem_append_right _ (H.inR _ (by decide))))
  have o₇ : Only [.x5, .x6] roundRegs s s₇ := by
    refine (o₂₆.mono (by simp) (fun _ h => h)).trans ⟨rfl, fun r hr => ?_, fun _ _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₇, gpr_write_of_ne _ _ _ hr.1]
  refine ⟨s₇, ?_, ?_, ?_, ?_, o₇⟩
  · rw [round_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
      (VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some
        (VG.AArch64.Tbl.runBlock_cat_some r₂ r₃) r₄) r₅) r₆) r₇
  · intro n hn
    have hk : n / 4 < 4 := by omega
    have nr : ∀ k < 4, L k ∉ [R 0, R 1, R 2, R 3] := fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨H.ne k hk 0 (by decide), H.ne k hk 1 (by decide), H.ne k hk 2 (by decide), H.ne k hk 3 (by decide)⟩
    simp only [lane] at L₃ ⊢
    rw [show s₇.v = s₆.v from rfl, o₆.v _ (nr _ hk), o₅.2 _ (hL _ hk).2.1, o₄.2 _ (hL _ hk).1, L₃ n hn]
  · intro n hn
    have hk : n / 4 < 4 := by omega
    have nl : R (n / 4) ∉ [L 0, L 1, L 2, L 3] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(H.ne 0 (by decide) _ hk).symm, (H.ne 1 (by decide) _ hk).symm,
        (H.ne 2 (by decide) _ hk).symm, (H.ne 3 (by decide) _ hk).symm⟩
    have hRv : s₅.v (R (n / 4)) = s.v (R (n / 4)) := by
      rw [o₅.2 _ (hR _ hk).2.1, o₄.2 _ (hR _ hk).1, o₃.v _ nl,
        o₂.v _ (by simp; exact (hR _ hk).2.2)]
    have L₃n := L₃ n hn
    simp only [lane] at v₅ L₃n ⊢
    rw [show s₇.v = s₆.v from rfl, v₆ _ hk, vword_xor, v₅ n hn, K₅, L₃n, hRv]
  · simp only [s₇, gpr_write_self, State.read, BitVec.setWidth_eq]
    rw [o₂₆.g _ (by simp)]
    cases up <;> rfl

end VG.Proof.Blowfish.AArch64
