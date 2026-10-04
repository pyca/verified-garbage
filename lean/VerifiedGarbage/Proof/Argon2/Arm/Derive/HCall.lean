import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial

/-!
# Argon2 on ARMv7: calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` with its register arguments in
`r0`–`r3` and `scratch` (from `r12`) pushed with `lr`, from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 40 bytes below the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat pushed_arg pushed_argAddr frameCall_ok stkR_inner stkR_sub)
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_stack : armStack Impl.Argon2.Arm.HPrime.code = 32 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

/-- The registers `hPrimeCall` pushes. -/
abbrev hregs : List Reg := [.r12, .lr]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem call_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (call_stk hp)

theorem loc_call : (locR s₀).Disjoint (callR s₀) := by
  have hE := E_nat hp
  have := hp.sp_lo
  have := E_hi hp
  show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
  rw [← addr_sub' (by omega)]
  exact disj32 (.inr (by rw [sub_toNat' (by omega)]; omega)) (by omega) (by rw [sub_toNat' (by omega)]; omega)

theorem loc_sub_stk : Region.Sub (locR s₀) (stkR0 s₀) := by
  simpa using frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (loc_sub_stk hp)

/-- The regions H′ is given. -/
abbrev hRd (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩]
abbrev hWr (s₀ s : State) : List Region := [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀]

/-- What H′ needs, from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) (hdx : s.gpr .r12 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) :
    HPrime.hPrimeArm.pre ((pushed hregs s).callEntry.withRegions (hRd s) (hWr s₀ s)) ∧
      Covers (hRd s ++ hWr s₀ s) ((pushed hregs s).rd ++ (pushed hregs s).wr) ∧
      Covers (hWr s₀ s) (pushed hregs s).wr := by
  have hE := E_nat hp
  have hlo := hp.sp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega
  have a0 : ∀ {rd wr}, stackArg ((pushed hregs s).callEntry.withRegions rd wr) 0 = scrP s₀ := by
    intro rd wr; rw [pushed_arg hn (by decide)]; exact hdx
  have eA : ∀ {rd wr}, stackArgAddr ((pushed hregs s).callEntry.withRegions rd wr) 0 =
      State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length) := pushed_argAddr hn
  have eSp : ∀ {rd wr}, ((pushed hregs s).callEntry.withRegions rd wr).sp = s.sp - BitVec.ofNat 32 8 := by
    intro rd wr; simp [pushed_sp]
  have g : ∀ r, r ∉ linkRegs → ∀ {rd wr}, ((pushed hregs s).callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun r hr rd wr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  have cI : Covers [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  have I_scr : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  have S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack and argument.
  have cA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩ (callR s₀) := by
    rw [sp]
    show Region.Sub ⟨State.addr (E s₀) - BitVec.ofNat 64 8, 4⟩ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    have t8 : (E s₀ - BitVec.ofNat 32 8).toNat = (E s₀).toNat - 8 := sub_toNat' (by omega)
    have t40 : (E s₀ - BitVec.ofNat 32 40).toNat = (E s₀).toNat - 40 := sub_toNat' (by omega)
    rw [← addr_sub' (x := E s₀) (k := 8) (by omega), ← addr_sub' (x := E s₀) (k := 40) (by omega)]
    exact sub32 (by rw [t8, t40]; omega) (by rw [t8, t40]; omega)
  have cS : Region.Sub (stkR (E s₀ - BitVec.ofNat 32 8) 32) (callR s₀) :=
    stkR_inner (sp := E s₀) (a := 32) (k := 8) (b := 40) (by omega) (by omega)
  have cS' : Region.Sub (stkR (s.sp - BitVec.ofNat 32 8) 32) (callR s₀) := by rw [sp]; exact cS
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeArm, State.withRegions_rd, State.withRegions_wr, a0, eA, eSp,
      g .r0 (by decide), g .r1 (by decide), g .r2 (by decide), g .r3 (by decide)]
    refine ⟨trivial, trivial, I_scr, O_scr, O_call.symm.sub_left cA, S_call.symm.sub_left cA,
      I_call.symm.sub_left cS', O_call.symm.sub_left cS', S_call.symm.sub_left cS', hinfit, houtfit, by omega,
      ?_, ?_, hL⟩
    · rw [sub_toNat' (by omega), sp]; omega
    · rw [sub_toNat' (by omega), sp]; omega
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_rd, pushed_wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [addr_sub' hn]
      simp only [Region.Contains, List.length_cons, List.length_nil] at hc ⊢
      omega
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) (hdx : s.gpr .r12 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) →
      Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀, callR s₀] s.mem t.mem →
      bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        Spec.Argon2.hPrime (s.gpr .r3).toNat
          (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) → Q t) :
    WP isa Impl.Argon2.Arm.Derive.hPrimeCall s Q := by
  have hE := E_nat hp
  have hlo := hp.sp_lo
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  obtain ⟨pre, cv, cw⟩ := hcall_pre hp h hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine frameCall_ok (rs := hregs) (t := .r12) (by decide) (by decide) (by decide) (k := HPrime.hPrimeArm)
    HPrime.hPrime_verified.1 (K := 40) (by rw [hPrime_stack]; decide) (by rw [sp]; omega) pre cv cw
    fun t af post => ?_
  simp only [HPrime.hPrimeArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
    pushed_gpr] at post
  have bk : bytesAt (pushed hregs s).mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat :=
    bytes_keep (VG.Proof.Argon2.Arm.pushed_stk hn)
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right (by rw [sp]; exact stkR_sub (by decide) (by omega)))
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .r1).isLt (by decide)))
  rw [bk] at post
  have f₁ : Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀, callR s₀] s.mem
      (popped .r12 (4 * hregs.length) t).mem :=
    af.frame.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨callR s₀, by simp, by rw [sp]; exact fun _ h => h⟩
  refine k _ (h.step af.sp (af.cs .r11 (by decide) (by decide)) af.rd af.wr (f₁.sub fun q hq => ?_))
    (fun q hq hl => af.cs q hq hl) f₁ (by simpa [popped_mem] using post)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.Arm.Derive
