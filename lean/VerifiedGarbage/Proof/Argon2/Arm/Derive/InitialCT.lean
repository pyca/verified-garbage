import VerifiedGarbage.Proof.Argon2.Arm.Derive.CTCall

/-!
# Argon2 on ARMv7: H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- Composition, with what each run satisfies after the first part. -/
theorem RelCT.seqW {F₁ F₂ G₁ G₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c₁ fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c₁ s G₁) (w₂ : ∀ s, F₂ s → WP isa c₁ s G₂)
    (h₂ : RelCT isa (fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂) c₂ Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq c₁ c₂) Q :=
  RelCT.seq (rel_wp h₁ w₁ w₂) h₂

/-- A branch on a condition that agrees in both runs. -/
theorem RelCT.iteF {F₁ F₂ : State → Prop} {c : Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) th Q) (he : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) el Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.ite c th el) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h.1 h.2) (ht.mono (fun _ _ h => h.1) fun _ _ h => h)
    (he.mono (fun _ _ h => h.1) fun _ _ h => h)

theorem slotsOkE (rs : List Reg) : VG.Arm.Taint.SlotsOk (τB [] rs) := by
  intro x hx
  simp only [τB, List.nil_append, List.mem_singleton] at hx
  subst hx; simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A piece the taint analysis proves from the arguments and the registers
`rs`, which both runs agree on. -/
theorem leafI {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf [] [] rs (slotsOkE rs) (fun _ h => (List.not_mem_nil h).elim)
    (fun s₁ s₂ h => let ⟨i₁, i₂, hr⟩ := hag s₁ s₂ h; ⟨i₁, i₂, fun _ h => (List.not_mem_nil h).elim, hr⟩) hc

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : Inv s₀₂ s) (hb : s.gpr .r4 = scrP s₀₂) : Ctx (scrP s₀₁) (E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.Arm.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => stA_ok T.hp₁ h.1 h.2) (fun s h => stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := scrP s₀₁) (SP := E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => stInit_ok T.hp₁ h) (fun s h => stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t ∧ t.gpr .r4 = scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀₁)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀₁) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₁))
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t ∧ t.gpr .r4 = scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀₂)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀₂) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀₂))
    (fun s h => (header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := scrP s₀₁) (SP := E s₀₁) (offset := 768) (size := 24)
      (by decide) (by decide) (by omega) (by decide) (by decide) (stk_scr T.hp₁ (by decide) (by decide))
      ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨ctx T.hp₁ h.1.1 h.1.2.2.1, scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => stFix_ok T.hp₁ h) (fun s h => stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈ [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁])
    (hR₂ : (⟨State.addr (arg s₀₂ ptr), (arg s₀₂ len).toNat⟩ : Region) ∈ [pwR s₀₂, saltR s₀₂, secR s₀₂, adR s₀₂])
    (hfit₁ : (arg s₀₁ ptr).toNat + (arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (arg s₀₂ ptr).toNat + (arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (τB [] [.r4]) (.block [ld .r0 (argOff len), .str .r0 .r4 792,
      ld .r2 countLoOff, ld .r3 countHiOff, .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (τB [] []) (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr))) hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (τB [] [])
      (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) (Impl.Argon2.Arm.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : State.addr (scrP s₀₁ + 792) = State.addr (scrP s₀₁) + BitVec.ofNat 64 792 :=
    scr_addr T.hp₁ (o := 792) (by decide)
  have cov792 : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      Covers [⟨State.addr (scrP s₀ + 792), 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    rw [show State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 from
      scr_addr hp (o := 792) (by decide)]
    exact Covers.right (scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, DPre s₀ → Inv s₀ s →
      (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀] →
      Covers [⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
        [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, memR s₀₁, scrR s₀₁, outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨State.addr (arg s₀₁ ptr), (arg s₀₁ len).toNat⟩ : Region) ∈
      [pwR s₀₁, saltR s₀₁, secR s₀₁, adR s₀₁, argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.Arm.Derive.absorb
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.r4, h.2.r4, T.pb.scrP_eq]⟩) hcA)
    (fun s h => absA_ok T.hp₁ hlen h.hc) (fun s h => absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (SP := E s₀₁) (D := scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (scrP s₀₁ + 792).toNat = (scrP s₀₁).toNat + 792 := add_nat (k := 792) (by omega)
          omega)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => absU1_ok T.hp₁ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => absU1_ok T.hp₂ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => absB_ok T.hp₁ hptr hlen (by omega) h) (fun s h => absB_ok T.hp₂ hptr hlen (by omega) h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := scrP s₀₁) (SP := E s₀₁) (D := arg s₀₁ ptr)
      (L := (arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => call_stk T.hp₁ a (stk32_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => HI s₀₁ data₁ s₁ ∧ HI s₀₂ data₂ s₂) Impl.Argon2.Arm.Derive.finish
      fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fiA_ok T.hp₁ h) (fun s h => fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := scrP s₀₁) (SP := E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨ctx T.hp₁ g₁.inv g₁.r4, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.r4, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁) ∧ (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.code fun _ _ => True := by
  have l1 := (arg s₀₁ 2).isLt
  have l2 := (arg s₀₁ 4).isLt
  have l3 := (arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (arg s₀₂ 2).toNat = (arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (arg s₀₂ 4).toNat = (arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (arg s₀₂ 10).toNat = (arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (arg s₀₂ 12).toNat = (arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.Arm.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => start_ok T.hp₁ h.1 h.2) (fun s h => start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]; omega) h)
    (fun s h => absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt_length]
          have := (arg s₀₂ 2).isLt; have := (arg s₀₂ 4).isLt; have := (arg s₀₂ 10).isLt; omega) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.Arm.Derive
