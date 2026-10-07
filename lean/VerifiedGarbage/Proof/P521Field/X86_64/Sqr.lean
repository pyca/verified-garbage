import VerifiedGarbage.Proof.P521Field.X86_64.Mul

/-!
# P-521's field squaring as a function, x86-64: correctness

`vg_p521_sqr_mont_adx` (`sqrCode`) meets `sqrC`, the contract
`Spec.P521.sqrMontContract` gives on x86-64 (with 40 bytes of stack for the
five saved registers), as `vg_p521_mul_mont_adx` does its (`Mul.lean`).
-/

namespace VG.Proof.P521Field.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.P521Field.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- The registers `vg_p521_sqr_mont_adx` saves. -/
abbrev sqrRegs : List Reg := [.rbp, .r12, .r13, .r14, .r15]

/-- `vg_p521_sqr_mont_adx`'s contract on x86-64: `Spec.P521.sqrMontContract`
as `Sig.contract` evaluates it with 40 bytes of stack. -/
def sqrC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 72⟩
    let a : Region := ⟨s.gpr .rsi, 72⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 40, 40⟩
    s.rd = [a] ∧ s.wr = [out] ∧ out.Disjoint a ∧ ret.Disjoint out ∧ ret.Disjoint a ∧
      stk.Disjoint out ∧ stk.Disjoint a ∧ 40 ≤ (s.gpr .rsp).toNat ∧
      (s.gpr .rdi).toNat + 72 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 72 ≤ 2 ^ 64 ∧
      Spec.P521.feAt s.mem (s.gpr .rsi) < Spec.P521.p
  post s s' :=
    Spec.P521.feAt s'.mem (s.gpr .rdi) < Spec.P521.p ∧
      Spec.P521.feAt s'.mem (s.gpr .rdi) * Spec.P521.montR % Spec.P521.p =
        Spec.P521.feAt s.mem (s.gpr .rsi) * Spec.P521.feAt s.mem (s.gpr .rsi) % Spec.P521.p
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

theorem sqr_correct (s : State) (h : sqrC.pre s) :
    WP isa sqrCode s fun s' => gprPreserved s s' ∧ sqrC.post s s' := by
  obtain ⟨hrd, hwr, hoa, hro, hra, hso, hsa, hsp, hwo, hwa, hB⟩ := h
  generalize hO : s.gpr .rdi = o at *
  generalize hA : s.gpr .rsi = pa at *
  generalize hS : s.gpr .rsp = S at *
  have notSp : Reg.rsp ∉ sqrRegs := by decide
  have hnd : sqrRegs.Nodup := by decide
  refine frames_ok s sqrRegs (.block sqrBody) _ notSp (by simpa [hS] using hsp) ?_
  -- The body's state.
  let s₀ := framesStart s sqrRegs
  have g₀ : ∀ r, r ≠ .rsp → s₀.gpr r = s.gpr r := fun r h => framesStart_gpr s sqrRegs h
  have sp₀ : s₀.gpr .rsp = S - BitVec.ofNat 64 40 := by
    rw [framesStart_rsp, hS]; rfl
  have F₀ : Frame [below S 40] s.mem s₀.mem := by
    have := framesStart_frame s sqrRegs notSp (by simpa [hS] using hsp)
    rwa [hS] at this
  have stk : ∀ r ∈ [below S 40], ∀ R : Region, R.Disjoint ⟨S - BitVec.ofNat 64 40, 40⟩ →
      R.Disjoint r := fun r hr R h => by
    simp only [List.mem_singleton] at hr; subst hr; exact h
  have hs₀ : ScrC s₀ o 72 0 :=
    ⟨by rw [g₀ _ (by decide), hO, off_zero], framesStart_wr s sqrRegs (by rw [hwr]; exact List.mem_singleton_self _),
      hwo⟩
  have hpa₀ : PtrC s₀ .rsi pa 72 0 :=
    ⟨by rw [g₀ _ (by decide), hA, off_zero], by rw [framesStart_rd, hrd]; simp, hwa, Or.inr (Or.inl rfl)⟩
  have hA₀ : wordsVal s₀.mem pa 0 9 = wordsVal s.mem pa 0 9 :=
    wordsVal_of_frame F₀ (stk · · _ hsa.symm) hwa 0 9 (by decide)
  refine WP.mono (sqrBody_ok hs₀ hpa₀ (apart_of_disjoint hoa.symm)
    (by rw [hA₀, ← feAt_eq]; exact hB)) fun t ⟨lt, eq, k, O⟩ => ?_
  have spt : t.gpr .rsp = s₀.gpr .rsp := k.gpr _ (by decide)
  have Ft : Frame [⟨o, 72⟩] s₀.mem t.mem := frame_of_outside O
  refine ⟨spt, k.wr, ?_, ?_⟩
  · -- The saved registers and the return address.
    have words : ∀ j (hj : j < sqrRegs.length),
        t.mem.readW (S - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr sqrRegs[j] := by
      intro j hj
      have hj5 : j < 5 := hj
      rw [← framesStart_word s sqrRegs notSp (by simpa [hS] using hsp) j hj, hS]
      refine Ft.readW (r := ⟨S - BitVec.ofNat 64 (8 * (j + 1)), 8⟩) (a := S - BitVec.ofNat 64 (8 * (j + 1)))
        (w := 64) (Region.contains_self _ _) ?_ (by decide)
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (Region.Disjoint.sub_left hso (Offset.sub_below S (by omega) (by omega)))
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hrsp : r = .rsp
      · subst hrsp
        rw [framesEnd_rsp, spt, sp₀, hS]
        simp only [List.length_cons, List.length_nil]
        exact BitVec.sub_add_cancel _ _
      · by_cases hrbx : r = .rbx
        · subst hrbx
          rw [framesEnd_other _ _ (by decide) (by decide), k.gpr _ (by decide), g₀ _ (by decide)]
        · have hm : r ∈ sqrRegs := by revert hr hrsp hrbx; revert r; decide
          exact (framesEnd_restore s t sqrRegs notSp hnd (by rw [spt, sp₀, hS]; rfl) (by
            intro j hj; rw [hS]; exact words j hj) r hm)
    · rw [framesEnd_mem, hS]
      have e₁ := Ft.readW (r := ⟨S, 8⟩) (a := S) (w := 64) (Region.contains_self _ _)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hro) (by decide)
      have e₂ := F₀.readW (r := ⟨S, 8⟩) (a := S) (w := 64) (Region.contains_self _ _)
        (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint_below S (by have := S.isLt; omega)) (by decide)
      exact e₁.trans e₂
  · -- The square.
    show Spec.P521.feAt (framesEnd t sqrRegs).mem (s.gpr .rdi) < _ ∧
      Spec.P521.feAt (framesEnd t sqrRegs).mem (s.gpr .rdi) * Spec.P521.montR % _ =
        Spec.P521.feAt s.mem (s.gpr .rsi) * Spec.P521.feAt s.mem (s.gpr .rsi) % _
    rw [hO, hA, framesEnd_mem, feAt_eq, feAt_eq, montR_eq]
    rw [hA₀] at eq
    exact ⟨lt, eq⟩

theorem sqr_ct : ConstantTime isa sqrC.pre sqrC.pub sqrCode :=
  RelCT.constantTime ((frames_ct (qs := [.rsp, .rdi, .rsi]) (by decide)
    (RelCT.taint (A := taintS) (Taint.ofRegs [.rsp, .rdi, .rsi]) (fun _ _ h => Taint.agree_ofRegs h)
      (by taint_decide)) sqrRegs).mono
    (fun _ _ h => by
      obtain ⟨-, -, h₁, h₂, h₃⟩ := h
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [h₁, h₂, h₃])
    (fun _ _ h => h))

/-- A state meeting the contract. -/
def sqrSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 72⟩]
  wr := [⟨0x1000, 72⟩]

theorem sqr_verified : Verified target sqrCode (Spec.P521.sqrMontContract abi 40) := by
  refine Verified.of_correct (fun s h => ?_) sqr_ct ?_
  · obtain ⟨t, s', he, gp, post⟩ := sqr_correct s h
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he gp, post⟩
  · exact
      { pre := by sig_implies_pre [Spec.P521.sqrMontContract, Spec.P521.sqrMontSig, sqrC, abi, argRegs]
        post := by sig_implies_post [Spec.P521.sqrMontContract, Spec.P521.sqrMontSig, sqrC, abi, argRegs]
        pub := by sig_implies_pub [Spec.P521.sqrMontContract, Spec.P521.sqrMontSig, sqrC, abi, argRegs]
        sat := ⟨sqrSat, by
          sig_pre [Spec.P521.sqrMontContract, Spec.P521.sqrMontSig, abi, argRegs]
          sig_and_intros
          all_goals first
            | exact Region.disjoint_of_sep (by decide)
            | decide +kernel⟩ }

end VG.Proof.P521Field.X86_64
