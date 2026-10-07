import VerifiedGarbage.Proof.P521Field.X86_64.Body
import VerifiedGarbage.Proof.P521Field.X86_64.Frames
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.P521.Field
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-521's field multiplication as a function, x86-64: correctness

`vg_p521_mul_mont_adx` (`mulCode`) meets `mulC`, the contract
`Spec.P521.mulMontContract` gives on x86-64 (with 48 bytes of stack for the
six saved registers): the frames save `rbx`, `rbp`, `r12`–`r15` below `rsp`
(`framesStart_word`), where nothing else lies; `mulBody_ok` leaves the
product in `out`, changing no other memory; and the pops restore them.
-/

namespace VG.Proof.P521Field.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.P521Field.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem feAt_eq (m : Mem) (p : Addr) : Spec.P521.feAt m p = wordsVal m p 0 9 := by
  simp only [Spec.P521.feAt, wordsVal, List.range, List.range.loop, List.foldr, Mont.word, off,
    Nat.reduceMul, Nat.reduceAdd]

theorem montR_eq : Spec.P521.montR = (2 ^ 64) ^ 9 := by decide +kernel

/-- The words of a region apart from what changed. -/
theorem wordsVal_of_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 72⟩ : Region).Disjoint r) (hw : p.toNat + 72 ≤ 2 ^ 64) :
    ∀ d n, d + 8 * n ≤ 72 → wordsVal m' p d n = wordsVal m p d n
  | _, 0, _ => rfl
  | d, n + 1, h => by
    simp only [wordsVal]
    rw [wordsVal_of_frame hf hd hw (d + 8) n (by omega)]
    congr 2
    exact hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- Memory outside the nine words at `o` as a frame. -/
theorem frame_of_outside {o : Addr} {m m' : Mem} (h : Outside o 0 72 m m') :
    Frame [⟨o, 72⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains, Nat.not_le] at this
  show 72 ≤ (x - o).toNat
  omega))

/-- The registers `vg_p521_mul_mont_adx` saves. -/
abbrev mulRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `vg_p521_mul_mont_adx`'s contract on x86-64: `Spec.P521.mulMontContract`
as `Sig.contract` evaluates it with 48 bytes of stack. -/
def mulC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 72⟩
    let a : Region := ⟨s.gpr .rsi, 72⟩
    let b : Region := ⟨s.gpr .rdx, 72⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 48, 48⟩
    s.rd = [a, b] ∧ s.wr = [out] ∧ out.Disjoint a ∧ out.Disjoint b ∧
      ret.Disjoint out ∧ ret.Disjoint a ∧ ret.Disjoint b ∧
      stk.Disjoint out ∧ stk.Disjoint a ∧ stk.Disjoint b ∧ 48 ≤ (s.gpr .rsp).toNat ∧
      (s.gpr .rdi).toNat + 72 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 72 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 72 ≤ 2 ^ 64 ∧ Spec.P521.feAt s.mem (s.gpr .rdx) < Spec.P521.p
  post s s' :=
    Spec.P521.feAt s'.mem (s.gpr .rdi) < Spec.P521.p ∧
      Spec.P521.feAt s'.mem (s.gpr .rdi) * Spec.P521.montR % Spec.P521.p =
        Spec.P521.feAt s.mem (s.gpr .rsi) * Spec.P521.feAt s.mem (s.gpr .rdx) % Spec.P521.p
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx

theorem mul_correct (s : State) (h : mulC.pre s) :
    WP isa mulCode s fun s' => gprPreserved s s' ∧ mulC.post s s' := by
  obtain ⟨hrd, hwr, hoa, hob, hro, hra, hrb, hso, hsa, hsb, hsp, hwo, hwa, hwb, hB⟩ := h
  generalize hO : s.gpr .rdi = o at *
  generalize hA : s.gpr .rsi = pa at *
  generalize hBp : s.gpr .rdx = pb at *
  generalize hS : s.gpr .rsp = S at *
  have notSp : Reg.rsp ∉ mulRegs := by decide
  have hnd : mulRegs.Nodup := by decide
  refine frames_ok s mulRegs (.block mulBody) _ notSp (by simpa [hS] using hsp) ?_
  -- The body's state.
  let s₀ := framesStart s mulRegs
  have g₀ : ∀ r, r ≠ .rsp → s₀.gpr r = s.gpr r := fun r h => framesStart_gpr s mulRegs h
  have sp₀ : s₀.gpr .rsp = S - BitVec.ofNat 64 48 := by
    rw [framesStart_rsp, hS]; rfl
  have F₀ : Frame [below S 48] s.mem s₀.mem := by
    have := framesStart_frame s mulRegs notSp (by simpa [hS] using hsp)
    rwa [hS] at this
  have stk : ∀ r ∈ [below S 48], ∀ R : Region, R.Disjoint ⟨S - BitVec.ofNat 64 48, 48⟩ →
      R.Disjoint r := fun r hr R h => by
    simp only [List.mem_singleton] at hr; subst hr; exact h
  have hs₀ : ScrC s₀ o 72 0 :=
    ⟨by rw [g₀ _ (by decide), hO, off_zero], framesStart_wr s mulRegs (by rw [hwr]; exact List.mem_singleton_self _),
      hwo⟩
  have hpa₀ : PtrC s₀ .rsi pa 72 0 :=
    ⟨by rw [g₀ _ (by decide), hA, off_zero], by rw [framesStart_rd, hrd]; simp, hwa, Or.inr (Or.inl rfl)⟩
  have hbr₀ : (⟨pb, 72⟩ : Region) ∈ s₀.rd ++ s₀.wr := by rw [framesStart_rd, hrd]; simp
  have hA₀ : wordsVal s₀.mem pa 0 9 = wordsVal s.mem pa 0 9 :=
    wordsVal_of_frame F₀ (stk · · _ hsa.symm) hwa 0 9 (by decide)
  have hB₀ : wordsVal s₀.mem pb 0 9 = wordsVal s.mem pb 0 9 :=
    wordsVal_of_frame F₀ (stk · · _ hsb.symm) hwb 0 9 (by decide)
  refine WP.mono (mulBody_ok hs₀ hpa₀ (by rw [g₀ _ (by decide), hBp]) hbr₀ hwb
    (apart_of_disjoint hoa.symm) (apart_of_disjoint hob.symm)
    (by rw [hB₀, ← feAt_eq]; exact hB)) fun t ⟨lt, eq, k, O⟩ => ?_
  have spt : t.gpr .rsp = s₀.gpr .rsp := k.gpr _ (by decide)
  have Ft : Frame [⟨o, 72⟩] s₀.mem t.mem := frame_of_outside O
  refine ⟨spt, k.wr, ?_, ?_⟩
  · -- The saved registers and the return address.
    have words : ∀ j (hj : j < mulRegs.length),
        t.mem.readW (S - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr mulRegs[j] := by
      intro j hj
      have hj6 : j < 6 := hj
      rw [← framesStart_word s mulRegs notSp (by simpa [hS] using hsp) j hj, hS]
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
      · have hm : r ∈ mulRegs := by revert hr hrsp; revert r; decide
        exact (framesEnd_restore s t mulRegs notSp hnd (by rw [spt, sp₀, hS]; rfl) (by
          intro j hj; rw [hS]; exact words j hj) r hm)
    · rw [framesEnd_mem, hS]
      have e₁ := Ft.readW (r := ⟨S, 8⟩) (a := S) (w := 64) (Region.contains_self _ _)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hro) (by decide)
      have e₂ := F₀.readW (r := ⟨S, 8⟩) (a := S) (w := 64) (Region.contains_self _ _)
        (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint_below S (by have := S.isLt; omega)) (by decide)
      exact e₁.trans e₂
  · -- The product.
    show Spec.P521.feAt (framesEnd t mulRegs).mem (s.gpr .rdi) < _ ∧
      Spec.P521.feAt (framesEnd t mulRegs).mem (s.gpr .rdi) * Spec.P521.montR % _ =
        Spec.P521.feAt s.mem (s.gpr .rsi) * Spec.P521.feAt s.mem (s.gpr .rdx) % _
    rw [hO, hA, hBp, framesEnd_mem, feAt_eq, feAt_eq, feAt_eq, montR_eq]
    rw [hA₀, hB₀] at eq
    exact ⟨lt, eq⟩

theorem mul_ct : ConstantTime isa mulC.pre mulC.pub mulCode :=
  RelCT.constantTime ((frames_ct (qs := [.rsp, .rdi, .rsi, .rdx]) (by decide)
    (RelCT.taint (A := taintS) (Taint.ofRegs [.rsp, .rdi, .rsi, .rdx]) (fun _ _ h => Taint.agree_ofRegs h)
      (by taint_decide)) mulRegs).mono
    (fun _ _ h => by
      obtain ⟨-, -, h₁, h₂, h₃, h₄⟩ := h
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      exacts [h₁, h₂, h₃, h₄])
    (fun _ _ h => h))

/-- A state meeting the contract. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 72⟩, ⟨0x3000, 72⟩]
  wr := [⟨0x1000, 72⟩]

theorem mul_verified : Verified target mulCode (Spec.P521.mulMontContract abi 48) := by
  refine Verified.of_correct (fun s h => ?_) mul_ct ?_
  · obtain ⟨t, s', he, gp, post⟩ := mul_correct s h
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he gp, post⟩
  · exact
      { pre := by sig_implies_pre [Spec.P521.mulMontContract, Spec.P521.mulMontSig, mulC, abi, argRegs]
        post := by sig_implies_post [Spec.P521.mulMontContract, Spec.P521.mulMontSig, mulC, abi, argRegs]
        pub := by sig_implies_pub [Spec.P521.mulMontContract, Spec.P521.mulMontSig, mulC, abi, argRegs]
        sat := ⟨mulSat, by
          sig_pre [Spec.P521.mulMontContract, Spec.P521.mulMontSig, abi, argRegs]
          sig_and_intros
          all_goals first
            | exact Region.disjoint_of_sep (by decide)
            | decide +kernel⟩ }

end VG.Proof.P521Field.X86_64
