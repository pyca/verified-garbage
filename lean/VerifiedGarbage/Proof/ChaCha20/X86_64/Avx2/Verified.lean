import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Last8

/-!
# `vg_chacha20_xor_avx2` verified

The loop over 512-byte chunks (`Avx2/Xor.lean`), then the last bytes
(`Avx2/Last8.lean`, `Avx2Tail/Tail.lean`); constant time and the calling
convention.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2

theorem tinv_of {s₀ : State} {t : Nat} {s : State} (h : LInv s₀ t s) : Avx2Tail.TInv s₀ (512 * t) s where
  rdi := h.rdi
  rcx := h.rcx
  rsi := h.rsi
  rdx := h.rdx
  le := h.le
  dvd := ⟨8 * t, by omega⟩
  keep := h.keep
  rd := h.rd
  wr := h.wr
  cnt := by rw [h.cnt, show 512 * t / 64 = 8 * t by omega]
  data := h.data
  consts := h.consts
  incs := h.incs
  frame := h.frame

set_option simprocs false in
theorem cmp385_ok {s₀ : State} {t : Nat} {s : State} (h : LInv s₀ t s) :
    WP isa (.block [.alu .cmp .rdx (.imm 385)]) s fun s' =>
      LInv s₀ t s' ∧ s'.cf = some (decide (eL s₀ - 512 * t < 385)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (385 : BitVec 32) = 385 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.keep, h.rd, h.wr, h.cnt, h.data, h.consts, h.incs,
    h.frame⟩, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega)]
  rfl

theorem xor_eq : Impl.ChaCha20.X86_64.Avx2.xor =
    .seq (.block (Impl.ChaCha20.X86_64.Avx2Tail.consts ++ consts ++
      ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body .ae))
    (.seq (.block [.alu .cmp .rdx (.imm 385)]) (.ite .b Impl.ChaCha20.X86_64.Avx2Tail.tail last8))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20.X86_64.Avx2.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ < 512)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv : Nat → State → Prop := fun n s =>
        ∃ t, n = eL s₀ - 512 * t ∧ 512 ≤ eL s₀ - 512 * t ∧ LInv s₀ t s
      have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
          (eval .ae s' = some false ∧ ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s') ∨
          (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
        rintro n s ⟨t, rfl, ht, hI⟩
        refine WP.mono (body_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
        by_cases hl : eL s₀ - 512 * (t + 1) < 512
        · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
        · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 512 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
      exact WP.loop (M := isa) Inv hstep (eL s₀ - 512 * 0) s₁ ⟨0, rfl, by omega, h₁⟩
  · refine WP.seq (WP.mono (cmp385_ok h₂) fun s₃ ⟨h₃, c₃⟩ => ?_)
    refine WP.ite (decide (eL s₀ - 512 * t < 385)) (by simp [eval, c₃]) (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact Avx2Tail.tail_ok hp hs (tinv_of h₃)
    · simp only [decide_eq_false_iff_not] at hs
      exact last8_ok hp (by omega) ht h₃

/-- `vg_chacha20_xor_avx2` returns with `rsi` pointing at `buf`, as
`vg_chacha20_xor` does, for a caller that recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx2.xor s t s' ∧ abiPreserved s s' ∧
      (xorAvx2X86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hpost⟩, hr⟩ := correct (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost, hr⟩

theorem xor_correct (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx2.xor s t s' ∧ abiPreserved s s' ∧
      xorAvx2X86_64.post s s' :=
  (xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa xorAvx2X86_64.pre xorAvx2X86_64.pub
    Impl.ChaCha20.X86_64.Avx2.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Avx2.xor
      (Spec.ChaCha20.xorContract X86_64.abi 16) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      xorAvx2X86_64, Proof.ChaCha20.xorX86_64]
      [sat] using sat)

end VG.Proof.ChaCha20.X86_64.Avx2
