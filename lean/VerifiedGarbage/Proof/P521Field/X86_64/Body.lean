import VerifiedGarbage.Impl.P521Field.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Spec.P521

/-!
# P-521's field multiplication and squaring as functions, x86-64: the bodies

`mulBody` and `sqrBody` (`Impl/P521Field/X86_64.lean`) run `mulPX`'s and
`sqrPX`'s rows, reduction and final reduction with the temporary area and
the result at `out` (`rdi`, `ScrC` with `c = 0`), and the operands read
through `rsi` and `rbx` (`PtrC`), apart from `out` (`Apart.of_disjoint`).
-/

namespace VG.Proof.P521Field.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.P521Field.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

/-- Nine words at `p` apart from the nine at `o`, from their regions being
disjoint. -/
theorem apart_of_disjoint {p o : Addr} (h : Region.Disjoint ⟨p, 72⟩ ⟨o, 72⟩) : Apart p 0 72 o 0 72 :=
  fun i hi => by
    right
    have hc : (⟨p, 72⟩ : Region).Contains (off p 0 + BitVec.ofNat 64 i) 1 := by
      show ofs p (off p 0 + BitVec.ofNat 64 i) + 1 ≤ 72
      rw [ofs_off p (by omega)]; omega
    have := h _ hc
    simp only [Region.Contains, Nat.not_le] at this
    show 72 ≤ (off p 0 + BitVec.ofNat 64 i - o).toNat
    omega

theorem off_zero (p : Addr) : off p 0 = p := by simp [off]

/-- `mov rbx, rdx`. -/
theorem movRbx_ok (s : State) :
    WP isa (.block [.mov .rbx (.reg .rdx)]) s fun s' => s'.gpr .rbx = s.gpr .rdx ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, readSrc, exec, Option.map_some, runStep_some, runBlock_nil,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- P-521's `p + 1 = 2⁵²¹`. -/
theorem p_succ : Spec.P521.p + 1 = 512 * (2 ^ 64) ^ 8 := by decide +kernel

/-- The registers the bodies may change. -/
theorem body_regs : ∀ r ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs, r ∈ rowRegs := by decide

/-- `mulBody`: from `out` at `rdi`, `a` at `rsi` and `b` at `rdx`, nine words
each, `b < p`, `out` apart from both: `out = a b R⁻¹ mod p`, below `p`. -/
theorem mulBody_ok {s : State} {o pa pb : Addr} (hs : ScrC s o 72 0) (hpa : PtrC s .rsi pa 72 0)
    (hdx : s.gpr .rdx = pb) (hbr : (⟨pb, 72⟩ : Region) ∈ s.rd ++ s.wr) (hbw : pb.toNat + 72 ≤ 2 ^ 64)
    (hat : Apart pa 0 72 o 0 72) (hbt : Apart pb 0 72 o 0 72) (hB : wordsVal s.mem pb 0 9 < Spec.P521.p) :
    WP isa (.block mulBody) s fun s' =>
      wordsVal s'.mem o 0 9 < Spec.P521.p ∧
      wordsVal s'.mem o 0 9 * (2 ^ 64) ^ 9 % Spec.P521.p =
        wordsVal s.mem pa 0 9 * wordsVal s.mem pb 0 9 % Spec.P521.p ∧
      KeepRegs (.rbx :: .rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside o 0 72 s.mem s'.mem := by
  have hm := p_succ
  rw [mulBody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movRbx_ok s) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hpa₁ : PtrC s₁ .rsi pa 72 0 :=
    ⟨(k₁.1 .rsi (by decide)).trans hpa.gpr, by rw [k₁.2.2.1, k₁.2.2.2]; exact hpa.rd, hpa.nowrap, hpa.reg⟩
  have hpb₁ : PtrC s₁ .rbx pb 72 0 :=
    ⟨by rw [b₁, hdx, off_zero], by rw [k₁.2.2.1, k₁.2.2.2]; exact hbr, hbw, Or.inr (Or.inr rfl)⟩
  rw [WP.block_append_iff]
  refine WP.mono (xRows_ok hs₁ hpa₁ hpb₁ (M := fm) (a := 0) (b := 0) (by decide) (by decide) (by decide)
    hat hbt 8 (Nat.le_refl _)) fun s₂ ⟨k₂, O₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xRed_ok (hs₁.of_keepRegs k₂ (by decide)) (M := fm) (by decide))
    fun s₃ ⟨acc, e₃, k₃, O₃⟩ => ?_
  rw [k₁.2.1] at e₂
  rw [e₂] at e₃
  have hA : wordsVal s.mem pa 0 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  have hU : wordsVal s₃.mem o fm.tmp 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hA hB hU e₃.symm
  refine WP.mono (xCanon_ok ((hs₁.of_keepRegs k₂ (by decide)).of_keepRegs k₃ (by decide)) (o := 0)
    (by omega) hm hW1 hW2) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hmo : 0 < Spec.P521.p := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e₄]; exact Nat.mod_lt _ hmo
  · rw [e₄, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right]
  · refine ⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁.2.2.1], by rw [k₄.wr, k₃.wr, k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨hb, hr'⟩ := hr
    have hr'' : r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := by simpa only [List.mem_cons, not_or] using hr'
    rw [k₄.gpr r (fun h => hr'' (by
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))),
      k₃.gpr r hr'', k₂.gpr r hr'', k₁.1 r (by simpa using hb)]
  · intro x hx
    have h72 := hx.resolve_left (Nat.not_lt_zero _)
    rw [O₄ x hx, O₃ x (Or.inr (by show 0 + 64 + 8 ≤ _; omega_using [h72])), O₂ x hx, k₁.2.1]

/-- `sqrBody`: from `out` at `rdi` and `a` at `rsi`, nine words each,
`a < p`, `out` apart from `a`: `out = a² R⁻¹ mod p`, below `p`. -/
theorem sqrBody_ok {s : State} {o pa : Addr} (hs : ScrC s o 72 0) (hpa : PtrC s .rsi pa 72 0)
    (hat : Apart pa 0 72 o 0 72) (hB : wordsVal s.mem pa 0 9 < Spec.P521.p) :
    WP isa (.block sqrBody) s fun s' =>
      wordsVal s'.mem o 0 9 < Spec.P521.p ∧
      wordsVal s'.mem o 0 9 * (2 ^ 64) ^ 9 % Spec.P521.p =
        wordsVal s.mem pa 0 9 * wordsVal s.mem pa 0 9 % Spec.P521.p ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside o 0 72 s.mem s'.mem := by
  have hm := p_succ
  have hnw := hs.nowrap
  have htmp : fm.tmp = 0 := rfl
  rw [sqrBody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sRows_ok hs hpa (M := fm) (a := 0) (by decide) (by decide) hat 7 (by omega))
    fun s₂ ⟨k₂, O₂, e₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  have hpa₂ := hpa.of_keepRegs k₂ (by rows_sub)
  rw [WP.block_append_iff, sDiag, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₂ (xAcc 8) (d := fm.tmp + 64) (by decide))
    fun s₃ ⟨m₃, g₃, cf₃, of₃, rd₃, wr₃⟩ => ?_
  have hs₃ : ScrC s₃ o 72 0 := ⟨by rw [g₃]; exact hs₂.rdi, by rw [wr₃]; exact hs₂.wr, hs₂.nowrap⟩
  have hpa₃ := hpa₂.of_store g₃ rd₃ wr₃
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movZero_ok s₃ (xAcc 17)) fun s₄ ⟨z₄, _, _, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by simpa using (xAcc_ne 17).2.2.2.1.symm)
  have hpa₄ := hpa₃.of_keeps k₄ (by rows_sub)
  refine WP.mono (xorRax_ok s₄) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hpa₅ := hpa₄.of_keeps k₅ (by rows_sub)
  have hm₅ : s₅.mem = s₃.mem := k₅.2.1.trans k₄.2.1
  have O₃ : Outside o (fm.tmp + 64) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ _ _ (by omega)
  -- The accumulator before the squares is the products of two different words.
  have hx₅ : ∀ c, 9 ≤ c → c < 17 → xg s₅ c = xg s₂ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₅.1 _ (by simpa using (xAcc_ne c).1), k₄.1 _ (by simpa using (xAcc_ne_of h2 (by omega))), g₃]
  have h17 : xg s₅ 17 = 0 := by
    simp only [xg]; rw [k₅.1 _ (by simpa using (xAcc_ne 17).1), z₄]; rfl
  have hS₅ : hval (sqWord fm o s₅) 0 18 = wordsVal s₂.mem o fm.tmp 8 + (2 ^ 64) ^ 8 * hval (xg s₂) 8 9 := by
    have hlo : hval (sqWord fm o s₅) 0 8 = wordsVal s₂.mem o fm.tmp 8 := by
      rw [show fm.tmp = fm.tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by
        simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte, hm₅]
        exact congrArg BitVec.toNat (O₃.word (by omega) (by omega))
    have h8 : sqWord fm o s₅ 8 = xg s₂ 8 := by
      simp only [sqWord, show (8 : Nat) ≤ 8 from Nat.le_refl _, ↓reduceIte, hm₅, m₃, xg]
      rw [show fm.tmp + 8 * 8 = fm.tmp + 64 from rfl, word_writeW_self]
    have hhi : hval (sqWord fm o s₅) 9 8 = hval (xg s₂) 9 8 :=
      hval_congr fun c h1 h2 => by
        simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
        exact hx₅ c h1 (by omega)
    have h17' : sqWord fm o s₅ 17 = 0 := by simp only [sqWord, show ¬ (17 ≤ 8) by decide, ↓reduceIte]; exact h17
    rw [hval_add (sqWord fm o s₅) 0 8 10, Nat.zero_add, hlo, show (10 : Nat) = 9 + 1 from rfl, hval, h8,
      hval_succ_last, hhi, h17', Nat.mul_zero, Nat.add_zero]
    rw [show hval (xg s₂) 8 9 = xg s₂ 8 + 2 ^ 64 * hval (xg s₂) 9 8 from rfl]
  refine WP.mono (sDiags_ok hs₅ hpa₅ (M := fm) (a := 0) (by decide) (by decide) hat c₅ o₅ 9 (Nat.le_refl _))
    fun s₆ ⟨c₆, o₆, _, _, e₆, _, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- The square.
  generalize hf : (fun j => (word s.mem pa (0 + 8 * j)).toNat) = f at e₂
  have hf₅ : sDg (fun j => (word s₅.mem pa (0 + 8 * j)).toNat) 9 = sDg f 9 :=
    sDg_congr fun j hj => by
      rw [← hf, hm₅]
      exact congrArg BitVec.toNat ((O₃.word' ((hat.sub (by omega) (by omega)).mono (by decide) (by decide))).trans
        (O₂.word' (hat.sub (by omega) (by omega))))
  have hA : wordsVal s.mem pa 0 9 = hval f 0 9 := by
    rw [← hf, ← wordsVal_hval s.mem pa 0 0 9, Nat.mul_zero, Nat.add_zero]
  have hAl : wordsVal s.mem pa 0 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  rw [hS₅, e₂, hf₅, ← sq_ident, ← hA, show 2 * 9 = 18 from rfl] at e₆
  have hAA : wordsVal s.mem pa 0 9 * wordsVal s.mem pa 0 9 < (2 ^ 64) ^ 18 := by
    rw [show (18 : Nat) = 9 + 9 from rfl, Nat.pow_add]; exact Nat.mul_lt_mul'' hAl hAl
  have hT : hval (sqWord fm o s₆) 0 18 = wordsVal s₆.mem o fm.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 := by
    have h1 : hval (sqWord fm o s₆) 0 9 = wordsVal s₆.mem o fm.tmp 9 := by
      rw [show fm.tmp = fm.tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte]
    have h2 : hval (sqWord fm o s₆) 9 9 = hval (xg s₆) 9 9 :=
      hval_congr fun c h1 _ => by simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
    rw [show (18 : Nat) = 9 + 9 from rfl, hval_add, Nat.zero_add, h1, h2]
  have e₆' : wordsVal s₆.mem o fm.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 =
      wordsVal s.mem pa 0 9 * wordsVal s.mem pa 0 9 := by
    rw [← hT]
    have : (2 ^ 64) ^ 18 * (c₆.toNat + o₆.toNat) < (2 ^ 64) ^ 18 * 1 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  rw [WP.block_append_iff]
  refine WP.mono (xRed_ok hs₆ (M := fm) (by decide)) fun s₇ ⟨acc, e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  rw [e₆'] at e₇
  have hU : wordsVal s₇.mem o fm.tmp 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hAl hB hU e₇.symm
  refine WP.mono (xCanon_ok hs₇ (o := 0) (by omega) hm hW1 hW2) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  have hmo : 0 < Spec.P521.p := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e₈]; exact Nat.mod_lt _ hmo
  · rw [e₈, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right]
  · refine ⟨fun r hr => ?_, by rw [k₈.rd, k₇.rd, k₆.rd, k₅.2.2.1, k₄.2.2.1, rd₃, k₂.rd],
      by rw [k₈.wr, k₇.wr, k₆.wr, k₅.2.2.2, k₄.2.2.2, wr₃, k₂.wr]⟩
    have hx : ∀ k, xAcc k ≠ r := fun k h => hr (h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (xAcc_ne k).2.2.2.2)))
    rw [k₈.gpr r (fun h => hr (by
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))),
      k₇.gpr r hr, k₆.gpr r hr,
      k₅.1 r (fun h => hr (by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self ..)),
      k₄.1 r (by simpa using (hx 17).symm), g₃, k₂.gpr r hr]
  · intro x hx
    have h72 := hx.resolve_left (Nat.not_lt_zero _)
    rw [O₈ x hx, O₇ x (Or.inr (by show 0 + 64 + 8 ≤ _; omega_using [h72])), O₆ x hx, hm₅,
      O₃ x (Or.inr (by show 0 + 64 + 8 ≤ _; omega_using [h72])), O₂ x hx]

end VG.Proof.P521Field.X86_64
