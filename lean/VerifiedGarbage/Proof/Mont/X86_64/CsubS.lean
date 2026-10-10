import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery arithmetic on x86-64: P-384's masked modulus in registers

P-384's `p` has the words `2³² - 1`, `2⁶⁴ - 2³²`, `2⁶⁴ - 2` and three of all
ones, so `p` masked by `rax` (all ones or zero) is `rax`'s low half in `rcx`,
`rax ≪ 32` in `rdx`, `rax ≪ 1` in `rbp`, and `rax` itself
(`p384Mask_ok`), which `p384Add` adds to six words (`p384Add_ok`). The
conditional subtraction `csubS` subtracts `p` in place and adds it back under
the mask of the borrow (`csubS_ok`), with no temporary memory; `csub_ok`
covers each of `csub`'s three cases. `sbbMask_ok` is the mask of a borrow.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry)

theorem sbbMask_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .rax (.reg .rax)]) s fun s' =>
      s'.gpr .rax = (if c then BitVec.allOnes 64 else 0) ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by cases c <;> simp, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- P-384's `p` masked by `rax`, in `rcx`, `rdx`, `rbp` and `rax`. -/
theorem p384Mask_ok (s : State) (c : Bool) (hx : s.gpr .rax = if c then BitVec.allOnes 64 else 0) :
    WP isa (.block p384Mask) s fun s' =>
      regsVal s' [.rcx, .rdx, .rbp, .rax, .rax, .rax] =
        (if c then
          39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
        else 0) ∧
      Keeps [.rcx, .rdx, .rbp] s s' := by
  have hs : 1 ≤ 32 ∧ 32 ≤ 63 := by decide
  have hs1 : 1 ≤ 1 ∧ 1 ≤ 63 := by decide
  apply WP.of_runBlock
  simp only [p384Mask, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc, readSrc32,
    State.setReg32, hs, hs1, and_self, ↓reduceIte, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    reduceCtorEq, Option.some.injEq, exists_eq_left', regsVal]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hx]
    cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `ts += rcx + 2⁶⁴ rdx + 2¹²⁸ rbp + 2¹⁹² rax (1 + 2⁶⁴ + 2¹²⁸)`, six words, the
carry out in `CF`. -/
theorem p384Add_ok (s : State) {ts : List Reg} (hlen : ts.length = 6) (hf : Fresh ts) :
    WP isa (.block (p384Add ts)) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      regsVal s' ts + 2 ^ 128 * (2 ^ 256 * c.toNat) =
        regsVal s ts + regsVal s [.rcx, .rdx, .rbp, .rax, .rax, .rax] ∧ Keeps ts s s' := by
  obtain ⟨t0, t1, t2, t3, t4, t5, rfl⟩ : ∃ t0 t1 t2 t3 t4 t5, ts = [t0, t1, t2, t3, t4, t5] := by
    match ts, hlen with
    | [t0, t1, t2, t3, t4, t5], _ => exact ⟨t0, t1, t2, t3, t4, t5, rfl⟩
  obtain ⟨hnd, hr⟩ := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨⟨n01, n02, n03, n04, n05⟩, ⟨n12, n13, n14, n15⟩, ⟨n23, n24, n25⟩, ⟨n34, n35⟩, n45, -⟩ := hnd
  obtain ⟨⟨a0, c0, d0, b0, -⟩, ⟨a1, c1, d1, b1, -⟩, ⟨a2, c2, d2, b2, -⟩, ⟨a3, c3, d3, b3, -⟩,
    ⟨a4, c4, d4, b4, -⟩, ⟨a5, c5, d5, b5, -⟩⟩ := hr
  have m01 := Ne.symm n01; have m02 := Ne.symm n02; have m03 := Ne.symm n03; have m04 := Ne.symm n04
  have m05 := Ne.symm n05; have m12 := Ne.symm n12; have m13 := Ne.symm n13; have m14 := Ne.symm n14
  have m15 := Ne.symm n15; have m23 := Ne.symm n23; have m24 := Ne.symm n24; have m25 := Ne.symm n25
  have m34 := Ne.symm n34; have m35 := Ne.symm n35; have m45 := Ne.symm n45
  have a0' := Ne.symm a0; have a1' := Ne.symm a1; have a2' := Ne.symm a2; have a3' := Ne.symm a3
  have a4' := Ne.symm a4; have a5' := Ne.symm a5; have c0' := Ne.symm c0; have c1' := Ne.symm c1
  have c2' := Ne.symm c2; have c3' := Ne.symm c3; have c4' := Ne.symm c4; have c5' := Ne.symm c5
  have d0' := Ne.symm d0; have d1' := Ne.symm d1; have d2' := Ne.symm d2; have d3' := Ne.symm d3
  have d4' := Ne.symm d4; have d5' := Ne.symm d5; have b0' := Ne.symm b0; have b1' := Ne.symm b1
  have b2' := Ne.symm b2; have b3' := Ne.symm b3; have b4' := Ne.symm b4; have b5' := Ne.symm b5
  apply WP.of_runBlock
  simp only [p384Add, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ↓reduceIte, *]
    generalize s.gpr .rcx = x at *
    generalize s.gpr .rdx = y at *
    generalize s.gpr .rbp = z at *
    generalize s.gpr .rax = w at *
    have e1 := add_carry (s.gpr t0) x
    generalize decide (2 ^ 64 ≤ (s.gpr t0).toNat + x.toNat) = k₁ at e1 ⊢
    have e2 := adc_carry (s.gpr t1) y k₁
    generalize decide (2 ^ 64 ≤ (s.gpr t1).toNat + y.toNat + k₁.toNat) = k₂ at e2 ⊢
    have e3 := adc_carry (s.gpr t2) z k₂
    generalize decide (2 ^ 64 ≤ (s.gpr t2).toNat + z.toNat + k₂.toNat) = k₃ at e3 ⊢
    have e4 := adc_carry (s.gpr t3) w k₃
    generalize decide (2 ^ 64 ≤ (s.gpr t3).toNat + w.toNat + k₃.toNat) = k₄ at e4 ⊢
    have e5 := adc_carry (s.gpr t4) w k₄
    generalize decide (2 ^ 64 ≤ (s.gpr t4).toNat + w.toNat + k₄.toNat) = k₅ at e5 ⊢
    have e6 := adc_carry (s.gpr t5) w k₅
    generalize decide (2 ^ 64 ≤ (s.gpr t5).toNat + w.toNat + k₅.toNat) = k₆ at e6 ⊢
    grind only
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, ite_false]

/-- `csubS`: `ts + 2³⁸⁴ top < 2p` reduced modulo P-384's `p`. -/
theorem csubS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hn : M.n = 6) (hlen : ts.length = M.n) (hf : Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) {m : Nat}
    (hm6 : m =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubS M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: top :: ts) s s' := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  have hW : 2 ^ (64 * M.n) = 2 ^ 128 * 2 ^ 256 :=
    calc 2 ^ (64 * M.n) = 2 ^ (128 + 256) := congrArg (2 ^ ·) (by rw [hn])
      _ = 2 ^ 128 * 2 ^ 256 := Nat.pow_add 2 128 256
  rw [hW] at hV ⊢
  rw [csubS, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (chainSub_ok hs (b := M.mo) (by omega) hft) fun s₁ ⟨b₁, cf₁, e₁, k₁⟩ => ?_
  rw [show ([.alu .sbb top (.imm 0), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (p384Mask ++ p384Add (t :: ts')) = [.alu .sbb top (.imm 0)] ++
      ([.alu .sbb .rax (.reg .rax)] ++ (p384Mask ++ p384Add (t :: ts'))) from rfl, WP.block_append_iff]
  refine WP.mono (sbbTop_ok s₁ top cf₁) fun s₂ ⟨cf₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ cf₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Mask_ok s₃ _ x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  refine WP.mono (p384Add_ok s₄ (hlen.trans hn) hft) fun s₅ ⟨c₅, _, e₅, k₅⟩ => ⟨?_, ?_⟩
  · have hR₄ : regsVal s₄ (t :: ts') = regsVal s₁ (t :: ts') := regsVal_congr fun q hq => by
      obtain ⟨qa, qc, qd, qb, -⟩ := hft.2 q hq
      have qt : q ≠ top := fun h => htop.1 (h ▸ hq)
      rw [k₄.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qc, qd, qb⟩),
        k₃.1 q (by simp only [List.mem_singleton]; exact qa), k₂.1 q (by simp only [List.mem_singleton]; exact qt)]
    have hT₁ : s₁.gpr top = s.gpr top := k₁.1 top htop.1
    rw [hR₄, e₄, hT₁] at e₅
    rw [hlen, hm, hW] at e₁
    have l₅ := regsVal_lt s₅ (t :: ts')
    have l₁ := regsVal_lt s₁ (t :: ts')
    rw [hlen, hW] at l₅ l₁
    subst hm6
    generalize hB : decide ((s.gpr top).toNat < b₁.toNat) = B at e₅
    have hT := (s.gpr top).isLt
    cases b₁ <;> cases B <;> cases c₅ <;>
      simp only [Bool.toNat_true, Bool.toNat_false, ite_true, ite_false, Bool.false_eq_true,
        decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at hB e₁ e₅ ⊢ <;>
      omega
  · exact (((k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs)))).trans
      (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))

/-- `csub`: `ts + 2^(64 n) top < 2m` reduced modulo `m`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (hf : Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hsep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo) {m : Nat}
    (hsp : M.sparse = true → M.n = 6 ∧
      m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csub M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      KeepRegs (.rax :: .rcx :: .rdx :: .rbp :: top :: ts) s s' ∧
      Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  unfold csub
  split
  · exact WP.mono (csubC_ok hs hlen hn (by omega) hf hmo hm hV) fun s' ⟨e, k⟩ =>
      ⟨e, Keeps.regs k, fun x _ => by rw [k.2.1]⟩
  split
  · obtain ⟨hn6, hm6⟩ := hsp ‹_›
    exact WP.mono (csubS_ok hs hn6 hlen hf hmo hm6 hm hV) fun s' ⟨e, k⟩ =>
      ⟨e, Keeps.regs k, fun x _ => by rw [k.2.1]⟩
  · exact WP.mono (csubM_ok hs hlen hn hf hmo htmp hsep hm hV) fun s' ⟨e, k, O⟩ =>
      ⟨e, k.mono fun r hr => by
        simp only [List.mem_cons] at hr ⊢
        rcases hr with h | h | h
        exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))], O⟩

end VG.Proof.Mont.X86_64
