import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.SqrS
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery arithmetic on x86-64: P-384's conditional subtraction in registers

`csubR` is `csubS` with P-384's `p` built in registers (`p384Mask` of all
ones) rather than read from memory: `p384Sub_ok` subtracts it, as
`p384Add_ok` adds it, and `csubR_ok` is `csubS_ok`'s reduction.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono sub_borrow sbb_borrow)

/-- `rax = 2⁶⁴ - 1`. -/
theorem movAllOnes_ok (s : State) :
    WP isa (.block [.mov .rax (.imm (-1))]) s fun s' =>
      s'.gpr .rax = BitVec.allOnes 64 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `ts -= rcx + 2⁶⁴ rdx + 2¹²⁸ rbp + 2¹⁹² rax (1 + 2⁶⁴ + 2¹²⁸)`, six words, the
borrow out in `CF`. -/
theorem p384Sub_ok (s : State) {ts : List Reg} (hlen : ts.length = 6) (hf : Fresh ts) :
    WP isa (.block (p384Sub ts)) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      regsVal s' ts + regsVal s [.rcx, .rdx, .rbp, .rax, .rax, .rax] =
        regsVal s ts + 2 ^ 128 * (2 ^ 256 * c.toNat) ∧ Keeps ts s s' := by
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
  simp only [p384Sub, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ↓reduceIte, *]
    generalize s.gpr .rcx = x at *
    generalize s.gpr .rdx = y at *
    generalize s.gpr .rbp = z at *
    generalize s.gpr .rax = w at *
    have e1 := sub_borrow (s.gpr t0) x
    generalize decide ((s.gpr t0).toNat < x.toNat) = k₁ at e1 ⊢
    have e2 := sbb_borrow (s.gpr t1) y k₁
    generalize decide ((s.gpr t1).toNat < y.toNat + k₁.toNat) = k₂ at e2 ⊢
    have e3 := sbb_borrow (s.gpr t2) z k₂
    generalize decide ((s.gpr t2).toNat < z.toNat + k₂.toNat) = k₃ at e3 ⊢
    have e4 := sbb_borrow (s.gpr t3) w k₃
    generalize decide ((s.gpr t3).toNat < w.toNat + k₃.toNat) = k₄ at e4 ⊢
    have e5 := sbb_borrow (s.gpr t4) w k₄
    generalize decide ((s.gpr t4).toNat < w.toNat + k₄.toNat) = k₅ at e5 ⊢
    have e6 := sbb_borrow (s.gpr t5) w k₅
    generalize decide ((s.gpr t5).toNat < w.toNat + k₅.toNat) = k₆ at e6 ⊢
    omega_using [e1, e2, e3, e4, e5, e6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, ite_false]

/-- `csubR`: `ts + 2³⁸⁴ top < 2p` reduced modulo P-384's `p`, without memory. -/
theorem csubR_ok (s : State) {ts : List Reg} {top : Reg} (hlen : ts.length = 6) (hf : Fresh (top :: ts))
    {m : Nat}
    (hm6 : m =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (hV : regsVal s ts + 2 ^ (64 * 6) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubR ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * 6) * (s.gpr top).toNat) % m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: top :: ts) s s' := by
  have hft := hf.tail
  have htop := hf.head
  have hW := pow_split 2 128 256 (64 * 6) (by omega)
  rw [hW] at hV ⊢
  have hfr : ∀ q ∈ ts, q ≠ .rax ∧ q ≠ .rcx ∧ q ≠ .rdx ∧ q ≠ .rbp ∧ q ≠ top := fun q hq =>
    have := hft.2 q hq
    ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, fun h => htop.1 (h ▸ hq)⟩
  simp only [csubR, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movAllOnes_ok s) fun s₀ ⟨x₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Mask_ok s₀ true (by rw [x₀]; rfl)) fun s₀' ⟨p₀, k₀'⟩ => ?_
  simp only [ite_true] at p₀
  rw [WP.block_append_iff]
  refine WP.mono (p384Sub_ok s₀' hlen hft) fun s₁ ⟨b₁, cf₁, e₁, k₁⟩ => ?_
  rw [show ([.alu .sbb top (.imm 0), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (p384Mask ++ p384Add ts) = [.alu .sbb top (.imm 0)] ++
      ([.alu .sbb .rax (.reg .rax)] ++ (p384Mask ++ p384Add ts)) from rfl, WP.block_append_iff]
  refine WP.mono (sbbTop_ok s₁ top cf₁) fun s₂ ⟨cf₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ cf₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Mask_ok s₃ _ x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  refine WP.mono (p384Add_ok s₄ hlen hft) fun s₅ ⟨c₅, _, e₅, k₅⟩ => ⟨?_, ?_⟩
  · have hR₄ : regsVal s₄ ts = regsVal s₁ ts := regsVal_congr fun q hq => by
      obtain ⟨qa, qc, qd, qb, qt⟩ := hfr q hq
      rw [k₄.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qc, qd, qb⟩),
        k₃.1 q (by simp only [List.mem_singleton]; exact qa), k₂.1 q (by simp only [List.mem_singleton]; exact qt)]
    have hR₀ : regsVal s₀' ts = regsVal s ts := regsVal_congr fun q hq => by
      obtain ⟨qa, qc, qd, qb, -⟩ := hfr q hq
      rw [k₀'.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qc, qd, qb⟩),
        k₀.1 q (by simp only [List.mem_singleton]; exact qa)]
    have t₀' : top ∉ [Reg.rcx, .rdx, .rbp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1⟩
    have t₀ : top ∉ [Reg.rax] := by simp only [List.mem_singleton]; exact htop.2.1
    have hT₁ : s₁.gpr top = s.gpr top := by rw [k₁.1 top htop.1, k₀'.1 top t₀', k₀.1 top t₀]
    rw [hR₄, e₄, hT₁] at e₅
    rw [p₀, hR₀] at e₁
    have l₅ := regsVal_lt s₅ ts
    have l₁ := regsVal_lt s₁ ts
    rw [hlen, hW] at l₅ l₁
    subst hm6
    generalize hB : decide ((s.gpr top).toNat < b₁.toNat) = B at e₅
    have hT := (s.gpr top).isLt
    cases b₁ <;> cases B <;> cases c₅ <;>
      simp only [Bool.toNat_true, Bool.toNat_false, ite_true, ite_false, Bool.false_eq_true,
        decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at hB e₁ e₅ ⊢ <;>
      omega
  · exact ((((k₀.mono (by sub_regs)).trans (k₀'.mono (by sub_regs))).trans
      ((k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))))).trans
      (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))

end VG.Proof.Mont.X86_64
