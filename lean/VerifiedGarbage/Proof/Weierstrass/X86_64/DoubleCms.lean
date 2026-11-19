module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Proof.Weierstrass.Cms
public import VerifiedGarbage.Impl.Mont.X86_64.Cms
public import VerifiedGarbage.Proof.Mont.X86_64.MulP
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Mont.X86_64.Cms`, which only this module used -/

section

/-!
# P-384's `C [a] - D [b] mod p` on x86-64 with BMI2 and ADX

`cms_ok`: `p - [b]` by `loads`, `chainSub_ok` and `stores_ok`, the sum
`N = D (p - [b]) + C [a]` by `rowS0_ok` and `rowX_ok`, its words above
`2³⁸⁴` folded down by `cmsFold_ok` (`2³⁸⁴ = p + c`, so `L + 2³⁸⁴ h ≡ L + h c`),
which leaves `L + h c < 2p`, and `csub_ok`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono clear_ok madd_ok carries_ok of_setReg of_setFlags
  adc_carry movRdxImm_ok movRdx_ok)

/-- `movabs r, k`: the flags unchanged. -/
theorem movImm64_ok (s : State) (r : Reg) (k : BitVec 64) :
    WP isa (.block [.movImm64 r k]) s fun s' =>
      s'.gpr r = k ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov r32, k`: the flags unchanged. -/
theorem mov32Imm_ok (s : State) (r : Reg) (k : BitVec 32) :
    WP isa (.block [.mov32 r (.imm k)]) s fun s' =>
      (s'.gpr r).toNat = k.toNat ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, (by trivial), (by trivial), fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `adox x, y`: `x + 2⁶⁴ OF' = x + y + OF`, CF unchanged. -/
theorem adoxR_ok (s : State) {x y : Reg} {o : Bool} (ho : s.of = some o) :
    WP isa (.block [.adox x (.reg y)]) s fun s' => ∃ o' : Bool, s'.of = some o' ∧ s'.cf = s.cf ∧
      (s'.gpr x).toNat + 2 ^ 64 * o'.toNat = (s.gpr x).toNat + (s.gpr y).toNat + o.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, readSrc, ho,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, of_setReg, of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, adc_carry _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `r8 … r14 = L + h c` for `L` in `r8 … r13`, `h` in `rdx` and P-384's
`c = 2³⁸⁴ - p` (`r14` cleared first). -/
theorem cmsFold_ok (s : State) :
    WP isa (.block cmsFold) s fun s' =>
      regsVal s' [.r8, .r9, .r10, .r11, .r12, .r13, .r14] =
        regsVal s [.r8, .r9, .r10, .r11, .r12, .r13] +
          (s.gpr .rdx).toNat * 0x100000000ffffffffffffffff00000001 ∧
      Keeps [.rbp, .rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s s' := by
  rw [cmsFold, show ([Impl.X25519.X86_64.clear, .movImm64 .rax sparseC0] : List Instr) =
    [Impl.X25519.X86_64.clear] ++ [.movImm64 .rax sparseC0] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movImm64_ok s₁ .rax sparseC0) fun s₂ ⟨a₂, cf₂, of₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s₂ (x := .r8) (y := .r9) (v := s₂.gpr .rax) rfl (fun _ h => nomatch h) (cf₂.trans cf₁)
    (of₂.trans of₁) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨c₃, o₃, cf₃, of₃, e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mov32Imm_ok s₃ .rax sparseC1) fun s₄ ⟨a₄, cf₄, of₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s₄ (x := .r9) (y := .r10) (v := s₄.gpr .rax) rfl (fun _ h => nomatch h) (cf₄.trans cf₃)
    (of₄.trans of₃) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨c₅, o₅, cf₅, of₅, e₅, k₅⟩ => ?_
  rw [show ([.adox .r10 (.reg .rdx), .mov32 .r14 (.imm 0), .adcx .r11 (.reg .rbp), .adox .r11 (.reg .rbp),
      .adcx .r12 (.reg .rbp), .adox .r12 (.reg .rbp), .adcx .r13 (.reg .rbp), .adox .r13 (.reg .rbp),
      .adcx .r14 (.reg .rbp), .adox .r14 (.reg .rbp)] : List Instr) =
    [.adox .r10 (.reg .rdx)] ++ [.mov32 .r14 (.imm 0)] ++ [.adcx .r11 (.reg .rbp), .adox .r11 (.reg .rbp)] ++
      [.adcx .r12 (.reg .rbp), .adox .r12 (.reg .rbp)] ++ [.adcx .r13 (.reg .rbp), .adox .r13 (.reg .rbp)] ++
      [.adcx .r14 (.reg .rbp), .adox .r14 (.reg .rbp)] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (adoxR_ok s₅ of₅) fun s₆ ⟨o₆, of₆, cf₆, e₆, k₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mov32Imm_ok s₆ .r14 0) fun s₇ ⟨z₇, cf₇, of₇, k₇⟩ => ?_
  obtain zb : ∀ {t : State}, Keeps [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s₁ t → t.gpr .rbp = 0 :=
    fun h => (h.1 .rbp (by decide)).trans z₁
  obtain K₇ : Keeps [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s₁ s₇ :=
    (((((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))).trans
      (k₅.mono (by sub_regs))).trans (k₆.mono (by sub_regs))).trans (k₇.mono (by sub_regs))
  rw [WP.block_append_iff]
  refine WP.mono (carries_ok s₇ (cf₇.trans (cf₆.trans cf₅)) (of₇.trans of₆) (zb K₇) (by decide))
    fun s₈ ⟨c₈, o₈, cf₈, of₈, e₈, k₈⟩ => ?_
  obtain K₈ := K₇.trans (k₈.mono (by sub_regs))
  rw [WP.block_append_iff]
  refine WP.mono (carries_ok s₈ cf₈ of₈ (zb (K₈.mono (by sub_regs))) (by decide))
    fun s₉ ⟨c₉, o₉, cf₉, of₉, e₉, k₉⟩ => ?_
  obtain K₉ := K₈.trans (k₉.mono (by sub_regs))
  rw [WP.block_append_iff]
  refine WP.mono (carries_ok s₉ cf₉ of₉ (zb (K₉.mono (by sub_regs))) (by decide))
    fun s₁₀ ⟨c₁₀, o₁₀, cf₁₀, of₁₀, e₁₀, k₁₀⟩ => ?_
  obtain K₁₀ := K₉.trans (k₁₀.mono (by sub_regs))
  refine WP.mono (carries_ok s₁₀ cf₁₀ of₁₀ (zb (K₁₀.mono (by sub_regs))) (by decide))
    fun s₁₁ ⟨c₁₁, o₁₁, cf₁₁, of₁₁, e₁₁, k₁₁⟩ => ⟨?_, ?_⟩
  · have g : ∀ {r : Reg} {t t' : State} {rs : List Reg}, Keeps rs t t' → r ∉ rs → t'.gpr r = t.gpr r :=
      fun h hr => h.1 _ hr
    obtain f8 : s₁₁.gpr .r8 = s₃.gpr .r8 := by
      rw [g k₁₁ (by decide), g k₁₀ (by decide), g k₉ (by decide), g k₈ (by decide), g k₇ (by decide),
        g k₆ (by decide), g k₅ (by decide), g k₄ (by decide)]
    obtain f9 : s₁₁.gpr .r9 = s₅.gpr .r9 := by
      rw [g k₁₁ (by decide), g k₁₀ (by decide), g k₉ (by decide), g k₈ (by decide), g k₇ (by decide),
        g k₆ (by decide)]
    obtain f10 : s₁₁.gpr .r10 = s₆.gpr .r10 := by
      rw [g k₁₁ (by decide), g k₁₀ (by decide), g k₉ (by decide), g k₈ (by decide), g k₇ (by decide)]
    obtain f11 : s₁₁.gpr .r11 = s₈.gpr .r11 := by
      rw [g k₁₁ (by decide), g k₁₀ (by decide), g k₉ (by decide)]
    obtain f12 : s₁₁.gpr .r12 = s₉.gpr .r12 := by rw [g k₁₁ (by decide), g k₁₀ (by decide)]
    obtain f13 : s₁₁.gpr .r13 = s₁₀.gpr .r13 := by rw [g k₁₁ (by decide)]
    obtain i8 : s₂.gpr .r8 = s.gpr .r8 := by rw [g k₂ (by decide), g k₁ (by decide)]
    obtain i9 : s₂.gpr .r9 = s.gpr .r9 := by rw [g k₂ (by decide), g k₁ (by decide)]
    obtain j9 : s₄.gpr .r9 = s₃.gpr .r9 := by rw [g k₄ (by decide)]
    obtain i10 : s₄.gpr .r10 = s.gpr .r10 := by
      rw [g k₄ (by decide), g k₃ (by decide), g k₂ (by decide), g k₁ (by decide)]
    obtain d2 : s₂.gpr .rdx = s.gpr .rdx := by rw [g k₂ (by decide), g k₁ (by decide)]
    obtain d4 : s₄.gpr .rdx = s.gpr .rdx := by rw [g k₄ (by decide), g k₃ (by decide), d2]
    obtain d5 : s₅.gpr .rdx = s.gpr .rdx := by rw [g k₅ (by decide), d4]
    obtain i11 : s₇.gpr .r11 = s.gpr .r11 := by
      rw [g k₇ (by decide), g k₆ (by decide), g k₅ (by decide), g k₄ (by decide), g k₃ (by decide),
        g k₂ (by decide), g k₁ (by decide)]
    obtain i12 : s₈.gpr .r12 = s.gpr .r12 := by
      rw [g k₈ (by decide), g k₇ (by decide), g k₆ (by decide), g k₅ (by decide), g k₄ (by decide),
        g k₃ (by decide), g k₂ (by decide), g k₁ (by decide)]
    obtain i13 : s₉.gpr .r13 = s.gpr .r13 := by
      rw [g k₉ (by decide), g k₈ (by decide), g k₇ (by decide), g k₆ (by decide), g k₅ (by decide),
        g k₄ (by decide), g k₃ (by decide), g k₂ (by decide), g k₁ (by decide)]
    obtain i14 : (s₁₀.gpr .r14).toNat = 0 := by
      rw [g k₁₀ (by decide), g k₉ (by decide), g k₈ (by decide)]; exact z₇.trans rfl
    rw [a₂, i8, i9, d2] at e₃
    rw [j9, i10, d4, a₄] at e₅
    rw [d5] at e₆
    rw [i11] at e₈
    rw [i12] at e₉
    rw [i13] at e₁₀
    rw [i14] at e₁₁
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rw [f8, f9, f10, f11, f12, f13]
    have hC0 : sparseC0.toNat = 0xffffffff00000001 := rfl
    have hC1 : sparseC1.toNat = 0xffffffff := rfl
    rw [hC0] at e₃
    rw [hC1] at e₅
    have := (s.gpr .rdx).isLt
    have := (s₁₁.gpr .r14).isLt
    have := (s₃.gpr .r8).isLt
    have := (s₅.gpr .r9).isLt
    have := (s₆.gpr .r10).isLt
    have := (s₈.gpr .r11).isLt
    have := (s₉.gpr .r12).isLt
    have := (s₁₀.gpr .r13).isLt
    simp only [Bool.toNat_false] at e₃
    omega_arith
  · exact (k₁.mono (by sub_regs)).trans ((K₁₀.trans (k₁₁.mono (by sub_regs))).mono (by sub_regs))

/-- `[o] = (C [a] - D [b]) mod p` for P-384's `p`, `C` and `D` below `64`:
`p - [b]` into the temporary area, `D (p - [b]) + C [a]` in `r8 … r15`, its
words above `2³⁸⁴` folded down by `2³⁸⁴ ≡ c (mod p)` and the sum reduced. -/
theorem cms_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hsp : M.sparse = true) {o a b C D : Nat} (hC : C < 64) (hD : D < 64)
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (cms M o C a D b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (C * wordsVal s.mem base a M.n + D * (m - wordsVal s.mem base b M.n)) % m := by
  obtain ⟨hn6, hm6⟩ := Mod.ok_sparse hM.red hsp
  have hn := hs.nowrap
  have hmo := hM.mo
  have htmp := hM.tmp
  have hsep := hM.sep
  rw [hn6] at ho ha hb haT hA hB hmo htmp hsep ⊢
  have hf : Fresh (low 6) := (fresh_top_low (n := 6) (by decide)).tail
  have hl : (low 6).length = 6 := rfl
  have hW : 2 ^ (64 * 6) = 2 ^ 128 * 2 ^ 256 :=
    calc 2 ^ (64 * 6) = 2 ^ (128 + 256) := congrArg (2 ^ ·) rfl
      _ = 2 ^ 128 * 2 ^ 256 := Nat.pow_add 2 128 256
  simp only [cms, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low 6) hs (a := M.mo) (by rw [hl]; omega_using [hmo]) hf) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := [.r9, .r10, .r11, .r12, .r13]) (b := b) hb hf)
    fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok (low 6) hs₂ (o := M.tmp) (by rw [hl]; omega_using [htmp]) hf.1) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s₃ (BitVec.ofNat 32 D)) fun s₄ ⟨d₄, _, _, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowS0_ok hs₄ (b := M.tmp) (by omega_using [htmp])) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s₅ (BitVec.ofNat 32 C)) fun s₆ ⟨d₆, _, _, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have mA : wordsVal s₆.mem base a 6 = wordsVal s.mem base a 6 := by
    rw [k₆.2.1, k₅.2.1, k₄.2.1, O₃.wordsVal (by rw [hl]; omega_using [haT]) (by omega_using [ha, hn]), k₂.2.1, k₁.2.1]
  have mT : wordsVal s₄.mem base M.tmp 6 = regsVal s₂ (low 6) := by rw [hl] at e₃; rw [k₄.2.1]; exact e₃
  have hval : wordsVal s.mem base M.mo 6 = m := hn6 ▸ hM.val
  rw [k₁.2.1] at e₂
  rw [hl, hval] at e₁
  have hP : regsVal s₂ (low 6) + wordsVal s.mem base b 6 = m := by
    have hR := regsVal_lt s₂ (low 6)
    rw [hl, hW] at hR
    have e₂' := e₂
    rw [show ([.r8, .r9, .r10, .r11, .r12, .r13] : List Reg).length = 6 from rfl, hW,
      show regsVal s₁ [.r8, .r9, .r10, .r11, .r12, .r13] = m from e₁] at e₂'
    change regsVal s₂ (low 6) + _ = _ at e₂'
    have h384 : m < 2 ^ 128 * 2 ^ 256 := by subst hm6; decide
    cases c₂ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e₂' <;>
      omega_using [e₂', hB, hR]
  rw [mT, d₄] at e₅
  rw [show rowX 6 (acc 6) a = rowX (low 6).length (low 6 ++ [.r14, .r15]) a from rfl, WP.block_append_iff]
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hC' : (BitVec.ofNat 32 C).toNat = C := by rw [BitVec.toNat_ofNat]; omega_using [hC]
  rw [hD'] at e₅
  rw [hC'] at d₆
  have r₆ : regsVal s₆ (low 6 ++ [.r14, .r15]) = regsVal s₅ (wins 6 0) :=
    regsVal_congr fun q hq => k₆.1 q (by revert q; decide)
  have hBd : regsVal s₆ (low 6 ++ [.r14, .r15]) + (s₆.gpr .rdx).toNat * wordsVal s₆.mem base a (low 6).length <
      2 ^ (64 * ((low 6).length + 2)) := by
    have pw : 2 ^ (64 * ((low 6).length + 2)) = 2 ^ 128 * 2 ^ 128 * 2 ^ 256 :=
      calc 2 ^ (64 * ((low 6).length + 2)) = 2 ^ (128 + 128 + 256) := congrArg (2 ^ ·) rfl
        _ = 2 ^ (128 + 128) * 2 ^ 256 := Nat.pow_add 2 (128 + 128) 256
        _ = 2 ^ 128 * 2 ^ 128 * 2 ^ 256 := congrArg (· * 2 ^ 256) (Nat.pow_add 2 128 128)
    refine Nat.lt_of_lt_of_eq ?_ pw.symm
    rewrite [r₆, e₅, d₆, hl, mA]
    have h384 : m < 2 ^ 128 * 2 ^ 256 := by subst hm6; decide
    have : D * regsVal s₂ (low 6) ≤ 64 * m := Nat.mul_le_mul (by omega_using [hD]) (by omega_using [hP])
    have : C * wordsVal s.mem base a 6 ≤ 64 * m := Nat.mul_le_mul (by omega_using [hC]) (by omega_using [hA])
    omega_arith
  refine WP.mono (rowX_ok hs₆ (L := low 6) (tn := .r14) (tn1 := .r15) (fresh_wins (n := 6) (by decide) 0) (d := a)
      (by rw [hl]; omega_using [ha]) hBd)
    fun s₇ ⟨e₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRdx_ok s₇ (src := .reg .r14) rfl) fun s₈ ⟨d₈, _, _, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cmsFold_ok s₈) fun s₉ ⟨e₉, k₉⟩ => ?_
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  have hWn : 2 ^ (64 * M.n) = 2 ^ 128 * 2 ^ 256 := by rw [hn6]; exact hW
  have hval₉ : wordsVal s₉.mem base M.mo M.n = m := by
    rw [k₉.2.1, k₈.2.1, k₇.2.1, k₆.2.1, k₅.2.1, k₄.2.1, hn6, O₃.wordsVal (by omega_using [hsep, hl]) (by omega_using [hn, hmo]), k₂.2.1,
      k₁.2.1, hval]
  -- The value before the fold: `L + 2³⁸⁴ (h + 2⁶⁴ r15) = D (p - [b]) + C [a]`.
  have hL₇ := regsVal_lt s₇ (low 6)
  rw [hl, hW] at hL₇
  have F1 : regsVal s₇ (low 6) + 2 ^ 128 * 2 ^ 256 * ((s₇.gpr .r14).toNat + 2 ^ 64 * (s₇.gpr .r15).toNat) =
      D * regsVal s₂ (low 6) + C * wordsVal s.mem base a 6 := by
    have e₇' := e₇
    rw [r₆, e₅, d₆, hl, mA] at e₇'
    rw [← e₇', regsVal_append, hl, hW]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
  -- The fold.
  have F2 : regsVal s₉ (low 6) + 2 ^ 128 * 2 ^ 256 * (s₉.gpr .r14).toNat =
      regsVal s₇ (low 6) + (s₇.gpr .r14).toNat * 0x100000000ffffffffffffffff00000001 := by
    have h8 : regsVal s₈ [.r8, .r9, .r10, .r11, .r12, .r13] = regsVal s₇ (low 6) :=
      regsVal_congr fun q hq => k₈.1 q (by revert q; decide)
    have hd : (s₈.gpr .rdx).toNat = (s₇.gpr .r14).toNat := by rw [d₈]
    rw [h8, hd] at e₉
    rw [← e₉]
    simp only [low, acc, List.take, regsVal, Nat.mul_zero, Nat.add_zero]
    omega_using []
  have hm2 : m < 2 ^ 128 * 2 ^ 256 := by subst hm6; decide
  have hX : D * regsVal s₂ (low 6) ≤ 64 * m := Nat.mul_le_mul (by omega_using [hD]) (by omega_using [hP])
  have hY : C * wordsVal s.mem base a 6 ≤ 64 * m := Nat.mul_le_mul (by omega_using [hC]) (by omega_using [hA])
  have hh : (s₇.gpr .r14).toNat < 128 ∧ (s₇.gpr .r15).toNat = 0 := by
    subst hm6; omega_using [F1, hX, hY]
  have hV : regsVal s₉ (low 6) + 2 ^ (64 * M.n) * (s₉.gpr .r14).toNat < 2 * m := by
    rw [hWn, F2]; subst hm6; omega_using [hL₇]
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₉ (ts := low 6) (top := .r14) (hl.trans hn6.symm) hM.n0
    (fresh_top_low (n := 6) (by decide)) hM.mo hM.tmp hM.sep (fun _ => ⟨hn6, hm6⟩) hval₉ hV)
    fun s₁₀ ⟨e₁₀, k₁₀, O₁₀⟩ => ?_
  have hs₁₀ := hs₉.of_keepRegs k₁₀ (by decide)
  refine WP.mono (stores_ok (low 6) hs₁₀ (o := o) (by rw [hl]; omega_using [ho]) hf.1) fun s₁₁ ⟨e₁₁, k₁₁, O₁₁⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_, fun x hx ht => ?_⟩
    · have hsub : ∀ q ∈ ([.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] : List Reg),
          q ∈ clob 6 := by decide
      have g : ∀ rs : List Reg, (∀ q ∈ rs, q ∈ ([.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14,
          .r15] : List Reg)) → r ∉ rs := fun rs h hm => hr (hn6 ▸ hsub r (h r hm))
      rw [k₁₁.gpr r (g _ (by decide)), k₁₀.gpr r (g _ (by decide)), k₉.1 r (g _ (by decide)),
        k₈.1 r (g _ (by decide)), k₇.1 r (g _ (by decide)), k₆.1 r (g _ (by decide)),
        k₅.1 r (g _ (by decide)), k₄.1 r (g _ (by decide)), k₃.gpr r (g _ (by decide)),
        k₂.1 r (g _ (by decide)), k₁.1 r (g _ (by decide))]
    · rw [k₁₁.rd, k₁₀.rd, k₉.2.2.1, k₈.2.2.1, k₇.2.2.1, k₆.2.2.1, k₅.2.2.1, k₄.2.2.1, k₃.rd, k₂.2.2.1,
        k₁.2.2.1]
    · rw [k₁₁.wr, k₁₀.wr, k₉.2.2.2, k₈.2.2.2, k₇.2.2.2, k₆.2.2.2, k₅.2.2.2, k₄.2.2.2, k₃.wr, k₂.2.2.2,
        k₁.2.2.2]
    · rw [hn6] at hx ht
      rw [O₁₁ x (by rw [hl]; omega_using [hx]), O₁₀ x (by rw [hn6]; omega_using [ht]), k₉.2.1, k₈.2.1, k₇.2.1, k₆.2.1, k₅.2.1,
        k₄.2.1, O₃ x (by rw [hl]; omega_using [ht]), k₂.2.1, k₁.2.1]
  · rw [hl] at e₁₁
    rw [e₁₁, e₁₀, hWn, F2]
    have hBm : m - wordsVal s.mem base b 6 = regsVal s₂ (low 6) := by omega_using [hP]
    rw [hBm]
    generalize D * regsVal s₂ (low 6) = X at *
    generalize C * wordsVal s.mem base a 6 = Y at *
    subst hm6
    omega_using [hh, F1]

end VG.Proof.Mont.X86_64

end

end


/-!
# Doubling with fused small multiples, on x86-64

`doubleCms M S` (`Impl/Weierstrass/X86_64/DoubleCms.lean`) is a doubling the
Jacobian window method can use (`doubleCms_dblOk`) for a curve with `a = -3`
whose field is P-384's (`M.sparse`, which `cms` needs):

* each step keeps the invariant `Inv` (`dstep_ok`): a field operation by
  `fop_ok`, `cms` by `cms_ok`, what its result stands for being
  `C a - D b` (`toM_cms`, with `smulN` for the small multiples);
* on distinct slots the steps compute `dblJF` (`dblCms_run`), the same
  triple as `dblJMul`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.Proof.Weierstrass

export VG.Proof.Weierstrass.Cms (smulN smulN_fin toM_cms)

end VG.Proof.Weierstrass.X86_64

namespace VG.Impl.Weierstrass.X86_64

open VG.Proof.Weierstrass.X86_64 (smulN)

/-- The slot a step writes. -/
def DStep.out : DStep → Nat
  | .op f => f.out
  | .cms o _ _ _ _ => o

/-- The slots a step reads. -/
def DStep.ins : DStep → List Nat
  | .op f => f.ins
  | .cms _ _ a _ b => [a, b]

/-- `cms`'s factors are below `64`. -/
def DStep.small : DStep → Bool
  | .op _ => true
  | .cms _ C _ D _ => C < 64 && D < 64

/-- A step on environments. -/
def DStep.run {F : Type _} [Lean.Grind.CommRing F] : DStep → (Nat → F) → Nat → F
  | .op f, e => f.run e
  | .cms o C a D b, e => Function.update e o (smulN C (e a) - smulN D (e b))

/-- Steps on environments. -/
def runSteps {F : Type _} [Lean.Grind.CommRing F] (l : List DStep) (e : Nat → F) : Nat → F :=
  l.foldl (fun e st => st.run e) e

end VG.Impl.Weierstrass.X86_64

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- Every slot a step reads holds a value: one of `V` or written before. -/
def stepsReadOk : List DStep → List Nat → Bool
  | [], _ => true
  | st :: l, V => st.ins.all (fun x => decide (x ∈ V)) && stepsReadOk l (st.out :: V)

/-- The slots holding a value after the steps. -/
def stepsValid : List DStep → List Nat → List Nat
  | [], V => V
  | st :: l, V => stepsValid l (st.out :: V)

theorem mem_stepsValid {x : Nat} :
    ∀ (l : List DStep) (V : List Nat), x ∈ V ∨ x ∈ l.map DStep.out → x ∈ stepsValid l V
  | [], V, h => by simpa [stepsValid] using h
  | st :: l, V, h => by
    refine mem_stepsValid l _ ?_
    simp only [List.map_cons, List.mem_cons] at h ⊢
    grind

/-- One step. -/
theorem dstep_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : M.sparse = true)
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {st : DStep} (hsm : st.small = true) (hS : ∀ x ∈ st.out :: st.ins, Sl x)
    (hR : ∀ x ∈ st.ins, x ∈ V) :
    WP isa (.block (st.code M)) s fun s' =>
      OpKeep M base st.out s s' ∧ Inv M base size m Sl (st.out :: V) (st.run E) s' := by
  cases st with
  | op f => exact fop_ok hL hm hI hS hR
  | cms o C a D b =>
    simp only [DStep.small, Bool.and_eq_true, decide_eq_true_eq] at hsm
    simp only [DStep.out, DStep.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (cms_ok hI.scr hI.mod hsp hsm.1 hsm.2 (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hL.tmp a hS.2.1) hA hB) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
    · rw [heq, toM_cms _ _ _ _ _ (Nat.le_of_lt hB), hI.val a hR.1, hI.val b hR.2]

/-- Steps, a block each. -/
theorem dsteps_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : M.sparse = true)
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (l : List DStep) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ st ∈ l, st.small = true) → (∀ st ∈ l, ∀ x ∈ st.out :: st.ins, Sl x) →
      stepsReadOk l V = true →
      WP isa (.block (l.map (DStep.code M)).flatten) s fun s' =>
        ProgKeep M base (l.map DStep.out) s s' ∧ Inv M base size m Sl (stepsValid l V) (runSteps l E) s'
  | [], _, _, s, hI, _, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | st :: l, V, E, s, hI, hsm, hS, hR => by
    simp only [stepsReadOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.map_cons, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (dstep_ok hsp hL hm hI (hsm st (List.mem_cons_self ..)) (hS st (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (dsteps_ok hsp hL hm l I₁ (fun st' h => hsm st' (List.mem_cons_of_mem _ h))
      (fun st' h => hS st' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

theorem dblCms_run {F : Type _} [Lean.Grind.CommRing F] (S : RcbSlots) (p : Pt) (E : Nat → F)
    (hd : (rcbW S p).Nodup) :
    (runSteps (dblCmsSteps S p) E p.x, runSteps (dblCmsSteps S p) E p.y, runSteps (dblCmsSteps S p) E p.z) =
      dblJF (E p.x) (E p.y) (E p.z) := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  obtain h10 := Ne.symm h01
  obtain h20 := Ne.symm h02
  obtain h30 := Ne.symm h03
  obtain h40 := Ne.symm h04
  obtain h50 := Ne.symm h05
  obtain h60 := Ne.symm h06
  obtain h70 := Ne.symm h07
  obtain h80 := Ne.symm h08
  obtain h21 := Ne.symm h12
  obtain h31 := Ne.symm h13
  obtain h41 := Ne.symm h14
  obtain h51 := Ne.symm h15
  obtain h61 := Ne.symm h16
  obtain h71 := Ne.symm h17
  obtain h81 := Ne.symm h18
  obtain h32 := Ne.symm h23
  obtain h42 := Ne.symm h24
  obtain h52 := Ne.symm h25
  obtain h62 := Ne.symm h26
  obtain h72 := Ne.symm h27
  obtain h82 := Ne.symm h28
  obtain h43 := Ne.symm h34
  obtain h53 := Ne.symm h35
  obtain h63 := Ne.symm h36
  obtain h73 := Ne.symm h37
  obtain h83 := Ne.symm h38
  obtain h54 := Ne.symm h45
  obtain h64 := Ne.symm h46
  obtain h74 := Ne.symm h47
  obtain h84 := Ne.symm h48
  obtain h65 := Ne.symm h56
  obtain h75 := Ne.symm h57
  obtain h85 := Ne.symm h58
  obtain h76 := Ne.symm h67
  obtain h86 := Ne.symm h68
  obtain h87 := Ne.symm h78
  simp only [dblCmsSteps, runSteps, List.foldl, DStep.run, FOp.run, Function.update_apply, dblJF, smulN,
    Prod.mk.injEq, *, ite_true, ite_false]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem dblCms_reads (S : RcbSlots) (p : Pt) : stepsReadOk (dblCmsSteps S p) [p.x, p.y, p.z] = true := by
  simp [dblCmsSteps, stepsReadOk, DStep.ins, DStep.out, FOp.ins, FOp.out]

theorem dblCms_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop} (h : ∀ x ∈ rcbW S p, Sl x) :
    ∀ st ∈ dblCmsSteps S p, ∀ x ∈ st.out :: st.ins, Sl x := by
  intro st hst x hx
  apply h x
  simp only [dblCmsSteps, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [DStep.out, DStep.ins, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] <;> grind

/-- The doubling with `cms` doubles a Jacobian triple, for P-384's `p` with BMI2 and ADX. -/
theorem doubleCms_dblOk {M : Mod} {C : Curve} (hsp : M.sparse = true) (hm : UnitMod C.p (2 ^ (64 * M.n)))
    (hC : Law C) (ha : AM3 C) {S : RcbSlots} : DblOk M S C (doubleCms M S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  refine WP.mono ((blocks_wp _).mpr (dsteps_ok hsp hL hm _ hI
    (fun st hst => by
      simp only [dblCmsSteps, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rfl)
    (dblCms_slots hSl) (dblCms_reads S p))) fun t ⟨k, I⟩ =>
    ⟨k.mono fun x hx => ?_, _, I.sub fun x hx => ?_, InvJ.dbl' hC ha hQ hJ (dblCms_run S p E hnd)⟩
  · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
    exact dblCms_slots (fun _ h => h) st hst st.out (List.mem_cons_self ..)
  · apply mem_stepsValid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [dblCmsSteps, DStep.out, FOp.out]

end VG.Proof.Weierstrass.X86_64
