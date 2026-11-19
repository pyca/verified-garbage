module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86_64.MulP
public import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Mont.X86_64.ProdX
public import VerifiedGarbage.Proof.Mont.X86_64.SqrM
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Mont.X86_64.WideMul`, which only this module used -/

section

/-!
# Montgomery arithmetic on x86-64: the multiplication with the accumulator in memory

The accumulator of `mulW` is `T = [tmp] + 2^(64 n) (r9 + 2⁶⁴ r10)` (`accW`). A
row of `rcx · [d]` and its carry add `rcx [d]` to it (`memRowCarry_ok`); a
round makes `2⁶⁴ T' = T + a_i B + u m` and keeps `T < 2m` (`roundW_ok`), as
`round_ok` does with the accumulator in registers; `n` rounds from zero give
`2^(64 n) T = A B + U m` (`roundsW_ok`). Then `csubW` reduces `T` below `m`
into `[o]` (`csubW_ok`), and `mulW_ok` is `mul_ok` for any number of words.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 sub_borrow sbb_borrow)

/-- The accumulator: `[tmp] + 2^(64 n) (r9 + 2⁶⁴ r10)`. -/
def accW (s : State) (base : Addr) (M : Mod) : Nat :=
  wordsVal s.mem base M.tmp M.n + 2 ^ (64 * M.n) * ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat)

/-- The registers a round changes. -/
abbrev roundRegs : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10]

/-- A row of `rcx · [d]` into the accumulator, and its carry into `r9` and
`r10`, if the sum fits. -/
theorem memRowCarry_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {d : Nat} (htmp : M.tmp + 8 * M.n ≤ size) (hd : d + 8 * M.n ≤ size)
    (hsep : d + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ d)
    (hb : accW s base M + (s.gpr .rcx).toNat * wordsVal s.mem base d M.n < 2 ^ (64 * M.n) * 2 ^ 128) :
    WP isa (.block (memRow M.n M.tmp d ++ carryUp .r9 .r10)) s fun s' =>
      accW s' base M = accW s base M + (s.gpr .rcx).toNat * wordsVal s.mem base d M.n ∧
      KeepRegs [.r8, .rbp, .rax, .rdx, .r9, .r10] s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs htmp hd hsep) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain g9 : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr .r9 (by decide)
  obtain g10 : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr .r10 (by decide)
  simp only [accW] at hb ⊢
  generalize hP : 2 ^ (64 * M.n) = P at hb e₁ ⊢
  obtain hP0 : 0 < P := hP ▸ Nat.two_pow_pos _
  obtain hc : (s₁.gpr .r9).toNat + 2 ^ 64 * (s₁.gpr .r10).toNat + (s₁.gpr .rbp).toNat < 2 ^ 128 := by
    rw [g9, g10]
    obtain h' : P * (((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat) + (s₁.gpr .rbp).toNat) <
        P * 2 ^ 128 := by
      rw [Nat.mul_add]; omega_arith
    exact Nat.lt_of_mul_lt_mul_left h'
  refine WP.mono (carryUp_ok s₁ (by decide) hc) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs')).trans ((Keeps.regs k₂).mono (by sub_regs')),
    fun x hx => by rw [k₂.2.1, O₁ x hx]⟩
  rw [k₂.2.1, e₂, g9, g10, Nat.mul_add P _ (s₁.gpr .rbp).toNat]
  omega_arith

/-- Round `i` of `mulW`: `2⁶⁴ T' = T + a_i B + u m`, and `T' < 2m` if `T < 2m`. -/
theorem roundW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : 0 < M.n) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b)
    (hmT : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo)
    (hm : wordsVal s.mem base M.mo M.n = m) (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) (hT : accW s base M < 2 * m) :
    WP isa (.block (roundW M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * accW s' base M = accW s base M +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      accW s' base M < 2 * m ∧ s'.gpr .r10 = 0 ∧
      KeepRegs roundRegs s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  obtain hP : 2 ^ (64 * M.n) * 2 ^ 128 = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by rw [Nat.mul_assoc]
  obtain hlim : (2 ^ 64 + 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    have : (2 ^ 64 + 1) * m ≤ (2 ^ 64 + 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ (by omega_arith)
    obtain h2 : (2 ^ 64 + 1) * 2 ^ (64 * M.n) ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
      rw [Nat.mul_comm (2 ^ 64 + 1), Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by decide)
    omega_arith
  simp only [roundW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rcx ha) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain hA := (word s.mem base (a + 8 * i)).isLt
  obtain hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  obtain hT₁ : accW s₁ base M = accW s base M := by
    simp only [accW, hm₁, k₁.1 .r9 (by decide), k₁.1 .r10 (by decide)]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (memRowCarry_ok hs₁ (d := b) htmp hb hbT (by
      rw [hT₁, c₁, hm₁, hP]; omega_arith)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hT₁, c₁, hm₁] at e₂
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `u = t₀ m' mod 2⁶⁴`.
  rw [WP.block_append_iff, show ([.mov .r8 (.mem (sc M.tmp)), .mov .rax (.reg .r8), .movImm64 .rcx M.minv,
      .mul .rcx, .mov .rcx (.reg .rax)] : List Instr) = [.mov .r8 (.mem (sc M.tmp))] ++
      [.mov .rax (.reg .r8), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] from rfl,
    WP.block_append_iff]
  refine WP.mono (movMem_ok hs₂ .r8 (d := M.tmp) (by omega_arith)) fun s₃ ⟨l₃, _, k₃⟩ => ?_
  refine WP.mono (uBlock_ok s₃ .r8 M.minv) fun s₄ ⟨u₄, k₄⟩ => ?_
  obtain hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  obtain hm₄ : s₄.mem = s₂.mem := by rw [k₄.2.1, k₃.2.1]
  obtain hT₄ : accW s₄ base M = accW s₂ base M := by
    simp only [accW, hm₄, k₄.1 .r9 (by decide), k₄.1 .r10 (by decide), k₃.1 .r9 (by decide),
      k₃.1 .r10 (by decide)]
  obtain hmo₂ : wordsVal s₂.mem base M.mo M.n = m := by
    rw [O₂.wordsVal hmT (by omega_arith), hm₁, hm]
  obtain hu := (s₄.gpr .rcx).isLt
  obtain hum : (s₄.gpr .rcx).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega_arith) (Nat.le_refl _)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (memRowCarry_ok hs₄ (d := M.mo) htmp hmo hmT (by
      rw [hT₄, e₂, hm₄, hmo₂, hP]; omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [hT₄, e₂, hm₄, hmo₂] at e₅
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- The low word is zero.
  obtain hlow : (word s₅.mem base M.tmp).toNat = 0 := by
    obtain hmod : ∀ u : State, accW u base M % 2 ^ 64 = (word u.mem base M.tmp).toNat := by
      intro u
      obtain ⟨n', hn'⟩ : ∃ n', M.n = n' + 1 := ⟨M.n - 1, by omega_arith⟩
      simp only [accW, hn', wordsVal, pow64_succ]
      rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (word u.mem base M.tmp).isLt
    obtain hl := mont_low (word s₂.mem base M.tmp).toNat M.minv.toNat m hinv
    rw [l₃] at u₄
    rw [← u₄] at hl
    obtain h₂ := hmod s₂
    obtain h₅ := hmod s₅
    obtain e₅' : accW s₅ base M = accW s₂ base M + (s₄.gpr .rcx).toNat * m := by rw [e₅, e₂]
    omega_arith
  refine WP.mono (shiftDown_ok hs₅ hn htmp) fun s₆ ⟨e₆, r9₆, r10₆, k₆, O₆⟩ => ?_
  obtain hshift : 2 ^ 64 * accW s₆ base M = accW s₅ base M := by
    obtain ⟨n', hn'⟩ : ∃ n', M.n = n' + 1 := ⟨M.n - 1, by omega_arith⟩
    obtain hw5 : wordsVal s₅.mem base M.tmp M.n =
        (word s₅.mem base M.tmp).toNat + 2 ^ 64 * wordsVal s₅.mem base (M.tmp + 8) (M.n - 1) := by
      rw [hn']; rfl
    obtain hp : 2 ^ (64 * M.n) = 2 ^ 64 * 2 ^ (64 * (M.n - 1)) := by
      rw [hn', pow64_succ, Nat.add_sub_cancel]
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [accW]
    rw [e₆, r9₆, r10₆, hw5, hlow, hz, hp]
    grind
  refine ⟨⟨(s₄.gpr .rcx).toNat, by rw [hshift, e₅]⟩, ?_, r10₆, ?_, fun x hx => ?_⟩
  · have : 2 ^ 64 * accW s₆ base M < 2 ^ 64 * (2 * m) := by rw [hshift, e₅]; omega_arith
    exact Nat.lt_of_mul_lt_mul_left this
  · exact ((((((Keeps.regs k₁).mono (by sub_regs')).trans (k₂.mono (by sub_regs'))).trans
      ((Keeps.regs k₃).mono (by sub_regs'))).trans ((Keeps.regs k₄).mono (by sub_regs'))).trans
      (k₅.mono (by sub_regs'))).trans (k₆.mono (by sub_regs'))
  · rw [O₆ x hx, O₅ x hx, hm₄, O₂ x hx, hm₁]

/-- `k` rounds of `mulW`, from a cleared accumulator. -/
theorem roundsW_ok {M : Mod} (hn : 0 < M.n) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htmp : M.tmp + 8 * M.n ≤ size) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b)
    (hmT : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size →
      wordsVal s.mem base M.mo M.n = m → wordsVal s.mem base b M.n < m → accW s base M = 0 →
      s.gpr .r10 = 0 →
      WP isa (.block ((List.range k).flatMap (roundW M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * accW s' base M =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        accW s' base M < 2 * m ∧ s'.gpr .r10 = 0 ∧
        KeepRegs roundRegs s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem
  | 0, _, s, _, _, _, hB, h0, h10 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega_arith,
      h10, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk, s, base, hs, hm, hB, h0, h10 => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (roundsW_ok hn ha hb hmo htmp haT hbT hmT hinv k (by omega_arith) hs hm hB h0 h10)
      fun s₁ ⟨⟨U, eU⟩, hT, _, k₁, O₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by decide)
    obtain hm₁ : wordsVal s₁.mem base M.mo M.n = m := by rw [O₁.wordsVal hmT (by omega_arith), hm]
    obtain hB₁ : wordsVal s₁.mem base b M.n = wordsVal s.mem base b M.n := O₁.wordsVal hbT (by omega_arith)
    obtain hA₁ : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) :=
      O₁.word (by omega_arith) (by omega_arith)
    refine WP.mono (roundW_ok hs₁ hn (i := k) (by omega_arith) hb hmo htmp hbT hmT hm₁ hinv
      (by rw [hB₁]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, h10₂, k₂, O₂⟩ => ?_
    rw [hB₁, hA₁] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, h10₂, k₁.trans k₂, fun x hx => by rw [O₂ x hx, O₁ x hx]⟩
    calc 2 ^ (64 * (k + 1)) * accW s₂ base M
        = 2 ^ (64 * k) * (2 ^ 64 * accW s₂ base M) := by
          rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ (64 * k) * accW s₁ base M +
          2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
          2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
      _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) *
          wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
          rw [eU, Nat.add_mul, Nat.add_mul]; omega_arith
      _ = _ := by rw [wordsVal_succ_top]

end VG.Proof.Mont.X86_64

end

end


/-!
# Montgomery arithmetic on x86-64: P-521's product by rows, with BMI2 and ADX

`mulPX o a b` (`Impl/Mont/X86_64.lean`) for P-521's `p = 2⁵²¹ - 1`: the
first row puts `a_0 [b]` in the nine registers of the accumulator, whatever
they held, by one carry chain (`mulAccs_ok`, `accRow_ok`), and stores its low
word (`xRow0_ok`); each later row adds `a_i [b]` to them and stores its low
word (`xRow_inv`), and the nine rows (`xRows_ok`) leave
`a b` in the temporary area (its low words) and the registers (its high
ones). The reduction (`xRed_ok`) then leaves `W` with
`2⁵⁷⁶ W = a b + U p` in the registers, as `mulP`'s columns do (`mulP_arith`),
and `xCanon_ok` stores `W mod p` (`mulPX_ok`).

The rows run with `rdi` moved `c` bytes into the working space (`ScrC`,
`rdiAdd_ok`, `rdiSub_ok`), their operands at `rc c d` (`readSrc_rc`,
`storeXC_ok`, `maddStepsC_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono madd_ok movRdx_ok movRdxImm_ok of_setReg
  of_setFlags adc_carry add_carry mulx_arith execMulx_eq se0 mulx_ok mulAcc_ok)

/-! ## The registers -/

theorem xAcc_add9 (k : Nat) : xAcc (k + 9) = xAcc k := by
  simp only [xAcc, Nat.add_mod_right]

theorem xAcc_mod (k : Nat) : xAcc k = xAcc (k % 9) := by
  simp only [xAcc, Nat.mod_mod]

theorem xWin_mod (k : Nat) : xWin k = xWin (k % 9) := by
  simp only [xWin]
  exact List.map_congr_left fun j _ => by
    rw [xAcc_mod, xAcc_mod (k % 9 + j)]
    congr 1
    omega_arith

theorem xWin_fresh (k : Nat) : FreshX (xWin k) := by
  rw [xWin_mod]
  obtain h : ∀ k < 9, FreshX (xWin k) := by unfold FreshX; decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem xAcc_ne (k : Nat) :
    xAcc k ≠ .rax ∧ xAcc k ≠ .rcx ∧ xAcc k ≠ .rdx ∧ xAcc k ≠ .rdi ∧ xAcc k ∈ xRegs := by
  rw [xAcc_mod]
  obtain h : ∀ k < 9, xAcc k ≠ .rax ∧ xAcc k ≠ .rcx ∧ xAcc k ≠ .rdx ∧ xAcc k ≠ .rdi ∧ xAcc k ∈ xRegs := by
    decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem xWin_sub (k : Nat) : ∀ r ∈ xWin k, r ∈ xRegs := by
  intro r hr
  simp only [xWin, List.mem_map, List.mem_range] at hr
  obtain ⟨j, -, rfl⟩ := hr
  exact (xAcc_ne _).2.2.2.2

/-! ## Steps -/

/-- `xor eax, eax`: both carries clear. -/
theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun s' =>
      s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, BitVec.xor_self,
    RegUpd.cf_setReg, of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov r32, 0`, the flags unchanged. -/
theorem movZero_ok (s : State) (t : Reg) :
    WP isa (.block [.mov32 t (.imm 0)]) s fun s' =>
      s'.gpr t = 0 ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `[d] = r`, the flags unchanged. -/
theorem storeX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.store (sc d) r]) s fun s' =>
      s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.of = s.of ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `rdi` moved into the working space

`mulPX` and `sqrPX` move `rdi` to their operand (`rc`), so that its words
are at displacements of a byte, shorter to encode. -/

/-- The working space while `rdi` is `c` bytes past its base. -/
structure ScrC (s : State) (base : Addr) (size c : Nat) : Prop where
  rdi : s.gpr .rdi = off base c
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64

theorem ScrC.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size c : Nat}
    (hs : ScrC s base size c) (h : Keeps rs s s') (hr : .rdi ∉ rs) : ScrC s' base size c :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

theorem ScrC.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size c : Nat}
    (hs : ScrC s base size c) (h : KeepRegs rs s s') (hr : .rdi ∉ rs) : ScrC s' base size c :=
  ⟨(h.gpr _ hr).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem off_ofInt (base : Addr) (c d : Nat) :
    off base c + BitVec.ofInt 64 ((d : Int) - c) = off base d := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega_arith

theorem ea_rc {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c) (d : Nat) :
    s.ea (rc c d) = off base d := by
  simp only [State.ea, rc, hs.rdi]
  exact off_ofInt base c d

theorem readSrc_rc {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c) {d : Nat}
    (hd : d + 8 ≤ size) : readSrc s (.mem (rc c d)) = some (word s.mem base d) := by
  show s.load64 (s.ea (rc c d)) = _
  rw [ea_rc hs, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr,
    Offset.contains_base base hd (by have := hs.nowrap; omega_arith)⟩]

theorem store_rc {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c) {d : Nat}
    (hd : d + 8 ≤ size) (v : BitVec 64) :
    s.store64 (s.ea (rc c d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [ea_rc hs, State.store64, ite_eq_left ⟨_, hs.wr,
    Offset.contains_base base hd (by have := hs.nowrap; omega_arith)⟩]

/-- `storeX_ok` while `rdi` is moved. -/
theorem storeXC_ok {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c) (r : Reg)
    {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.store (rc c d) r]) s fun s' =>
      s'.mem = s.mem.writeW (off base d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.of = s.of ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_rc hs hd, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## Operands through other registers

The rows read their operands through a register `r` (`rcR`): `rdi` inline,
or the register a pointer to the operand is passed in (`PtrC`). What the
rows store goes to the temporary area at `rdi` (`ScrC`), apart from the
operands (`Apart`). -/

/-- The registers the rows may change: none of them is one an operand is
read through. -/
abbrev rowRegs : List Reg := .rax :: .rcx :: .rdx :: xRegs

theorem mem_rowRegs_x {t : Reg} (h : t ∈ xRegs) : t ∈ rowRegs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

/-- Every register of a list of `rax`, `rcx`, `rdx` and `xAcc`s is in
`rowRegs`. -/
macro "rows_sub" : tactic => `(tactic| plain_simp_names (
                   simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
                   try and_intros
                   all_goals first | decide | exact mem_rowRegs_x (xAcc_ne _).2.2.2.2))

/-- The memory `⟨base, size⟩`, readable (within a readable or writable
region), while the register `r` (`rdi`, `rsi` or `rbx`) is `c` bytes past its
base. -/
structure PtrC (s : State) (r : Reg) (base : Addr) (size c : Nat) : Prop where
  gpr : s.gpr r = off base c
  rd : ∃ R ∈ s.rd ++ s.wr, ∀ d, d + 8 ≤ size → R.Contains (off base d) 8
  nowrap : base.toNat + size ≤ 2 ^ 64
  reg : r = .rdi ∨ r = .rsi ∨ r = .rbx

theorem PtrC.not_mem {s : State} {r : Reg} {base : Addr} {size c : Nat} (hp : PtrC s r base size c)
    {t : Reg} (ht : t ∈ rowRegs) : t ≠ r := by
  rcases hp.reg with rfl | rfl | rfl <;> revert t <;> decide

theorem PtrC.of_keeps {rs : List Reg} {s s' : State} {r : Reg} {base : Addr} {size c : Nat}
    (hp : PtrC s r base size c) (h : Keeps rs s s') (hr : ∀ t ∈ rs, t ∈ rowRegs) :
    PtrC s' r base size c :=
  ⟨(h.1 _ fun hm => hp.not_mem (hr _ hm) rfl).trans hp.gpr, by rw [h.2.2.1, h.2.2.2]; exact hp.rd,
    hp.nowrap, hp.reg⟩

theorem PtrC.of_keepRegs {rs : List Reg} {s s' : State} {r : Reg} {base : Addr} {size c : Nat}
    (hp : PtrC s r base size c) (h : KeepRegs rs s s') (hr : ∀ t ∈ rs, t ∈ rowRegs) :
    PtrC s' r base size c :=
  ⟨(h.gpr _ fun hm => hp.not_mem (hr _ hm) rfl).trans hp.gpr, by rw [h.rd, h.wr]; exact hp.rd,
    hp.nowrap, hp.reg⟩

/-- `PtrC` after a store: the registers and regions unchanged. -/
theorem PtrC.of_store {s s' : State} {r : Reg} {base : Addr} {size c : Nat} (hp : PtrC s r base size c)
    (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : PtrC s' r base size c :=
  ⟨by rw [hg]; exact hp.gpr, by rw [hrd, hwr]; exact hp.rd, hp.nowrap, hp.reg⟩

theorem ScrC.toPtr {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c) :
    PtrC s .rdi base size c :=
  ⟨hs.rdi, ⟨_, List.mem_append_right _ hs.wr, fun _ hd =>
    Offset.contains_base base hd (by have := hs.nowrap; omega_using [hd, this])⟩, hs.nowrap, Or.inl rfl⟩

theorem ea_rcR {s : State} {r : Reg} {base : Addr} {size c : Nat} (hp : PtrC s r base size c) (d : Nat) :
    s.ea (rcR r c d) = off base d := by
  simp only [State.ea, rcR, hp.gpr]
  exact off_ofInt base c d

theorem readSrc_rcR {s : State} {r : Reg} {base : Addr} {size c : Nat} (hp : PtrC s r base size c)
    {d : Nat} (hd : d + 8 ≤ size) : readSrc s (.mem (rcR r c d)) = some (word s.mem base d) := by
  show s.load64 (s.ea (rcR r c d)) = _
  obtain ⟨R, hR, hc⟩ := hp.rd
  rw [ea_rcR hp, State.load64, ite_eq_left ⟨R, hR, hc d hd⟩]

/-- The `n` bytes at `off p d` are outside the offsets `[o, o + k)` of
`base`. -/
def Apart (p : Addr) (d n : Nat) (base : Addr) (o k : Nat) : Prop :=
  ∀ i < n, ofs base (off p d + BitVec.ofNat 64 i) < o ∨ o + k ≤ ofs base (off p d + BitVec.ofNat 64 i)

theorem Apart.sub {p base : Addr} {d n o k d' n' : Nat} (h : Apart p d n base o k) (h₁ : d ≤ d')
    (h₂ : d' + n' ≤ d + n) : Apart p d' n' base o k := fun i hi => by
  obtain e : off p d + BitVec.ofNat 64 (d' - d + i) = off p d' + BitVec.ofNat 64 i := by
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega_arith
  have := h (d' - d + i) (by omega_arith)
  rwa [e] at this

theorem Apart.mono {p base : Addr} {d n o k o' k' : Nat} (h : Apart p d n base o k) (h₁ : o ≤ o')
    (h₂ : o' + k' ≤ o + k) : Apart p d n base o' k' := fun i hi => by
  have := h i hi
  omega_arith

/-- Offsets apart in the same memory. -/
theorem Apart.of_sep (base : Addr) {d n o k : Nat} (h : d + n ≤ o ∨ o + k ≤ d) (hw : d + n ≤ 2 ^ 64) :
    Apart base d n base o k := fun i hi => by
  rw [ofs_off base (by omega_arith)]
  omega_arith

theorem _root_.VG.Proof.Mont.Outside.word' {base p : Addr} {o k d : Nat} {m m' : Mem} (h : Outside base o k m m')
    (hp : Apart p d 8 base o k) : word m' p d = word m p d :=
  (Mem.readW_congr fun i hi => (h _ (hp i (by omega_arith))).symm).symm

theorem _root_.VG.Proof.Mont.Outside.wordsVal' {base p : Addr} {o k : Nat} {m m' : Mem} (h : Outside base o k m m') :
    ∀ {d n : Nat}, Apart p d (8 * n) base o k → wordsVal m' p d n = wordsVal m p d n
  | _, 0, _ => rfl
  | d, n + 1, hp => by
    simp only [VG.Proof.Mont.wordsVal]
    rw [h.word' (hp.sub (Nat.le_refl _) (by omega_arith)), h.wordsVal' (hp.sub (Nat.le_add_right d 8) (by omega_arith))]

theorem se_imm {c : Nat} (hc : c < 2 ^ 31) : (BitVec.ofNat 32 c).signExtend 64 = BitVec.ofNat 64 c := by
  obtain hm : (BitVec.ofNat 32 c).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_arith
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem cOf_lt (d : Nat) : cOf d < 2 ^ 31 := by
  unfold cOf; split <;> omega_arith

/-- `rdi += c`: the working space with `rdi` moved by `c`. -/
theorem rdiAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {c : Nat}
    (hc : c < 2 ^ 31) :
    WP isa (.block [rdiAdd c]) s fun s' => ScrC s' base size c ∧ Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp only [rdiAdd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, hs.wr, hs.nowrap⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, hs.rdi, se_imm hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rdi -= c`: back to the working space. -/
theorem rdiSub_ok {s : State} {base : Addr} {size c : Nat} (hs : ScrC s base size c)
    (hc : c < 2 ^ 31) :
    WP isa (.block [rdiSub c]) s fun s' => Scr s' base size ∧ Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp only [rdiSub, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, hs.wr, hs.nowrap⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, hs.rdi, se_imm hc]
    rw [BitVec.add_sub_cancel]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem Scr.toC {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    ScrC s base size 0 :=
  ⟨by rw [hs.rdi]; simp [off], hs.wr, hs.nowrap⟩

theorem se_ofInt {z : Int} (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) :
    (BitVec.ofInt 32 z).signExtend 64 = BitVec.ofInt 64 z := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  rw [Int.bmod_def, Int.bmod_def]; split <;> split <;> omega_arith

/-- `rdi` from `c` to `c'` bytes past the base. -/
theorem rdiMove_ok {s : State} {base : Addr} {size c c' : Nat} (hs : ScrC s base size c)
    (hc : c < 2 ^ 31) (hc' : c' < 2 ^ 31) :
    WP isa (.block [rdiMove c c']) s fun s' => ScrC s' base size c' ∧ Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp only [rdiMove, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, hs.wr, hs.nowrap⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, hs.rdi, se_ofInt (z := (c' : Int) - c) (by omega_arith) (by omega_arith)]
    exact off_ofInt base c c'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `stores_ok` while `rdi` is moved (`storesC`). -/
theorem storesC_ok {size c : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {o : Nat},
    ScrC s base size c → o + 8 * ts.length ≤ size → ts.Nodup →
    WP isa (.block (storesC c ts o)) s fun s' =>
      wordsVal s'.mem base o ts.length = regsVal s ts ∧ KeepRegs [] s s' ∧
      Outside base o (8 * ts.length) s.mem s'.mem
  | [], s, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, o, hs, ho, hd => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ho
    rw [storesC, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.store (rc c o) t]) s
        (fun s₁ => s₁.mem = s.mem.writeW (off base o) (s.gpr t) ∧ KeepRegs [] s s₁ ∧
          s₁.gpr = s.gpr) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_rc hs (d := o) (by omega_arith),
        Option.some.injEq, exists_eq_left']
      exact ⟨trivial, ⟨fun _ _ => rfl, rfl, rfl⟩, trivial⟩)
      fun s₁ ⟨m₁, k₁, g₁⟩ => ?_
    obtain hs₁ := hs.of_keepRegs k₁ (by simp)
    obtain O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
    refine WP.mono (storesC_ok ts hs₁ (o := o + 8) (by omega_arith) (List.nodup_cons.mp hd).2)
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => ?_⟩
    · rw [List.length_cons, wordsVal, O₂.word (by omega_arith) (by omega_arith), m₁, word_writeW_self, e₂, regsVal,
        regsVal_congr (s := s) fun q _ => congrFun g₁ q]
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega_arith), O₁ x (by omega_arith)]

/-- `maddSteps_ok` while `rdi` is moved (`maddStepsC`): `k` products along `ts`: `rdx · [d … d + 8k)` added at the words
`ts₀ … ts_k`, with the carries OF into `ts₀` and CF into `ts₁` in, and OF
(into `ts_k`) and CF (into `ts_{k+1}`) out. -/
theorem maddStepsC_ok {r : Reg} {size c₀ : Nat} : ∀ (k : Nat) (ts : List Reg) {s : State} {base : Addr}
    {d : Nat} {c o : Bool}, PtrC s r base size c₀ → (∀ t ∈ ts, t ∈ xRegs) → d + 8 * k ≤ size →
    k + 1 ≤ ts.length → FreshX ts → s.cf = some c → s.of = some o →
    WP isa (.block (maddStepsC r c₀ k ts d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (ts.take (k + 1)) + 2 ^ (64 * k) * o'.toNat + 2 ^ (64 * (k + 1)) * c'.toNat =
        regsVal s (ts.take (k + 1)) + o.toNat + 2 ^ 64 * c.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rcx :: .rax :: ts.take (k + 1)) s s'
  | 0, ts, s, _, _, c, o, _, _, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, [_], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | k + 1, x :: y :: rest, s, base, d, c, o, hs, hts, hd, hl, hf, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, -⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, -⟩ := hf.tail.head
    obtain hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hl
    rw [maddStepsC, madd_eq, WP.block_append_iff]
    refine WP.mono (madd_ok s (readSrc_rcR hs (d := d) (by omega_arith)) (fun _ h => nomatch h) hc ho hxc hxa
      hyc hya hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    obtain hx := mem_rowRegs_x (hts x (List.mem_cons_self ..))
    obtain hy := mem_rowRegs_x (hts y (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    obtain hs₁ := hs.of_keeps k₁ (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> first | decide | exact hx | exact hy)
    refine WP.mono (maddStepsC_ok k (y :: rest) hs₁ (fun t ht => hts t (List.mem_cons_of_mem _ ht))
      (d := d + 8) (by omega_arith)
      (by simp only [List.length_cons]; omega_arith) hf.tail cf₁ of₁) fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ =>
      ⟨c', o', cf₂, of₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      obtain hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxc, hxa, fun h => hxn (List.mem_of_mem_take h)⟩)
      obtain hR : regsVal s₁ (rest.take k) = regsVal s (rest.take k) := regsVal_congr fun q hq => k₁.1 q (by
        obtain hq' := List.mem_of_mem_take hq
        have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
          fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      simp only [wordsVal]
      rw [hx₂]
      rw [pow64_succ (k + 1), pow64_succ k] at *
      simp only [Nat.mul_assoc] at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      omega_arith
    · simp only [List.take_succ_cons] at k₂ ⊢
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `mov eax, 0`, `adox t, rax`: the carry OF added into `t`, CF unchanged. -/
theorem xTail_ok (s : State) {t : Reg} {o : Bool} (ho : s.of = some o) (hta : t ≠ .rax) :
    WP isa (.block (xTail t)) s fun s' =>
      ∃ o', s'.of = some o' ∧ s'.cf = s.cf ∧
        (s'.gpr t).toNat + 2 ^ 64 * o'.toNat = (s.gpr t).toNat + o.toNat ∧ Keeps [.rax, t] s s' := by
  apply WP.of_runBlock
  simp only [xTail, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, execAdox, readSrc, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hta, of_setReg, of_setFlags, ho, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have := adc_carry (s.gpr t) (BitVec.setWidth 64 (0 : BitVec 32)) o
    simp only [show (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2,
      RegUpd.gpr_setFlags]

/-! ## A row -/

/-- The accumulator's words: word `c` is the register `xAcc c`. -/
def xg (s : State) (c : Nat) : Nat := (s.gpr (xAcc c)).toNat

theorem regsVal_xAccs (s : State) : ∀ n k,
    regsVal s ((List.range n).map fun j => xAcc (k + j)) = hval (xg s) k n := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, regsVal, hval, Nat.add_zero]
    congr 2
    rw [← ih (k + 1)]
    congr 1
    exact List.map_congr_left fun j _ => by simp only [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]

theorem regsVal_xWin (s : State) (k : Nat) : regsVal s (xWin k) = hval (xg s) k 9 :=
  regsVal_xAccs s 9 k

theorem rdi_not_rows (k n : Nat) : Reg.rdi ∉ Reg.rcx :: Reg.rax :: (xWin k).take n := by
  intro h
  simp only [List.mem_cons, reduceCtorEq, false_or] at h
  have := xWin_sub k .rdi (List.mem_of_mem_take h)
  simp [xRegs] at this

/-- Registers `xAcc c` and `xAcc d` of one window (`c < d < c + 9`) differ. -/
theorem xAcc_ne_of {c d : Nat} (h1 : c < d) (h2 : d < c + 9) : xAcc c ≠ xAcc d := by
  rw [xAcc_mod c, xAcc_mod d]
  obtain h : ∀ i < 9, ∀ j < 9, i ≠ j → xAcc i ≠ xAcc j := by decide
  exact h _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) (by omega_arith)

theorem xRow_eq (M : Mod) (ra rb : Reg) (c a b i : Nat) :
    xRow M ra rb c a b i = .mov .rdx (.mem (rcR ra c (a + 8 * i))) :: xRowR M rb c b i := rfl

/-- `xRow` but its first instruction, with `rdx = v` (`a_i`) already loaded. -/
theorem xRowR_ok {s : State} {base bB : Addr} {size zB c₀ : Nat} (hs : ScrC s base size c₀)
    {rb : Reg} (hpb : PtrC s rb bB zB c₀) {M : Mod} {b : Nat}
    (i : Nat) {v : BitVec 64} (hdx : s.gpr .rdx = v) (hb : b + 72 ≤ zB) (ht : M.tmp + 8 * i + 8 ≤ size)
    (hbt : Apart bB b 72 base (M.tmp + 8 * i) 8)
    (hB : hval (xg s) i 9 + v.toNat * wordsVal s.mem bB b 9 < (2 ^ 64) ^ 10) :
    WP isa (.block (xRowR M rb c₀ b i)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * i)).toNat + 2 ^ 64 * hval (xg s') (i + 1) 9 =
        hval (xg s) i 9 + v.toNat * wordsVal s.mem bB b 9 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base (M.tmp + 8 * i) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain ⟨hia, hic, hid, hii, -⟩ := xAcc_ne i
  obtain ⟨hja, hjc, hjd, hji, -⟩ := xAcc_ne (i + 1)
  obtain hij : xAcc i ≠ xAcc (i + 1) := xAcc_ne_of (by omega_using []) (by omega_using [])
  rw [xRowR, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have d₁ : s.gpr .rdx = v := hdx
  obtain k₁ : Keeps [.rdx] s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain hpb₁ := hpb.of_keeps k₁ (by rows_sub)
  refine WP.mono (xorRax_ok s) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_
  obtain hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  obtain hpb₂ := hpb₁.of_keeps k₂ (by rows_sub)
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s₂ (readSrc_rcR hpb₂ (d := b) (by omega_arith)) (fun _ h => nomatch h) c₂ o₂ hic hia
    hjc hja hij) fun s₃ ⟨c₃, o₃, cf₃, of₃, e₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, Ne.symm hii, Ne.symm hji⟩)
  obtain hpb₃ := hpb₂.of_keeps k₃ (by rows_sub)
  rw [WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₃ (xAcc i) ht) fun s₄ ⟨m₄, g₄, cf₄, of₄, rd₄, wr₄⟩ => ?_
  obtain hs₄ : ScrC s₄ base size c₀ := ⟨by rw [g₄]; exact hs₃.rdi, by rw [wr₄]; exact hs₃.wr, hs₃.nowrap⟩
  obtain hpb₄ := hpb₃.of_store g₄ rd₄ wr₄
  refine WP.mono (movZero_ok s₄ (xAcc i)) fun s₅ ⟨z₅, cf₅, of₅, k₅⟩ => ?_
  obtain hpb₅ := hpb₄.of_keeps k₅ (by rows_sub)
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsC_ok 8 (xWin (i + 1)) hpb₅ (xWin_sub _) (d := b + 8) (by omega_arith) (by simp [xWin])
    (xWin_fresh _) (cf₅.trans (cf₄.trans cf₃)) (of₅.trans (of₄.trans of₃)))
    fun s₆ ⟨c₆, o₆, cf₆, of₆, e₆, k₆⟩ => ?_
  obtain ⟨hka, -, -, -, -⟩ := xAcc_ne (i + 9)
  refine WP.mono (xTail_ok s₆ of₆ hka) fun s₇ ⟨o₇, _, cf₇, e₇, k₇⟩ => ?_
  -- The memory.
  obtain hm₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  obtain hm₃ : s₃.mem = s.mem := k₃.2.1.trans hm₂
  obtain hm₇ : s₇.mem = s₄.mem := k₇.2.1.trans (k₆.2.1.trans k₅.2.1)
  obtain O₄ : Outside base (M.tmp + 8 * i) 8 s.mem s₄.mem := by
    rw [m₄, hm₃]; exact writeW_outside _ _ _ (by omega_arith)
  obtain hw : (word s₇.mem base (M.tmp + 8 * i)).toNat = xg s₃ i := by
    rw [hm₇, m₄, word_writeW_self]; rfl
  obtain hB₅ : wordsVal s₅.mem bB (b + 8) 8 = wordsVal s.mem bB (b + 8) 8 := by
    rw [k₅.2.1]; exact O₄.wordsVal' (hbt.sub (by omega_arith) (by omega_arith))
  obtain hb₂ : word s₂.mem bB b = word s.mem bB b := by rw [hm₂]
  -- `rdx` is `a_i` until the products.
  obtain hdx₅ : s₅.gpr .rdx = v := by
    rw [k₅.1 .rdx (by simpa using Ne.symm hid), g₄, k₃.1 .rdx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, Ne.symm hid, Ne.symm hjd⟩), k₂.1 .rdx (by decide), d₁]
  obtain hdx₂ : s₂.gpr .rdx = v := by rw [k₂.1 .rdx (by decide), d₁]
  -- The registers through the steps.
  obtain hx₂ : ∀ c, xg s₂ c = xg s c := fun c => by
    simp only [xg]
    rw [k₂.1 _ (by simpa using (xAcc_ne c).1), k₁.1 _ (by simpa using (xAcc_ne c).2.2.1)]
  obtain h₅ : ∀ c, i + 2 ≤ c → c < i + 9 → xg s₅ c = xg s c := fun c h1 h2 => by
    obtain n1 : xAcc c ≠ xAcc i := (xAcc_ne_of (show i < c by omega_arith) (by omega_arith)).symm
    obtain n2 : xAcc c ≠ xAcc (i + 1) := (xAcc_ne_of (show i + 1 < c by omega_arith) (by omega_arith)).symm
    simp only [xg]
    rw [k₅.1 _ (by simpa using n1), g₄, k₃.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(xAcc_ne c).2.1, (xAcc_ne c).1, n1, n2⟩)]
    exact hx₂ c
  obtain h₅₁ : xg s₅ (i + 1) = xg s₃ (i + 1) := by
    simp only [xg]
    rw [k₅.1 _ (by simpa using hij.symm), g₄]
  obtain h₅₉ : xg s₅ (i + 9) = 0 := by simp only [xg, xAcc_add9, z₅]; rfl
  obtain h₇ : ∀ c, i + 1 ≤ c → c < i + 9 → xg s₇ c = xg s₆ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₇.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(xAcc_ne c).1, xAcc_ne_of (by omega_arith) (by omega_arith)⟩)]
  -- The values.
  obtain hT₆ : regsVal s₆ ((xWin (i + 1)).take (8 + 1)) = hval (xg s₆) (i + 1) 8 + (2 ^ 64) ^ 8 * xg s₆ (i + 9) := by
    rw [List.take_of_length_le (by simp [xWin]), regsVal_xWin, hval_succ_last]
  obtain hT₅ : regsVal s₅ ((xWin (i + 1)).take (8 + 1)) = xg s₃ (i + 1) + 2 ^ 64 * hval (xg s) (i + 2) 7 := by
    rw [List.take_of_length_le (by simp [xWin]), regsVal_xWin, hval_succ_last, h₅₉, Nat.mul_zero,
      Nat.add_zero, hval, h₅₁, hval_congr (g := xg s) (fun c h1 h2 => h₅ c (by omega_arith) (by omega_arith))]
  obtain hT₇ : hval (xg s₇) (i + 1) 9 = hval (xg s₆) (i + 1) 8 + (2 ^ 64) ^ 8 * xg s₇ (i + 9) := by
    rw [hval_succ_last, hval_congr (g := xg s₆) (fun c h1 h2 => h₇ c (by omega_arith) (by omega_arith))]
  obtain hV : hval (xg s) i 9 = xg s i + 2 ^ 64 * (xg s (i + 1) + 2 ^ 64 * hval (xg s) (i + 2) 7) := by
    simp only [hval]
  have hBv : wordsVal s.mem bB b 9 = (word s.mem bB b).toNat + 2 ^ 64 * wordsVal s.mem bB (b + 8) 8 := rfl
  rw [hT₆, hT₅, hdx₅, hB₅] at e₆
  rw [hdx₂, hb₂] at e₃
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₃
  change xg s₃ i + 2 ^ 64 * xg s₃ (i + 1) + 2 ^ 64 * o₃.toNat + 2 ^ 128 * c₃.toNat =
    xg s₂ i + 2 ^ 64 * xg s₂ (i + 1) + _ at e₃
  rw [hx₂, hx₂] at e₃
  change xg s₇ (i + 9) + 2 ^ 64 * o₇.toNat = xg s₆ (i + 9) + o₆.toNat at e₇
  refine ⟨?_, ?_, ?_⟩
  · rw [hw, hT₇]
    rw [hV, hBv] at hB ⊢
    generalize v.toNat = A at *
    generalize (word s.mem bB b).toNat = B0 at *
    generalize wordsVal s.mem bB (b + 8) 8 = B1 at *
    generalize hval (xg s) (i + 2) 7 = H at *
    generalize hval (xg s₆) (i + 1) 8 = G at *
    rw [Nat.mul_add A, Nat.mul_left_comm A] at hB ⊢
    generalize A * B0 = P0 at *
    generalize A * B1 = P1 at *
    have := Bool.toNat_le o₇
    have := Bool.toNat_le c₆
    omega_arith
  · have hr' : ∀ r, r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs →
        r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ ∀ k, xAcc k ≠ r := fun r hr => by
      simp only [List.mem_cons, not_or] at hr
      exact ⟨hr.1, hr.2.1, hr.2.2.1, fun k h => hr.2.2.2 (h ▸ (xAcc_ne k).2.2.2.2)⟩
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨ra, rc, rd, rx⟩ := hr' r hr
      obtain hw : r ∉ Reg.rcx :: Reg.rax :: (xWin (i + 1)).take (8 + 1) := by
        simp only [List.mem_cons, not_or]
        exact ⟨rc, ra, fun h => by
          have := List.mem_of_mem_take h
          simp only [xWin, List.mem_map] at this
          obtain ⟨j, -, hj⟩ := this
          exact rx _ hj⟩
      rw [k₇.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ra, (rx _).symm⟩),
        k₆.1 r hw, k₅.1 r (by simpa using (rx i).symm), g₄,
        k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                   exact ⟨rc, ra, (rx i).symm, (rx (i + 1)).symm⟩),
        k₂.1 r (by simpa using ra), k₁.1 r (by simpa using rd)]
    · rw [k₇.2.2.1, k₆.2.2.1, k₅.2.2.1, rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₇.2.2.2, k₆.2.2.2, k₅.2.2.2, wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [hm₇]; exact O₄

theorem wordsVal_succ_last (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d (n + 1) = wordsVal m base d n + (2 ^ 64) ^ n * (word m base (d + 8 * n)).toNat := by
  obtain h := wordsVal_hval m base d 0
  simp only [Nat.mul_zero, Nat.add_zero] at h
  rw [h, h, hval_succ_last, Nat.zero_add]

/-- `xRowR` as row `n` after the first `n` (`xRow_inv`), from `rdx = a_n`. -/
theorem xRowR_inv {s₀ s : State} {base bA bB : Addr} {size zB c₀ : Nat} (hsS : ScrC s base size c₀)
    {rb : Reg} (hpb : PtrC s rb bB zB c₀) {M : Mod} {a b : Nat}
    (hb : b + 72 ≤ zB) (ht : M.tmp + 72 ≤ size)
    (hbt : Apart bB b 72 base M.tmp 72) {n : Nat} (hn : n < 9) (hat : Apart bA (a + 8 * n) 8 base M.tmp (8 * n))
    (hdx : s.gpr .rdx = word s₀.mem bA (a + 8 * n)) (O : Outside base M.tmp (8 * n) s₀.mem s.mem)
    (e : wordsVal s.mem base M.tmp n + (2 ^ 64) ^ n * hval (xg s) n 9 =
      wordsVal s₀.mem bA a n * wordsVal s₀.mem bB b 9) :
    WP isa (.block (xRowR M rb c₀ b n)) s fun s' =>
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base M.tmp (8 * (n + 1)) s₀.mem s'.mem ∧
      wordsVal s'.mem base M.tmp (n + 1) + (2 ^ 64) ^ (n + 1) * hval (xg s') (n + 1) 9 =
        wordsVal s₀.mem bA a (n + 1) * wordsVal s₀.mem bB b 9 := by
    have hnw := hsS.nowrap
    obtain hA : (word s.mem bA (a + 8 * n)) = word s₀.mem bA (a + 8 * n) :=
      O.word' hat
    obtain hBv : wordsVal s.mem bB b 9 = wordsVal s₀.mem bB b 9 := O.wordsVal' (hbt.mono (Nat.le_refl _) (by omega_using [hn]))
    obtain hAn : wordsVal s₀.mem bA a n < (2 ^ 64) ^ n := by
      rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ _
    obtain hBlt : wordsVal s₀.mem bB b 9 < (2 ^ 64) ^ 9 := by
      rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
    obtain hAw := (word s₀.mem bA (a + 8 * n)).isLt
    -- The registers' value is below `[b]`.
    obtain hV : hval (xg s) n 9 < wordsVal s₀.mem bB b 9 + 1 := by
      obtain h1 : (2 ^ 64) ^ n * hval (xg s) n 9 ≤ wordsVal s₀.mem bA a n * wordsVal s₀.mem bB b 9 := by
        omega_arith
      obtain h2 : wordsVal s₀.mem bA a n * wordsVal s₀.mem bB b 9 ≤
          (2 ^ 64) ^ n * wordsVal s₀.mem bB b 9 := Nat.mul_le_mul_right _ (Nat.le_of_lt hAn)
      obtain h3 := Nat.le_of_mul_le_mul_left (Nat.le_trans h1 h2) (Nat.pow_pos (by decide))
      omega_arith
    obtain hrow : hval (xg s) n 9 + (word s.mem bA (a + 8 * n)).toNat * wordsVal s.mem bB b 9 <
        (2 ^ 64) ^ 10 := by
      rw [hA, hBv]
      have : (word s₀.mem bA (a + 8 * n)).toNat * wordsVal s₀.mem bB b 9 ≤
          (2 ^ 64 - 1) * wordsVal s₀.mem bB b 9 := Nat.mul_le_mul_right _ (by omega_arith)
      have : (2 ^ 64 - 1) * wordsVal s₀.mem bB b 9 + wordsVal s₀.mem bB b 9 + 1 ≤ (2 ^ 64) ^ 10 := by
        have : (2 ^ 64 - 1) * wordsVal s₀.mem bB b 9 + wordsVal s₀.mem bB b 9 =
            2 ^ 64 * wordsVal s₀.mem bB b 9 := by
          rw [← Nat.succ_mul]
        rw [this, show (2 ^ 64) ^ 10 = 2 ^ 64 * (2 ^ 64) ^ 9 by rw [pow64_succ']]
        have := Nat.mul_le_mul_left (2 ^ 64) (show wordsVal s₀.mem bB b 9 + 1 ≤ (2 ^ 64) ^ 9 by omega_using [hBlt])
        omega_using [hBlt]
      omega_arith
    refine WP.mono (xRowR_ok hsS hpb n (hdx.trans hA.symm) (by omega_using [hb]) (by omega_using [ht, hn]) (hbt.mono (by omega_using []) (by omega_using [hn])) hrow)
      fun s' ⟨e', k', O'⟩ => ⟨k', (O.mono (Nat.le_refl _) (by omega_using [])).trans (O'.mono (by omega_using []) (by omega_using [])), ?_⟩
    rw [hA, hBv] at e'
    rw [wordsVal_succ_last s'.mem, wordsVal_succ_last s₀.mem bA a, O'.wordsVal (by omega_arith) (by omega_arith),
      pow64_succ', Nat.mul_comm (2 ^ 64), Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, e',
      Nat.mul_add, ← Nat.add_assoc, e, Nat.add_mul, Nat.mul_assoc]


/-- Row `n` after the first `n`: from the low `n` words of `[a]_n · [b]` in
the temporary area and the others in the registers of `xWin n`, the same
for `n + 1`. -/
theorem xRow_inv {s₀ s : State} {base bA bB : Addr} {size zA zB c₀ : Nat} (hs : ScrC s₀ base size c₀)
    {ra rb : Reg} (hpa : PtrC s₀ ra bA zA c₀) (hpb : PtrC s₀ rb bB zB c₀) {M : Mod} {a b : Nat}
    (ha : a + 72 ≤ zA) (hb : b + 72 ≤ zB) (ht : M.tmp + 72 ≤ size)
    (hbt : Apart bB b 72 base M.tmp 72) {n : Nat} (hn : n < 9) (hat : Apart bA (a + 8 * n) 8 base M.tmp (8 * n))
    (k : KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s) (O : Outside base M.tmp (8 * n) s₀.mem s.mem)
    (e : wordsVal s.mem base M.tmp n + (2 ^ 64) ^ n * hval (xg s) n 9 =
      wordsVal s₀.mem bA a n * wordsVal s₀.mem bB b 9) :
    WP isa (.block (xRow M ra rb c₀ a b n)) s fun s' =>
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s' ∧ Outside base M.tmp (8 * (n + 1)) s₀.mem s'.mem ∧
      wordsVal s'.mem base M.tmp (n + 1) + (2 ^ 64) ^ (n + 1) * hval (xg s') (n + 1) 9 =
        wordsVal s₀.mem bA a (n + 1) * wordsVal s₀.mem bB b 9 := by
    have hnw := hs.nowrap
    obtain hsS : ScrC s base size c₀ := hs.of_keepRegs k (by decide)
    obtain hA : (word s.mem bA (a + 8 * n)) = word s₀.mem bA (a + 8 * n) :=
      O.word' hat
    rw [xRow_eq, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movRdx_ok s (readSrc_rcR (hpa.of_keepRegs k (by rows_sub)) (d := a + 8 * n) (by omega_using [ha, hn])))
      fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
    obtain hx : ∀ c, xg s₁ c = xg s c := fun c => by
      simp only [xg]; rw [k₁.1 _ (by simpa using (xAcc_ne c).2.2.1)]
    have hm : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (xRowR_inv (hsS.of_keeps k₁ (by decide)) ((hpb.of_keepRegs k (by rows_sub)).of_keeps k₁
      (by rows_sub)) hb ht hbt hn hat (d₁.trans hA) (by rw [hm]; exact O)
      (by rw [hm, hval_congr (g := xg s) (fun c _ _ => hx c)]; exact e)) fun s' ⟨k', O', e'⟩ => ⟨?_, O', e'⟩
    refine ⟨fun r hr => ?_, k'.rd.trans (k₁.2.2.1.trans k.rd), k'.wr.trans (k₁.2.2.2.trans k.wr)⟩
    rw [k'.gpr r hr, k₁.1 r (by simp only [List.mem_singleton]; intro h; exact hr (h ▸ by simp)), k.gpr r hr]

/-! ## The reduction -/

/-- `adox x, src`: `src` and OF added into `x`, CF unchanged. -/
theorem adoxS_ok (s : State) {x : Reg} {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v)
    (himm : ∀ n, src ≠ .imm n) {o : Bool} (ho : s.of = some o) :
    WP isa (.block [.adox x src]) s fun s' =>
      ∃ o', s'.of = some o' ∧ s'.cf = s.cf ∧
        (s'.gpr x).toNat + 2 ^ 64 * o'.toNat = (s.gpr x).toNat + v.toNat + o.toNat ∧ Keeps [x] s s' := by
  obtain e : execAdox x src s = some ((s.setFlags s.cf (some (2 ^ 64 ≤ (s.gpr x).toNat + v.toNat + o.toNat))
      s.zf s.sf).setReg x (s.gpr x + v + (BitVec.ofBool o).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, e, RegUpd.gpr_setReg_self, of_setReg,
    of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adcx x, src`: `src` and CF added into `x`, OF unchanged. -/
theorem adcxS_ok (s : State) {x : Reg} {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v)
    (himm : ∀ n, src ≠ .imm n) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.adcx x src]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
        (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + v.toNat + c.toNat ∧ Keeps [x] s s' := by
  obtain e : execAdcx x src s = some ((s.setFlags (some (2 ^ 64 ≤ (s.gpr x).toNat + v.toNat + c.toNat)) s.of
      s.zf s.sf).setReg x (s.gpr x + v + (BitVec.ofBool c).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, e, RegUpd.gpr_setReg_self, of_setReg,
    of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `setCF`: CF set, OF clear. -/
theorem setCF_ok (s : State) :
    WP isa (.block setCF) s fun s' => s'.cf = some true ∧ s'.of = some false ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [setCF, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, execAlu, readSrc32,
    readSrc, Option.bind_some, State.setReg32, BitVec.xor_self, RegUpd.gpr_setReg_self, arithFlags,
    State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- The reduction: for `P` with its low words at `[tmp]` and its high words
`H` in `xWin 9`, `U + 2⁵⁷⁶ W + 2¹¹⁵² acc = P + 512 · 2⁵¹² U + 2⁵⁷⁶`, for `U`
the words left at `[tmp]` (`P`'s but `u₈` over `P₈`) and `W` those in
`xWin 9` (the carry of one in at word 9 for `xCanon`). -/
theorem xRed_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod}
    (ht : M.tmp + 72 ≤ size) :
    WP isa (.block (xRed M c₀)) s fun s' => ∃ acc : Nat,
      wordsVal s'.mem base M.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s') 9 9 + (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 * acc =
        wordsVal s.mem base M.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s) 9 9 +
          512 * (2 ^ 64) ^ 8 * wordsVal s'.mem base M.tmp 9 + (2 ^ 64) ^ 9 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base (M.tmp + 64) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain ⟨h9a, h9c, h9d, h9i, -⟩ := xAcc_ne 9
  rw [show xRed M c₀ = [.mov32 .rdx (.imm 512)] ++ (setCF ++ ([.mulx .rcx .rax (.mem (rc c₀ M.tmp)),
      .adox .rax (.mem (rc c₀ (M.tmp + 64))), .store (rc c₀ (M.tmp + 64)) .rax, .adcx (xAcc 9) (.reg .rcx)] ++
      (maddStepsC .rdi c₀ 8 (xWin 9) (M.tmp + 8) ++ xTail (xAcc 17)))) by simp only [xRed, List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s 512) fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setCF_ok s₁) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_
  rw [WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s₂ (readSrc_rc hs₂ (d := M.tmp) (by omega_arith))
    (fun _ h => nomatch h) (by decide : Reg.rcx ≠ .rax)) fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adoxS_ok s₃ (readSrc_rc hs₃ (d := M.tmp + 64) (by omega_arith)) (fun _ h => nomatch h)
    (of₃.trans o₂)) fun s₄ ⟨o₄, of₄, cf₄, e₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₄ .rax (d := M.tmp + 64) (by omega_arith)) fun s₅ ⟨m₅, g₅, cf₅, of₅, rd₅, wr₅⟩ => ?_
  obtain hs₅ : ScrC s₅ base size c₀ := ⟨by rw [g₅]; exact hs₄.rdi, by rw [wr₅]; exact hs₄.wr, hs₄.nowrap⟩
  refine WP.mono (adcxS_ok s₅ (x := xAcc 9) (src := .reg .rcx) rfl (fun _ h => nomatch h)
    (cf₅.trans (cf₄.trans (cf₃.trans c₂)))) fun s₆ ⟨c₆, cf₆, of₆, e₆, k₆⟩ => ?_
  obtain hs₆ := hs₅.of_keeps k₆ (by simpa using Ne.symm h9i)
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsC_ok 8 (xWin 9) hs₆.toPtr (xWin_sub _) (d := M.tmp + 8) (by omega_arith) (by simp [xWin])
    (xWin_fresh _) cf₆ (of₆.trans (of₅.trans of₄))) fun s₇ ⟨c₇, o₇, cf₇, of₇, e₇, k₇⟩ => ?_
  obtain hs₇ := hs₆.of_keeps k₇ (rdi_not_rows _ _)
  obtain ⟨h17a, -, -, -, -⟩ := xAcc_ne 17
  refine WP.mono (xTail_ok s₇ of₇ h17a) fun s₈ ⟨o₈, _, cf₈, e₈, k₈⟩ => ?_
  -- The memory.
  obtain hm₄ : s₄.mem = s.mem := k₄.2.1.trans (k₃.2.1.trans (k₂.2.1.trans k₁.2.1))
  obtain hm₈ : s₈.mem = s₅.mem := k₈.2.1.trans (k₇.2.1.trans k₆.2.1)
  obtain O₅ : Outside base (M.tmp + 64) 8 s.mem s₅.mem := by
    rw [m₅, hm₄]; exact writeW_outside _ _ _ (by omega_arith)
  obtain hU : wordsVal s₅.mem base M.tmp 9 = (word s.mem base M.tmp).toNat + 2 ^ 64 *
      (wordsVal s.mem base (M.tmp + 8) 7 + (2 ^ 64) ^ 7 * (s₄.gpr .rax).toNat) := by
    rw [show wordsVal s₅.mem base M.tmp 9 = (word s₅.mem base M.tmp).toNat + 2 ^ 64 *
      wordsVal s₅.mem base (M.tmp + 8) (7 + 1) from rfl, wordsVal_succ_last,
      O₅.word (by omega_arith) (by omega_arith), O₅.wordsVal (by omega_arith) (by omega_arith), m₅,
      show M.tmp + 8 + 8 * 7 = M.tmp + 64 by omega_arith, word_writeW_self]
  obtain hP : wordsVal s.mem base M.tmp 9 = (word s.mem base M.tmp).toNat + 2 ^ 64 *
      (wordsVal s.mem base (M.tmp + 8) 7 + (2 ^ 64) ^ 7 * (word s.mem base (M.tmp + 64)).toNat) := by
    rw [show wordsVal s.mem base M.tmp 9 = (word s.mem base M.tmp).toNat + 2 ^ 64 *
      wordsVal s.mem base (M.tmp + 8) (7 + 1) from rfl, wordsVal_succ_last,
      show M.tmp + 8 + 8 * 7 = M.tmp + 64 by omega_arith]
  obtain hUhi : wordsVal s₆.mem base (M.tmp + 8) 8 =
      wordsVal s.mem base (M.tmp + 8) 7 + (2 ^ 64) ^ 7 * (s₄.gpr .rax).toNat := by
    rw [k₆.2.1, wordsVal_succ_last, O₅.wordsVal (by omega_arith) (by omega_arith), m₅,
      show M.tmp + 8 + 8 * 7 = M.tmp + 64 by omega_arith, word_writeW_self]
  refine ⟨o₈.toNat + c₇.toNat, ?_, ?_, ?_⟩
  -- The registers.
  obtain hdx : (s₆.gpr .rdx).toNat = 512 := by
    rw [k₆.1 .rdx (by simpa using Ne.symm h9d), g₅, k₄.1 .rdx (by decide), k₃.1 .rdx (by decide),
      k₂.1 .rdx (by decide), d₁]; rfl
  obtain hdx₂ : (s₂.gpr .rdx).toNat = 512 := by rw [k₂.1 .rdx (by decide), d₁]; rfl
  obtain hrcx : s₅.gpr .rcx = s₃.gpr .rcx := by rw [g₅, k₄.1 .rcx (by decide)]
  obtain hrax : s₅.gpr .rax = s₄.gpr .rax := by rw [g₅]
  obtain h₆ : ∀ c, 10 ≤ c → c < 18 → xg s₆ c = xg s c := fun c h1 h2 => by
    obtain n9 : xAcc c ≠ xAcc 9 := (xAcc_ne_of (show 9 < c by omega_arith) (by omega_arith)).symm
    simp only [xg]
    rw [k₆.1 _ (by simpa using n9), g₅, k₄.1 _ (by simpa using (xAcc_ne c).1),
      k₃.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                 exact ⟨(xAcc_ne c).2.1, (xAcc_ne c).1⟩),
      k₂.1 _ (by simpa using (xAcc_ne c).1), k₁.1 _ (by simpa using (xAcc_ne c).2.2.1)]
  obtain h9₅ : xg s₅ 9 = xg s 9 := by
    simp only [xg]
    rw [g₅, k₄.1 _ (by simpa using h9a),
      k₃.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9c, h9a⟩),
      k₂.1 _ (by simpa using h9a), k₁.1 _ (by simpa using h9d)]
  obtain h₈ : ∀ c, 9 ≤ c → c < 17 → xg s₈ c = xg s₇ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₈.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(xAcc_ne c).1, xAcc_ne_of (by omega_arith) (by omega_arith)⟩)]
  obtain hT₇ : regsVal s₇ ((xWin 9).take (8 + 1)) = hval (xg s₇) 9 8 + (2 ^ 64) ^ 8 * xg s₇ 17 := by
    rw [List.take_of_length_le (by simp [xWin]), regsVal_xWin, hval_succ_last]
  obtain hT₆ : regsVal s₆ ((xWin 9).take (8 + 1)) = xg s₆ 9 + 2 ^ 64 * hval (xg s) 10 8 := by
    rw [List.take_of_length_le (by simp [xWin]), regsVal_xWin, hval,
      hval_congr (g := xg s) (fun c h1 h2 => h₆ c (by omega_arith) (by omega_arith))]
  obtain hT₈ : hval (xg s₈) 9 9 = hval (xg s₇) 9 8 + (2 ^ 64) ^ 8 * xg s₈ 17 := by
    rw [hval_succ_last, hval_congr (g := xg s₇) (fun c h1 h2 => h₈ c (by omega_arith) (by omega_arith))]
  have hH : hval (xg s) 9 9 = xg s 9 + 2 ^ 64 * hval (xg s) 10 8 := rfl
  rw [hT₇, hT₆, hdx, hUhi] at e₇
  change xg s₆ 9 + 2 ^ 64 * c₆.toNat = xg s₅ 9 + (s₅.gpr .rcx).toNat + true.toNat at e₆
  change xg s₈ 17 + 2 ^ 64 * o₈.toNat = xg s₇ 17 + o₇.toNat at e₈
  rw [hdx₂, show word s₂.mem base M.tmp = word s.mem base M.tmp by
    rw [k₂.2.1, k₁.2.1]] at e₃
  rw [show word s₃.mem base (M.tmp + 64) = word s.mem base (M.tmp + 64) by
    rw [k₃.2.1, k₂.2.1, k₁.2.1]] at e₄
  rw [hrcx, h9₅] at e₆
  rw [hm₈, hU, hP, hT₈, hH]
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at e₄ e₆
  generalize (word s.mem base M.tmp).toNat = P0 at *
  generalize (word s.mem base (M.tmp + 64)).toNat = P8 at *
  generalize wordsVal s.mem base (M.tmp + 8) 7 = L at *
  generalize (s₄.gpr .rax).toNat = u at *
  generalize (s₃.gpr .rax).toNat = r0 at *
  generalize (s₃.gpr .rcx).toNat = r1 at *
  generalize hval (xg s) 10 8 = Hr at *
  generalize hval (xg s₇) 9 8 = G at *
  omega_arith
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      obtain ⟨ra, rc, rd, rx⟩ := hr
      obtain rx' : ∀ k, xAcc k ≠ r := fun k h => rx (h ▸ (xAcc_ne k).2.2.2.2)
      obtain hw : r ∉ Reg.rcx :: Reg.rax :: (xWin 9).take (8 + 1) := by
        simp only [List.mem_cons, not_or]
        exact ⟨rc, ra, fun h => by
          have := List.mem_of_mem_take h
          simp only [xWin, List.mem_map] at this
          obtain ⟨j, -, hj⟩ := this
          exact rx' _ hj⟩
      rw [k₈.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ra, (rx' _).symm⟩),
        k₇.1 r hw, k₆.1 r (by simpa using (rx' 9).symm), g₅, k₄.1 r (by simpa using ra),
        k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨rc, ra⟩),
        k₂.1 r (by simpa using ra), k₁.1 r (by simpa using rd)]
    · rw [k₈.2.2.1, k₇.2.2.1, k₆.2.2.1, rd₅, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₈.2.2.2, k₇.2.2.2, k₆.2.2.2, wr₅, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [hm₈]; exact O₅

/-! ## The final reduction -/

/-- `adc t, 0`. -/
theorem adcZ_ok (s : State) (t : Reg) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .adc t (.imm 0)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ (s'.gpr t).toNat + 2 ^ 64 * c'.toNat = (s.gpr t).toNat + c.toNat ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have := adc_carry (s.gpr t) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `sbb t, 0`. -/
theorem sbbZ_ok (s : State) (t : Reg) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb t (.imm 0)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ (s'.gpr t).toNat + c.toNat = (s.gpr t).toNat + 2 ^ 64 * c'.toNat ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have := VG.Proof.X25519.X86_64.sbb_borrow (s.gpr t) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A borrow `c` subtracted down the words `ts`. -/
theorem sbbZs_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, ts.Nodup → s.cf = some c →
    WP isa (.block (ts.map fun t => .alu .sbb t (.imm 0))) s fun s' =>
      ∃ c', s'.cf = some c' ∧ regsVal s' ts + c.toNat = regsVal s ts + 2 ^ (64 * ts.length) * c'.toNat ∧
        Keeps ts s s'
  | [], s, c, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hn, hc => by
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (sbbZ_ok s t hc) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    obtain htn := (List.nodup_cons.mp hn).1
    refine WP.mono (sbbZs_ok ts (List.nodup_cons.mp hn).2 cf₁) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ =>
      ⟨c₂, cf₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    obtain hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    obtain ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t htn
    simp only [regsVal, List.length_cons, ht₂]
    rw [hR] at e₂
    rw [show 64 * (ts.length + 1) = 64 + 64 * ts.length by omega_arith, Nat.pow_add, Nat.mul_assoc]
    generalize 2 ^ (64 * ts.length) * c₂.toNat = X at *
    omega_arith

/-- `sub t, rax`. -/
theorem subRax_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .sub t (.reg .rax)]) s fun s' =>
      ∃ c, s'.cf = some c ∧ (s'.gpr t).toNat + (s.gpr .rax).toNat = (s.gpr t).toNat + 2 ^ 64 * c.toNat ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X25519.X86_64.sub_borrow _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `and t, 511`. -/
theorem and511_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .and t (.imm 511)]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat % 512 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [show ((511 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 9 - 1) by decide,
      BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rax = 1 - ⌊t / 512⌋` for `t < 1024`. -/
theorem notTop_ok (s : State) (t : Reg) (ht : (s.gpr t).toNat < 1024) :
    WP isa (.block [.mov .rax (.reg t), .shift .shr .rax 9, .alu .xor .rax (.imm 1)]) s fun s' =>
      (s'.gpr .rax).toNat = 1 - (s.gpr t).toNat / 512 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left',
    show 1 ≤ 9 ∧ 9 ≤ 63 from ⟨by decide, by decide⟩, and_self, ite_true]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, show ((1 : BitVec 32).signExtend 64).toNat = 1 by decide,
      Nat.shiftRight_eq_div_pow]
    have : (s.gpr t).toNat / 2 ^ 9 < 2 := by omega_arith
    rw [show (s.gpr t).toNat / 512 = (s.gpr t).toNat / 2 ^ 9 from rfl]
    rcases (by omega_arith : (s.gpr t).toNat / 2 ^ 9 = 0 ∨ (s.gpr t).toNat / 2 ^ 9 = 1) with h | h <;>
      rw [h] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr, ite_false]

/-! ## The first row -/

/-- The registers of words `j … j + k`. -/
def xSpan (j k : Nat) : List Reg := (List.range (k + 1)).map fun i => xAcc (j + i)

theorem mem_xSpan {j k : Nat} {r : Reg} (h : r ∈ xSpan j k) : ∃ i, i ≤ k ∧ r = xAcc (j + i) := by
  simp only [xSpan, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, by omega_arith, rfl⟩

theorem xAcc_mem_xSpan {j k i : Nat} (hi : i ≤ k) : xAcc (j + i) ∈ xSpan j k :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega_arith), rfl⟩

theorem not_mem_xSpan {r : Reg} (h : ∀ k, xAcc k ≠ r) (j k : Nat) : r ∉ xSpan j k := fun hr => by
  obtain ⟨i, -, e⟩ := mem_xSpan hr
  exact h _ e.symm

theorem mulAccs_eq (r : Reg) (c k j d : Nat) :
    mulAccs r c (k + 1) j d = Impl.X25519.X86_64.mulAcc (xAcc j) (xAcc (j + 1)) (.mem (rcR r c d)) ++
      mulAccs r c k (j + 1) (d + 8) := rfl

/-- `k` products into words that held nothing but word `j`: `rdx · [d … d + 8k)`
added at word `j` (with the carry CF in), each product's high half into the
next word, and the carry CF out of word `j + k - 1` into word `j + k`. -/
theorem mulAccs_ok {r : Reg} {size c₀ : Nat} : ∀ (k j : Nat) {s : State} {base : Addr} {d : Nat} {c : Bool},
    PtrC s r base size c₀ → d + 8 * k ≤ size → k ≤ 8 → s.cf = some c →
    WP isa (.block (mulAccs r c₀ k j d)) s fun s' => ∃ c', s'.cf = some c' ∧
      hval (xg s') j (k + 1) + (2 ^ 64) ^ k * c'.toNat =
        xg s j + c.toNat + (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rax :: xSpan j k) s s'
  | 0, j, s, base, d, c, _, _, _, hc => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, hc, by simp [hval, wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, j, s, base, d, c, hs, hd, hk, hc => by
    obtain ⟨hxa, -, hxd, -, -⟩ := xAcc_ne j
    obtain ⟨hya, -, hyd, -, -⟩ := xAcc_ne (j + 1)
    obtain hxy : xAcc j ≠ xAcc (j + 1) := xAcc_ne_of (by omega_arith) (by omega_arith)
    rw [mulAccs_eq, WP.block_append_iff]
    refine WP.mono (mulAcc_ok s (readSrc_rcR hs (d := d) (by omega_arith)) (fun _ h => nomatch h) hc hxa hya hxy)
      fun s₁ ⟨c₁, cf₁, _, e₁, k₁⟩ => ?_
    obtain hs₁ := hs.of_keeps k₁ (by rows_sub)
    refine WP.mono (mulAccs_ok k (j + 1) hs₁ (d := d + 8) (by omega_arith) (by omega_arith) cf₁)
      fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ⟨c₂, cf₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, Ne.symm hxd, Ne.symm hyd⟩)
      obtain hx₂ : xg s₂ j = xg s₁ j := congrArg BitVec.toNat (k₂.1 _ fun h => by
        rcases List.mem_cons.mp h with h | h
        · exact hxa h
        · obtain ⟨i, hi, e⟩ := mem_xSpan h
          exact xAcc_ne_of (show j < j + 1 + i by omega_arith) (by omega_arith) e)
      rw [k₁.2.1, hdx] at e₂
      change xg s₁ j + 2 ^ 64 * xg s₁ (j + 1) + 2 ^ 64 * c₁.toNat =
        xg s j + c.toNat + (s.gpr .rdx).toNat * (word s.mem base d).toNat at e₁
      rw [hval, hx₂, pow64_succ' k]
      simp only [wordsVal]
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      generalize hval (xg s₂) (j + 1) (k + 1) = H at *
      generalize (2 ^ 64) ^ k = Q at *
      generalize (s.gpr .rdx).toNat * wordsVal s.mem base (d + 8) k = W at *
      rw [Nat.mul_assoc]
      omega_arith
    · refine (k₁.mono fun r hr => ?_).trans (k₂.mono fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (by simpa using xAcc_mem_xSpan (j := j) (k := k + 1) (i := 0) (by omega_arith))
        · exact List.mem_cons_of_mem _ (xAcc_mem_xSpan (j := j) (k := k + 1) (i := 1) (by omega_arith))
      · rcases List.mem_cons.mp hr with h | h
        · exact h ▸ List.mem_cons_self ..
        · obtain ⟨i, hi, rfl⟩ := mem_xSpan h
          exact List.mem_cons_of_mem _ (by
            rw [show j + 1 + i = j + (i + 1) by omega_arith]; exact xAcc_mem_xSpan (by omega_arith))

/-- `mulAccs` from CF clear, then the carry into word `j + k` (`adc`): the
words `j … j + k` are word `j` plus `rdx · [d … d + 8k)`, if that fits. -/
theorem accRow_ok {s : State} {r : Reg} {base : Addr} {size c₀ : Nat} (hs : PtrC s r base size c₀) {k j d : Nat}
    (hd : d + 8 * k ≤ size) (hk : 1 ≤ k) (hk8 : k ≤ 8) (hc : s.cf = some false)
    (hB : xg s j + (s.gpr .rdx).toNat * wordsVal s.mem base d k < (2 ^ 64) ^ (k + 1)) :
    WP isa (.block (mulAccs r c₀ k j d ++ ([.alu .adc (xAcc (j + k)) (.imm 0)] : List Instr))) s fun s' =>
      hval (xg s') j (k + 1) = xg s j + (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rax :: xSpan j k) s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulAccs_ok k j hs hd hk8 hc) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
  refine WP.mono (adcZ_ok s₁ (xAcc (j + k)) cf₁) fun s₂ ⟨c₂, _, e₂, k₂⟩ => ⟨?_, ?_⟩
  · have hlo : hval (xg s₂) j k = hval (xg s₁) j k := hval_congr fun c h1 h2 => by
      simp only [xg]
      rw [k₂.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact xAcc_ne_of (show c < j + k by omega_arith) (by omega_arith))]
    rw [hval_succ_last] at e₁ ⊢
    rw [hlo]
    change xg s₂ (j + k) + 2 ^ 64 * c₂.toNat = xg s₁ (j + k) + c₁.toNat at e₂
    simp only [Bool.toNat_false, Nat.add_zero] at e₁ hB
    obtain hQ : (2 ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 := Nat.pow_succ ..
    rw [hQ] at hB
    generalize (2 ^ 64) ^ k = Q at *
    obtain hc₂ : c₂.toNat = 0 := by
      rcases c₂ with _ | _
      · rfl
      · exfalso
        simp only [Bool.toNat_true, Nat.mul_one] at e₂
        have : Q * 2 ^ 64 ≤ Q * (xg s₁ (j + k) + c₁.toNat) := Nat.mul_le_mul_left _ (by omega_arith)
        rw [Nat.mul_add] at this
        omega_arith
    rw [hc₂, Nat.mul_zero, Nat.add_zero] at e₂
    rw [e₂, Nat.mul_add]
    omega_arith
  · exact k₁.trans (k₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact hr ▸ List.mem_cons_of_mem _ (xAcc_mem_xSpan (Nat.le_refl _)))

/-- Row 0: `a_0 [b]`, its word 0 stored at `[tmp]`, the words `1 … 9` in the
registers, whatever they held before. -/
theorem xRow0_ok {s : State} {base bA bB : Addr} {size zA zB c₀ : Nat} (hs : ScrC s base size c₀)
    {ra rb : Reg} (hpa : PtrC s ra bA zA c₀) (hpb : PtrC s rb bB zB c₀) {M : Mod} {a b : Nat}
    (ha : a + 8 ≤ zA) (hb : b + 72 ≤ zB) (ht : M.tmp + 8 ≤ size)
    (hbt : Apart bB b 72 base M.tmp 8) :
    WP isa (.block (xRow0 M ra rb c₀ a b)) s fun s' =>
      (word s'.mem base M.tmp).toNat + 2 ^ 64 * hval (xg s') 1 9 =
        (word s.mem bA a).toNat * wordsVal s.mem bB b 9 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base M.tmp 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain ⟨h1a, -, h1d, h1i, -⟩ := xAcc_ne 1
  rw [xRow0, List.append_assoc, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_rcR hpa (d := a) (by omega_arith))) fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hpb₁ := hpb.of_keeps k₁ (by rows_sub)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (xorRax_ok s₁) fun s₂ ⟨c₂, _, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain hpb₂ := hpb₁.of_keeps k₂ (by rows_sub)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ (readSrc_rcR hpb₂ (d := b) (by omega_arith)) (fun _ h => nomatch h) h1a)
    fun s₃ ⟨e₃, cf₃, _, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h1i, by decide⟩)
  obtain hpb₃ := hpb₂.of_keeps k₃ (by rows_sub)
  refine WP.mono (storeXC_ok hs₃ .rax ht) fun s₄ ⟨m₄, g₄, cf₄, _, rd₄, wr₄⟩ => ?_
  obtain hpb₄ := hpb₃.of_store g₄ rd₄ wr₄
  -- The memory.
  obtain hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
  obtain O₄ : Outside base M.tmp 8 s.mem s₄.mem := by
    rw [m₄, hm₃]; exact writeW_outside _ _ _ (by omega_arith)
  obtain hB₄ : wordsVal s₄.mem bB (b + 8) 8 = wordsVal s.mem bB (b + 8) 8 :=
    O₄.wordsVal' (hbt.sub (by omega_arith) (by omega_arith))
  -- `rdx` is `a_0`.
  obtain hdx₂ : s₂.gpr .rdx = word s.mem bA a := by rw [k₂.1 .rdx (by decide), d₁]
  obtain hdx₄ : s₄.gpr .rdx = word s.mem bA a := by
    rw [g₄, k₃.1 .rdx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm h1d, by decide⟩), hdx₂]
  obtain hb₂ : word s₂.mem bB b = word s.mem bB b := by rw [k₂.2.1, k₁.2.1]
  rw [hdx₂, hb₂] at e₃
  have hBv : wordsVal s.mem bB b 9 = (word s.mem bB b).toNat + 2 ^ 64 * wordsVal s.mem bB (b + 8) 8 := rfl
  obtain hA := (word s.mem bA a).isLt
  obtain hB8 : wordsVal s.mem bB (b + 8) 8 < (2 ^ 64) ^ 8 := by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 8
  obtain hx₄ : xg s₄ 1 = (s₃.gpr (xAcc 1)).toNat := by simp only [xg, g₄]
  -- The products of `a_0` by `b_1 … b_8`.
  obtain hrow : xg s₄ 1 + (s₄.gpr .rdx).toNat * wordsVal s₄.mem bB (b + 8) 8 < (2 ^ 64) ^ (8 + 1) := by
    rw [hx₄, hdx₄, hB₄, pow64_succ']
    obtain h1 : (word s.mem bA a).toNat * (word s.mem bB b).toNat < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_lt_of_lt hA (word s.mem bB b).isLt
    obtain h2 : (word s.mem bA a).toNat * wordsVal s.mem bB (b + 8) 8 ≤
        (2 ^ 64 - 1) * wordsVal s.mem bB (b + 8) 8 := Nat.mul_le_mul_right _ (by omega_arith)
    obtain h3 : (2 ^ 64 - 1) * wordsVal s.mem bB (b + 8) 8 + wordsVal s.mem bB (b + 8) 8 =
        2 ^ 64 * wordsVal s.mem bB (b + 8) 8 := by rw [← Nat.succ_mul]
    obtain h4 : 2 ^ 64 * wordsVal s.mem bB (b + 8) 8 + 2 ^ 64 ≤ 2 ^ 64 * (2 ^ 64) ^ 8 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hB8
    omega_arith
  refine WP.mono (accRow_ok hpb₄ (k := 8) (j := 1) (d := b + 8) (by omega_arith) (by omega_arith) (by omega_arith)
    (cf₄.trans (cf₃.trans c₂)) hrow) fun s₅ ⟨e₅, k₅⟩ => ⟨?_, ?_, ?_⟩
  · have hw : (word s₅.mem base M.tmp).toNat = (s₃.gpr .rax).toNat := by
      rw [k₅.2.1, m₄, word_writeW_self]
    rw [hw, e₅, hx₄, hdx₄, hB₄, hBv]
    generalize (word s.mem bA a).toNat = A at *
    generalize wordsVal s.mem bB (b + 8) 8 = W at *
    generalize (word s.mem bB b).toNat = B0 at *
    rw [Nat.mul_add A B0, Nat.mul_left_comm A (2 ^ 64) W, Nat.mul_add (2 ^ 64)]
    omega_arith
  · have hr' : ∀ r, r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs →
        r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ ∀ k, xAcc k ≠ r := fun r hr => by
      simp only [List.mem_cons, not_or] at hr
      exact ⟨hr.1, hr.2.1, hr.2.2.1, fun k h => hr.2.2.2 (h ▸ (xAcc_ne k).2.2.2.2)⟩
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨ra, -, rd, rx⟩ := hr' r hr
      rw [k₅.1 r (by
          simp only [List.mem_cons, not_or]
          exact ⟨ra, not_mem_xSpan rx 1 8⟩), g₄,
        k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨(rx 1).symm, ra⟩),
        k₂.1 r (by simpa using ra), k₁.1 r (by simpa using rd)]
    · rw [k₅.2.2.1, rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₅.2.2.2, wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [k₅.2.1]; exact O₄

/-- The first `n + 1` rows: the low `n + 1` words of `[a]_(n+1) · [b]`
stored in the temporary area, the others in the registers of `xWin (n + 1)`. -/
theorem xRows_ok {s₀ : State} {base bA bB : Addr} {size zA zB c₀ : Nat} (hs : ScrC s₀ base size c₀)
    {ra rb : Reg} (hpa : PtrC s₀ ra bA zA c₀) (hpb : PtrC s₀ rb bB zB c₀) {M : Mod} {a b : Nat}
    (ha : a + 72 ≤ zA) (hb : b + 72 ≤ zB) (ht : M.tmp + 72 ≤ size)
    (hat : ∀ n < 9, Apart bA (a + 8 * n) 8 base M.tmp (8 * n)) (hbt : Apart bB b 72 base M.tmp 72) :
    ∀ n ≤ 8, WP isa (.block ((List.range (n + 1)).flatMap (xRowV M ra rb c₀ a b))) s₀ fun s =>
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s ∧ Outside base M.tmp (8 * (n + 1)) s₀.mem s.mem ∧
      wordsVal s.mem base M.tmp (n + 1) + (2 ^ 64) ^ (n + 1) * hval (xg s) (n + 1) 9 =
        wordsVal s₀.mem bA a (n + 1) * wordsVal s₀.mem bB b 9
  | 0, _ => by
    rw [show (List.range (0 + 1)).flatMap (xRowV M ra rb c₀ a b) = xRow0 M ra rb c₀ a b by simp [xRowV]]
    refine WP.mono (xRow0_ok hs hpa hpb (by omega_using [ha]) hb (by omega_using [ht]) (hbt.mono (by omega_using []) (by omega_using [])))
      fun s ⟨e, k, O⟩ => ⟨k, O, ?_⟩
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.pow_one, Nat.zero_add]
    exact e
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (xRows_ok hs hpa hpb ha hb ht hat hbt n (by omega_using [hn])) fun s ⟨k, O, e⟩ => ?_
    rw [xRowV, ite_eq_right_iff.mpr (fun h => absurd h (by omega_using []))]
    exact xRow_inv hs hpa hpb ha hb ht hbt (by omega_using [hn]) (hat (n + 1) (by omega_using [hn])) k O e

/-- The words `10 … 17` of the accumulator. -/
def xHi : List Reg := (List.range 8).map fun k => xAcc (10 + k)

theorem xHi_nodup : xHi.Nodup := by decide

theorem xHi_sub : ∀ r ∈ xHi, r ∈ xRegs ∧ r ≠ xAcc 9 := by decide

theorem xWin9 : xWin 9 = xAcc 9 :: xHi := rfl

theorem regsVal_xHi (s : State) : regsVal s xHi = hval (xg s) 10 8 := regsVal_xAccs s 8 10

/-- `[o] = (T - 1) mod p` for `1 ≤ T ≤ 2p` in `xWin 9`, `p = 2⁵²¹ - 1`. -/
theorem xCanon_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {o : Nat}
    (ho : o + 72 ≤ size) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hT1 : 1 ≤ hval (xg s) 9 9)
    (hT : hval (xg s) 9 9 ≤ 2 * m) :
    WP isa (.block (xCanon c₀ o)) s fun s' =>
      wordsVal s'.mem base o 9 = (hval (xg s) 9 9 - 1) % m ∧ KeepRegs (.rax :: xRegs) s s' ∧
        Outside base o 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain hmap : ∀ op : AluOp, ((List.range 8).map fun k => Instr.alu op (xAcc (10 + k)) (.imm 0)) =
      xHi.map fun t => .alu op t (.imm 0) := fun op => by simp only [xHi, List.map_map]; rfl
  rw [xCanon, hmap]
  have hW' : hval (xg s) 9 9 = xg s 9 + 2 ^ 64 * hval (xg s) 10 8 := rfl
  obtain h17 : hval (xg s) 10 8 = hval (xg s) 10 7 + (2 ^ 64) ^ 7 * xg s 17 := hval_succ_last _ _ _
  obtain hlo : hval (xg s) 10 7 < (2 ^ 64) ^ 7 := hval_lt fun c _ _ => (s.gpr _).isLt
  obtain hx9 : xg s 9 < 2 ^ 64 := (s.gpr _).isLt
  obtain ht17 : xg s 17 < 1024 := by omega_arith
  rw [show ([.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .xor .rax (.imm 1),
      .alu .sub (xAcc 9) (.reg .rax)] : List Instr) = [.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9,
      .alu .xor .rax (.imm 1)] ++ [.alu .sub (xAcc 9) (.reg .rax)] from rfl, List.append_assoc,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (notTop_ok s (xAcc 17) ht17) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subRax_ok s₃ (xAcc 9)) fun s₄ ⟨c₄, cf₄, e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbZs_ok xHi xHi_nodup cf₄) fun s₅ ⟨c₅, cf₅, e₅, k₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and511_ok s₅ (xAcc 17)) fun s₆ ⟨e₆, k₆⟩ => ?_
  obtain hK : Keeps (.rax :: xRegs) s s₆ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [k₆.1 r (fun h => hr (by simp at h; simp [h, (xAcc_ne 17).2.2.2.2])),
        k₅.1 r (fun h => hr (List.mem_cons_of_mem _ (xHi_sub r h).1)),
        k₄.1 r (fun h => hr (by simp at h; simp [h, (xAcc_ne 9).2.2.2.2])),
        k₃.1 r (fun h => hr (by simp at h; simp [h]))]
    · rw [k₆.2.1, k₅.2.1, k₄.2.1, k₃.2.1]
    · rw [k₆.2.2.1, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1]
    · rw [k₆.2.2.2, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2]
  obtain hs₆ : ScrC s₆ base size c₀ := hs.of_keeps hK (by decide)
  refine WP.mono (storesC_ok (xWin 9) hs₆ (o := o) (by simp [xWin]; omega_arith) (xWin_fresh 9).1)
    fun s₇ ⟨e₇, k₇, O₇⟩ => ⟨?_, (Keeps.regs hK).trans (k₇.mono (by simp)), ?_⟩
  · rw [show (xWin 9).length = 9 from rfl] at e₇
    rw [e₇, xWin9, regsVal, regsVal_xHi, hval_succ_last]
    -- The registers through the steps.
    obtain n17 : ∀ c, 10 ≤ c → c < 17 → xAcc c ≠ xAcc 17 := fun c h1 h2 => xAcc_ne_of (by omega_arith) (by omega_arith)
    obtain n9 : ∀ c, 10 ≤ c → c < 18 → xAcc c ≠ xAcc 9 := fun c h1 h2 =>
      (xAcc_ne_of (show 9 < c by omega_arith) (by omega_arith)).symm
    obtain a₆ : xg s₆ 9 = xg s₄ 9 := by
      simp only [xg]
      rw [k₆.1 _ (by simpa using (xAcc_ne_of (show 9 < 17 by omega_arith) (by omega_arith))),
        k₅.1 _ (fun h => (xHi_sub _ h).2 rfl)]
    obtain b₆ : hval (xg s₆) 10 7 = hval (xg s₅) 10 7 :=
      hval_congr fun c h1 h2 => by simp only [xg]; rw [k₆.1 _ (by simpa using n17 c h1 (by omega_arith))]
    have d₆ : xg s₆ 17 = xg s₅ 17 % 512 := e₆
    obtain h₅ : hval (xg s₅) 10 8 = hval (xg s₅) 10 7 + (2 ^ 64) ^ 7 * xg s₅ 17 := hval_succ_last _ _ _
    obtain h₄ : hval (xg s₄) 10 8 = hval (xg s) 10 8 := hval_congr fun c h1 h2 => by
      simp only [xg]
      rw [k₄.1 _ (by simpa using n9 c h1 h2), k₃.1 _ (by simpa using (xAcc_ne c).1)]
    obtain a₃ : xg s₃ 9 = xg s 9 := by simp only [xg]; rw [k₃.1 _ (by simpa using (xAcc_ne 9).1)]
    rw [regsVal_xHi, regsVal_xHi, show xHi.length = 8 from rfl, h₅, h₄] at e₅
    change xg s₄ 9 + (s₃.gpr .rax).toNat = xg s₃ 9 + 2 ^ 64 * c₄.toNat at e₄
    change (s₃.gpr .rax).toNat = 1 - xg s 17 / 512 at e₃
    show xg s₆ 9 + 2 ^ 64 * (hval (xg s₆) 10 7 + (2 ^ 64) ^ 7 * xg s₆ 17) = _
    rw [a₆, b₆, d₆]
    obtain hl5 := hval_lt (f := xg s₅) (k := 10) (n := 7) fun c _ _ => (s₅.gpr _).isLt
    obtain hx4 : xg s₄ 9 < 2 ^ 64 := (s₄.gpr _).isLt
    obtain hx5 : xg s₅ 17 < 2 ^ 64 := (s₅.gpr _).isLt
    obtain hc₄ := Bool.toNat_le c₄
    obtain hc₅ := Bool.toNat_le c₅
    rw [hW'] at hT hT1 ⊢
    rw [a₃] at e₄
    rw [h17] at hT hT1 ⊢
    generalize hval (xg s) 10 7 = L at *
    generalize hval (xg s₅) 10 7 = L5 at *
    obtain hc : xg s 17 / 512 = if xg s 9 + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * xg s 17) - 1 < m then 0 else 1 := by
      split <;> omega_arith
    obtain hV : xg s₄ 9 + 2 ^ 64 * (L5 + (2 ^ 64) ^ 7 * xg s₅ 17) + (1 - xg s 17 / 512) =
        xg s 9 + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * xg s 17) := by
      omega_arith
    generalize xg s 9 + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * xg s 17) = T at *
    by_cases hlt : T - 1 < m
    · simp only [hlt, ↓reduceIte] at hc
      rw [Nat.mod_eq_of_lt hlt]
      have : xg s₅ 17 < 512 := by omega_arith
      rw [Nat.mod_eq_of_lt this]
      omega_arith
    · simp only [hlt, ↓reduceIte] at hc
      rw [Nat.mod_eq_sub_mod (a := T - 1) (by omega_arith), Nat.mod_eq_of_lt (a := T - 1 - m) (by omega_arith)]
      obtain h1 : 512 ≤ xg s₅ 17 := by omega_arith
      obtain h2 : xg s₅ 17 < 1024 := by omega_arith
      rw [show xg s₅ 17 % 512 = xg s₅ 17 - 512 by omega_arith]
      omega_arith
  · rw [← hK.2.1]; exact O₇.mono (by omega_arith) (by simp [xWin])

/-! ## The multiplication -/

/-- `mulP_arith` for a result plus one, `W`, from the reduction's carry in. -/
theorem mulP_arith1 {A B U W m acc : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : A < (2 ^ 64) ^ 9) (hB : B < m) (hU : U < (2 ^ 64) ^ 9)
    (e : A * B + 512 * (2 ^ 64) ^ 8 * U + (2 ^ 64) ^ 9 = U + (2 ^ 64) ^ 9 * W + (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 * acc) :
    1 ≤ W ∧ W ≤ 2 * m ∧ (2 ^ 64) ^ 9 * (W - 1) = A * B + U * m := by
  obtain hAB : A * B < (2 ^ 64) ^ 9 * m := Nat.mul_lt_mul'' hA hB
  obtain hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_arith
  subst hm'
  generalize A * B = P at *
  -- No carry out: the sum is below `2¹¹⁵²`.
  obtain hacc : acc = 0 := by omega_arith
  subst hacc
  refine ⟨by omega_arith, by omega_arith, by omega_arith⟩

theorem xRegs_clob : ∀ r ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs, r ∈ clob 9 := by decide

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`, with BMI2 and ADX. -/
theorem mulPX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (_hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (_hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulPX M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  have htmp := hM.tmp
  have hnw := hs.nowrap
  rw [Nat.pow_mul]
  rw [hn9] at ho ha hb haT hbT htmp ⊢
  rw [hn9] at hB
  rw [mulPX]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rdiAdd_ok hs (cOf_lt b)) fun s₁ ⟨hs₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xRows_ok hs₁ hs₁.toPtr hs₁.toPtr (M := M) (a := a) (b := b) (by omega_using [ha]) (by omega_using [hb])
    (by omega_using [htmp]) (fun n hn => (((Apart.of_sep base (by omega_using [haT]) (by omega_using [ha, hnw]) : Apart base a 72 base M.tmp 72).sub
      (by omega_using []) (by omega_using [hn])).mono (Nat.le_refl _) (by omega_using [hn])))
    (Apart.of_sep base (by omega_using [hbT]) (by omega_using [hb, hnw])) 8 (Nat.le_refl _)) fun s₁' ⟨k₂, O₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok (hs₁.of_keepRegs k₂ (by decide)) (cOf_lt b) (cOf_lt M.tmp))
    fun s₂ ⟨hs₂, k₂'⟩ => ?_
  obtain hx₂ : hval (xg s₂) 9 9 = hval (xg s₁') 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₂'.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  rw [k₁.2.1, ← k₂'.2.1, ← hx₂] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (xRed_ok hs₂ (M := M) (by omega_arith)) fun s₃ ⟨acc, e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [e₂] at e₃
  obtain hA : wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain hU : wordsVal s₃.mem base M.tmp 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hA hB hU e₃.symm
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₃ (cOf_lt M.tmp) (cOf_lt o)) fun s₃' ⟨hs₃', k₃'⟩ => ?_
  obtain hx₃ : hval (xg s₃') 9 9 = hval (xg s₃) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₃'.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  rw [WP.block_append_iff]
  refine WP.mono (xCanon_ok hs₃' (o := o) (by omega_arith) hm (by rw [hx₃]; exact hW1) (by rw [hx₃]; exact hW2))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hx₃] at e₄
  refine WP.mono (rdiSub_ok (hs₃'.of_keepRegs k₄ (by decide)) (cOf_lt o)) fun s₅ ⟨hs₅, k₅⟩ => ?_
  rw [← k₅.2.1] at e₄
  obtain hmo : 0 < m := by omega_arith
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hr' : r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := fun h => hr (by rw [hn9]; exact xRegs_clob r h)
    by_cases hrd : r = .rdi
    · rw [hrd, hs₅.rdi, hs.rdi]
    · rw [k₅.1 r (by simpa using hrd), k₄.gpr r (fun h => hr' (by
          rcases List.mem_cons.mp h with h | h
          · exact h ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))),
        k₃'.1 r (by simpa using hrd), k₃.gpr r hr', k₂'.1 r (by simpa using hrd), k₂.gpr r hr',
        k₁.1 r (by simpa using hrd)]
  · rw [k₅.2.2.1, k₄.rd, k₃'.2.2.1, k₃.rd, k₂'.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₅.2.2.2, k₄.wr, k₃'.2.2.2, k₃.wr, k₂'.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [hn9] at hx hx'
    rw [k₅.2.1, O₄ x hx, k₃'.2.1, O₃ x (by omega_arith), k₂'.2.1, O₂ x hx', k₁.2.1]
  · rw [e₄]; exact Nat.mod_lt _ hmo
  · rw [e₄, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86_64
