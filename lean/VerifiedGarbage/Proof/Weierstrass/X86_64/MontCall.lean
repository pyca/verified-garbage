module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Sub256
import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import Batteries.Logic
import VerifiedGarbage.Proof.Mont.X86_64.SqrS
public import VerifiedGarbage.Proof.Mont.X86_64.Row
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Mont.X86_64.CsubR`, which this module and modules that import it used -/

section

/-!
# Montgomery arithmetic on x86-64: P-384's conditional subtraction in registers

`csubR` is `csubS` with P-384's `p` built in registers (`p384Mask` of all
ones) rather than read from memory: `p384Sub_ok` subtracts it, as
`p384Add_ok` adds it, and `csubR_ok` is `csubS_ok`'s reduction.
-/

@[expose] public section

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
    omega_arith
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
  have hW := pow_split 2 128 256 (64 * 6) (by omega_using [])
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
      omega_arith
  · exact ((((k₀.mono (by sub_regs)).trans (k₀'.mono (by sub_regs))).trans
      ((k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))))).trans
      (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))

end VG.Proof.Mont.X86_64

end

end

/-! ### `Weierstrass.X86_64.MontFnB`, which this module and modules that import it used -/

section

/-!
# P-521's product modulo `p` as a function, on x86-64

`mulFn` (`Impl/Weierstrass/X86_64/Mont.lean`) runs the columns of the
inline product `mulP` (or of the square `sqrP`, when `a = b`) with their
operands read through `rsi = ws + a` and `rbx = ws + b`: a term reads any
operands whose registers it does not change (`termR_ok`), so the columns'
arithmetic is `mulP`'s and `sqrP`'s (`pColSum`, `sColSum`). The result plus
one then goes into `xWin 9` (`plusOne_ok`) for `mulFnX`'s exit.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry mulx_arith)

/-! ## Operands -/

/-- The registers an operand's value depends on. -/
def srcRegs : Src → List Reg
  | .reg r => [r]
  | .imm _ => []
  | .mem m => m.base :: m.index.toList

theorem readSrc_congr {s s' : State} {x : Src} (hg : ∀ r ∈ srcRegs x, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : readSrc s' x = readSrc s x := by
  cases x with
  | reg r => simp only [readSrc, hg r (by simp [srcRegs])]
  | imm v => rfl
  | mem m =>
    have he : s'.ea m = s.ea m := by
      unfold State.ea
      cases hi : m.index with
      | none => simp only [hg m.base (by simp [srcRegs])]
      | some i => simp only [hg m.base (by simp [srcRegs]), hg i (by simp [srcRegs, hi])]
    simp only [readSrc, State.load64, he, hm, hrd, hwr]

/-- The registers a term changes. -/
abbrev termRegs : List Reg := [.rax, .rcx, .rdx, .r9, .r10, .r11]

theorem pAccs_sub (c : Nat) : ∀ r ∈ pAccs c, r ∈ termRegs := by
  intro r hr
  have := (pAccs_ok c).2 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases this with rfl | rfl | rfl <;> simp

/-! ## A term -/

/-- `rcx = y`. -/
theorem movRcxSrc_ok (s : State) {sy : Src} {wy : BitVec 64} (hy : readSrc s sy = some wy) :
    WP isa (.block [.mov .rcx sy]) s fun s' => s'.gpr .rcx = wy ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hy, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `rdx:rax = [mx] · rcx`, then `r0–r2 += rdx:rax` (`pMulAcc_ok` through
any operand). -/
theorem pMulAccR_ok {s : State} {r0 r1 r2 : Reg} (hd : [r0, r1, r2, .rax, .rcx, .rdx, .rdi].Nodup)
    {mx : MemOp} {wx : BitVec 64} (hx : readSrc s (.mem mx) = some wx)
    (hb : regsVal s [r0, r1, r2] + wx.toNat * (s.gpr .rcx).toNat < 2 ^ 192) :
    WP isa (.block [.mov .rax (.mem mx), .mul .rcx, .alu .add r0 (.reg .rax),
      .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s fun s' =>
      regsVal s' [r0, r1, r2] = regsVal s [r0, r1, r2] + wx.toNat * (s.gpr .rcx).toNat ∧
      Keeps [.rax, .rdx, r0, r1, r2] s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = wx.toNat * (s.gpr .rcx).toNat := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0c, h0d, h0i⟩, ⟨h12, h1a, h1c, h1d, h1i⟩, ⟨h2a, h2c, h2d, h2i⟩, -⟩ := hd
  have hx' : s.load64 (s.ea mx) = some wx := hx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hx', readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Ne.symm h01, Ne.symm h02, Ne.symm h12, h0a, h1a, h2a, h0d, h1d, h2d,
    Ne.symm h0d, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ite_true, ite_false,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, Nat.mul_zero, Nat.add_zero]
    have em := mulx_arith wx (s.gpr .rcx)
    generalize BitVec.ofNat 64 (wx.toNat * (s.gpr .rcx).toNat) = lo at em ⊢
    generalize BitVec.ofNat 64 (wx.toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at em ⊢
    have e0 := add_carry (s.gpr r0) lo
    generalize decide (2 ^ 64 ≤ (s.gpr r0).toNat + lo.toNat) = c0 at e0 ⊢
    have e1 := adc_carry (s.gpr r1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr r1).toNat + hi.toNat + c0.toNat) = c1 at e1 ⊢
    have e2 := adc_carry (s.gpr r2) 0 c1
    generalize decide (2 ^ 64 ≤ (s.gpr r2).toNat + (0 : BitVec 64).toNat + c1.toNat) = c2 at e2
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hb
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have := Bool.toNat_le c2
    have := (s.gpr r0 + lo).isLt; have := (s.gpr r1 + hi + (BitVec.ofBool c0).setWidth 64).isLt
    have := (s.gpr r2 + 0 + (BitVec.ofBool c1).setWidth 64).isLt
    rw [z] at e2
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a, Ne.symm h1d, Ne.symm h2d, ite_false]
    exact mulx_arith wx (s.gpr .rcx)

/-- A term: `acc += x · y`, twice if `two`, for operands whose registers it
does not change. -/
theorem termR_ok (s : State) (c : Nat) {mx : MemOp} {sy : Src} {wx wy : BitVec 64} (two : Bool)
    (hx : readSrc s (.mem mx) = some wx) (hy : readSrc s sy = some wy)
    (hreg : ∀ r ∈ srcRegs (.mem mx), r ∉ termRegs)
    (hb : regsVal s (pAccs c) + mult two * (wx.toNat * wy.toNat) < 2 ^ 192) :
    WP isa (.block (termR2 c mx sy two)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + mult two * (wx.toNat * wy.toNat) ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s' := by
  have hok := pAccs_ok c
  rw [termR2, termR, show ([.mov .rcx sy, .mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
      .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)] : List Instr) =
      [.mov .rcx sy] ++ [.mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
      .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)] from rfl, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (movRcxSrc_ok s hy) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hx₁ : readSrc s₁ (.mem mx) = some wx := by
    rw [readSrc_congr (fun r hr => k₁.1 r (by
      simp only [List.mem_singleton]; intro h; exact hreg r hr (by simp [h]))) k₁.2.1 k₁.2.2.1 k₁.2.2.2, hx]
  have hacc : regsVal s₁ (pAccs c) = regsVal s (pAccs c) := regsVal_congr fun r hr => k₁.1 r (by
    have := hok.2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl | rfl <;> decide)
  rw [WP.block_append_iff]
  refine WP.mono (pMulAccR_ok hok.1 hx₁ (by
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, e₁]
    cases two <;> simp only [mult, Bool.false_eq_true, ↓reduceIte] at hb <;> omega_arith))
    fun s₂ ⟨e₂, k₂, x₂⟩ => ?_
  rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, e₁] at e₂
  rw [e₁] at x₂
  have k₁₂ : Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s₂ :=
    (k₁.mono (by simp)).trans (k₂.mono (by simp [pAccs]))
  cases two with
  | false => exact WP.block_nil ⟨by rw [e₂]; simp [mult], k₁₂⟩
  | true =>
    simp only [ite_true]
    refine WP.mono (sAdd_ok s₂ hok.1 (by
      rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₂, x₂]
      simp only [mult, ↓reduceIte] at hb; omega_arith)) fun s₃ ⟨e₃, k₃⟩ =>
        ⟨?_, k₁₂.trans (k₃.mono (by simp [pAccs]))⟩
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₂, x₂] at e₃
    rw [e₃]; simp only [mult, ↓reduceIte]; omega_arith

/-! ## A column -/

/-- An operand's value, as a number. -/
abbrev val (s : State) (x : Src) : Nat := ((readSrc s x).getD 0).toNat

/-- The sum of a column's terms, with their multiplicities. -/
def tSum (s : State) (ts : List (MemOp × Src × Bool)) : Nat :=
  (ts.map fun t => mult t.2.2 * (val s (.mem t.1) * val s t.2.1)).sum

/-- The terms read operands, through registers they do not change. -/
def TermsOk (s : State) (ts : List (MemOp × Src × Bool)) : Prop :=
  ∀ t ∈ ts, (readSrc s (.mem t.1)).isSome ∧ (readSrc s t.2.1).isSome ∧
    (∀ r ∈ srcRegs (.mem t.1), r ∉ termRegs) ∧ (∀ r ∈ srcRegs t.2.1, r ∉ termRegs)

theorem readSrc_keep {s s' : State} {rs : List Reg} (k : Keeps rs s s') (hsub : ∀ r ∈ rs, r ∈ termRegs)
    {x : Src} (hx : ∀ r ∈ srcRegs x, r ∉ termRegs) : readSrc s' x = readSrc s x :=
  readSrc_congr (fun r hr => k.1 r (fun h => hx r hr (hsub r h))) k.2.1 k.2.2.1 k.2.2.2

theorem term_sub (c : Nat) : ∀ r ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs c, r ∈ termRegs := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · simp
  · simp
  · simp
  · exact pAccs_sub c r hr

/-- A column's terms, by induction on them. -/
theorem termsR_ok (c : Nat) : ∀ (ts : List (MemOp × Src × Bool)) {s : State},
    TermsOk s ts → regsVal s (pAccs c) + tSum s ts < 2 ^ 192 →
    WP isa (.block (ts.flatMap fun t => termR2 c t.1 t.2.1 t.2.2)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + tSum s ts ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s'
  | [], s, _, _ => WP.block_nil ⟨by simp [tSum], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, hok, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨hx, hy, hrx, hry⟩ := hok t List.mem_cons_self
    obtain ⟨wx, ewx⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨wy, ewy⟩ := Option.isSome_iff_exists.mp hy
    have hv : mult t.2.2 * (val s (.mem t.1) * val s t.2.1) = mult t.2.2 * (wx.toNat * wy.toNat) := by
      simp only [val, ewx, ewy, Option.getD_some]
    simp only [tSum, List.map_cons, List.sum_cons] at hb
    refine WP.mono (termR_ok s c t.2.2 ewx ewy hrx (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hok₁ : TermsOk s₁ ts := fun t' ht' => by
      obtain ⟨a1, a2, a3, a4⟩ := hok t' (List.mem_cons_of_mem _ ht')
      rw [readSrc_keep k₁ (term_sub c) a3, readSrc_keep k₁ (term_sub c) a4]
      exact ⟨a1, a2, a3, a4⟩
    have hsum : tSum s₁ ts = tSum s ts := by
      simp only [tSum]
      congr 1
      apply List.map_congr_left
      intro t' ht'
      obtain ⟨-, -, a3, a4⟩ := hok t' (List.mem_cons_of_mem _ ht')
      simp only [val, readSrc_keep k₁ (term_sub c) a3, readSrc_keep k₁ (term_sub c) a4]
    refine WP.mono (termsR_ok c ts hok₁ (by rw [e₁, hsum]; simp only [tSum] at hb ⊢; omega_arith))
      fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hsum]
    simp only [tSum, List.map_cons, List.sum_cons]
    omega_arith

/-- Column `c`: its terms, and its low word stored at `[fnTmp + 8 (c mod 9)]`;
the rest of the accumulator is the next column's. -/
theorem colR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {ts : Nat → List (MemOp × Src × Bool)} {c : Nat} (htmp : fnTmp + 72 ≤ size) (hok : TermsOk s (ts c))
    (hb : regsVal s (pAccs c) + tSum s (ts c) < 2 ^ 192) :
    WP isa (.block (colR ts c)) s fun s' =>
      (word s'.mem base (fnTmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + tSum s (ts c) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (fnTmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  rw [colR, WP.block_append_iff]
  refine WP.mono (termsR_ok c _ hok hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => absurd (term_sub c _ h) (by decide))
  refine WP.mono (pEnd_ok hs₁ c (t := fnTmp + 8 * (c % 9)) (by omega_arith)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
  refine ⟨?_, ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩, ?_⟩
  · rw [m₂, word_writeW_self, ← e₂, e₁]
  · rw [k₂.gpr r (fun h => hr (by
        simp only [List.mem_singleton] at h; exact h ▸ pAccs_sub c _ (by simp [pAccs]))),
      k₁.1 r (fun h => hr (term_sub c r h))]
  · rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)

/-! ## The columns -/

/-- The pointers to the operands. -/
def Ptrs (base : Addr) (a b : Nat) (s : State) : Prop := s.gpr .rbx = off base a ∧ s.gpr .rbp = off base b

theorem ptrs_keep {base : Addr} {a b : Nat} {s s' : State} (h : Ptrs base a b s)
    (k : KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s') : Ptrs base a b s' :=
  ⟨(k.gpr _ (by decide)).trans h.1, (k.gpr _ (by decide)).trans h.2⟩

theorem readSrc_opA {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {a : Nat} (hsi : s.gpr .rbx = off base a)
    (ha : a + 72 ≤ Z) {i : Nat} (hi : i < 9) :
    readSrc s (.mem (opA i)) = some (Mont.word s.mem base (a + 8 * i)) :=
  readSrc_ptr hs hsi (by omega_arith)

theorem readSrc_opB {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {b : Nat} (hbx : s.gpr .rbp = off base b)
    (hb : b + 72 ≤ Z) {j : Nat} (hj : j < 9) :
    readSrc s (.mem (opB j)) = some (Mont.word s.mem base (b + 8 * j)) :=
  readSrc_ptr hs hbx (by omega_arith)

theorem val_512 (s : State) : val s (.imm 512) = 512 := by
  show ((512 : BitVec 32).signExtend 64).toNat = 512
  decide

theorem fnTmp_eq : fnTmp = 4024 := rfl

/-- The reduction's term of column `c`. -/
theorem redTerms_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {c : Nat} {l : Nat → Nat}
    (hL : 8 ≤ c → c ≤ 16 → (Mont.word s.mem base (fnTmp + 8 * (c - 8))).toNat = l (c - 8)) :
    TermsOk s (redTerms c) ∧ tSum s (redTerms c) = if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0 := by
  unfold redTerms
  split
  · rename_i h
    have hr := readSrc_sc hs (d := fnTmp + 8 * (c - 8)) (by rw [fnTmp_eq]; omega_arith)
    refine ⟨fun t ht => ?_, ?_⟩
    · simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨by rw [hr]; rfl, rfl, by simp [srcRegs, sc], by simp [srcRegs]⟩
    · simp only [tSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, mult,
        Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val_512, val, hr, Option.getD_some, hL h.1 h.2]
  · exact ⟨fun t ht => by simp at ht, rfl⟩

/-- The product's columns. -/
theorem mulCols_ok {base : Addr} {Z : Nat} (hZ : 4096 ≤ Z) {m₀ : Mem} {a b : Nat} (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) :
    ColOk (fnMod true) base Z m₀ (colR mulTerms)
      (pColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (fun j => (Mont.word m₀ base (b + 8 * j)).toNat))
      (Ptrs base a b) :=
  fun c hc s l hs hP O hacc hL => by
    have hnw := hs.nowrap
    have hA : ∀ i < 9, Mont.word s.mem base (a + 8 * i) = Mont.word m₀ base (a + 8 * i) :=
      fun i hi => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    have hB : ∀ j < 9, Mont.word s.mem base (b + 8 * j) = Mont.word m₀ base (b + 8 * j) :=
      fun j hj => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    obtain ⟨rok, rsum⟩ := redTerms_ok hs hZ (c := c) hL
    have hok : TermsOk s (mulTerms c) := by
      intro t ht
      simp only [mulTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht
      · exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) hi]; rfl, by rw [readSrc_opB hs hP.2 (by omega_arith) hj]; rfl,
          by simp [srcRegs, opA, rcR], by simp [srcRegs, opB, rcR]⟩
      · exact rok t ht
    have hsum : tSum s (mulTerms c) = pColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat)
        (fun j => (Mont.word m₀ base (b + 8 * j)).toNat) l c := by
      rw [mulTerms, pColSum, ← rsum]
      simp only [tSum, List.map_append, List.sum_append, List.map_map]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
      simp only [Function.comp, mult, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val,
        readSrc_opA hs hP.1 (by omega_arith) hi.1, readSrc_opB hs hP.2 (by omega_arith) hi.2.2, Option.getD_some,
        hA i hi.1, hB (c - i) hi.2.2]
    have hcol := pColSum_lt (A := fun i => (Mont.word m₀ base (a + 8 * i)).toNat)
      (B := fun j => (Mont.word m₀ base (b + 8 * j)).toNat) (l := l) c (fun i => (Mont.word _ _ _).isLt)
      (fun j => (Mont.word _ _ _).isLt) (fun h1 h2 => by rw [← hL h1 h2]; exact (Mont.word _ _ _).isLt)
    refine WP.mono (colR_ok hs (ts := mulTerms) (c := c) (by rw [fnTmp_eq]; omega_arith) hok (by rw [hsum]; omega_arith))
      fun s' ⟨e', k', O'⟩ => ⟨by rw [hsum] at e'; exact e', k', O'⟩

/-- The square's columns. -/
theorem sqrCols_ok {base : Addr} {Z : Nat} (hZ : 4096 ≤ Z) {m₀ : Mem} {a : Nat} (ha : a + 72 ≤ 3520) :
    ColOk (fnMod true) base Z m₀ (colR sqrTerms)
      (sColSum fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (Ptrs base a a) :=
  fun c hc s l hs hP O hacc hL => by
    have hnw := hs.nowrap
    have hA : ∀ i < 9, Mont.word s.mem base (a + 8 * i) = Mont.word m₀ base (a + 8 * i) :=
      fun i hi => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    obtain ⟨rok, rsum⟩ := redTerms_ok hs hZ (c := c) hL
    have hok : TermsOk s (sqrTerms c) := by
      intro t ht
      simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with (⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht) | ht
      · exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) hi]; rfl, by rw [readSrc_opA hs hP.1 (by omega_arith) hj]; rfl,
          by simp [srcRegs, opA, rcR], by simp [srcRegs, opA, rcR]⟩
      · split at ht
        · rename_i h
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) h.2]; rfl, by rw [readSrc_opA hs hP.1 (by omega_arith) h.2]; rfl,
            by simp [srcRegs, opA, rcR], by simp [srcRegs, opA, rcR]⟩
        · simp at ht
      · exact rok t ht
    have hsum : tSum s (sqrTerms c) = sColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) l c := by
      rw [sqrTerms, sColSum, ← rsum]
      simp only [tSum, List.map_append, List.sum_append, List.map_map]
      rw [Nat.add_assoc]
      refine congrArg₂ (· + ·) ?_ (congrArg (· + _) ?_)
      · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
        simp only [Function.comp, mult, ↓reduceIte, val, readSrc_opA hs hP.1 (by omega_arith) hi.1,
          readSrc_opA hs hP.1 (by omega_arith) hi.2.2, Option.getD_some, hA i hi.1, hA (c - i) hi.2.2]
      · split
        · rename_i h
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, mult,
            Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val, readSrc_opA hs hP.1 (by omega_arith) h.2,
            Option.getD_some, hA _ h.2]
        · simp
    have hcol := (colSum_s (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (fun _ => (Mont.word _ _ _).isLt)).lt l c
      fun h1 h2 => by rw [← hL h1 h2]; exact (Mont.word _ _ _).isLt
    refine WP.mono (colR_ok hs (ts := sqrTerms) (c := c) (by rw [fnTmp_eq]; omega_arith) hok (by rw [hsum]; omega_arith))
      fun s' ⟨e', k', O'⟩ => ⟨by rw [hsum] at e'; exact e', k', O'⟩

/-! ## The result plus one -/

/-- `add t, 1`. -/
theorem addOne_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .add t (.imm 1)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ (s'.gpr t).toNat + 2 ^ 64 * c'.toNat = (s.gpr t).toNat + 1 ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : ((1 : BitVec 32).signExtend 64).toNat = 1 := by decide
    have := add_carry (s.gpr t) ((1 : BitVec 32).signExtend 64)
    rw [h1] at this
    simpa [h1] using this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A carry `c` added up the words `ts`. -/
theorem adcZs_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, ts.Nodup → s.cf = some c →
    WP isa (.block (ts.map fun t => .alu .adc t (.imm 0))) s fun s' =>
      ∃ c', s'.cf = some c' ∧ regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat = regsVal s ts + c.toNat ∧
        Keeps ts s s'
  | [], s, c, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hn, hc => by
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (adcZ_ok s t hc) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    have htn := (List.nodup_cons.mp hn).1
    refine WP.mono (adcZs_ok ts (List.nodup_cons.mp hn).2 cf₁) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ =>
      ⟨c₂, cf₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t htn
    simp only [regsVal, List.length_cons, ht₂]
    rw [hR] at e₂
    rw [show 64 * (ts.length + 1) = 64 + 64 * ts.length by omega_arith, Nat.pow_add, Nat.mul_assoc]
    generalize 2 ^ (64 * ts.length) * c₂.toNat = X at *
    omega_arith

theorem xWin9_get (j : Nat) (h : j < (xWin 9).length) : (xWin 9)[j] = xAcc (9 + j) := by
  simp [xWin]

/-- The number in the temporary area plus one, into `xWin 9`. -/
theorem plusOne_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (hW : wordsVal s.mem base fnTmp 9 + 1 < (2 ^ 64) ^ 9) :
    WP isa (.block plusOne) s fun s' =>
      hval (xg s') 9 9 = wordsVal s.mem base fnTmp 9 + 1 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ s'.mem = s.mem := by
  rw [plusOne, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_words (xWin 9) hs (a := fnTmp) (by rw [fnTmp_eq]; simp only [xWin, List.length_map, List.length_range]; omega_arith) (xWin_fresh 9).1
    (by decide)) fun s₁ ⟨v₁, k₁⟩ => ?_
  have e₁ : hval (xg s₁) 9 9 = wordsVal s.mem base fnTmp 9 := by
    rw [show fnTmp = fnTmp + 8 * 0 from rfl, wordsVal_hval, hval_shift (xg s₁) 9 0 9]
    refine hval_congr fun j _ hj => ?_
    have := v₁ j (by simp [xWin]; omega_arith)
    rw [xWin9_get j (by simp [xWin]; omega_arith)] at this
    simp only [xg, Nat.add_comm j 9, this, Nat.mul_comm]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addOne_ok s₁ (xAcc 9)) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ?_
  have hnd : ((List.range 8).map fun k => xAcc (10 + k)).Nodup := by decide
  rw [show ((List.range 8).map fun k => (.alu .adc (xAcc (10 + k)) (.imm 0) : Instr)) =
    ((List.range 8).map fun k => xAcc (10 + k)).map fun t => .alu .adc t (.imm 0) by simp]
  refine WP.mono (adcZs_ok _ hnd cf₂) fun s₃ ⟨c₃, _, e₃, k₃⟩ => ?_
  have hsplit : ∀ s : State, hval (xg s) 9 9 = xg s 9 + 2 ^ 64 * regsVal s ((List.range 8).map fun k => xAcc (10 + k)) := by
    intro s
    rw [regsVal_xAccs s 8 10]; rfl
  have hr₂ : regsVal s₂ ((List.range 8).map fun k => xAcc (10 + k)) =
      regsVal s₁ ((List.range 8).map fun k => xAcc (10 + k)) := regsVal_congr fun q hq => k₂.1 q (by
    simp only [List.mem_singleton]; intro h; subst h; revert hq; decide)
  have hx₃ : xg s₃ 9 = xg s₂ 9 := by
    simp only [xg]; rw [k₃.1 _ (by decide)]
  have hlen : ((List.range 8).map fun k => xAcc (10 + k)).length = 8 := by simp
  rw [hlen] at e₃
  have hl := regsVal_lt s₃ ((List.range 8).map fun k => xAcc (10 + k))
  rw [hlen] at hl
  have hx := (s₃.gpr (xAcc 9)).isLt
  have e : hval (xg s₃) 9 9 + (2 ^ 64) ^ 9 * c₃.toNat = wordsVal s.mem base fnTmp 9 + 1 := by
    rw [hsplit, hx₃, ← e₁, hsplit s₁, ← hr₂]
    simp only [xg] at e₂ ⊢
    rw [Nat.pow_mul 2 64 8] at e₃
    rw [show (2 ^ 64) ^ 9 = 2 ^ 64 * (2 ^ 64) ^ 8 from (Nat.pow_succ' (m := 2 ^ 64) (n := 8)), Nat.mul_assoc]
    generalize (2 ^ 64) ^ 8 * c₃.toNat = Zc at *
    generalize regsVal s₃ ((List.range 8).map fun k => xAcc (10 + k)) = R₃ at *
    generalize regsVal s₂ ((List.range 8).map fun k => xAcc (10 + k)) = R₂ at *
    omega_arith
  refine ⟨?_, ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.2.2.1, k₁.2.2.1], by rw [k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩,
    by rw [k₃.2.1, k₂.2.1, k₁.2.1]⟩
  · rcases Nat.eq_zero_or_pos c₃.toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at e; exact e
    · have : (2 ^ 64) ^ 9 * 1 ≤ (2 ^ 64) ^ 9 * c₃.toNat := Nat.mul_le_mul_left _ h
      omega_arith
  · have hx : ∀ q ∈ xWin 9, q ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := fun q hq =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (xWin_sub 9 q hq)))
    have h8 : ∀ q ∈ (List.range 8).map (fun k => xAcc (10 + k)), q ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := by
      decide
    rw [k₃.1 r (fun h => hr (h8 r h)), k₂.1 r (fun h => hr (by
      simp only [List.mem_singleton] at h; subst h; decide)), k₁.1 r (fun h => hr (hx r h))]

/-! ## The branches -/

/-- What a branch leaves: only the registers of the columns and the
temporary area changed, and there the result `W < 2m`, with
`2⁵⁷⁶ W = A B + U p`. -/
def BMid (m : Nat) (base : Addr) (A B : Nat) (s s' : State) : Prop :=
  KeepRegs termRegs s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
    wordsVal s'.mem base fnTmp 9 < 2 * m ∧ ∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = A * B + U * m

/-- The columns, from any column sums that add up to `A B` and the
reduction's `2⁵²¹ U`. -/
theorem colsR_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {ts : Nat → List (MemOp × Src × Bool)}
    {S : (Nat → Nat) → Nat → Nat} {P : State → Prop} (hS : ColSum S)
    (hcol : ColOk (fnMod true) base Z s.mem (colR ts) S P) (hP₀ : P s)
    (hP : ∀ s s', P s → KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' → P s') {A B m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : A < (2 ^ 64) ^ 9) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (colsR ts)) s (BMid m base A B s) := by
  have hnw := hs.nowrap
  rw [colsR, WP.block_append_iff,
    show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) =
      zeros [.r9, .r10, .r11] from rfl]
  refine WP.mono (zeros_ok s [.r9, .r10, .r11]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h0 : regsVal s₁ (pAccs 0) = 0 := by
    simp only [show pAccs 0 = [.r9, .r10, .r11] from rfl, regsVal, z₁ .r9 (by simp),
      z₁ .r10 (by simp), z₁ .r11 (by simp)]
    rfl
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hP₁ : P s₁ := hP _ _ hP₀ ⟨(k₁.mono (by decide)).1, k₁.2.2.1, k₁.2.2.2⟩
  refine WP.mono (cols_ok hs₁ (M := fnMod true) (by rw [fnTmp_val]; omega_arith) hS (by rw [hm₁]; exact hcol) hP₁ hP
    h0 18 (Nat.le_refl _)) fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  rw [htot, hval_add l 0 9 9, Nat.zero_add,
    show (2 ^ 64) ^ 18 = (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 by rw [← Nat.pow_add]] at e₂
  have hW : wordsVal s₂.mem base fnTmp 9 = hval l 9 9 := by
    rw [show fnTmp = fnTmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base fnTmp 0 9,
      show (9 : Nat) = 0 + 9 from rfl, hval_shift l 9 0 9]
    exact hval_congr fun c _ hc => by
      have := hlm (c + 9) (by omega_arith) (by omega_arith)
      rwa [show (c + 9) % 9 = c by omega_arith] at this
  have hU : hval l 0 9 < (2 ^ 64) ^ 9 := hval_lt fun c _ hc => hl64 c (by omega_arith)
  rw [← hW, show pAccs 18 = [.r9, .r10, .r11] from rfl] at e₂
  obtain ⟨-, hT2, eT⟩ := mulP_arith (by decide) hm hA hB hU e₂
  refine ⟨⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩,
    by rw [← hm₁]; exact O₂, hT2, _, eT⟩
  rw [k₂.gpr r (by simpa [termRegs] using hr), k₁.1 r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp))]

/-- `colsR`, from `rbx = ws + a` and `rcx = ws + b`, moved into `rbp`. -/
theorem colsO_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {ts : Nat → List (MemOp × Src × Bool)}
    {S : (Nat → Nat) → Nat → Nat} {a b : Nat} (hS : ColSum S)
    (hcol : ColOk (fnMod true) base Z s.mem (colR ts) S (Ptrs base a b)) (hbx : s.gpr .rbx = off base a)
    (hcx : s.gpr .rcx = off base b) {A B m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : A < (2 ^ 64) ^ 9) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (colsO ts)) s fun s' =>
      KeepRegs (.rbp :: termRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
      wordsVal s'.mem base fnTmp 9 < 2 * m ∧ (∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = A * B + U * m) := by
  rw [colsO, WP.block_append_iff]
  refine WP.mono (movReg_ok s .rbp .rcx) fun s₁ ⟨v₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.mono (colsR_ok hs₁ hZ hS (by rw [hm₁]; exact hcol)
    ⟨(k₁.1 _ (by decide)).trans hbx, v₁.trans hcx⟩ (fun _ _ h k => ptrs_keep h k) hm hA hB htot)
    fun s₂ ⟨k₂, O₂, hW, U, eW⟩ => ?_
  rw [hm₁] at O₂
  refine ⟨⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩, O₂, hW, ⟨U, eW⟩⟩
  have ht : r ∉ termRegs := fun h => hr (List.mem_cons_of_mem _ h)
  rw [k₂.gpr r ht, k₁.1 r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; simp))]

/-! ## The function -/

theorem hval_words (m : Mem) (base : Addr) (a : Nat) :
    wordsVal m base a 9 = hval (fun i => (Mont.word m base (a + 8 * i)).toNat) 0 9 := by
  rw [← wordsVal_hval m base a 0 9, Nat.mul_zero, Nat.add_zero]

/-- The middle of `mulFn`: the product or the square, by columns, then plus one. -/
theorem midB_ok {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    MidOk (.seq (.ite .e (.block (colsO sqrTerms)) (.block (colsO mulTerms))) (.block plusOne)) m := by
  intro Z hZ s base a b hs bx cx zf ha hb hB
  have hX : ∀ x, wordsVal s.mem base x 9 < (2 ^ 64) ^ 9 := fun x => by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  refine WP.seq (WP.mono (Q := fun (s' : State) => KeepRegs (.rbp :: termRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
      wordsVal s'.mem base fnTmp 9 < 2 * m ∧
      (∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 + U * m))
    (WP.ite (decide (a = b)) zf (fun h => ?_) (fun _ => ?_)) fun s₂ ⟨k₂, O₂, hW, ⟨U, eW⟩⟩ => ?_)
  · have hab : a = b := of_decide_eq_true h
    subst hab
    rw [hval_words s.mem base a]
    exact colsO_ok hs hZ (colSum_s _ fun _ => (Mont.word _ _ _).isLt) (sqrCols_ok hZ ha) bx cx
      hm (by rw [← hval_words]; exact hX a) (by rw [← hval_words]; exact hB) fun l => sColSum_total _ l
  · rw [hval_words s.mem base a, hval_words s.mem base b]
    exact colsO_ok hs hZ (colSum_p _ _ (fun _ => (Mont.word _ _ _).isLt) (fun _ => (Mont.word _ _ _).isLt))
      (mulCols_ok hZ ha hb) bx cx hm (by rw [← hval_words]; exact hX a)
      (by rw [← hval_words]; exact hB) fun l => pColSum_total _ _ l
  have hs₂ : Scr s₂ base Z := ⟨(k₂.gpr _ (by decide)).trans hs.rdi, k₂.wr ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (plusOne_ok hs₂ hZ (by omega_arith)) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd], by rw [k₃.wr, k₂.wr]⟩, by rw [m₃]; exact O₂,
    by rw [e₃]; omega_arith, by rw [e₃]; omega_arith, U, by rw [e₃, Nat.add_sub_cancel]; exact eW⟩
  rw [k₃.gpr r (fun h => hr (by
    simp only [List.mem_cons] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h))))), k₂.gpr r (fun h => hr (by
    simp only [termRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p` for P-521's `p = m`, without BMI2 and ADX. -/
theorem mulFn_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520)
    (hb : argOf s .rcx + 72 ≤ 3520) (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa mulFn s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x :=
  fnShape_ok (by decide +kernel) hs hZ hm (midB_ok hm) ho ha hb hB

end VG.Proof.Weierstrass.X86_64.Mont

end

end

/-! ### `Weierstrass.X86_64.MontFnN6`, which only this module used -/

section

/-! ### `Weierstrass.X86_64.MontFn6`, which only this module used -/

section

/-!
# P-384's product modulo `p` as a function, on x86-64

`mulFn6 adx` (`Impl/Weierstrass/X86_64/Mont.lean`) runs the inline product
`mulRounds` (or `sqrSA`, when `a = b`) relocated: its operands at the
markers read through `rbx = ws + a`, `rsi = ws + b` and `rsi = ws + o`.
With those registers so (`PtrsAt`), the relocated code runs as the inline
code at the offsets `a`, `b` and `o` (`wp_unptr`, with `sqrSA_reloc`,
`mulRounds_reloc`, `stores_reloc`), whose proofs then apply
(`sqrSA_ok`, `mulRounds_ok`); `csubR_ok` reduces the result without the
modulus in memory. The function changes only `fnClob`, `[o]` and its
temporary area, bytes `fnTmp6` to 4095 (`mulFn6_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- P-384's prime. -/
abbrev p384 : Nat :=
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- An offset the functions of six words take: apart from their temporary
area, and within the working space. -/
def Arg6 (Z x : Nat) : Prop := (x + 48 ≤ fnTmp6 ∨ 4096 ≤ x) ∧ x + 48 ≤ Z

theorem fnTmp6_eq : fnTmp6 = 4048 := rfl

/-! ## The relocated code is the inline code -/

theorem sqrSA_reloc (adx : Bool) (a o : Nat) :
    (sqrSA (fnMod6 adx) mO mA).map (Instr.mapMem (unptr [(.rbx, a), (.rsi, o)] ∘ relocTo [(mA, .rbx), (mO, .rsi)])) =
      sqrSA (fnMod6 adx) o a := by
  cases adx <;> kernel_rfl

theorem mulRounds_reloc (adx : Bool) (a b : Nat) :
    (mulRounds (fnMod6 adx) mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rsi, b)] ∘ relocTo [(mA, .rbx), (mB, .rsi)])) =
      mulRounds (fnMod6 adx) a b := by
  cases adx <;> kernel_rfl

theorem storesW_reloc (o : Nat) :
    (stores sqWin6 mO).map (Instr.mapMem (unptr [(.rsi, o)] ∘ relocTo [(mO, .rsi)])) = stores sqWin6 o := rfl

theorem storesL_reloc (o : Nat) :
    (stores low6 mO).map (Instr.mapMem (unptr [(.rsi, o)] ∘ relocTo [(mO, .rsi)])) = stores low6 o := rfl

/-! ## The relocated code keeps its pointers -/

theorem sqr_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mO, .rsi)] (sqrSA (fnMod6 adx) mO mA)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem mul_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem storesW_keeps : (reloc [(mO, .rsi)] (stores sqWin6 mO)).all (keepsPtrs [.rsi]) = true := by
  decide +kernel

theorem storesL_keeps : (reloc [(mO, .rsi)] (stores low6 mO)).all (keepsPtrs [.rsi]) = true := by
  decide +kernel

theorem mul_scal : ∀ adx : Bool,
    scalCode (.block (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnMod6 adx) mA mB))) = true := by
  decide +kernel

theorem csubR_scal : scalCode (.block (csubR low6 top6)) = true := by decide +kernel

theorem storesL_scal : scalCode (.block (reloc [(mO, .rsi)] (stores low6 mO))) = true := by decide +kernel

theorem sqr6_scal : ∀ adx : Bool, scalCode (.block (sqr6 adx)) = true := by decide +kernel

/-- The modulus of the function, as the rounds take it: P-384's `p`, never read
from memory. -/
theorem modOkR6 (adx : Bool) {Z m : Nat} (hZ : 48 ≤ Z) (hm : m = p384) (mem : Mem) (base : Addr) :
    ModOkR (fnMod6 adx) Z m mem base where
  n0 := by cases adx <;> decide
  n7 := by cases adx <;> decide
  mo := hZ
  val := fun h => absurd h (by cases adx <;> decide)
  inv := by subst hm; cases adx <;> decide +kernel
  red := by subst hm; cases adx <;> decide +kernel

/-! ## Steps -/

/-- `add rsi, rdi`. -/
theorem addRsiRdi_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rdi + s.gpr .rsi ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `o` into `xmm6`, `rsi = rcx`. -/
theorem keepO_ok (s : State) :
    WP isa (.block [.xop (.movq .xmm6 .rsi), .mov .rsi (.reg .rcx)]) s fun s' =>
      s'.xmm .xmm6 = (0 : BitVec 64) ++ s.gpr .rsi ∧ (∀ x, x ≠ .xmm6 → s'.xmm x = s.xmm x) ∧
        s'.gpr .rsi = s.gpr .rcx ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.xmm_setReg, setXmm_xmm, setXmm_gpr,
    ↓reduceIte]
  refine ⟨trivial, fun x hx => ?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hx, ↓reduceIte]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, setXmm_gpr]

/-- `rsi` from `xmm6`, plus `rdi`. -/
theorem backO_ok (s : State) :
    WP isa (.block [.movqR .rsi .xmm6, .alu .add .rsi (.reg .rdi)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rdi + qword (s.xmm .xmm6) 0 ∧ s'.xmm = s.xmm ∧ Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [BitVec.add_comm]; rfl
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The registers the products' branches change. -/
abbrev brClob : List Reg := [.rax, .rcx, .rdx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The square, `a = b`: `[o] = [a]² R⁻¹ mod p`. -/
theorem sqr6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a m : Nat} (hm : m = p384) (hbx : s.gpr .rbx = off base a) (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : Arg6 Z o) (ha : Arg6 Z a) (hA : wordsVal s.mem base a 6 < m) :
    WP isa (.block (sqr6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % m := by
  have hnw := hs.nowrap
  unfold Arg6 at ho ha
  rw [fnTmp6_eq] at ho ha ⊢
  simp only [sqr6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addRsiRdi_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hp₁ : PtrsAt [(.rbx, a), (.rsi, o)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, k₁.1 _ (by decide), hs.rdi, hsi])
  obtain w₂ := sqrSA_ok (M := fnMod6 adx) hs₁ hm (by simp only [fnMod6, fnTmp6]; omega_using [hZ]) (o := o) (a := a)
    (by omega_using [ho]) (by omega_using [ha]) (by simp only [fnMod6, fnTmp6]; omega_using [ho]) (by simp only [fnMod6, fnTmp6]; omega_using [ha])
    (by rw [k₁.2.1]; exact hA)
  rw [← sqrSA_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (sqr_keeps adx) hp₁ w₂)
    fun s₂ ⟨k₂, O₂, _, lt₂, res₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok s₂ (ts := sqWin6) (top := .r8) rfl ⟨by decide, by decide⟩ hm lt₂)
    fun s₃ ⟨e₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain hp₃ : PtrsAt [(.rsi, o)] s₃ := .one (by
    rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₃.1 .rdi (by decide), k₂.gpr .rdi (by decide)]
    exact hp₁ .rsi o rfl)
  obtain w₄ := stores_ok sqWin6 hs₃ (o := o) (by simp only [sqWin6, List.length_cons, List.length_nil]; omega_using [ho])
    (by decide)
  rw [← storesW_reloc, ← reloc_unptr] at w₄
  refine WP.mono (wp_unptr (rs := [.rsi]) (by simp) _ storesW_keeps hp₃ w₄)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  simp only [show sqWin6.length = 6 from rfl, Nat.reduceMul] at e₄ O₄
  obtain hval : wordsVal s₄.mem base o 6 =
      (regsVal s₂ sqWin6 + 2 ^ (64 * 6) * (s₂.gpr .r8).toNat) % m := by rw [e₄, e₃]
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_⟩
  · rw [k₄.gpr r (by simp), k₃.1 r (not_mem_of hr (by decide)), k₂.gpr r (not_mem_of hr (by decide)),
      k₁.1 r (not_mem_of hr (by decide))]
  · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [O₄ x hx, k₃.2.1, O₂ x hx (by simp only [fnMod6, fnTmp6]; omega_using [hx']), hmem₁]
  · rw [hval]; exact Nat.mod_lt _ (by rw [hm]; decide)
  · rw [hval, ← hmem₁]; exact res₂

/-- The product, `a ≠ b`: `[o] = [a] [b] R⁻¹ mod p`. -/
theorem mul6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b m : Nat} (hm : m = p384) (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : Arg6 Z o) (ha : Arg6 Z a) (hb : Arg6 Z b) (hB : wordsVal s.mem base b 6 < m) :
    WP isa (.block (mul6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % m ∧
      ∀ x, x ≠ .xmm6 → s'.xmm x = s.xmm x := by
  have hnw := hs.nowrap
  unfold Arg6 at ho ha hb
  rw [fnTmp6_eq] at ho ha hb ⊢
  simp only [mul6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (keepO_ok s) fun s₁ ⟨x₁, xo₁, e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hp₁ : PtrsAt [(.rbx, a), (.rsi, b)] s₁ := .two (by rw [k₁.1 _ (by decide), hbx, hs₁.rdi])
    (by rw [e₁, hcx, hs₁.rdi])
  have hmem₁ : s₁.mem = s.mem := k₁.2.1
  obtain w₂ := mulRounds_ok (M := fnMod6 adx) hs₁ (modOkR6 adx (by omega_using [hZ]) hm _ _) (a := a) (b := b)
    (by simp only [fnMod6]; omega_using [ha]) (by simp only [fnMod6]; omega_using [hb]) (by rw [hmem₁]; exact hB)
  rw [← mulRounds_reloc, ← reloc_unptr] at w₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mul_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mul_keeps adx) hp₁ w₂))
    fun s₂ ⟨⟨⟨U, eU⟩, hT, k₂⟩, x₂, _⟩ => ?_
  simp only [show (fnMod6 adx).n = 6 from rfl] at eU hT k₂
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  -- The accumulator's value as `csubR` sees it: its top word is zero.
  obtain hV : regsVal s₂ low6 + 2 ^ (64 * 6) * (s₂.gpr top6).toNat = regsVal s₂ (wins 6 6) := by
    simp only [low6, top6]
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    obtain hm' : m < 2 ^ (64 * 6) := (p384_bounds hm).1
    have : (s₂.gpr (win 6 6 (6 + 1))).toNat = 0 := by
      generalize (2 : Nat) ^ (64 * 6) = Q at hT' hm'
      by_contra hne
      have : Q * 2 ^ 64 ≤ Q * ((s₂.gpr (win 6 6 6)).toNat + 2 ^ 64 * (s₂.gpr (win 6 6 (6 + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_using [hne])
      omega_using [hZ, hm, hbx, hcx, hsi, ho, ha, hb, hB, hnw, x₁, e₁, eU, hT, hT', hm', hne, this]
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep csubR_scal (csubR_ok s₂ (ts := low6) (top := top6) rfl ⟨by decide, by decide⟩ hm
    (by rw [hV]; exact hT))) fun s₃ ⟨⟨e₃, k₃⟩, x₃, _⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₃) fun s₄ ⟨e₄, x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hp₄ : PtrsAt [(.rsi, o)] s₄ := .one (by
    rw [e₄, x₃, x₂, x₁, qword_lo, hsi, k₄.1 .rdi (by decide)])
  obtain w₅ := stores_ok low6 hs₄ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega_using [ho])
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₅
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₄ w₅))
    fun s₅ ⟨⟨e₅, k₅, O₅⟩, x₅, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₅ O₅
  obtain hval : wordsVal s₅.mem base o 6 = regsVal s₂ (wins 6 6) % m := by
    rw [e₅, show regsVal s₄ low6 = regsVal s₃ low6 from regsVal_congr fun q hq => k₄.1 q (by
      intro h; simp only [List.mem_singleton] at h; subst h; revert hq; decide), e₃, hV]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [k₅.gpr r (by simp), k₄.1 r (not_mem_of hr (by decide)), k₃.1 r (not_mem_of hr (by decide)),
      k₂.1 r (not_mem_of hr (by decide)), k₁.1 r (not_mem_of hr (by decide))]
  · rw [k₅.rd, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₅.wr, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₅ x hx, k₄.2.1, k₃.2.1, k₂.2.1, hmem₁]
  · rw [hval]; exact Nat.mod_lt _ (by rw [hm]; decide)
  · rw [hval, Nat.mod_mul_mod, Nat.mul_comm, eU, ← hmem₁]
    simp only [Nat.add_mul_mod_self_right]
  · rw [x₅, x₄, x₃, x₂, xo₁ x hx]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻³⁸⁴ mod p` for P-384's `p = m`, the offsets the low
halves of `rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]`
and its temporary area, bytes `fnTmp6` to 4095. -/
theorem mulFn6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {m : Nat} (hm : m = p384) (ho : Arg6 Z (argOf s .rsi)) (ha : Arg6 Z (argOf s .rdx))
    (hb : Arg6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < m) :
    WP isa (mulFn6 adx) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % m =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, zf₁, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  obtain hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (show WP isa (.ite .e (.block (sqr6 adx)) (.block (mul6 adx))) s₁ (fun s' =>
      KeepRegs brClob s₁ s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s₁.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s₁.mem base a 6 * wordsVal s₁.mem base b 6 % m ∧
      ∀ x, x ≠ .xmm6 → s'.xmm x = s₁.xmm x) from ?_) fun s₂ h₂ => ?_)
  · refine WP.ite (decide (a = b)) zf₁ (fun h => ?_) (fun _ => mul6_ok adx hs₁ hZ hm bx₁ cx₁ si₁ ho ha hb
      (by rw [m₁]; exact hB))
    obtain hab : a = b := of_decide_eq_true h
    subst hab
    exact WP.mono (WP.vecKeep (sqr6_scal adx) (sqr6_ok adx hs₁ hZ hm bx₁ si₁ ho ha (by rw [m₁]; exact hB)))
      fun s' ⟨⟨k, O, lt, e⟩, xm, _⟩ => ⟨k, O, lt, e, fun x _ => by rw [xm]⟩
  obtain ⟨k₂, O₂, lt₂, e₂, xm₂⟩ := h₂
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xm₂ _ (by decide), x0, qword_lo]
      · rw [p₃, xm₂ _ (by decide), x1, qword_lo]
      · rw [r12₃, xm₂ _ (by decide), x2, qword_lo]
      · rw [r13₃, xm₂ _ (by decide), x3, qword_lo]
      · rw [r14₃, xm₂ _ (by decide), x4, qword_lo]
      · rw [r15₃, xm₂ _ (by decide), x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']

end VG.Proof.Weierstrass.X86_64.Mont

end

end


/-!
# P-384's product modulo `n` as a function, on x86-64

`mulFnN6 adx` (`Impl/Weierstrass/X86_64/Mont.lean`) keeps `o` in `xmm6`
(`keepO_ok`) and the words at `fnMoN6` in `xmm7`–`xmm12`
(`saveSteps_ok`), stores `n` there (`setConst`), then runs the inline
product's rounds `mulRounds` relocated: its operands at the markers read
through `rbx = ws + a` and `rsi = ws + b`. With those registers so
(`PtrsAt`), the relocated code runs as the inline code at the offsets `a`
and `b` (`wp_unptr`, `mulRoundsN6_reloc`), whose proof then applies
(`mulRounds_ok`), `n` now in memory. `csub` reduces the result with `n` in
memory, which is stored through `rsi = ws + o` (`backO_ok`, `stores_ok`).
It puts the words back (`restoreSteps_ok`), so the function changes only
`fnClob`, `[o]` and its temporary area, bytes `fnTmp6` to 4095
(`mulFnN6_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.Weierstrass (Unch)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- An offset `vg_p384_mul_mod_n` takes: apart from `n` and its temporary
area, and within the working space. -/
def ArgN6 (Z x : Nat) : Prop := (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x) ∧ x + 48 ≤ Z

theorem fnMoN6_eq : fnMoN6 = 4000 := rfl

theorem n384_lt : n384 < 2 ^ (64 * 6) := by decide +kernel

/-! ## The relocated code is the inline code -/

theorem mulRoundsN6_reloc (adx : Bool) (a b : Nat) :
    (mulRounds (fnModN6 adx) mA mB).map
        (Instr.mapMem (unptr [(.rbx, a), (.rsi, b)] ∘ relocTo [(mA, .rbx), (mB, .rsi)])) =
      mulRounds (fnModN6 adx) a b := by
  cases adx <;> kernel_rfl

theorem mulN6_keeps : ∀ adx : Bool,
    (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnModN6 adx) mA mB)).all (keepsPtrs [.rbx, .rsi]) = true := by
  decide +kernel

theorem mulN6_scal : ∀ adx : Bool,
    scalCode (.block (reloc [(mA, .rbx), (mB, .rsi)] (mulRounds (fnModN6 adx) mA mB))) = true := by
  decide +kernel

theorem storeN6_scal : scalCode (.block storeN6) = true := by decide +kernel

theorem csubN6_scal : ∀ adx : Bool, scalCode (.block (csub (fnModN6 adx) low6 top6)) = true := by decide +kernel

/-- The modulus of the product, as the rounds take it, once stored. -/
theorem modOkRN6 (adx : Bool) {Z : Nat} (hZ : 4096 ≤ Z) {mem : Mem} {base : Addr}
    (hv : wordsVal mem base fnMoN6 6 = n384) : ModOkR (fnModN6 adx) Z n384 mem base where
  n0 := by cases adx <;> decide
  n7 := by cases adx <;> decide
  mo := by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using [hZ]
  val := .of_val hv
  inv := by cases adx <;> decide +kernel
  red := by cases adx <;> decide +kernel

theorem keepX6_ne : ∀ i j, i < j → j < 6 → keepX6 i ≠ keepX6 j := by
  intro i j hij hj
  obtain h : ∀ j < 6, ∀ i < j, keepX6 i ≠ keepX6 j := by decide
  exact h j hj i hij

theorem keepX6_ne6 : ∀ i < 6, keepX6 i ≠ .xmm6 := by decide

/-- The middle of `mulFnN6`: the product, `[o] = [a] [b] R⁻¹ mod n`, with `n`
stored over bytes it restores; it changes `[o]` and the temporary area only,
and no vector register but `xmm6`–`xmm12`. -/
theorem mulN6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    {o a b : Nat} (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 o)
    (ho : ArgN6 Z o) (ha : ArgN6 Z a) (hb : ArgN6 Z b) (hB : wordsVal s.mem base b 6 < n384) :
    WP isa (.block (mulN6 adx)) s fun s' =>
      KeepRegs brClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) → (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) →
        s'.mem x = s.mem x) ∧
      (∀ x, x ≠ .xmm6 → (∀ i < 6, x ≠ keepX6 i) → s'.xmm x = s.xmm x) ∧
      wordsVal s'.mem base o 6 < n384 ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % n384 = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % n384 := by
  have hnw := hs.nowrap
  unfold ArgN6 at ho ha hb
  rw [fnTmp6_eq] at ho ha hb ⊢
  simp only [mulN6, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (keepO_ok s) fun s₁ ⟨x₁, xo₁, e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (saveSteps_ok (d := fnMoN6) keepX6 6 s₁ hs₁ (by rw [fnMoN6_eq]; omega_using [hZ]) keepX6_ne)
    fun s₁' ⟨x₁', o₁', m₁', k₁'⟩ => ?_
  obtain hs₁' := hs₁.of_keepRegs k₁' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storeN6_scal
    (setConst_ok (n := 6) (o := fnMoN6) (x := n384) hs₁' (by rw [fnMoN6_eq]; omega_using [hZ]) n384_lt))
    fun s₂ ⟨⟨v₂, k₂, O₂⟩, x₂, _⟩ => ?_
  obtain hs₂ := hs₁'.of_keepRegs k₂ (by decide)
  obtain far : ∀ x, (x + 96 ≤ 4048 ∨ 4096 ≤ x) → x + 48 ≤ Z →
      wordsVal s₂.mem base x 6 = wordsVal s.mem base x 6 := fun x hx hxZ => by
    rw [(show Unch base [(fnMoN6, 8 * 6)] s₁'.mem s₂.mem from
      fun y hy => O₂ y (hy _ (List.mem_singleton_self _))).wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN6_eq]; omega_using [hx]) (by omega_using [hnw, hxZ]), m₁', hm₁]
  obtain g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r := fun r hr => by
    rw [k₂.gpr r (by simpa using hr), k₁'.gpr r (by simpa using hr)]
  have hp₂ : PtrsAt [(.rbx, a), (.rsi, b)] s₂ := .two
    (by rw [g₂ _ (by decide), k₁.1 _ (by decide), hbx, hs₂.rdi])
    (by rw [g₂ _ (by decide), e₁, hcx, hs₂.rdi])
  obtain w₃ := mulRounds_ok (M := fnModN6 adx) hs₂ (modOkRN6 adx hZ v₂) (a := a) (b := b)
    (by simp only [fnModN6]; omega_using [ha]) (by simp only [fnModN6]; omega_using [hb])
    (by simp only [fnModN6]; rw [far b hb.1 hb.2]; exact hB)
  rw [← mulRoundsN6_reloc adx, ← reloc_unptr] at w₃
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (mulN6_scal adx) (wp_unptr (rs := [.rbx, .rsi]) (by simp) _ (mulN6_keeps adx) hp₂ w₃))
    fun s₃ ⟨⟨⟨U, eU⟩, hT, k₃⟩, x₃, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at eU hT k₃
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  -- The accumulator's value as `csub` sees it: its top word is zero.
  obtain hV : regsVal s₃ low6 + 2 ^ (64 * 6) * (s₃.gpr top6).toNat = regsVal s₃ (wins 6 6) := by
    simp only [low6, top6]
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [wins_split 6 6, regsVal_append, show ((List.range 6).map (win 6 6)).length = 6 from rfl] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have hm' : n384 < 2 ^ (64 * 6) := n384_lt
    have : (s₃.gpr (win 6 6 (6 + 1))).toNat = 0 := by
      generalize (2 : Nat) ^ (64 * 6) = Q at hT' hm'
      by_contra hne
      have : Q * 2 ^ 64 ≤ Q * ((s₃.gpr (win 6 6 6)).toNat + 2 ^ 64 * (s₃.gpr (win 6 6 (6 + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_using [hne])
      omega_using [hT', hm', this]
    rw [this, Nat.mul_zero, Nat.add_zero]
  obtain hmo₃ : wordsVal s₃.mem base (fnModN6 adx).mo (fnModN6 adx).n = n384 := by rw [k₃.2.1]; exact v₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep (csubN6_scal adx) (csub_ok hs₃ (M := fnModN6 adx) (ts := low6) (top := top6) rfl (by simp only [fnModN6]; decide)
    ⟨by decide, by decide⟩ (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using [hZ]) (by simp only [fnModN6, fnTmp6]; omega_using [hZ])
    (by simp only [fnModN6, fnMoN6, fnTmp6]; omega_using []) (fun h => absurd h (by simp only [fnModN6]; decide)) hmo₃
    (by rw [show (fnModN6 adx).n = 6 from rfl, hV]; exact hT))) fun s₄ ⟨⟨e₄, k₄, O₄⟩, x₄, _⟩ => ?_
  simp only [show (fnModN6 adx).n = 6 from rfl] at e₄ O₄
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (backO_ok s₄) fun s₅ ⟨e₅, x₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain hp₅ : PtrsAt [(.rsi, o)] s₅ := .one (by
    rw [e₅, x₄, x₃, x₂, o₁' .xmm6 (fun j hj => (keepX6_ne6 j hj).symm), x₁, qword_lo, hsi, k₅.1 .rdi (by decide)])
  obtain w₆ := stores_ok low6 hs₅ (o := o) (by simp only [low6, List.length_map, List.length_range]; omega_using [ho])
    (by decide)
  rw [← storesL_reloc, ← reloc_unptr] at w₆
  rw [WP.block_append_iff]
  refine WP.mono (WP.vecKeep storesL_scal (wp_unptr (rs := [.rsi]) (by simp) _ storesL_keeps hp₅ w₆))
    fun s₆ ⟨⟨e₆, k₆, O₆⟩, x₆, _⟩ => ?_
  simp only [show low6.length = 6 from rfl, Nat.reduceMul] at e₆ O₆
  obtain hs₆ : Scr s₆ base Z := ⟨(k₆.gpr _ (by simp)).trans hs₅.rdi, k₆.wr ▸ hs₅.wr, hnw⟩
  refine WP.mono (restoreSteps_ok (d := fnMoN6) keepX6 6 s₆ hs₆ (by rw [fnMoN6_eq]; omega_using [hZ]))
    fun s₇ ⟨e₇, O₇, x₇, k₇⟩ => ?_
  obtain hval₆ : wordsVal s₆.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
    rw [e₆, show regsVal s₅ low6 = regsVal s₄ low6 from regsVal_congr fun q hq => k₅.1 q (by
      intro h; simp only [List.mem_singleton] at h; subst h; revert hq; decide), e₄, hV]
  obtain hval : wordsVal s₇.mem base o 6 = regsVal s₃ (wins 6 6) % n384 := by
    rw [O₇.unch.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; rw [fnMoN6_eq]; omega_using [ho]) (by omega_using [ho, hnw]), hval₆]
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₇.rd, k₆.rd, k₅.2.2.1, k₄.rd, k₃.2.2.1, k₂.rd, k₁'.rd, k₁.2.2.1],
      by rw [k₇.wr, k₆.wr, k₅.2.2.2, k₄.wr, k₃.2.2.2, k₂.wr, k₁'.wr, k₁.2.2.2]⟩,
    fun x hx hx' => ?_, fun x hx hx6 => ?_, ?_, ?_⟩
  · have hra : r ≠ .rax := fun h => hr (h ▸ by decide)
    rw [k₇.gpr r (by simpa using hra), k₆.gpr r (by simp), k₅.1 r (not_mem_of hr (by decide)),
      k₄.gpr r (not_mem_of hr (by decide)), k₃.1 r (not_mem_of hr (by decide)), g₂ r hra,
      k₁.1 r (not_mem_of hr (by decide))]
  · by_cases hin : 4000 ≤ ofs base x ∧ ofs base x < 4048
    · -- A byte of the words restored.
      obtain hp : ∃ i < 6, ∃ j < 8, x = off base (fnMoN6 + 8 * i) + BitVec.ofNat 64 j := by
        refine ⟨(ofs base x - 4000) / 8, by omega_using [hin], (ofs base x - 4000) % 8, Nat.mod_lt _ (by decide), ?_⟩
        rw [off, Offset.add_add, fnMoN6_eq, show 4000 + 8 * ((ofs base x - 4000) / 8) + (ofs base x - 4000) % 8 =
          ofs base x by omega_using [hin], BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      obtain ⟨i, hi, j, hj, rfl⟩ := hp
      obtain hw : word s₇.mem base (fnMoN6 + 8 * i) = word s.mem base (fnMoN6 + 8 * i) := by
        rw [e₇ i hi, x₆, x₅, x₄, x₃, x₂, x₁' i hi, qword_lo, hm₁]
      exact byte_of_word hw hj
    · rw [O₇ x (by rw [fnMoN6_eq]; omega_using [hin]), O₆ x hx, k₅.2.1, O₄ x (by simp only [fnModN6, fnTmp6]; omega_using [hx']), hm₃,
        O₂ x (by rw [fnMoN6_eq]; omega_using [hin]), m₁', hm₁]
  · rw [x₇, x₆, x₅, x₄, x₃, x₂, o₁' x hx6, xo₁ x hx]
  · rw [hval]; exact Nat.mod_lt _ (by decide)
  · rw [hval, Nat.mod_mul_mod, Nat.mul_comm, eU, far a ha.1 ha.2, far b hb.1 hb.2]
    simp only [Nat.add_mul_mod_self_right]

/-! ## The function -/

/-- `[o] = [a] [b] 2⁻³⁸⁴ mod n` for P-384's `n`, the offsets the low halves
of `rsi`, `rdx` and `rcx`: the function changes only `fnClob`, `[o]` and its
temporary area, bytes `fnTmp6` to 4095. -/
theorem mulFnN6_ok (adx : Bool) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (ho : ArgN6 Z (argOf s .rsi)) (ha : ArgN6 Z (argOf s .rdx)) (hb : ArgN6 Z (argOf s .rcx))
    (hB : wordsVal s.mem base (argOf s .rcx) 6 < n384) :
    WP isa (mulFnN6 adx) s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < n384 ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % n384 =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % n384 ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  refine WP.seq (WP.mono (WP.block_append_iff.mp (entry_ok hs)) fun s₀ h₀ => WP.seq (WP.mono h₀
    fun s₁ ⟨hs₁, bx₁, cx₁, _, si₁, x0, x1, x2, x3, x4, x5, k₁, m₁⟩ => ?_))
  generalize hO : argOf s .rsi = o at *
  generalize hA : argOf s .rdx = a at *
  generalize hBb : argOf s .rcx = b at *
  obtain hQ : (2 : Nat) ^ (64 * 6) = (2 ^ 64) ^ 6 := Nat.pow_mul 2 64 6
  refine WP.seq (WP.mono (mulN6_ok adx hs₁ hZ bx₁ cx₁ si₁ ho ha hb (by rw [m₁]; exact hB))
    fun s₂ ⟨k₂, O₂, xm₂, lt₂, e₂⟩ => ?_)
  obtain xk : ∀ x, x ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5] → s₂.xmm x = s₁.xmm x := fun x hx =>
    xm₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (restores_ok s₂) fun s₃ ⟨b₃, p₃, r12₃, r13₃, r14₃, r15₃, k₃⟩ => ?_
  rw [m₁] at e₂ O₂
  refine ⟨by rw [k₃.2.1]; exact lt₂, by rw [k₃.2.1, ← hQ]; exact e₂,
    ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.rd], by rw [k₃.2.2.2, k₂.wr, k₁.wr]⟩, fun x hx hx' => ?_⟩
  · rcases not_clob_cases r hr with hsv | rfl | rfl
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hsv
      rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b₃, xk _ (by simp), x0, qword_lo]
      · rw [p₃, xk _ (by simp), x1, qword_lo]
      · rw [r12₃, xk _ (by simp), x2, qword_lo]
      · rw [r13₃, xk _ (by simp), x3, qword_lo]
      · rw [r14₃, xk _ (by simp), x4, qword_lo]
      · rw [r15₃, xk _ (by simp), x5, qword_lo]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [k₃.2.1, O₂ x hx hx']

end VG.Proof.Weierstrass.X86_64.Mont

end

end


/-!
# Products modulo P-521's and P-384's `p` by calls, on x86-64

`mulCall_ok`: a call of `vg_p521_mul_mod_p` or `vg_p521_mul_mod_p_adx`
(`Mont.mulCall`), inlined (`Code.inline`, as `CallInline.lean` relates it to
the call), keeps and computes what the inline product does
(`Proof/Mont/X86_64/Ops.lean`'s `mul_ok`), for P-521's `p` with the
functions' temporary area: the functions change only `[o]` and that area, and
the call keeps `rsi` in `r12`, which the functions restore. `mulCall6_ok` is
the same for `vg_p384_mul_mod_p` and `vg_p384_mul_mod_p_adx`, for offsets
apart from their temporary area (`lowArgs 6`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps)

/-- The call's arguments: `rsi` into `r12`, the offsets into `esi`, `edx`
and `ecx`. -/
theorem callArgs_ok (s : State) {o a b : Nat} (ho : o < 2 ^ 32) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    WP isa (.block [.mov .r12 (.reg .rsi), .mov32 .rsi (.imm (BitVec.ofNat 32 o)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 a)), .mov32 .rcx (.imm (BitVec.ofNat 32 b))]) s fun s' =>
      s'.gpr .r12 = s.gpr .rsi ∧ argOf s' .rsi = o ∧ argOf s' .rdx = a ∧ argOf s' .rcx = b ∧
      Keeps [.r12, .rsi, .rdx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, reduceCtorEq, ite_true,
    ite_false, argOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine ⟨trivial, by omega_using [ho], by omega_using [ha], by omega_using [hb], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- The code of either function, which calls none. -/
theorem fn_ok {body : Prog isa} (hbody : body = mulFn ∨ body = mulFnX) {s : State} {base : Addr} {Z : Nat}
    (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520) (hb : argOf s .rcx + 72 ≤ 3520)
    (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFn_ok hs hZ hm ho ha hb hB
  · exact mulFnX_ok hs hZ hm ho ha hb hB

/-- The registers the inline products keep, for nine words. -/
theorem not_clob9 : ∀ r : Reg, r ∉ clob 9 → r = .rbx ∨ r = .rsp ∨ r = .rsi ∨ r = .rdi := by
  intro r; cases r <;> decide

/-- A product modulo P-521's `p` by a call of `body`, inlined: as the inline
product (`mul_ok`), for offsets below the functions' own working space. -/
theorem mulCall_ok {f : String} {body : Prog isa} (hbody : body = mulFn ∨ body = mulFnX) {s : State}
    {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat} (hM : ModOkW M Z m s.mem base)
    (hred : M.red = .friendly p521Ws) (ht : M.tmp = fnTmp) {o a b : Nat} (hlow : lowArgs 9 o a b = true)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn9] at this; simp only [fnTmp] at this; omega_using [this]
  simp only [lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn9] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (fn_ok hbody hs₁ hZ hm (by rw [o₁]; omega_using [ho]) (by rw [a₁]; omega_using [ha]) (by rw [b₁]; omega_using [hb])
    (by rw [b₁, hm₁]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 9]; exact e₂⟩
  · rw [hn9] at hr
    rcases not_clob9 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn9] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp] at ht' ⊢; omega_using [ht']), hm₁]

/-- The registers the inline products keep, for six words. -/
theorem not_clob6 : ∀ r : Reg, r ∉ clob 6 → r = .rbx ∨ r = .rsp ∨ r = .rsi ∨ r = .rdi := by
  intro r; cases r <;> decide

theorem fn6_ok {body : Prog isa} (hbody : body = mulFn6 false ∨ body = mulFn6 true) {s : State} {base : Addr}
    {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat} (hm : m = p384) (ho : Arg6 Z (argOf s .rsi))
    (ha : Arg6 Z (argOf s .rdx)) (hb : Arg6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < m) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % m =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFn6_ok false hs hZ hm ho ha hb hB
  · exact mulFn6_ok true hs hZ hm ho ha hb hB

/-- A product modulo P-384's `p` by a call of `body`, inlined: as the inline
product (`mul_ok`), for offsets apart from the functions' temporary area. -/
theorem mulCall6_ok {f : String} {body : Prog isa} (hbody : body = mulFn6 false ∨ body = mulFn6 true)
    {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat} (hM : ModOkW M Z m s.mem base)
    (hsp : M.sparse = true) (ht : M.tmp = fnTmp6) {o a b : Nat} (hlow : lowArgs 6 o a b = true)
    (hoZ : o + 8 * M.n ≤ Z) (haZ : a + 8 * M.n ≤ Z) (hbZ : b + 8 * M.n ≤ Z)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain ⟨hn6, hm⟩ := Mod.ok_sparse hM.red hsp
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn6] at this; simp only [fnTmp6] at this; omega_using [this]
  simp only [lowArgs, show ¬ (6 = 9) by decide, show ¬ (6 = 8) by decide, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn6] at hB hoZ haZ hbZ ⊢
  obtain h31 : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x < 2 ^ 32 := fun x h => by
    simp only [fnTmp6] at h; omega_using [h]
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (h31 o ho) (h31 a ha) (h31 b hb))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain arg : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x + 48 ≤ Z → Arg6 Z x := fun x h hz =>
    ⟨h.imp (fun h => by simp only [fnTmp6] at h ⊢; omega_using [h]) And.left, hz⟩
  refine WP.seq (WP.mono (fn6_ok hbody hs₁ hZ hm (by rw [o₁]; exact arg o ho hoZ) (by rw [a₁]; exact arg a ha haZ)
    (by rw [b₁]; exact arg b hb hbZ) (by rw [b₁, hm₁]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 6]; exact e₂⟩
  · rw [hn6] at hr
    rcases not_clob6 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn6] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp6] at ht' ⊢; omega_using [ht']), hm₁]

/-- A product modulo P-521's `n` (`Mod.fnN`) by a call of `mulFnN`, inlined: as
the inline product, for the functions' temporary area. -/
theorem mulCallN_ok {f : String} {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnN = true) (hn9 : M.n = 9) (ht : M.tmp = fnTmp)
    {o a b : Nat} (hlow : lowArgs 9 o a b = true) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f mulFnN o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm : m = n521 := by
    rcases Mod.ok_fnN hM.red hf with ⟨_, hm⟩ | ⟨h6, _⟩
    · exact hm
    · omega
  have hm' : m = n521 := hm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn9] at this; simp only [fnTmp] at this; omega_using [this]
  simp only [lowArgs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn9] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (mulFnN_ok hs₁ hZ (by rw [o₁]; exact ho) (by rw [a₁]; exact ha) (by rw [b₁]; exact hb)
    (by rw [b₁, hm₁, ← hm']; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm']; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 9, hm']; exact e₂⟩
  · rw [hn9] at hr
    rcases not_clob9 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn9] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp] at ht' ⊢; omega_using [ht']), hm₁]

theorem mulCall8_ok (order : Bool) {f : String} {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnMod = some (Wide8.modulus order)) (hn8 : M.n = 8) (ht : M.tmp = Wide8.tmp)
    {o a b : Nat} (hlow : lowArgs 8 o a b = true) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f (Wide8.fn order) o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm' : m = Wide8.modulus order := (Mod.ok_fnMod hM.red hf).symm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn8] at this; simp only [Wide8.tmp] at this; omega_using [this]
  simp only [lowArgs, show ¬ (8 = 9) by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn8] at hB ⊢
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb]))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.seq (WP.mono (Wide8.fn_ok order hs₁ hZ (by rw [o₁]; exact ho) (by rw [a₁]; exact ha) (by rw [b₁]; exact hb)
    (by rw [b₁, hm₁, ← hm']; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm']; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 8, hm']; exact e₂⟩
  · rw [hn8] at hr
    rcases not_clob9 r (show r ∉ clob 9 from hr) with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn8] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [Wide8.tmp] at ht' ⊢; omega_using [ht']), hm₁]

theorem fnN6_ok {body : Prog isa} (hbody : body = mulFnN6 false ∨ body = mulFnN6 true) {s : State} {base : Addr}
    {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) (ho : ArgN6 Z (argOf s .rsi))
    (ha : ArgN6 Z (argOf s .rdx)) (hb : ArgN6 Z (argOf s .rcx)) (hB : wordsVal s.mem base (argOf s .rcx) 6 < n384) :
    WP isa body s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 6 < n384 ∧
      wordsVal s'.mem base (argOf s .rsi) 6 * (2 ^ 64) ^ 6 % n384 =
        wordsVal s.mem base (argOf s .rdx) 6 * wordsVal s.mem base (argOf s .rcx) 6 % n384 ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 48 ≤ ofs base x) →
        (ofs base x < fnTmp6 ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x := by
  rcases hbody with rfl | rfl
  · exact mulFnN6_ok false hs hZ ho ha hb hB
  · exact mulFnN6_ok true hs hZ ho ha hb hB

/-- A product modulo P-384's `n` (`Mod.fnN`) by a call of `mulFnN6 adx`, inlined:
as the inline product, for offsets apart from `n` and the functions'
temporary area. -/
theorem mulCallN6_ok {f : String} {body : Prog isa} (hbody : body = mulFnN6 false ∨ body = mulFnN6 true) {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {M : Mod} {m : Nat}
    (hM : ModOkW M Z m s.mem base) (hf : M.fnN = true) (hn6 : M.n = 6) (ht : M.tmp = fnTmp6)
    {o a b : Nat} (hlow : lowArgs 6 o a b = true)
    (hoZ : o + 8 * M.n ≤ Z) (haZ : a + 8 * M.n ≤ Z) (hbZ : b + 8 * M.n ≤ Z)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f body o a b).inline s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  obtain hm : m = n384 := by
    rcases Mod.ok_fnN hM.red hf with ⟨h9, _⟩ | ⟨_, hm⟩
    · omega
    · exact hm
  obtain hZ : 4096 ≤ Z := by have := hM.tmp; rw [ht, hn6] at this; simp only [fnTmp6] at this; omega_using [this]
  simp only [lowArgs, show ¬ (6 = 9) by decide, show ¬ (6 = 8) by decide, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hlow
  obtain ⟨⟨ho, ha⟩, hb⟩ := hlow
  rw [hn6] at hB hoZ haZ hbZ ⊢
  obtain h31 : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x < 2 ^ 32 := fun x h => by
    simp only [fnTmp6] at h; omega_using [h]
  simp only [mulCall, Code.inline]
  refine WP.seq (WP.mono (callArgs_ok s (o := o) (a := a) (b := b) (h31 o ho) (h31 a ha) (h31 b hb))
    fun s₁ ⟨r12₁, o₁, a₁, b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain arg : ∀ x, (x + 96 ≤ fnTmp6 ∨ 4096 ≤ x ∧ x < 2 ^ 31) → x + 48 ≤ Z → ArgN6 Z x := fun x h hz =>
    ⟨h.imp id And.left, hz⟩
  refine WP.seq (WP.mono (fnN6_ok hbody hs₁ hZ (by rw [o₁]; exact arg o ho hoZ) (by rw [a₁]; exact arg a ha haZ)
    (by rw [b₁]; exact arg b hb hbZ) (by rw [b₁, hm₁, ← hm]; exact hB)) fun s₂ ⟨lt₂, e₂, k₂, m₂⟩ => ?_)
  refine WP.mono (movReg_ok s₂ .rsi .r12) fun s₃ ⟨v₃, k₃⟩ => ?_
  rw [o₁] at lt₂ e₂ m₂
  rw [a₁, b₁, hm₁] at e₂
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  refine ⟨⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.rd, k₁.2.2.1], by rw [k₃.2.2.2, k₂.wr, k₁.2.2.2],
    fun x hx ht' => ?_⟩, by rw [hm₃, hm]; exact lt₂, by rw [hm₃, Nat.pow_mul 2 64 6, hm]; exact e₂⟩
  · rw [hn6] at hr
    rcases not_clob6 r hr with rfl | rfl | rfl | rfl
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
    · rw [v₃, k₂.gpr _ (by decide), r12₁]
    · rw [k₃.1 _ (by decide), k₂.gpr _ (by decide), k₁.1 _ (by decide)]
  · rw [hn6] at hx ht'
    rw [ht] at ht'
    rw [hm₃, m₂ x hx (by simp only [fnTmp6] at ht' ⊢; omega_using [ht']), hm₁]

end VG.Proof.Weierstrass.X86_64.Mont
