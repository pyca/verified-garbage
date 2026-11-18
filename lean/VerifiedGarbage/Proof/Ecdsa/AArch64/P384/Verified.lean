module

import VerifiedGarbage.Proof.Weierstrass.AArch64.MontModuli
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.P384.Order
meta import VerifiedGarbage.Proof.P384.Order
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontModuli
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.P384.Prime
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.CombArithmetic
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Impl.P384.Linear
import VerifiedGarbage.Proof.Mont.AArch64.RowInit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.P256.EcdhDouble.Arithmetic
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.P384.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Impl.P384.CombArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
meta import VerifiedGarbage.Spec.P384
meta import VerifiedGarbage.Proof.P384.Ops
meta import VerifiedGarbage.Impl.P384.EcdhDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Impl.P384.Linear
meta import VerifiedGarbage.Proof.Mont.AArch64.RowInit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Weierstrass.Jac
meta import VerifiedGarbage.Proof.P256.EcdhDouble.Arithmetic
meta import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.P384.EcdhDouble.Certificate
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP2
meta import VerifiedGarbage.Proof.Weierstrass.Booth
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP2

/-! ### `Ecdsa.AArch64.P384.CombChecks`, which only this module used -/

section

/-!
# ECDSA over P-384 on AArch64: the pipelined comb's checks

`jp2_checks`: what `tcombJP2_ok` needs of P-384's comb
(`Impl.P384.CombArithmetic.comb`), evaluated on its code (`JPChecks2`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P384

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass

/-- The two-pass pipelined comb's code: its addition scalar code storing within
the working space, apart from the table its selection reads at `x30`. -/
theorem jp2_checks : JPChecks2 p384.combCfg 8192 Impl.P384.CombArithmetic.mixed :=
  ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end VG.Proof.Ecdsa.AArch64.P384

end

end

/-! ### `Ecdsa.AArch64.CombJP2`, which only this module used -/

section

/-!
# ECDSA on AArch64: the comb pipelined in two passes

`combJP2_correct`: for any curve the proof of the code supports, the comb
with Booth digits, Jacobian mixed additions in a straight line `mc` (of a
field compiler for its modulus), and each window's addition woven with the
next one's selection in two passes (`TCombCfg.combJP2`), gives what the
signing's and the public key's stages need of `[k]G` (`CombCorrect`), given
the bound on Booth digits (`BoothOk`) for scalars below `kmax` and the checks
on its code (`JPChecks2`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem combJP2_correct (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) {arithmetic : Mod → List FOp → Prog isa}
    {X : List Reg} (hcomp : FieldCompilerOn c.combCfg.M c.C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob c.combCfg.M.n ∧ r ≠ .x19) (hJ : c.combCfg.J < 4096)
    (hb : 1 ≤ c.combCfg.bits) {kmax : Nat} (hB : BoothOk c.C c.combCfg.w c.combCfg.J kmax)
    (hk : 2 ^ c.combCfg.kbytes ≤ kmax) {mc : List Instr}
    (hblk : arithmetic c.combCfg.M (maddJ c.combCfg.S c.combCfg.A c.combCfg.E c.combCfg.D) = .block mc)
    (hck : JPChecks2 c.combCfg size mc) :
    CombCorrect c (c.combCfg.combJP2 arithmetic mc) := by
  intro base k T s hs hm hf
  exact WP.mono (tcombJP2_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hcomp hX hJ hC
    hc.am3 hc.onG (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt hb hB (Nat.lt_of_lt_of_le hf.k_lt hk) hblk hck
    hs hm hf)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩

end VG.Proof.Ecdsa.AArch64

end

end

/-! ### `P384.CombArithmetic`, which this module and modules that import it used -/

section

/-! ### `P384.EcdhDouble.Verified`, which this module and modules that import it used -/

section

/-! ### `P384.EcdhDouble.Raw`, which only this module used -/

section

/-! ### `P384.Linear`, which only this module used -/

section

/-!
# P-384's small linear combinations on AArch64

`lin_ok`: `Linear.lin o a b c d` (`Impl/P384/Linear.lean`) stores
`(c [a] + d (p - [b])) mod p` at `o`, for `[a], [b] < p` and `c`, `d` below
`2^16`, changing only the registers `clobX` and `o` (`OpKeepX`). The sum
`V = c A + d (p - B)` is computed exactly (`scaleB_ok`, `addA_ok`); its top
word `T` gives the quotient estimate `T + 1`, whose multiple of
`2^384 - p` the fold adds (`foldPre_ok`), and `p` is added back where the
fold did not carry (`correctPre_ok`), which `reduce_arith` shows is
`V mod p`.
-/

@[expose] public section

-- Powers of two up to `2^448` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.Linear

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.P384.Linear VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.P384.Ops (clobX OpKeepX)
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `ts += hs`, `adds` first, with the carry out. -/
theorem addsIn_ok (s : State) {t h : Reg} {ts hs : List Reg} (hl : ts.length = hs.length)
    (hnd : (t :: ts).Nodup) (hd : ∀ q ∈ h :: hs, q ∉ t :: ts) :
    WP isa (.block (VG.Impl.Mont.AArch64.P384Mul.addsIn true (t :: ts) (h :: hs))) s fun u =>
      regsVal u (t :: ts) + 2 ^ (64 * (ts.length + 1)) * u.c.toNat =
        regsVal s (t :: ts) + regsVal s (h :: hs) ∧ Keeps (t :: ts) s u := by
  rw [VG.Impl.Mont.AArch64.P384Mul.addsIn, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s t t h true (c := false) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  obtain htn : t ∉ ts := (List.nodup_cons.mp hnd).1
  obtain hhs : ∀ q ∈ hs, q ∉ ts := fun q hq hm =>
    hd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hm)
  refine WP.mono (P384Mul.adcsIn_ok ts hs s₁ hl (List.nodup_cons.mp hnd).2 hhs)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  obtain g₁ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
  obtain gt : regsVal s₁ ts = regsVal s ts := regsVal_congr fun r hr => k₁.gpr r (by
    simp only [List.mem_singleton]; rintro rfl; exact htn hr)
  obtain gh : regsVal s₁ hs = regsVal s hs := regsVal_congr fun r hr => k₁.gpr r (by
    simp only [List.mem_singleton]; rintro rfl
    exact hd r (List.mem_cons_of_mem _ hr) (List.mem_cons_self ..))
  obtain ev := Word64.addCarry_value (s.gpr t) (s.gpr h) false
  rw [← v₁, ← c₁] at ev
  rw [gt, gh] at e₂
  simp only [regsVal, g₁, pow64_succ]
  simp only [Nat.mul_assoc, Bool.toNat_false, Nat.add_zero] at ev ⊢
  omega_arith

/-- `x17 = k` and `x16 = 0`, for `k < 2^16`. -/
theorem consts_ok (s : State) {k : Nat} (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x17 (BitVec.ofNat 16 k) 0, .movz .x .x16 0 0]) s fun t =>
      (t.gpr .x17).toNat = k ∧ t.gpr .x16 = 0 ∧ Keeps [.x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x17 = k`, for `k < 2^16`. -/
theorem const_ok (s : State) {k : Nat} (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x17 (BitVec.ofNat 16 k) 0]) s fun t =>
      (t.gpr .x17).toNat = k ∧ Keeps [.x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `q = x16 + 1` into `x16`, and `x3 = q << 32`. -/
theorem foldShift_ok (s : State) (hT : (s.gpr .x16).toNat + 1 < 2 ^ 32) :
    WP isa (.block [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32]) s fun t =>
      (t.gpr .x16).toNat = (s.gpr .x16).toNat + 1 ∧
      (t.gpr .x3).toNat = ((s.gpr .x16).toNat + 1) * 2 ^ 32 ∧ t.c = s.c ∧
      Keeps [.x2, .x3, .x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 16 * 0 < Size.x.bits by decide,
    show 32 < Size.x.bits by decide, ite_true, RegUpd.gpr_write, RegUpd.c_write, reduceCtorEq, ite_false,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  obtain h1 : (s.gpr .x16 + (1 : BitVec 16).setWidth 64 <<< (16 * 0)).toNat = (s.gpr .x16).toNat + 1 := by
    rw [BitVec.toNat_add]
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth]
    have : (1 : BitVec 16).toNat = 1 := rfl
    omega_arith
  refine ⟨h1, ?_, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The fold's words' arithmetic: `x2 = q - q 2^32` with the borrow `b`, and
`x3 = q 2^32 - b`. -/
theorem fold_arith {q x2 x3 b j : Nat} (hq : q < 2 ^ 32) (hb : b ≤ 1) (h2 : x2 < 2 ^ 64)
    (h3 : x3 < 2 ^ 64) (e2 : x2 + q * 2 ^ 32 = q + 2 ^ 64 * b) (e3 : x3 + b = q * 2 ^ 32 + 2 ^ 64 * j) :
    x2 + 2 ^ 64 * x3 + q * 2 ^ 32 = q + q * 2 ^ 96 := by
  obtain hj : j = 0 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact h
    · exfalso
      have : 2 ^ 64 * j ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ h
      omega_arith
  subst hj
  omega_arith

/-- The fold's words: `[x3 x2] = q (2^96 - 2^32 + 1)` and `x16 = q`, with
`q = x16 + 1`. -/
theorem foldPre_ok (s : State) (hz : s.gpr .x7 = 0) (hT : (s.gpr .x16).toNat + 1 < 2 ^ 32) :
    WP isa (.block ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32,
        .subs .x .x2 .x16 .x3, .sbc .x .x3 .x3 .x7] : List Instr)) s fun t =>
      (t.gpr .x16).toNat = (s.gpr .x16).toNat + 1 ∧
      (t.gpr .x2).toNat + 2 ^ 64 * (t.gpr .x3).toNat + ((s.gpr .x16).toNat + 1) * 2 ^ 32 =
        ((s.gpr .x16).toNat + 1) + ((s.gpr .x16).toNat + 1) * 2 ^ 96 ∧
      Keeps [.x2, .x3, .x16] s t := by
  rw [show ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32,
      .subs .x .x2 .x16 .x3, .sbc .x .x3 .x3 .x7] : List Instr) =
    [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32] ++ [.subs .x .x2 .x16 .x3] ++
      [.sbc .x .x3 .x3 .x7] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (foldShift_ok s hT) fun s₁ ⟨q₁, l₁, _, k₁⟩ => ?_
  refine WP.mono (subc_ok s₁ .x2 .x16 .x3 true rfl) fun s₂ ⟨v₂, c₂, k₂⟩ => ?_
  simp only [↓reduceIte] at v₂ c₂
  obtain z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  refine WP.mono (P384Mul.sbc0_ok s₂ .x3 z₂) fun s₃ ⟨⟨j, e₃⟩, k₃⟩ => ?_
  obtain b₂ := sub_borrow (s₁.gpr .x16) (s₁.gpr .x3) true
  rw [← v₂, ← c₂] at b₂
  obtain h16 : s₃.gpr .x16 = s₁.gpr .x16 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide)]
  obtain h2 : s₃.gpr .x2 = s₂.gpr .x2 := k₃.gpr _ (by decide)
  obtain h3 : s₂.gpr .x3 = s₁.gpr .x3 := k₂.gpr _ (by decide)
  rw [h3, l₁] at e₃
  rw [l₁, q₁] at b₂
  refine ⟨by rw [h16, q₁], ?_, (k₁.trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [h2]
  rw [show (!true).toNat = 0 from rfl, Nat.add_zero] at b₂
  exact fold_arith hT (Bool.toNat_le _) (s₂.gpr .x2).isLt (s₃.gpr .x3).isLt b₂ e₃

/-- P-384's prime under the mask `x17`: `[x17 x17 x17 x16 x3 x2] = p` if
the mask is set, else zero. -/
theorem maskWords_ok (s : State) {k : Bool} (hk : s.gpr .x17 = if k then BitVec.allOnes 64 else 0) :
    WP isa (.block [.lsr .x .x2 .x17 32, .logic .eor .x .x3 .x17 .x2, .lsl .x .x16 .x17 1]) s fun t =>
      regsVal t [.x2, .x3, .x16, .x17, .x17, .x17] = (if k then p384 else 0) ∧
      t.c = s.c ∧ Keeps [.x2, .x3, .x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits by decide,
    show 1 < Size.x.bits by decide, ite_true, RegUpd.gpr_write, RegUpd.c_write, reduceCtorEq, ite_false,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [regsVal, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hk]
    cases k <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The mask of the borrow `!c`, and `p` under it. -/
theorem correctPre_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block ([.sbc .x .x17 .x7 .x7, .lsr .x .x2 .x17 32, .logic .eor .x .x3 .x17 .x2,
        .lsl .x .x16 .x17 1] : List Instr)) s fun t =>
      regsVal t [.x2, .x3, .x16, .x17, .x17, .x17] = (if s.c then 0 else p384) ∧
      Keeps [.x2, .x3, .x16, .x17] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sbcMask_ok s hz) fun s₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (maskWords_ok s₁ m₁) fun t ⟨e, _, k⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k.mono (by sub_regs))⟩
  rw [e]
  cases s.c <;> rfl

/-- One quotient estimate reduces `V = L + 2^384 T` modulo `p`: `L₁` is
`L + (T + 1) (2^384 - p)` less its carry `c₁`, and `L₂` is `L₁ + p` where
`c₁` is clear, modulo `2^384`. -/
theorem reduce_arith {V L T L₁ L₂ c₁ c₂ : Nat} (hV : V = L + 2 ^ 384 * T) (hL : L < 2 ^ 384)
    (hT : T + 1 < 2 ^ 32)
    (hL₁ : L₁ < 2 ^ 384) (hc₁ : c₁ ≤ 1)
    (h₁ : L₁ + 2 ^ 384 * c₁ + (T + 1) * 2 ^ 32 = L + (T + 1) * (2 ^ 128 + 2 ^ 96 + 1))
    (hL₂ : L₂ < 2 ^ 384) (hc₂ : c₂ ≤ 1)
    (h₂ : L₂ + 2 ^ 384 * c₂ = L₁ + (if c₁ = 1 then 0 else p384)) :
    L₂ = V % p384 := by
  obtain hp : p384 = 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1 := by decide
  rcases (by omega_arith : c₁ = 0 ∨ c₁ = 1) with rfl | rfl
  · simp only [Nat.zero_ne_one, ↓reduceIte] at h₂
    obtain e : V = L₂ + T * p384 := by rw [hp] at h₂ ⊢; omega_arith
    obtain hl : L₂ < p384 := by rw [hp] at h₂ ⊢; omega_arith
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  · simp only [↓reduceIte, Nat.add_zero] at h₂
    obtain e : V = L₂ + (T + 1) * p384 := by rw [hp]; omega_arith
    obtain hl : L₂ < p384 := by rw [hp]; omega_arith
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- Three words and three zeros. -/
theorem regsVal_fold {s : State} (hz : s.gpr .x7 = 0) {a b c : Reg} :
    regsVal s [a, b, c, .x7, .x7, .x7] =
      (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + 2 ^ 128 * (s.gpr c).toNat := by
  simp only [regsVal, hz, show (0 : BitVec 64).toNat = 0 from rfl]
  omega_arith

/-- `[o] = (c [a] + d (p - [b])) mod p`. -/
theorem lin_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA Impl.P384.Ops.M size p384 s.mem base) {o a b c d : Nat} (ho : o + 48 ≤ size)
    (ha : a + 48 ≤ size) (hb : b + 48 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hc : c < 2 ^ 16) (hd : d < 2 ^ 16)
    (hA : wordsVal s.mem base a 6 < p384) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (lin o a b c d)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 =
        (c * wordsVal s.mem base a 6 + d * (p384 - wordsVal s.mem base b 6)) % p384 := by
  obtain kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ clobX) →
      ∀ r, r ∉ clobX → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  have hmo : Impl.P384.Ops.M.mo + 48 ≤ size := hM.mo
  have hm : wordsVal s.mem base Impl.P384.Ops.M.mo 6 = p384 := hM.val
  rw [lin, scaleB, List.cons_append, ← List.singleton_append]
  simp only [List.append_assoc]
  -- `x7 = 0`.
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  obtain hs₀ : Scr s₀ base size := hs.of_keeps k₀ (by decide)
  -- `p - [b]`.
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok qRegs hs₀ (a := Impl.P384.Ops.M.mo) hmo (by decide) ⟨by decide, by decide⟩)
    fun s₁ ⟨e₁, k₁, _⟩ => ?_
  obtain hs₁ : Scr s₁ base size := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSubs_ok hs₁ (t := .x8) (ts := [.x9, .x10, .x11, .x12, .x13]) (b := b) hb hb8
    ⟨by decide, by decide⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  obtain hs₂ : Scr s₂ base size := hs₁.of_keeps k₂ (by decide)
  obtain hQ : regsVal s₂ qRegs = p384 - wordsVal s.mem base b 6 := by
    obtain m₁ : s₁.mem = s.mem := by rw [k₁.mem, k₀.mem]
    obtain r₁ : regsVal s₁ qRegs = p384 := by
      change regsVal s₁ qRegs = wordsVal s₀.mem base Impl.P384.Ops.M.mo 6 at e₁
      rw [e₁, k₀.mem]; exact hm
    change regsVal s₂ qRegs + wordsVal s₁.mem base b 6 = regsVal s₁ qRegs + 2 ^ 384 * _ at e₂
    rw [m₁, r₁] at e₂
    obtain hl : regsVal s₂ qRegs < 2 ^ 384 := regsVal_lt s₂ qRegs
    obtain hb := Bool.toNat_le (!s₂.c)
    omega_using [e₂, hl, hb, hB]
  -- `d (p - [b])`.
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₂ hd) fun s₃ ⟨d₃, z₃', k₃⟩ => ?_
  obtain hs₃ : Scr s₃ base size := hs₂.of_keeps k₃ (by decide)
  obtain z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), z₀]
  rw [WP.block_append_iff]
  refine WP.mono (rowInit_ok hs₃.ptr z₃ (by decide) (by decide) (ts := rRegs) (bs := qRegs) (x := .x17) rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun t ht => by simp only [rRegs, qRegs, List.length_cons, List.length_nil, List.drop_succ_cons,
      List.drop_zero, List.mem_singleton] at ht; subst ht; exact z₃')) fun s₄ ⟨e₄, k₄⟩ => ?_
  obtain hQ₃ : regsVal s₃ qRegs = regsVal s₂ qRegs := regsVal_congr fun r hr => k₃.gpr r (by revert r; decide)
  rw [hQ₃, hQ, d₃] at e₄
  obtain hs₄ : Scr s₄ base size := hs₃.of_keeps k₄ (by decide)
  obtain z₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by decide), z₃]
  obtain hm₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem, k₀.mem]
  -- `+ c [a]`.
  rw [addA, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok s₄ hc) fun s₅ ⟨c₅, k₅⟩ => ?_
  obtain hs₅ : Scr s₅ base size := hs₄.of_keeps k₅ (by decide)
  obtain z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  obtain hR₅ : regsVal s₅ rRegs = regsVal s₄ rRegs := regsVal_congr fun r hr => k₅.gpr r (by revert r; decide)
  obtain hw : rwVal s₅ base (mWords a 0 6) = wordsVal s.mem base a 6 := by
    rw [rwVal_mWords, Nat.mul_zero, Nat.add_zero, k₅.mem, hm₄]
  obtain hV : regsVal s₅ rRegs + (s₅.gpr .x17).toNat * rwVal s₅ base (mWords a 0 6) =
      d * (p384 - wordsVal s.mem base b 6) + c * wordsVal s.mem base a 6 := by
    rw [hR₅, e₄, c₅, hw]
  obtain hVlt : d * (p384 - wordsVal s.mem base b 6) + c * wordsVal s.mem base a 6 < 2 ^ 17 * 2 ^ 384 := by
    obtain h1 := Nat.mul_le_mul_left d (Nat.sub_le p384 (wordsVal s.mem base b 6))
    obtain h2 := Nat.mul_le_mul_left c (Nat.le_of_lt hA)
    obtain hp : p384 < 2 ^ 384 := by decide
    obtain h3 := Nat.mul_le_mul_right p384 (Nat.le_of_lt hd)
    obtain h4 := Nat.mul_le_mul_right p384 (Nat.le_of_lt hc)
    omega_arith
  obtain hok : RowOk size .x17 rRegs (mWords a 0 6) := {
    nodup := by decide
    regs := by decide
    ok := by
      simp only [mWords, List.mem_cons, List.not_mem_nil, or_false]
      rintro w (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by omega_arith, by omega_arith⟩
    reads := by
      simp only [mWords, List.mem_cons, List.not_mem_nil, or_false]
      rintro w (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [RWord.reads, Src.reads]
    x2 := by decide
    x3 := by decide }
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs₅.ptr z₅ hok (by decide) (by decide) (by decide)
    (by simp only [mWords, rRegs, List.length_cons, List.length_nil]; omega_arith)
    (by rw [hV]; change _ < 2 ^ 448; omega_arith)) fun s₆ ⟨e₆, k₆⟩ => ?_
  rw [hV] at e₆
  obtain hs₆ : Scr s₆ base size := hs₅.of_keeps k₆ (by decide)
  obtain z₆ : s₆.gpr .x7 = 0 := by rw [k₆.gpr _ (by decide), z₅]
  obtain hm₆ : s₆.mem = s.mem := by rw [k₆.mem, k₅.mem, hm₄]
  -- The fold.
  obtain hsplit : regsVal s₆ rRegs = regsVal s₆ lowRegs + 2 ^ 384 * (s₆.gpr .x16).toNat := by
    rw [show rRegs = lowRegs ++ [.x16] from rfl, regsVal_append]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rfl
  obtain hLlt : regsVal s₆ lowRegs < 2 ^ 384 := regsVal_lt s₆ lowRegs
  obtain hT : (s₆.gpr .x16).toNat + 1 < 2 ^ 32 := by
    have h := hVlt
    rw [← e₆, hsplit] at h
    have : 2 ^ 384 * (s₆.gpr .x16).toNat < 2 ^ 384 * 2 ^ 17 := by omega_arith
    have := Nat.lt_of_mul_lt_mul_left this
    omega_arith
  rw [fold, List.append_assoc, WP.block_append_iff]
  refine WP.mono (foldPre_ok s₆ z₆ hT) fun s₇ ⟨q₇, w₇, k₇⟩ => ?_
  rw [WP.block_append_iff, show lowRegs = .x1 :: [.x4, .x5, .x6, .x14, .x15] from rfl]
  refine WP.mono (addsIn_ok s₇ (t := .x1) (ts := [.x4, .x5, .x6, .x14, .x15]) (h := .x2)
    (hs := [.x3, .x16, .x7, .x7, .x7]) rfl (by decide) (by decide)) fun s₈ ⟨e₈, k₈⟩ => ?_
  obtain z₇ : s₇.gpr .x7 = 0 := by rw [k₇.gpr _ (by decide), z₆]
  obtain hL₇ : regsVal s₇ [.x1, .x4, .x5, .x6, .x14, .x15] = regsVal s₆ lowRegs :=
    regsVal_congr fun r hr => k₇.gpr r (by revert r; decide)
  rw [hL₇, regsVal_fold z₇] at e₈
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₈
  -- The correction.
  obtain z₈ : s₈.gpr .x7 = 0 := by rw [k₈.gpr _ (by decide), z₇]
  rw [correct, List.append_assoc, WP.block_append_iff]
  refine WP.mono (correctPre_ok s₈ z₈) fun s₉ ⟨w₉, k₉⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addsIn_ok s₉ (t := .x1) (ts := [.x4, .x5, .x6, .x14, .x15]) (h := .x2)
    (hs := [.x3, .x16, .x17, .x17, .x17]) rfl (by decide) (by decide)) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  obtain hL₉ : regsVal s₉ [.x1, .x4, .x5, .x6, .x14, .x15] = regsVal s₈ [.x1, .x4, .x5, .x6, .x14, .x15] :=
    regsVal_congr fun r hr => k₉.gpr r (by revert r; decide)
  rw [hL₉, w₉] at e₁₀
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁₀
  -- The store.
  obtain hs₁₀ : Scr s₁₀ base size :=
    ((((hs₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)).of_keeps k₉ (by decide)).of_keeps k₁₀ (by decide))
  refine WP.mono (stores_ok lowRegs hs₁₀ (o := o) ho ho8 (by decide)) fun t ⟨et, kt, Ot⟩ => ?_
  obtain hm₁₀ : s₁₀.mem = s.mem := by rw [k₁₀.mem, k₉.mem, k₈.mem, k₇.mem, hm₆]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx _ => by rw [Ot x hx, hm₁₀]⟩, ?_⟩
  · rw [kt.gpr r (by simp), kw k₁₀ (by decide) r hr, kw k₉ (by decide) r hr, kw k₈ (by decide) r hr,
      kw k₇ (by decide) r hr, kw k₆ (by decide) r hr, kw k₅ (by decide) r hr, kw k₄ (by decide) r hr,
      kw k₃ (by decide) r hr, kw k₂ (by decide) r hr, kw k₁ (by decide) r hr, kw k₀ (by decide) r hr]
  · rw [kt.rd, k₁₀.rd, k₉.rd, k₈.rd, k₇.rd, k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd, k₀.rd]
  · rw [kt.wr, k₁₀.wr, k₉.wr, k₈.wr, k₇.wr, k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr, k₀.wr]
  · rw [kt.sp, k₁₀.sp, k₉.sp, k₈.sp, k₇.sp, k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₂.sp, k₁.sp, k₀.sp]
  · have et' : wordsVal t.mem base o 6 = regsVal s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15] := et
    rw [et']
    obtain h0 := regsVal_lt s₈ [.x1, .x4, .x5, .x6, .x14, .x15]
    obtain h1 := regsVal_lt s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15]
    refine reduce_arith (T := (s₆.gpr .x16).toNat) (c₁ := s₈.c.toNat) (c₂ := s₁₀.c.toNat)
      (L₁ := regsVal s₈ [.x1, .x4, .x5, .x6, .x14, .x15]) (L₂ := regsVal s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15]) (by rw [Nat.add_comm, ← e₆, hsplit]) hLlt hT h0
      (Bool.toNat_le _) (by rw [q₇] at e₈; omega_using [e₈, w₇]) h1 (Bool.toNat_le _) ?_
    rw [e₁₀]
    cases s₈.c <;> rfl

section
variable {m : Nat} [NeZero m] {R : Nat}

theorem toM_mod' (x : Nat) : toM m R (x % m) = toM m R x := by
  unfold toM; rw [ofNat_mod]

theorem toM_scale (c x : Nat) : toM m R (c * x) = Fin.ofNat m c * toM m R x := by
  unfold toM
  rw [ofNat_mul']
  grind

/-- A slot holding `(c a + d (m - b)) mod m` stands for `c A - d B`. -/
theorem toM_lin (a b c d : Nat) (hb : b < m) :
    toM m R ((c * a + d * (m - b)) % m) = Fin.ofNat m c * toM m R a - Fin.ofNat m d * toM m R b := by
  rw [toM_add, toM_scale, toM_scale]
  obtain h : toM m R (m - b) = -toM m R b := by
    obtain hh := toM_sub (m := m) (R := R) (A := 0) (B := b) (by omega_arith)
    simp only [Nat.zero_add, toM_mod', toM_zero] at hh
    grind
  rw [h]
  grind

end

/-- `Linear.lin` on the window's slots: `o` comes to stand for `c E_a - d E_b`. -/
theorem linOp_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop}
    (hL : Lay Impl.P384.Ops.M size Sl) (hAl : Aligned Impl.P384.Ops.M Sl) {base : Addr} {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv Impl.P384.Ops.M base size m Sl V E s) {o a b c d : Nat}
    (ho : Sl o) (ha : a ∈ V) (hb : b ∈ V) (hc : c < 2 ^ 16) (hd : d < 2 ^ 16) :
    WP isa (.block (lin o a b c d)) s fun t => OpKeepX base o s t ∧
      Inv Impl.P384.Ops.M base size m Sl (o :: V)
        (Function.update E o (Fin.ofNat m c * E a - Fin.ofNat m d * E b)) t := by
  subst hmp
  have hn := VG.Proof.P384.Ops.M_n
  obtain hla := hL.le a (hI.sl a ha)
  obtain hlb := hL.le b (hI.sl b hb)
  obtain hlo := hL.le o ho
  rw [hn] at hla hlb hlo
  obtain hA := hI.lt a ha
  obtain hB := hI.lt b hb
  rw [hn] at hA hB
  refine WP.mono (lin_ok hI.scr hI.mod hlo hla hlb (hAl.sl o ho) (hAl.sl a (hI.sl a ha))
    (hAl.sl b (hI.sl b hb)) hc hd hA hB) fun t ⟨hk, hv⟩ => ⟨hk, VG.Proof.P384.Ops.Inv.updateX hL hI ho hk ?_ ?_⟩
  · rw [hn, hv]; exact Nat.mod_lt _ (by decide)
  · rw [hn, hv, toM_lin _ _ _ _ hB]
    obtain va := hI.val a ha
    obtain vb := hI.val b hb
    rw [hn] at va vb
    rw [va, vb]

end VG.Proof.P384.Linear

end

end

/-! ### `P384.EcdhDouble.Vals`, which only this module used -/

section

/-!
# The values of P-384's raw doubling

`raw_vals`: the field operations of the raw doubling (`Impl/P384/EcdhDouble.lean`,
s2n-bignum's order, with its three linear combinations) leave in `b` the
window's Jacobian doubling of `a` (`dblJF`), by `values_eq`.
-/

@[expose] public section

namespace VG.Proof.P384.EcdhDouble
open VG VG.Impl.Weierstrass VG.Impl.P384.EcdhDouble VG.Proof.Weierstrass

/-- The environment after the raw doubling's operations and combinations. -/
def rawEnv {m : Nat} [NeZero m] (a b : Pt) (E : Nat → Fin m) : Nat → Fin m :=
  let e₁ := runOps (ops1 a b) E
  let e₂ := Function.update e₁ b.y (Fin.ofNat m 12 * e₁ K.S.t3 - Fin.ofNat m 9 * e₁ b.y)
  let e₃ := runOps (ops2 b) e₂
  let e₄ := Function.update e₃ b.x (Fin.ofNat m 4 * e₃ K.S.t3 - Fin.ofNat m 1 * e₃ b.y)
  Function.update e₄ b.y (Fin.ofNat m 3 * e₄ K.S.t1 - Fin.ofNat m 8 * e₄ K.S.t0)

set_option linter.unusedSimpArgs false in
theorem raw_vals {m : Nat} [NeZero m] (E : Nat → Fin m) {a b : Pt}
    (hd : [a.x, a.y, a.z, b.x, b.y, b.z, K.S.t0, K.S.t1, K.S.t2, K.S.t3].Nodup) :
    (rawEnv a b E b.x, rawEnv a b E b.y, rawEnv a b E b.z) = dblJF (E a.x) (E a.y) (E a.z) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08, h09⟩, ⟨h12, h13, h14, h15, h16, h17, h18, h19⟩,
    ⟨h23, h24, h25, h26, h27, h28, h29⟩, ⟨h34, h35, h36, h37, h38, h39⟩, ⟨h45, h46, h47, h48, h49⟩,
    ⟨h56, h57, h58, h59⟩, ⟨h67, h68, h69⟩, ⟨h78, h79⟩, h89, -⟩ := hd
  rw [← VG.Proof.P256.EcdhDouble.values_eq]
  simp only [rawEnv, ops1, ops2, runOps, List.foldl, FOp.run, Function.update_apply, VG.Proof.P256.EcdhDouble.values,
    h01, h02, h03, h04, h05, h06, h07, h08, h09, h12, h13, h14, h15, h16, h17, h18, h19,
    h23, h24, h25, h26, h27, h28, h29, h34, h35, h36, h37, h38, h39, h45, h46, h47, h48, h49,
    h56, h57, h58, h59, h67, h68, h69, h78, h79, h89, Ne.symm h01, Ne.symm h02, Ne.symm h03,
    Ne.symm h04, Ne.symm h05, Ne.symm h06, Ne.symm h07, Ne.symm h08, Ne.symm h09, Ne.symm h12,
    Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17, Ne.symm h18, Ne.symm h19,
    Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27, Ne.symm h28, Ne.symm h29,
    Ne.symm h34, Ne.symm h35, Ne.symm h36, Ne.symm h37, Ne.symm h38, Ne.symm h39, Ne.symm h45,
    Ne.symm h46, Ne.symm h47, Ne.symm h48, Ne.symm h49, Ne.symm h56, Ne.symm h57, Ne.symm h58,
    Ne.symm h59, Ne.symm h67, Ne.symm h68, Ne.symm h69, Ne.symm h78, Ne.symm h79, Ne.symm h89,
    ↓reduceIte, Prod.mk.injEq]
  have h1 : Fin.ofNat m 1 = 1 := rfl
  have h3 : Fin.ofNat m 3 = 3 := rfl
  have h4 : Fin.ofNat m 4 = 4 := rfl
  have h8 : Fin.ofNat m 8 = 8 := rfl
  have h9 : Fin.ofNat m 9 = 9 := rfl
  have h12 : Fin.ofNat m 12 = 12 := rfl
  simp only [h1, h3, h4, h8, h9, h12]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end VG.Proof.P384.EcdhDouble

end

end


/-!
# P-384's raw doubling

`raw_ok`: the raw doubling (`Impl/P384/EcdhDouble.lean`) from `p` into `o`
leaves in `o` the window's Jacobian doubling of `p` (`raw_vals`), changing
only the registers `clobX` and the slots `rcbW` and `tmp`. Its field
operations are `fprog_ok`'s, its linear combinations `linOp_ok`'s. The
conditions on its slots (`RawSlots`) are decided for each direction.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX OpKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

theorem _root_.VG.Proof.P384.Ops.ProgKeepX.ofOp {base : Addr} {o : Nat} {s t : State} (h : OpKeepX base o s t) :
    ProgKeepX base [o] s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (hx o (List.mem_singleton_self _)) ht⟩

theorem _root_.VG.Proof.P384.Ops.ProgKeepX.trans {base : Addr} {W W' : List Nat} {s t u : State} (h : ProgKeepX base W s t)
    (h' : ProgKeepX base W' t u) : ProgKeepX base (W ++ W') s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun x hx ht => (h'.mem x (fun w hw => hx w (List.mem_append_right _ hw)) ht).trans
      (h.mem x (fun w hw => hx w (List.mem_append_left _ hw)) ht)⟩

/-- What the raw doubling from `p` into `o` needs of its slots, decided for each direction. -/
structure RawSlots (p o : Pt) : Prop where
  nodup : [p.x, p.y, p.z, o.x, o.y, o.z, K.S.t0, K.S.t1, K.S.t2, K.S.t3].Nodup
  sl1 : ∀ op ∈ ops1 p o, ∀ x ∈ op.out :: op.ins, x ∈ winSlots K
  sl2 : ∀ op ∈ ops2 o, ∀ x ∈ op.out :: op.ins, x ∈ winSlots K
  out : ∀ x ∈ [o.x, o.y, o.z], x ∈ winSlots K
  rd1 : readsOk (ops1 p o) [p.x, p.y, p.z] = true
  rd2 : readsOk (ops2 o) [K.S.t0, K.S.t1, K.S.t2, K.S.t3, o.x, o.y, o.z] = true
  wr1 : ∀ x ∈ [K.S.t0, K.S.t1, K.S.t2, K.S.t3, o.x, o.y, o.z], x ∈ (ops1 p o).map FOp.out
  w1 : ∀ op ∈ ops1 p o, op.out ∈ rcbW K.S o
  w2 : ∀ op ∈ ops2 o, op.out ∈ rcbW K.S o
  other : ∀ x ∈ rcbW K.S o, x ∈ winOther K

theorem rawSlots_RD : RawSlots K.R K.D := ⟨by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

theorem rawSlots_DR : RawSlots K.D K.R := ⟨by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

/-- The raw doubling from `p` into `o`. -/
theorem raw_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hS : RawSlots p o)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V) :
    WP isa (.block (raw p o)) s fun s' => KeepRegs clobX s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = dblJF (E p.x) (E p.y) (E p.z) := by
  obtain mv : ∀ {ops : List FOp} {W : List Nat} {x : Nat}, x ∈ ops.map FOp.out → x ∈ validAfter ops W :=
    fun h => (mem_validAfter _ _).mpr (Or.inr h)
  obtain mw : ∀ {ops : List FOp} {W : List Nat} {x : Nat}, x ∈ W → x ∈ validAfter ops W :=
    fun h => (mem_validAfter _ _).mpr (Or.inl h)
  obtain w1 := fun x hx => mv (W := V) (hS.wr1 x hx)
  rw [raw, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- The operations before `d`.
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp (ops1 p o) hI hS.sl1 (readsOk_mono hS.rd1 hV))
    fun s₁ ⟨k₁, I₁⟩ => ?_
  -- `d = 12 x y² - 9 m²`.
  rw [WP.block_append_iff]
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₁ (hS.out _ (by simp)) (w1 _ (by simp))
    (w1 _ (by simp)) (by decide) (by decide)) fun s₂ ⟨k₂, I₂⟩ => ?_
  -- The operations after `d`.
  rw [WP.block_append_iff]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp (ops2 o) I₂ hS.sl2
    (readsOk_mono hS.rd2 fun x hx => List.mem_cons_of_mem _ (w1 x hx))) fun s₃ ⟨k₃, I₃⟩ => ?_
  -- `x' = 4 x y² - d` and `y' = 3 d m - 8 y⁴`.
  obtain w3 : ∀ x ∈ [K.S.t0, K.S.t1, K.S.t3, o.y], x ∈ validAfter (ops2 o)
      (o.y :: validAfter (ops1 p o) V) := by
    intro x hx
    refine mw (List.mem_cons_of_mem _ (w1 x ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  rw [WP.block_append_iff]
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₃ (hS.out _ (by simp)) (w3 _ (by simp))
    (w3 _ (by simp)) (by decide) (by decide)) fun s₄ ⟨k₄, I₄⟩ => ?_
  refine WP.mono (Linear.linOp_ok hC hL.lay hA.al I₄ (hS.out _ (by simp))
    (List.mem_cons_of_mem _ (w3 _ (by simp))) (List.mem_cons_of_mem _ (w3 _ (by simp)))
    (by decide) (by decide)) fun s₅ ⟨k₅, I₅⟩ => ?_
  -- The frame.
  obtain k := ((((k₁.trans (ProgKeepX.ofOp k₂)).trans k₃).trans (ProgKeepX.ofOp k₄)).trans (ProgKeepX.ofOp k₅))
  obtain hw : ∀ w ∈ (ops1 p o).map FOp.out ++ [o.y] ++ (ops2 o).map FOp.out ++ [o.x] ++ [o.y],
      w ∈ rcbW K.S o := by
    intro w hw
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with (((⟨op, hop, rfl⟩ | rfl) | ⟨op, hop, rfl⟩) | rfl) | rfl
    · exact hS.w1 op hop
    · simp [rcbW]
    · exact hS.w2 op hop
    · simp [rcbW]
    · simp [rcbW]
  refine ⟨⟨k.gpr, k.rd, k.wr, k.sp⟩, (ProgKeepX.mono (W' := rcbW K.S o) k hw).unch.mono fun w hw => ?_,
    rawEnv p o E, I₅.sub fun x hx => ?_, fun x hx => ?_, raw_vals E hS.nodup⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, hS.other y hy, rfl⟩
    · exact Or.inr rfl
  · rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mw (List.mem_cons_of_mem _ (w1 _ (by simp)))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mw (List.mem_cons_of_mem _ (mw hx))))
  · have hy : x ≠ o.y := fun h => hx (h ▸ by simp [rcbW])
    obtain hx' : x ≠ o.x := fun h => hx (h ▸ by simp [rcbW])
    simp only [rawEnv, Function.update_of_ne hy, Function.update_of_ne hx']
    rw [runOps_of_not_out _ _ fun op hop h => hx (by rw [← h]; exact hS.w2 op hop), Function.update_of_ne hy,
      runOps_of_not_out _ _ fun op hop h => hx (by rw [← h]; exact hS.w1 op hop)]

end VG.Proof.P384.EcdhDouble

end

end


/-!
# P-384's allocated doublings

`doubleRD_ok` and `doubleDR_ok`: the allocated doublings
(`Impl/P384/EcdhAllocatedCode.lean`) do what the raw ones do (`raw_ok`), as
their certificates (`Certificate.lean`) let the raw blocks' results stand for
theirs on every slot but the spills, which hold nothing the window reads.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

theorem wordsVal_of_words {m m' : Mem} {base : Addr} :
    ∀ {x k : Nat}, (∀ i < k, word m' base (x + 8 * i) = word m base (x + 8 * i)) →
      wordsVal m' base x k = wordsVal m base x k
  | _, 0, _ => rfl
  | x, k + 1, h => by
    simp only [wordsVal]
    obtain h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    obtain hk := wordsVal_of_words (m := m) (m' := m') (base := base) (x := x + 8) (k := k) fun i hi => by
      have := h (i + 1) (by omega_using [hi])
      rwa [show x + 8 * (i + 1) = x + 8 + 8 * i by omega_using []] at this
    rw [h0, hk]

theorem regs_clobX : ∀ r ∈ regs, r ∈ clobX := by decide

/-- What the window's doublings conclude, as `raw_ok` states it. -/
def DblPost (C : Curve) (base : Addr) (size : Nat) (p o : Pt) (V : List Nat) (E : Nat → Fe C)
    (s s' : State) : Prop :=
  KeepRegs clobX s s' ∧ Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
    (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
    (E' o.x, E' o.y, E' o.z) = dblJF (E p.x) (E p.y) (E p.z)

/-- An allocated block refining the raw doubling, which writes only within
the window's loop slots and agrees with it on the slots the result is read
from, concludes what the raw one does. -/
theorem alloc_ok {C : Curve} (hC : C.p = p384) {base : Addr} (hL : WinLay K 8192)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hS : RawSlots p o)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base 8192 C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V)
    {c : List Instr} {Wk : List (Nat × Nat)}
    (hR : ∀ {Q : State → Prop}, WP isa (.block (raw p o)) s Q → WP isa (.block c) s fun t => ∃ u, Q u ∧
      (∀ off, Certificate.observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base Wk s t)
    (hWk : ∀ w ∈ Wk, ∃ w' ∈ loopW K, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hobs : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), ∀ i < 6, Certificate.observe (x + 8 * i)) :
    WP isa (.block c) s fun t => DblPost C base 8192 p o V E s t := by
  refine WP.mono (hR (raw_ok hC hL hA hp hS hI hV)) fun t ⟨u, ⟨_, _, E', Iu, hE, hv⟩, hw, F⟩ => ?_
  obtain hs : Scr t base 8192 := F.scr (by decide) hI.scr
  obtain hwv : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), x + 48 ≤ 8192 →
      wordsVal t.mem base x 6 = wordsVal u.mem base x 6 := fun x hx hx8 =>
    wordsVal_of_words fun i hi => hw _ (hobs x hx i hi) (by
      have : x % 8 = 0 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · decide
        · exact hA.al.sl x (Iu.sl x hx)
      omega_using [this]) (by omega_using [hx8, hi])
  refine ⟨F.regs.mono regs_clobX, F.unch.cover hWk, E', ⟨hs, ?_, Iu.sl, fun x hx => ?_, fun x hx => ?_⟩, hE, hv⟩
  · have hmo := Iu.mod
    exact ⟨hmo.n0, hmo.n10, hmo.mo, hmo.tmp, hmo.sep,
      by rw [show K.M.n = 6 from rfl, hwv _ (List.mem_cons_self ..) (by decide)]; exact hmo.val,
      hmo.inv, hmo.red, hmo.call⟩
  · rw [show K.M.n = 6 from rfl, hwv x (List.mem_cons_of_mem _ hx) (hL.lay.le x (Iu.sl x hx))]
    exact Iu.lt x hx
  · rw [show K.M.n = 6 from rfl, hwv x (List.mem_cons_of_mem _ hx) (hL.lay.le x (Iu.sl x hx))]
    exact Iu.val x hx

/-- The window's spec of a doubling, from `alloc_ok`. -/
theorem dblSpec_of_alloc {C : Curve} (hC : C.p = p384) {base : Addr} (hL : WinLay K 8192)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt}
    (hS : RawSlots p o) {V : List Nat} (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V) {c : List Instr} {Wk : List (Nat × Nat)}
    (hR : ∀ {s : State}, Scr s base 8192 → ∀ {Q : State → Prop}, WP isa (.block (raw p o)) s Q →
      WP isa (.block c) s fun t => ∃ u, Q u ∧
      (∀ off, Certificate.observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base Wk s t)
    (hWk : ∀ w ∈ Wk, ∃ w' ∈ loopW K, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hobs : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), ∀ i < 6, Certificate.observe (x + 8 * i)) :
    DblSpec K C base 8192 (.block c) p o V := by
  intro E s hI
  obtain hv : dblJF (E p.x) (E p.y) (E p.z) =
      (runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 6,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 7,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 8) := by
    rw [dblJChoiceN_run]
    rfl
  exact WP.mono (alloc_ok hC hL hA hp hS hI hV (hR hI.scr) hWk hobs)
    fun t ⟨k, U, E', I, _, v⟩ => ⟨k.mono fun r h => by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h, U, E', I, v.trans hv⟩

theorem p384_C_p : Impl.Ecdsa.AArch64.p384.C.p = p384 := by decide

/-- P-384's allocated doublings do what the window's doublings must. -/
theorem dblsOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) :
    DblsOk K C base 8192
      (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR)) := by
  intro d hd
  cases hd
  refine ⟨dblSpec_of_alloc hC hL hA hp rawSlots_RD (by decide)
    (fun hs _ hq => Certificate.refineRD hs hq) (by decide) (by decide), ?_⟩
  exact dblSpec_of_alloc hC hL hA hp rawSlots_DR (by decide)
    (fun hs _ hq => Certificate.refineDR hs hq) (by decide) (by decide)

end VG.Proof.P384.EcdhDouble

end

end

/-!
# P-384's comb arithmetic on AArch64

`compiler_on`: a straight line of `Ops.op` (`Impl/P384/CombArithmetic.lean`)
computes a field program's values for P-384's modulus, as `fprogB` does
(`Ops.fprog_ok`), changing `x21`–`x25` besides `clob 6`.
-/

@[expose] public section

namespace VG.Proof.P384.CombArithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.P384.CombArithmetic
open VG.Proof.Weierstrass.AArch64

theorem compiler_on (size : Nat) :
    FieldCompilerOn Impl.P384.Ops.M Spec.P384.curve [.x21, .x22, .x23, .x24, .x25] program size := by
  intro base Sl hL hAl hm ops V E s hI hS _ hV
  exact WP.mono (Ops.fprog_ok P384.EcdhDouble.p384_C_p hL hAl hm ops hI hS hV)
    fun _ ⟨k, I⟩ => ⟨⟨k.gpr, k.rd, k.wr, k.sp, k.mem⟩, I⟩

end VG.Proof.P384.CombArithmetic

end

end

/-!
# ECDSA over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), so `sign_ok` gives
the contract's postcondition; `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P384

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384_nBits : 64 * p384.n ≤ Spec.Ecdsa.nBits p384.C := by
  show 384 ≤ Spec.P384.curve.n.log2 + 1
  have : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega_using [this]

theorem p384_ok (hI : Weierstrass.AArch64.InvSounds) : CfgOk p384 where
  window_tmp := by decide +kernel
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  n2 := by decide
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by have := p384_nBits; have : p384.n = 6 := rfl; have : p384.C.len = 48 := rfl; unfold Cfg.sh; omega_arith
  n4 := by decide
  sound_p := hI (by
    show Nat.Prime Spec.P384.curve.p
    rw [show Spec.P384.curve.p =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
      by decide +kernel]
    exact Proof.P384.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.P384.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  am3 := by unfold AM3; decide +kernel
  call_p := fun _ _ h => by
    have e : (Mont.callOf p384.MP').map Prod.snd = some p384.C.p := by decide +kernel
    obtain rfl : _ = _ := Option.some.inj (e.symm.trans (congrArg (Option.map Prod.snd) h))
    exact ⟨rfl, Mont.p384p_ok⟩
  call_n := fun _ _ h => by
    have e : (Mont.callOf p384.MN').map Prod.snd = some p384.C.n := by decide +kernel
    obtain rfl : _ = _ := Option.some.inj (e.symm.trans (congrArg (Option.map Prod.snd) h))
    exact ⟨rfl, Mont.p384n_ok⟩
  inv_at := .inr (by decide +kernel)
  inv_fn := fun _ => ⟨by decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩
  padd := fun h => absurd rfl h
  check_fn := fun _ => ⟨by lit_decide, by lit_decide, by lit_decide⟩

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

/-- The pipelined comb gives what the signing's stages need. -/
theorem comb_ok (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombCorrect p384 Impl.P384.CombArithmetic.comb :=
  combJP2_correct (p384_ok hI) hL hT (Proof.P384.CombArithmetic.compiler_on _) (by decide) (by decide)
    (by decide) (Proof.P384.booth hL rfl rfl) (by decide +kernel) rfl jp2_checks

theorem sign_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have hn : CallsKeep signP384 := by lit_decide
  have hu : KeepsUntouched signP384 := by lit_decide
  have hv : signP384.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ :=
    signWith_ok (p384_ok hI).toBaseCfgOk hL _ (comb_ok hL hI hT) (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signP384 :=
  VG.Taint.constantTime (A := taintS [p384.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ecdsa.AArch64.P384
