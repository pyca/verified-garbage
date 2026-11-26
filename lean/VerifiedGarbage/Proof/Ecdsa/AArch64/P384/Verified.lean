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
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombCall
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
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.CombCall
meta import VerifiedGarbage.Proof.P384.Prime
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.P384.CombArithmetic
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.P384.EcdhDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Impl.P384.CombArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
meta import VerifiedGarbage.Spec.P384
meta import VerifiedGarbage.Proof.P384.Ops
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Weierstrass.Jac
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
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by have := p384_nBits; have : p384.n = 6 := rfl; have : p384.C.len = 48 := rfl; unfold Cfg.sh; omega_arith
  n4 := by decide
  sound_p := hI (by
    show IsPrime Spec.P384.curve.p
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

/-- The pipelined comb, and so a call of `vg_p384_comb` (`combCorrect_call`), gives what the
signing's stages need. -/
theorem comb_ok (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombCorrect p384 Impl.P384.CombArithmetic.comb :=
  combCorrect_call (comb := Impl.P384.CombArithmetic.combBody)
    (combJP2_correct (p384_ok hI) hL hT (Proof.P384.CombArithmetic.compiler_on _) (by decide) (by decide)
      (by decide) (Proof.P384.booth hL rfl rfl) (by decide +kernel) rfl jp2_checks) (by lit_decide)

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
