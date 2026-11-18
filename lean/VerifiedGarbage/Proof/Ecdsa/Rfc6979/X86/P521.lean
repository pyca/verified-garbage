module

import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombCore
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Comb
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.Comb
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore

/-!
# Deterministic ECDSA on x86 (32-bit): P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign_k`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.X86.P521.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p521Comb
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := (Proof.Ecdsa.X86.Cfg.sh_withComb Impl.Ecdsa.X86.p521 Impl.Ecdsa.X86.p521d).trans Proof.Ecdsa.X86.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.X86.signP521Comb
  coreX := coreX_comb (Proof.Ecdsa.X86.P521.p521Comb_ok) hL (Proof.Ecdsa.X86.P521.p521Comb_tables hL) rfl Proof.Ecdsa.X86.P521.p521Comb_shape
    Proof.Ecdsa.X86.P521.signComb_sp
  coreCT := coreCT_comb (Proof.Ecdsa.X86.P521.p521Comb_ok) hL (Proof.Ecdsa.X86.P521.p521Comb_tables hL) rfl Proof.Ecdsa.X86.P521.p521Comb_shape
    (Proof.Ecdsa.X86.P521.p521Comb_gMul hL) Proof.Ecdsa.X86.P521.signCT Proof.Ecdsa.X86.P521.signComb_sp
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  blk := by rfcT_decide

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`. -/
theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) (vs : List Proof.HmacTable.X86.HVar) (h : OK vs ∧ "VG_P521_COMB" ∉ Proof.HmacTable.X86.names vs) :
    Verified X86.target (signCodeT (p521 hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86.p521Comb.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p521) h.1 (constMem 0x100000 Proof.Ecdsa.X86.P521.p521W) h.2
    (by rw [Proof.Ecdsa.X86.P521.p521W_length]; decide)
    (constMem_held 0x100000 Proof.Ecdsa.X86.P521.p521W (by rw [Proof.Ecdsa.X86.P521.p521W_length]; decide)) (by decide) rfl
  rw [show Impl.Ecdsa.X86.p521Comb.combConsts = [("VG_P521_COMB", Proof.Ecdsa.X86.P521.p521W)] from Proof.Ecdsa.X86.P521.p521Comb_consts]
  exact signT_verified (R := p521 hL) ⟨rfl, by decide, by decide⟩ rfl h.1
    (by rw [show (p521 hL).E.combConsts = [("VG_P521_COMB", Proof.Ecdsa.X86.P521.p521W)] from Proof.Ecdsa.X86.P521.p521Comb_consts]; exact hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
