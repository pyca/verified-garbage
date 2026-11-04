module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Lit
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
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.Lit
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
meta import VerifiedGarbage.Proof.X25519.X86.Arith

/-!
# Deterministic ECDSA on x86 (32-bit): P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.X86.P521.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem core_pre_521 {s : State} (h : (coreK Impl.Ecdsa.X86.p521).pre s) :
    Proof.Ecdsa.X86.P521.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-! ## The blocks for each hash function's sizes -/

theorem p521_blk₀ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 16 64) := by rfcT_decide
theorem p521_blk₁ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 20 64) := by rfcT_decide
theorem p521_blk₂ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 28 64) := by rfcT_decide
theorem p521_blk₃ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 32 64) := by rfcT_decide
theorem p521_blk₄ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 48 128) := by rfcT_decide
theorem p521_blk₅ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 64 128) := by rfcT_decide
theorem p521_blk₆ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 28 128) := by rfcT_decide
theorem p521_blk₇ : RfcT (cfgS Impl.Ecdsa.X86.p521 false 7 32 128) := by rfcT_decide

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.X86.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.X86.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.X86.signP521
  coreX := fun s h => Proof.Ecdsa.X86.P521.sign_x86 hL s (core_pre_521 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.P521.sign_ct s t tr₁ tr₂ s' t' (core_pre_521 hs) (core_pre_521 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := nofun
  blkT := blkT_of p521_blk₀ p521_blk₁ p521_blk₂ p521_blk₃ p521_blk₄ p521_blk₅ p521_blk₆ p521_blk₇

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`. -/
theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve)
    (vs : List Proof.HashTable.X86.TVar) (h : OK vs) :
    Verified X86.target (signCode (p521 hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.X86.p521.combConsts vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.p521) h (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat


end VG.Proof.Ecdsa.Rfc6979.X86
