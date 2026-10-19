module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lit
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.Ecdsa.P256
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombSat
public import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombSat
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
meta import VerifiedGarbage.Proof.Ecdsa.X86.Setup
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86.Csub
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.P256.Order
meta import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.Weierstrass.InvToM
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
meta import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
meta import VerifiedGarbage.Proof.Weierstrass.X86.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
meta import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
meta import VerifiedGarbage.Proof.Weierstrass.X86.Rep
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
meta import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.CombSat
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold

/-!
# Deterministic ECDSA on x86 (32-bit): P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes). Its seven-bit comb reads the same immutable
table as public-key generation and verification, using four bytes of stack
for position-independent addressing, within the 20 its calls use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

open VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

private theorem core_pre_256 {s : State} (h : (coreK p256Comb).pre s) : CombSignPre p256Comb s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, ds, gs, ks,
    ht⟩ := h
  exact ⟨⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩, ht, ds, gs, ks⟩

private theorem core_pub_256 {s t : State} (h : (coreK p256Comb).pub s t) : CombSignPub s t := by
  obtain ⟨he, a0, a1, a2, a3, a4, sy⟩ := h
  refine ⟨he, ?_, sy ("VG_P256_COMB", p256W) (by rw [p256Comb_consts]; simp)⟩
  intro j hj
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := p256Comb
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := signP256Comb
  coreX := by
    intro s h
    have co : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
      intro d hd
      have he : p256d = d := Option.some.inj hd
      rw [← he]; exact p256Comb_shape
    obtain ⟨tr, t, he, ha, hp⟩ := signComb_ok (p256Comb_ok hI) hL (p256Comb_tables hL) co p256Comb_am3 rfl signComb_spG
      signComb_spTail (core_pre_256 h)
    refine ⟨tr, t, he, ha, ?_⟩
    simp only [coreK, coreSigOf, SignPost, ptr, BitVec.setWidth_append_eq_right] at hp ⊢
    generalize Spec.Ecdsa.signWith p256Comb.C
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) p256Comb.C.len))
      (Spec.Ecdsa.hashToInt p256Comb.C (Spec.Ecdsa.bytesAt s.mem ((arg s 2).setWidth 64) p256Comb.C.len))
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) p256Comb.C.len)) = r at hp ⊢
    cases r <;> exact hp
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    exact signComb_ct (p256Comb_ok hI) hL (p256Comb_tables hL) p256Comb_shape p256Comb_am3 signComb_spMul
      s t tr₁ tr₂ s' t' (core_pre_256 hs) (core_pre_256 ht) (core_pub_256 hp)
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.X86
