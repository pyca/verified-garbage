module
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9

/-! # The recoding of both scalars of P-384's joint verification

`u`'s 385 digits of width nine, as words at `KG.bits`, past the window method's area of bits
(`winX`), where `v`'s digits of width five go. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

/-- The generator's digits: two bytes for each of `64 n + 1`. -/
def genW : List (Nat × Nat) := [(P384Joint.KG.bits, 770)]

theorem dimensions : P384Joint.K.M.n=6 ∧ P384Joint.KG.M.n=6 ∧ P384Joint.K.bits=2704 ∧
    P384Joint.KG.bits=3152 := by decide

theorem K_eq : P384Joint.K=winQ p384 := rfl

/-- The generator's digits miss the constants, the saved registers and every numbered slot. -/
theorem genW_fixed : FixedOk p384 genW := by unfold FixedOk; decide

theorem genW_apart : ∀ i ∈ List.range 45, ∀ w ∈ genW, p384.sl i + 48 ≤ w.1 ∨ w.1 + w.2 ≤ p384.sl i := by
  decide

/-- The generator's digits are past the window method's areas, which the peer's recoding writes. -/
theorem genW_winX : ∀ w ∈ winX p384, P384Joint.KG.bits + 770 ≤ w.1 ∨ w.1 + w.2 ≤ P384Joint.KG.bits := by
  decide

theorem prepare_ok (hc : CfgOk p384) (hC : Law p384.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed p384 base g s.mem) {P : Point p384.C}
    (hpx : sv p384 base s PX < p384.C.p) (hpy : sv p384 base s PY < p384.C.p)
    (hrep : Rep p384.C (tmv p384.C p384.n base s (p384.sl PX)) (tmv p384.C p384.n base s (p384.sl PY))
      (tmv p384.C p384.n base s (p384.sl ONEP)) P) :
    WP isa (.seq P384Joint.prep9 (PubNaf.prep (P384Joint.K) (p384.sl V))) s fun t =>
      Scr t base size ∧ ModOkA p384.MP' size p384.C.p t.mem base ∧
      PubNaf.NafFixed (P384Joint.K) p384.C base t P (sv p384 base s V) ∧
      (∀ x ∈ winRo (P384Joint.K), tmv p384.C p384.n base t x = tmv p384.C p384.n base s x) ∧
      t.sp = s.sp ∧ Unch base (genW ++ winX p384) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Fixed p384 base g t.mem ∧ tmv p384.C p384.n base t (P384Joint.K).P.z = 1 ∧
      (∀ j < 770, t.mem (off base (P384Joint.KG.bits + j)) = FastNaf.wbyte (sv p384 base s U) j) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  rw [K_eq,P384Joint.prep9]
  refine WP.seq (WP.mono (PubNafWide.prep9_ok P384Joint.KG (PubNaf.regs_ok9 6 (by decide) (by decide))
    hs (by decide) (by decide) (by decide) (by decide)) fun a ⟨pa, ka, oa⟩ => ?_)
  have Ua : Unch base genW s.mem a.mem := oa.unch
  have Fa := F.unch h7 hn genW_fixed Ua
  have e : ∀ {i}, i < 45 → sv p384 base a i = sv p384 base s i := fun {i} hi =>
    Ua.wordsVal (genW_apart i (List.mem_range.mpr hi)) (by have h := sl_le p384 h7 hi; omega)
  have tv : ∀ {i}, i < 45 → tmv p384.C p384.n base a (p384.sl i) = tmv p384.C p384.n base s (p384.sl i) :=
    fun hi => by show toM _ _ (sv p384 base a _) = toM _ _ (sv p384 base s _); rw [e hi]
  have hrep' : Rep p384.C (tmv p384.C p384.n base a (p384.sl PX)) (tmv p384.C p384.n base a (p384.sl PY))
      (tmv p384.C p384.n base a (p384.sl ONEP)) P := by
    rw [tv (by decide), tv (by decide), tv (by decide)]; exact hrep
  refine WP.mono (pubNafPrep_ok hc (by decide) hC pa.scr Fa
    (by rw [e (by decide)]; exact hpx) (by rw [e (by decide)]; exact hpy) hrep')
    fun t ⟨st, mt, nt, rt, spt, ut, rdt, wrt, ft, zt⟩ => ?_
  rw [e (by decide)] at nt
  refine ⟨st, mt, nt, ?_, spt.trans ka.sp, ?_, rdt.trans ka.rd, wrt.trans ka.wr, ft, zt, ?_⟩
  · intro x hx
    rw [rt x hx]
    simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [tv (i := AP) (by decide), tv (i := BM) (by decide), tv (i := ZERO) (by decide),
      tv (i := PX) (by decide), tv (i := PY) (by decide), tv (i := ONEP) (by decide)]
  · intro x hx
    rw [ut x (fun w hw => hx w (List.mem_append_right _ hw)),
      Ua x (fun w hw => hx w (List.mem_append_left _ hw))]
  · intro j hj
    rw [ut.byte (fun w hw => by have := genW_winX w hw; have hb : P384Joint.KG.bits = 3152 := rfl; omega) (by have := hs.nowrap; change 3152 + j < 2 ^ 64; omega)]
    exact pa.digits j (by have : P384Joint.KG.M.n = 6 := rfl; omega)

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
