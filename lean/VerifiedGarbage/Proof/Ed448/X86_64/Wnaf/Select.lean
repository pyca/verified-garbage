module

import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.ReadDigit
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectBase
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Sign
import VerifiedGarbage.Proof.Framework.Block

/-! Sparse signed-digit selection preserves the accumulator and curve constant. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448.X86_64.Window (SelKeeps KeyKeeps tablePoint)
open VG.Proof.X448.X86_64
open VG.Proof.Ed448 (pt)

def baseEntry (d : Int) : Spec.X448.Fe × Spec.X448.Fe :=
  let p := Impl.Ed448.SignedWindow.entry d.natAbs
  (if d < 0 then -p.1 else p.1, p.2)

theorem abs_lt {d : Int} (hd : -15 ≤ d ∧ d ≤ 15) : d.natAbs < 17 := by omega

theorem code_keep {base : Addr} {o t : Nat} {d : Int} {s u : State} (h : Keep base s u)
    (ho : 2048 ≤ o) (hb : o + t + 1 ≤ 8192) (hm : s.mem (off base (o + t)) = CodeByte d) :
    u.mem (off base (o + t)) = CodeByte d := by
  rw [h.mem _ (Or.inr (by rw [ofs_off' base (by omega)]; omega))]
  exact hm

theorem selectBase_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} {d : Int}
    (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (SDIG + t)) = CodeByte d) (hdigit : s.gpr .r15 = DigitWord d) :
    WP isa selectBase s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = baseEntry d ∧ SelKeeps (E s.mem base) (E u.mem base) := by
  rw [selectBase]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (magnitude_ok hd hdigit) fun a ⟨da, ka⟩ => ?_
  have ka' : Keep base s a := keeps_keep (ka.mono (by decide))
  refine WP.mono (baseCoords_ok (ka'.scr hs) (abs_lt hd) da) fun b ⟨kb, pb, fb⟩ => ?_
  have kab := ka'.trans kb
  refine WP.mono (negateSelected_ok (kab.scr hs) (by decide : 2048 ≤ SDIG)
    (by simp only [SDIG]; omega) hd ((kab.gpr _ (by decide)).trans hr)
    (code_keep kab (by decide) (by simp only [SDIG]; omega) hm)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kab.trans ku, ?_, ?_⟩
  · have px := congrArg Prod.fst pb
    have py := congrArg Prod.snd pb
    dsimp only at px py
    rw [xu, fu 9 (by decide) (by decide), px, py]
    rfl
  · intro j h3 h4 h8 h9
    rw [fu j h3 h8, fb j h3 h4 h8 h9, ka.2.1]

theorem selectKey_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} {d : Int}
    (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (KDIG + t)) = CodeByte d) (hdigit : s.gpr .r15 = DigitWord d) :
    WP isa selectKey s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = Proof.Ed448.SignedWindow.signedPoint (decide (d < 0))
        (tablePoint s.mem base d.natAbs) ∧ KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [selectKey]
  apply WP.seq
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (magnitude_ok hd hdigit) fun a ⟨da, ka⟩ => ?_
  have ka' : Keep base s a := keeps_keep (ka.mono (by decide))
  refine WP.mono (keyCoords_ok (ka'.scr hs) (abs_lt hd) da) fun b ⟨kb, pb, fb⟩ => ?_
  have kab := ka'.trans kb
  refine WP.mono (negateSelected_ok (kab.scr hs) (by decide : 2048 ≤ KDIG)
    (by simp only [KDIG]; omega) hd ((kab.gpr _ (by decide)).trans hr)
    (code_keep kab (by decide) (by simp only [KDIG]; omega) hm)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kab.trans ku, ?_, ?_⟩
  · have px := congrArg Spec.Ed448.Point.X pb
    have py := congrArg Spec.Ed448.Point.Y pb
    have pz := congrArg Spec.Ed448.Point.Z pb
    dsimp only [pt] at px py pz
    simp only [pt, xu, fu 9 (by decide) (by decide), fu 10 (by decide) (by decide), px, py, pz, ka.2.1]
    by_cases hn : d < 0 <;>
      simp only [hn, decide_true, decide_false, Proof.Ed448.SignedWindow.signedPoint,
        ite_true, Bool.false_eq_true, ite_false, Proof.Ed448.negPoint, zero_sub]
  · intro j h3 h4 h5 h8 h9 h10
    rw [fu j h3 h8, fb j h3 h4 h5 h8 h9 h10, ka.2.1]

end VG.Proof.Ed448.X86_64.Wnaf
