module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Square
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Counter
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # The tested power in a P-224 descent round -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.X86.Wp

theorem descentPower_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (Impl.EcKey.Compressed.X86.descentPower c) s fun t =>
      Keeps powClob s t ∧ Unch base (slWk c [T3, TMP]) s.mem t.mem ∧
      sv c base t T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++
    [.mov .esi (.mem (sc (c.sl T2))), decCounter])) (Impl.EcKey.Compressed.X86.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega) (by have := sl_le c h7 (i := T0) (by decide); omega)
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₁
  have v₁' : sv c base s₁ T3 = sv c base s T0 := by
    simpa only [sv, wordsVal_eq_val32] using v₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine wp_movS (show readSrc s₁ (.mem (sc (c.sl T2))) = some (s₁.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs₁.ea (d := c.sl T2) (by omega), hs₁.read (by omega : c.sl T2 + 4 ≤ size), ite_true]) fun s₂ u₂ _ => ?_
  have hb₂ : s₂.gpr .esi = BitVec.ofNat 32 j := by
    rw [u₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32 (by have := sl_apart c (i := T2) (j := T3) (by decide); omega) (by omega)), hword]
  refine wp_decCounter hj hb₂ fun s₃ hb₃ k₃ m₃' => WP.block_nil ?_
  have K : Keeps powClob s s₃ := (k₁.mono (by decide)).trans
    ((u₂.keeps.mono (by decide)).trans (k₃.mono (by decide)))
  have hs₃ := hs.of_keeps K (by decide)
  have m₃ : s₃.mem = s₁.mem := m₃'.trans u₂.mem
  have M₃ : ModOkW c.MP' size c.C.p s₃.mem base := modP_of hc (by
    rw [m₃, O₁.wordsVal (sl_apart c (i := MP) (j := T3) (by decide))
      (by have := sl_le c h7 (i := MP) (by decide); omega)]
    exact hM.val)
  refine WP.mono (squarePower_ok hc hs₃ M₃
    (by rw [sv, m₃]; change sv c base s₁ T3 < _; rw [v₁']; exact hlt) hb₃ (by omega))
    fun t ⟨Kt, Ut, lt, vt⟩ => ?_
  refine ⟨K.trans Kt, ?_, lt, ?_⟩
  · rw [m₃] at Ut
    exact unch_same ((slot_frame (slots := [T3, TMP]) (by simp) (Nat.le_refl _) O₁).mono
      (fun w hw => List.mem_append_left _ hw)) Ut
  · simpa only [sv, m₃, show wordsVal s₁.mem base (c.sl T3) c.n = sv c base s T0 from v₁'] using vt

end VG.Proof.EcKey.Compressed.X86
