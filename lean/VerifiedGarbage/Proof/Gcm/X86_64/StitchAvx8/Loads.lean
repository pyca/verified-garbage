import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Aes
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Loading the eight counter templates

Every AES state has a distinct register. Loading the next state preserves
the states already loaded, and changes no memory or integer registers.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs)
open VG.Impl.Aes.X86_64.AesNi (at_)

theorem aregs_distinct : ∀ i < 8, ∀ j < 8,
    aregs.getD i .xmm3 = aregs.getD j .xmm3 → i = j := by decide

theorem aregs_member : ∀ i < 8, aregs.getD i .xmm3 ∈ aregs := by decide

theorem loadCounters_ok (s : State)
    (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (640 + 16 * i))) 16)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun i =>
      .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640 + 16 * i)))) s fun t =>
      (∀ i < n, t.lane (aregs.getD i .xmm3) 0 =
        s.mem.readW (s.ea (at_ .r11 (640 + 16 * i))) 128) ∧ YFrame aregs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), YFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hv, hf⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    have hi : InRegions (t.rd ++ t.wr) (t.ea (at_ .r11 (640 + 16 * n))) 16 := by
      simpa only [hf.rd, hf.wr, State.ea, hf.gpr] using hin n (by omega)
    rw [WP.block_cons_iff]
    refine ⟨t.setV .l128 (aregs.getD n .xmm3)
      (t.mem.readW (t.ea (at_ .r11 (640 + 16 * n))) 128) 0,
      by simp only [isa, exec, State.load128, hi, ite_true, Option.map_some],
      WP.block_nil ⟨?_, ?_⟩⟩
    · intro i hi
      simp only [State.lane, xmm_setV, ite_true]
      by_cases he : i = n
      · subst i
        simp only [ite_true, hf.mem, State.ea, hf.gpr]
      · have hr : aregs.getD i .xmm3 ≠ aregs.getD n .xmm3 :=
          fun h => he (aregs_distinct i (by omega) n (by omega) h)
        rw [ite_eq_right hr]
        exact hv i (by omega)
    · refine hf.trans ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro r hr l hl
      have he : r ≠ aregs.getD n .xmm3 := fun h => hr (h ▸ aregs_member n (by omega))
      simp only [State.lane, xmm_setV, ymmHi_setV_128, he, ite_false]

end VG.Proof.Gcm.X86_64.StitchAvx8
