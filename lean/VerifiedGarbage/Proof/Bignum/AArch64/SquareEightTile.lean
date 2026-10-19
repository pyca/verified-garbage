module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightProducts
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightWord
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightPolynomial
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumn
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.Call

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight
open VG.Proof.MlKem.AArch64 (Keep)

abbrev codeRegs : List Reg := inputs ++ workRegs

theorem final_carry {s : State} {v low : Nat}
    (hv : low + (2 ^ 64) ^ 14 * accValue s = v) (hb : v < (2 ^ 64) ^ 15) :
    accValue s = (s.gpr .x19).toNat := by
  have ha : accValue s < 2 ^ 64 := by
    by_contra hh
    have hm := Nat.mul_le_mul_left ((2 ^ 64) ^ 14) (show 2 ^ 64 ≤ accValue s by omega)
    have hp : (2 ^ 64) ^ 14 * 2 ^ 64 = (2 ^ 64) ^ 15 := (Nat.pow_succ _ 14).symm
    rw [hp] at hm
    omega
  unfold accValue at ha ⊢
  omega

theorem finalStore_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (he : e + 120 ≤ Z) :
    WP isa (.block [st .x19 .x16 112]) s fun t =>
      (wv t.mem B e 15 = wv s.mem B e 14 + 2 ^ (64*14) * (s.gpr .x19).toNat ∧
        Outside B (e + 112) 8 s.mem t.mem) ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (e + 112)) (s.gpr .x19))
    (by brun [h16, hs.st he]) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  refine ⟨⟨?_, ?_⟩, kt⟩
  · rw [hm]
    exact wv_writeW_top s.mem B e 14 (s.gpr .x19) (by omega)
  · intro x hx
    exact (congrArg (fun m : Mem => m x) hm).trans
      (writeW_outside s.mem B (s.gpr .x19) (d := e + 112) (by omega) x hx)

/-- The exact scheduled eight-limb triangular product from the measured
prototype, including input loads, every carry, and the final output word. -/
theorem code_ok {s : State} {B : Addr} {Z eA eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h16 : s.gpr .x16 = off B eT)
    (hA : eA + 64 ≤ Z) (hT : eT + 120 ≤ Z) (h7 : s.gpr .x7 = 0)
    (hz : wv s.mem B eT 1 = 0) :
    WP isa (.block code) s fun t =>
      wv t.mem B eT 15 = Square.crossValue s.mem B eA 8 ∧
        Outside B (eT + 8) 112 s.mem t.mem ∧ Keep codeRegs s t := by
  change WP isa (.block (loadInputs ++ clearAcc ++ columns 13 ++ ([st .x19 .x16 112] : List Instr))) s _
  rw [List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (loadInputs_ok hs h8 hA) fun a ⟨⟨hai, ham⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (clearAcc_ok a) fun b ⟨⟨hba, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  have hm := hbm.trans ham
  have hbi : ∀ i < 8, b.gpr inputs[i]! = word s.mem B (eA + 8*i) := by
    intro i hi
    have hn : inputs[i]! ∉ [.x19, .x20, .x21] := by
      have h := input_not_work ⟨i, hi⟩
      simp only [workRegs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    exact (kb.gpr _ hn).trans (hai i hi)
  apply WP.block_append
  refine WP.mono (columns_ok (hs.congr kab.wr) ((kab.gpr _ (by decide)).trans h16)
    (by omega) (by decide) ((kab.gpr _ (by decide)).trans h7) hba
    ((congrArg (fun m : Mem => wv m B eT 1) hm).trans hz)) fun c ⟨hcv, _, hco, kc⟩ => ?_
  simp only [show 13 + 1 = 14 from rfl] at hcv
  have hx := (columnTotal_cross b).trans (inputs_cross hbi)
  have hc : wv c.mem B eT 14 + (2 ^ 64) ^ 14 * accValue c = Square.crossValue s.mem B eA 8 := by
    rw [← Nat.pow_mul]
    exact hcv.trans hx
  have hcarry := final_carry hc (cross_words_lt s.mem B eA)
  refine WP.mono (finalStore_ok (hs.congr (kc.wr.trans kab.wr))
    ((kc.gpr _ (by decide)).trans ((kab.gpr _ (by decide)).trans h16)) hT)
    fun t ⟨⟨htv, hto⟩, kt⟩ => ?_
  refine ⟨?_, ?_, (((ka.trans kb).trans kc).trans kt).mono (by decide)⟩
  · rw [← hcarry] at htv
    exact htv.trans (hcv.trans hx)
  · have ho : Outside B (eT + 8) 104 s.mem c.mem := by
      intro x hh
      exact (hco x hh).trans (congrArg (fun m : Mem => m x) hm)
    exact (ho.mono (by omega) (by omega)).trans (hto.mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.SquareEight
