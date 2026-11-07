module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exponentiate
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Set
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

/-! # The setup of public RSA at a run-time width

The modulus and the input read, the input's acceptance kept as a mask at
144 and `-M⁻¹ mod 2³²` at 152 (`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

/-- The acceptance mask and the inverse. -/
theorem setup_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {c : Bool} (hc : s.gpr .ecx = cmask c)
    (hodd : val32 s.mem base numOff (nw len) % 2 = 1) :
    WP isa (.block (([.store (sc PublicFn.acceptanceOffset) .ecx] : List Instr) ++ VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) s fun t =>
      t.mem.readW (off base PublicFn.acceptanceOffset) 32 = cmask c ∧
      (val32 s.mem base numOff (nw len) * w32 t.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Outside base PublicFn.acceptanceOffset 12 s.mem t.mem ∧ Keeps clob s t := by
  have nw' := h.scratch.nowrap
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have wbe := wb_eq len
  rw [n0] at f0
  have b264 : 264 ≤ bytes := by have := dims.1; simp only [wb] at f0; omega
  simp only [List.cons_append, List.nil_append, PublicFn.acceptanceOffset] at *
  refine wp_storeS (h.scratch.ea (d := 144) (by omega)) (h.scratch.write (d := 144) (n := 4) (by omega))
    fun u m => ?_
  have hu : Scr u base bytes := h.scratch.of_keeps (m.keeps []) (by decide) (by decide)
  have O₁ : Outside base 144 4 s.mem u.mem := by rw [m.mem]; exact writeW32_outside _ _ _ (by omega)
  have w₁ : w32 u.mem base numOff = w32 s.mem base numOff :=
    Outside.w32 O₁ (by simp only [numOff]; omega) (by simp only [numOff]; omega)
  have hodd' : w32 u.mem base numOff % 2 = 1 := by
    rw [w₁]
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
    rw [hk, val32_parity] at hodd; exact hodd
  refine WP.mono (setupInverse_ok hu (mo := numOff) (inv := invOff) (by simp only [numOff]; omega) (by simp only [invOff]; omega) hodd')
    fun t ⟨I, O₂, K⟩ => ⟨?_, ?_, ?_, (m.keeps _).trans K⟩
  · have a₂ : t.mem.readW (off base 144) 32 = u.mem.readW (off base 144) 32 :=
      BitVec.eq_of_toNat_eq (Outside.w32 O₂ (by simp only [invOff]; omega) (by omega))
    rw [a₂, m.mem, Mem.readW_writeW_self32, hc]
  · rw [w₁] at I
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
    rw [hk, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
    exact I
  · exact (O₁.mono (by decide) (by decide)).trans (O₂.mono (by simp [invOff]) (by simp [invOff]))

end VG.Proof.Bignum.X86.PublicRt
