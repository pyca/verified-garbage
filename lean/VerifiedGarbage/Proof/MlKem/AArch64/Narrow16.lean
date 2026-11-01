module

public import VerifiedGarbage.Impl.MlKem.AArch64.Narrow16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on AArch64: a polynomial from 32-bit to 16-bit coefficients

`narrow_ok`: `Impl.MlKem.AArch64.Narrow16.narrow` stores the polynomial at `x0`, with 32-bit
coefficients, at `x1` with 16-bit ones. Each iteration loads eight coefficients in two vectors,
whose low halfwords `uzp1` takes (`vhalf_perm_h8`), and stores them as one.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Narrow16

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (vhalf_perm_h8 vword_lo)
open VG.Impl.MlKem.AArch64.Narrow16 (narrowBody narrow)

/-- The registers `narrow` writes. -/
abbrev clob : List Reg := [.x0, .x1, .x10]

/-- What `narrow` needs: the polynomial `F` with 32-bit coefficients at `x0`, readable, and 512
writable bytes at `x1` apart from it. -/
structure NarrowData (s₀ : State) (F : Poly) : Prop where
  src : PolyIs s₀.mem (s₀.gpr .x0) F
  read : ∀ j, j + 16 ≤ 1024 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  write : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (polyRegion (s₀.gpr .x0)).Disjoint ⟨s₀.gpr .x1, 512⟩

/-- Coefficient `i` of the output. -/
def G (F : Poly) (i : Nat) : BitVec 16 := BitVec.ofNat 16 (F[i]!).val

theorem G_toNat (F : Poly) (i : Nat) : (G F i).toNat = (F[i]!).val := by
  rw [G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt F[i]!; omega)]

/-- After `k` iterations. -/
structure Inv (s₀ : State) (F : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (32 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x10).toNat = 32 - k
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  out : CoeffsInW s.mem (s₀.gpr .x1) (· < 8 * k) (G F) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x1) i
  frame : Frame [⟨s₀.gpr .x1, 512⟩] s₀.mem s.mem

theorem step {s₀ : State} {F : Poly} (hd : NarrowData s₀ F) {k : Nat} (hk : k < 32) {s : State}
    (h : Inv s₀ F k s) :
    WP isa (.block narrowBody) s fun t => Inv s₀ F (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  have src := polyIs_frame h.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.apart) hd.src
  have a0 : s.gpr .x0 + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .x0) (8 * k) := by
    rw [h.x0, BitVec.add_zero, coeffAddr]; congr 2; omega
  refine wp_ldrq (a := coeffAddr (s₀.gpr .x0) (8 * k)) (by decide) a0 ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr, coeffAddr, show 4 * (8 * k) = 32 * k by omega]; exact hd.read _ (by omega)
  have a1 : s1.gpr .x0 + BitVec.ofNat 64 16 = coeffAddr (s₀.gpr .x0) (8 * k + 4) := by
    rw [h1.gpr, h.x0, coeffAddr, ptr_add]; congr 2; omega
  refine wp_ldrq (a := coeffAddr (s₀.gpr .x0) (8 * k + 4)) (by decide) a1 ?_ fun s2 h2 => ?_
  · rw [h1.rd, h1.wr, h.rd, h.wr, coeffAddr, show 4 * (8 * k + 4) = 32 * k + 16 by omega]
    exact hd.read _ (by omega)
  refine wp_vop (d := .v2) rfl fun s3 h3 => ?_
  have key : ∀ (x : BitVec 128) (c e : Nat), (vword x c).toNat = (F[8 * k + e]!).val →
      vhalf x (2 * c) = G F (8 * k + e) := fun x c e hx => BitVec.eq_of_toNat_eq (by
    rw [← vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hx, G_toNat,
      Nat.mod_eq_of_lt (by have := val_lt F[8 * k + e]!; omega)])
  have hv : ∀ e < 8, vhalf (s3.v .v2) e = G F (8 * k + e) := fun e he => by
    rw [h3.v, h2.other .v0 (by decide), h2.v, h1.v, h1.mem, vhalf_perm_h8 _ _ _ he]
    by_cases c : e < 4
    · rw [ite_eq_left c]; exact key _ e e (lanes_load src (j := 8 * k) (by omega) e c)
    · rw [ite_eq_right c, show 2 * e - 8 = 2 * (e - 4) by omega]
      have := lanes_load src (j := 8 * k + 4) (by omega) (e - 4) (by omega)
      simp only [show 8 * k + 4 + (e - 4) = 8 * k + e by omega] at this
      exact key _ _ e this
  have g3 : s3.gpr = s.gpr := by rw [h3.gpr, h2.gpr, h1.gpr]
  have dst : s3.gpr .x1 + BitVec.ofNat 64 0 = s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k)) := by
    rw [g3, h.x1, BitVec.add_zero]; congr 2; omega
  refine wp_strq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide) dst ?_ fun s4 h4 => ?_
  · rw [h3.wr, h2.wr, h1.wr, h.wr, show 2 * (8 * k) = 16 * k by omega]
    exact hd.write _ (by omega)
  have scalar : WP isa (.block [.addImm .x .x0 .x0 32, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1]) s4
      fun t => Only [.x0, .x1, .x10] s4 t ∧ t.gpr .x0 = s4.gpr .x0 + 32 ∧
        t.gpr .x1 = s4.gpr .x1 + 16 ∧ (t.gpr .x10).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x10).toNat = 32 - k := by
        rw [h7.get .x10, h6.get .x10, h4.gpr, g3, h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega), cnt]; simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  have g4 : s4.gpr = s.gpr := by rw [h4.gpr, g3]
  have vv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2) : t.v r = s.v r := by
    rw [vt, h4.v, h3.other _ r2, h2.other _ r1, h1.other _ r0]
  have mt : t.mem = s.mem.write (s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s3.v .v2) := by
    rw [ht.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, fun r hr => ?_, ?_, ?_⟩, by rw [cnt]; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), g4, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [ht.rd, h4.rd, h3.rd, h2.rd, h1.rd, h.rd]
  · rw [ht.wr, h4.wr, h3.wr, h2.wr, h1.wr, h.wr]
  · rw [ht.sp, h4.sp, h3.sp, h2.sp, h1.sp, h.sp]
  · rw [p0, g4, h.x0, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add]; congr 2
  · rw [p1, g4, h.x1, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · have hr0 : r ≠ .v0 := by revert r hr; decide
    have hr1 : r ≠ .v1 := by revert r hr; decide
    have hr2 : r ≠ .v2 := by revert r hr; decide
    rw [vv r hr0 hr1 hr2]; exact h.vcs r hr
  · rw [mt]
    exact h.out.write16 (by omega) hv (fun i _ => by omega)
  · rw [mt]
    refine h.frame.write (List.mem_singleton_self _) _ ?_
    rw [show 2 * (8 * k) = 16 * k by omega]
    exact Offset.contains_base (s₀.gpr .x1) (d := 16 * k) (n := 16) (k := 512) (by omega) (by omega)

theorem init (s : State) : WP isa (.block [.movz .x .x10 32 0]) s fun t => ∀ F, Inv s F 0 t := by
  refine wp_movz fun s1 h1 e1 => wp_nil fun F => ?_
  refine ⟨fun r hr => ?_, h1.rd, h1.wr, h1.sp, ?_, ?_, by rw [e1]; rfl, fun r hr => h1.vcs r hr,
    fun i _ => ?_, ?_⟩
  · rw [h1.get r (by simp at hr ⊢; exact hr.2.2)]
  · rw [h1.get .x0 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h1.get .x1 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [ite_eq_right (by omega), h1.mem]
  · rw [h1.mem]; exact Frame.refl _ _

theorem narrow_ok {s : State} {F : Poly} (hd : NarrowData s F) :
    WP isa narrow s fun s' => Keep clob s s' ∧ Frame [⟨s.gpr .x1, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x1) F := by
  refine WP.seq (WP.mono (init s) fun s₁ h₁ =>
    WP.mono (count_loop (by decide) (Inv s F) (fun k hk t ht => step hd hk ht) (h₁ F)) fun s' h' => ?_)
  exact ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, h'.vcs⟩, h'.frame,
    h'.out.polyIs (fun i hi => by omega) fun i _ => G_toNat F i⟩

end VG.Proof.MlKem.AArch64.Narrow16
