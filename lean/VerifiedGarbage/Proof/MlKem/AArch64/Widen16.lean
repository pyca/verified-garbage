module

public import VerifiedGarbage.Impl.MlKem.AArch64.Widen16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on AArch64: a polynomial from 16-bit to 32-bit coefficients

`widen_ok`: `Impl.MlKem.AArch64.Widen16.widen` stores the polynomial at `x0`, with 16-bit
coefficients, at `x1` with 32-bit ones. Each iteration loads eight coefficients, which `zip1`
and `zip2` with zero (`v29`) widen into two vectors of four (`Ntt16.vword_zip_zero`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Widen16

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (vword_zip_zero)
open VG.Impl.MlKem.AArch64.Widen16 (widenBody widen)

/-- The coefficients `i ∈ S` of the polynomial at `p` are `G i`, the others `old i`. -/
def CoeffsIn (m : Mem) (p : Addr) (S : Nat → Prop) [DecidablePred S] (G old : Nat → BitVec 32) :
    Prop :=
  ∀ i < 256, coeffAt m p i = if S i then G i else old i

theorem CoeffsIn.congr {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S] [DecidablePred S']
    {G old : Nat → BitVec 32} (h : CoeffsIn m p S G old) (hS : ∀ i < 256, (S' i ↔ S i)) :
    CoeffsIn m p S' G old := fun i hi => by
  rw [h i hi]
  by_cases c : S i
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 c)]
  · rw [ite_eq_right c, ite_eq_right (fun h' => c ((hS i hi).1 h'))]

/-- Storing four coefficients `t, …, t + 3`. -/
theorem CoeffsIn.write16 {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S]
    [DecidablePred S'] {G old : Nat → BitVec 32} (h : CoeffsIn m p S G old) {t : Nat} (ht : t + 4 ≤ 256)
    {x : BitVec 128} (hx : ∀ e < 4, vword x e = G (t + e))
    (hS : ∀ i < 256, (S' i ↔ S i ∨ (t ≤ i ∧ i < t + 4))) :
    CoeffsIn (m.write (coeffAddr p t) 16 x) p S' G old := fun i hi => by
  rw [coeffAt_write16 _ _ ht _ hi, h i hi]
  by_cases c : t ≤ i ∧ i < t + 4
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 (Or.inr c)), hx _ (by omega),
      show t + (i - t) = i by omega]
  · rw [ite_eq_right c]
    by_cases c' : S i
    · rw [ite_eq_left c', ite_eq_left ((hS i hi).2 (Or.inl c'))]
    · rw [ite_eq_right c', ite_eq_right (fun h' => ((hS i hi).1 h').elim c' c)]

/-- The registers `widen` writes. -/
abbrev clob : List Reg := [.x0, .x1, .x10]

/-- What `widen` needs: the polynomial `F` with 16-bit coefficients at `x0`, readable, and 1024
writable bytes at `x1` apart from it. -/
structure WidenData (s₀ : State) (F : Poly) : Prop where
  src : PolyIsW 16 s₀.mem (s₀.gpr .x0) F
  read : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  write : ∀ j, j + 16 ≤ 1024 → InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 512⟩ : Region).Disjoint ⟨s₀.gpr .x1, 1024⟩

/-- Coefficient `i` of the output. -/
def G (F : Poly) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (F[i]!).val

/-- After `k` iterations. -/
structure Inv (s₀ : State) (F : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (32 * k)
  count : (s.gpr .x10).toNat = 32 - k
  zero : ∀ e < 8, vhalf (s.v .v29) e = 0
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  out : CoeffsIn s.mem (s₀.gpr .x1) (· < 8 * k) (G F) fun i => coeffAt s₀.mem (s₀.gpr .x1) i
  frame : Frame [⟨s₀.gpr .x1, 1024⟩] s₀.mem s.mem

theorem G_toNat (F : Poly) (i : Nat) : (G F i).toNat = (F[i]!).val := by
  rw [G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt F[i]!; omega)]

theorem step {s₀ : State} {F : Poly} (hd : WidenData s₀ F) {k : Nat} (hk : k < 32) {s : State}
    (h : Inv s₀ F k s) :
    WP isa (.block widenBody) s fun t => Inv s₀ F (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  have srcAt : s.gpr .x0 + BitVec.ofNat 64 0 = s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k)) := by
    rw [h.x0, BitVec.add_zero]; congr 2; omega
  refine wp_ldrq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide) srcAt ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr]; exact hd.read _ (by omega)
  have ld : ∀ e < 8, (vhalf (s1.v .v0) e).toNat = (F[8 * k + e]!).val := fun e he => by
    rw [h1.v, vhalf_read_coeff _ _ _ he]
    have hf : coeffAtW 16 s.mem (s₀.gpr .x0) (8 * k + e) = coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e) :=
      coeffAtW16_congr (bytes_frame h.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hd.apart) (by decide)) (by rw [n_eq]; omega)
    rw [hf, polyIsW_toNat hd.src (by rw [n_eq]; omega)]
  have z1 : ∀ e < 8, vhalf (s1.v .v29) e = 0 := fun e he => by rw [h1.other _ (by decide)]; exact h.zero e he
  refine wp_vop (d := .v1) rfl fun s2 h2 => ?_
  refine wp_vop (d := .v2) rfl fun s3 h3 => ?_
  have w1 : ∀ e < 4, vword (s3.v .v1) e = G F (8 * k + e) := fun e he => BitVec.eq_of_toNat_eq (by
    rw [h3.other _ (by decide), h2.v, G_toNat, (vword_zip_zero z1 he).1]
    exact ld e (by omega))
  have w2 : ∀ e < 4, vword (s3.v .v2) e = G F (8 * k + 4 + e) := fun e he => BitVec.eq_of_toNat_eq (by
    rw [h3.v, G_toNat, show 8 * k + 4 + e = 8 * k + (4 + e) by omega,
      h2.other .v0 (by decide), h2.other .v29 (by decide), (vword_zip_zero z1 he).2]
    exact ld _ (by omega))
  have g3 : s3.gpr = s.gpr := by rw [h3.gpr, h2.gpr, h1.gpr]
  have dst0 : s3.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .x1) (8 * k) := by
    rw [g3, h.x1, BitVec.add_zero, coeffAddr]; congr 2; omega
  refine wp_strq (a := coeffAddr (s₀.gpr .x1) (8 * k)) (by decide) dst0 ?_ fun s4 h4 => ?_
  · rw [h3.wr, h2.wr, h1.wr, h.wr, coeffAddr]
    exact hd.write _ (by omega)
  have dst1 : s4.gpr .x1 + BitVec.ofNat 64 16 = coeffAddr (s₀.gpr .x1) (8 * k + 4) := by
    rw [h4.gpr, g3, h.x1, coeffAddr, ptr_add]; congr 2; omega
  refine wp_strq (a := coeffAddr (s₀.gpr .x1) (8 * k + 4)) (by decide) dst1 ?_ fun s5 h5 => ?_
  · rw [h4.wr, h3.wr, h2.wr, h1.wr, h.wr, coeffAddr]
    exact hd.write _ (by omega)
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 32, .subImm .x .x10 .x10 1]) s5
      fun t => Only [.x0, .x1, .x10] s5 t ∧ t.gpr .x0 = s5.gpr .x0 + 16 ∧
        t.gpr .x1 = s5.gpr .x1 + 32 ∧ (t.gpr .x10).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x10).toNat = 32 - k := by
        rw [h7.get .x10, h6.get .x10, h5.gpr, h4.gpr, g3, h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega), cnt]; simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  have g5 : s5.gpr = s.gpr := by rw [h5.gpr, h4.gpr, g3]
  have vv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2) : t.v r = s.v r := by
    rw [vt, h5.v, h4.v, h3.other _ r2, h2.other _ r1, h1.other _ r0]
  have mt : t.mem = (s.mem.write (coeffAddr (s₀.gpr .x1) (8 * k)) 16 (s3.v .v1)).write
      (coeffAddr (s₀.gpr .x1) (8 * k + 4)) 16 (s3.v .v2) := by
    rw [ht.mem, h5.mem, h4.mem, h4.v, h3.mem, h2.mem, h1.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, ?_, fun r hr => ?_, ?_, ?_⟩, by rw [cnt]; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), g5, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [ht.rd, h5.rd, h4.rd, h3.rd, h2.rd, h1.rd, h.rd]
  · rw [ht.wr, h5.wr, h4.wr, h3.wr, h2.wr, h1.wr, h.wr]
  · rw [ht.sp, h5.sp, h4.sp, h3.sp, h2.sp, h1.sp, h.sp]
  · rw [p0, g5, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · rw [p1, g5, h.x1, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add]; congr 2
  · intro e he; rw [vv .v29 (by decide) (by decide) (by decide)]; exact h.zero e he
  · have hr0 : r ≠ .v0 := by revert r hr; decide
    have hr1 : r ≠ .v1 := by revert r hr; decide
    have hr2 : r ≠ .v2 := by revert r hr; decide
    rw [vv r hr0 hr1 hr2]; exact h.vcs r hr
  · rw [mt]
    refine (h.out.write16 (S' := fun i => i < 8 * k + 4) (t := 8 * k) (by omega) w1
      (fun i _ => by omega)).write16 (by omega) w2 (fun i _ => by omega)
  · rw [mt]
    have c0 := Offset.contains_base (s₀.gpr .x1) (d := 32 * k) (n := 16) (k := 1024) (by omega) (by omega)
    have c1 := Offset.contains_base (s₀.gpr .x1) (d := 32 * k + 16) (n := 16) (k := 1024) (by omega) (by omega)
    refine (h.frame.write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
    · rw [coeffAddr, show 4 * (8 * k) = 32 * k by omega]; exact c0
    · rw [coeffAddr, show 4 * (8 * k + 4) = 32 * k + 16 by omega]; exact c1

theorem init (s : State) : WP isa (.block [.movz .x .x10 32 0, .vop (.movi0 .v29)]) s fun t =>
    ∀ F, Inv s F 0 t := by
  refine wp_movz fun s1 h1 e1 => wp_vop (d := .v29) rfl fun s2 h2 => wp_nil fun F => ?_
  refine ⟨fun r hr => ?_, by rw [h2.rd, h1.rd], by rw [h2.wr, h1.wr], by rw [h2.sp, h1.sp], ?_, ?_,
    by rw [h2.gpr, e1]; rfl, fun e he => ?_, fun r hr => ?_, fun i _ => ?_, ?_⟩
  · rw [h2.gpr, h1.get r (by simp at hr ⊢; exact hr.2.2)]
  · rw [h2.gpr, h1.get .x0 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h2.gpr, h1.get .x1 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h2.v]; simp [vhalf]
  · rw [h2.other _ (by revert r hr; decide)]; exact h1.vcs r hr
  · rw [ite_eq_right (by omega), h2.mem, h1.mem]
  · rw [h2.mem, h1.mem]; exact Frame.refl _ _

theorem widen_ok {s : State} {F : Poly} (hd : WidenData s F) :
    WP isa widen s fun s' => Keep clob s s' ∧ Frame [⟨s.gpr .x1, 1024⟩] s.mem s'.mem ∧
      PolyIs s'.mem (s.gpr .x1) F := by
  refine WP.seq (WP.mono (init s) fun s₁ h₁ =>
    WP.mono (count_loop (by decide) (Inv s F) (fun k hk t ht => step hd hk ht) (h₁ F)) fun s' h' => ?_)
  refine ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, h'.vcs⟩, h'.frame, polyIs_of_toNat fun i hi => ?_⟩
  rw [n_eq] at hi
  rw [h'.out i hi, ite_eq_left (by omega), G_toNat]

end VG.Proof.MlKem.AArch64.Widen16
