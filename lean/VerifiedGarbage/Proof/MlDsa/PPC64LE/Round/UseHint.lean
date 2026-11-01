module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Bits
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Bits
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
meta import VerifiedGarbage.Proof.MlDsa.Round.Ones
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# ML-DSA on PPC64LE: `vg_mldsa_use_hint`

The selection of `γ₂` (`sel_ok'`), then the loop for it: one symbolic
execution of its body for any pointers (`body_ok`), which stores `uhv` of
the coefficient of `r` and the hint word (`uh_val`: the value
`useHint_eq` gives); the invariant says which coefficients of `out` are
done.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.UseHint

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW coeffAt_frame zipWith_get useHint_eq
  mem_gamma2s hbF hbM hbF_le hintAt_get natPolyIs_of_toNat reduced_zero)
open VG.Proof.MlDsa.PPC64LE.Round
open VG.Proof.MlDsa.PPC64LE.Round.Bits (dMod_le dMul_lt kgpr selGpr sel_ok' sel_ct consts_ok)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## Values -/

/-- What the body stores for the coefficient `a` and the hint word `w`. -/
def uhv (g : Nat) (a w : BitVec 64) : BitVec 64 :=
  fixk (BitVec.ofNat 64 (dMod g)) (fixk (BitVec.ofNat 64 (dMod g))
    (hbr g a + (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 -
      (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 * ((w - 1) >>> 63) + (w - 1) >>> 63 - 1) -
    BitVec.ofNat 64 (dMod g))

/-- The value `useHint_eq` gives. -/
def uhNat (g a : Nat) (b : Bool) : Nat :=
  (if b then (if hbF g a * (2 * g) < a then hbF g a + hbM g + 1 else hbF g a + hbM g - 1)
    else hbF g a + hbM g) % hbM g

/-- `fixup`, a subtraction of `m` and `fixup` again, of `u` in `[-1, m + 1]`:
`u mod m`. -/
theorem fixk2 {m : Nat} (hm : m < 64) (hm0 : 0 < m) {u : BitVec 64} (hu : u.toNat ≤ m + 1 ∨ u.toNat = 2 ^ 64 - 1) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat =
      if u.toNat < m then u.toNat else if u.toNat ≤ m + 1 then u.toNat - m else m - 1 := by
  have hM : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
  generalize BitVec.ofNat 64 m = M at hM ⊢
  unfold fixk
  have h1 : u >>> 63 = 0 ∨ u >>> 63 = 1 := by bv_omega
  rcases h1 with h1 | h1 <;> rw [h1]
  · have h2 : (u + 0 * M - M) >>> 63 = 0 ∨ (u + 0 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega
  · have h2 : (u + 1 * M - M) >>> 63 = 0 ∨ (u + 1 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega

/-- `fixk2` of `u = x - m`, for `x` in `[m - 1, 2m + 1]`: `x mod m`. -/
theorem fixk2_mod {m : Nat} (hm : m < 64) (hm1 : 1 < m) {u : BitVec 64} {x : Nat} (hx : x ≤ 2 * m + 1)
    (hu : u.toNat + m = x ∨ (u.toNat = 2 ^ 64 - 1 ∧ x = m - 1)) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat = x % m := by
  rw [fixk2 hm (by omega) (by omega)]
  have m1 : ∀ y, m ≤ y → y < 2 * m → y % m = y - m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  have m2 : ∀ y, 2 * m ≤ y → y < 3 * m → y % m = y - 2 * m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod (by omega), m1 _ (by omega) (by omega)]; omega
  rcases hu with hu | ⟨hu, rfl⟩
  · split
    · rw [m1 _ (by omega) (by omega)]; omega
    · split
      · rw [m2 _ (by omega) (by omega)]; omega
      · omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    split
    · omega
    · split <;> omega

theorem uh_val {g : Nat} (hg : g ∈ gamma2s) {a w : BitVec 64} (ha : a.toNat < q) (hw : w.toNat < 2 ^ 32) :
    (uhv g a w).toNat = uhNat g a.toNat (decide (w.toNat ≠ 0)) := by
  have hr := hbr_toNat hg ha
  have hf := hbF_le hg ha
  have hm := dMod_eq hg
  obtain ⟨-, m64⟩ := dMod_pos hg
  have m1 : 1 < dMod g := by unfold dMod; split <;> decide
  have hg2 : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hF : (hbr g a).toNat ≤ dMod g := by rw [hr, hm]; exact hf
  unfold uhv uhNat
  rw [← hr, ← hm]
  generalize hbr g a = F at hF ⊢
  have hF44 : F.toNat ≤ 44 := Nat.le_trans hF (by unfold dMod; split <;> decide)
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  have hP : (F * BitVec.ofNat 64 (2 * g)).toNat = F.toNat * (2 * g) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 2 * g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul hF44 hg2) (by decide))
  have hpf : F.toNat * (2 * g) ≤ 44 * 523776 := Nat.mul_le_mul hF44 hg2
  generalize F * BitVec.ofNat 64 (2 * g) = P at hP ⊢
  have z : (w - 1) >>> 63 = if w.toNat = 0 then 1 else 0 := by split <;> bv_omega
  have s : (P - a) >>> 63 = if P.toNat < a.toNat then 1 else 0 := by split <;> bv_omega
  rw [z, s, ← hP]
  by_cases hw0 : w.toNat = 0 <;> by_cases hs : P.toNat < a.toNat <;>
    simp only [hw0, hs, ite_true, ite_false, decide_true, decide_false, ne_eq, not_true_eq_false,
      not_false_eq_true, Bool.false_eq_true]
  · exact fixk2_mod m64 m1 (by omega) (Or.inl (by bv_omega))
  · exact fixk2_mod m64 m1 (by omega) (Or.inl (by bv_omega))
  · exact fixk2_mod m64 m1 (by omega) (Or.inl (by bv_omega))
  · exact fixk2_mod m64 m1 (by omega) (by bv_omega)

/-! ## The loop body -/

/-- What an iteration does, for the value stored. -/
def Step (s : State) (x y w c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r4 = y + 4 ∧ s'.gpr .r6 = w + 4 ∧ s'.gpr .r7 = c - 1 ∧
    (∀ r ∈ [Reg.r5, .r10, .r11, .r12], s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem.writeW w v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {g : Nat} {s : State} {x y w c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y)
  (h6 : s.gpr .r6 = w) (h7 : s.gpr .r7 = c) (h5 : s.gpr .r5 = BitVec.ofNat 64 (2 * g))
  (h10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g))
  (ix : InRegions (s.rd ++ s.wr) x 4) (iy : InRegions (s.rd ++ s.wr) y 4) (ow : InRegions s.wr w 4)
include h3 h4 h6 h7 h5 h10 h11 h12 ix iy ow

theorem body_ok :
    WP isa (.block (uhBody g)) s
      (Step s x y w c ((uhv g ((s.mem.readW y 32).setWidth 64) ((s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  have hS := dShift_lt g
  have hM := dMod_le g
  crun [uhBody, hbRaw, fixup, Step, uhv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12, ix, iy, ow, hS, hM,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Hp : Addr := s₀.gpr .r3
abbrev Rp : Addr := s₀.gpr .r4
abbrev G : BitVec 32 := (s₀.gpr .r5).setWidth 32
abbrev O : Addr := s₀.gpr .r6

/-- The values stored. -/
def outs (g : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj rj => (useHint g hj rj).toNat) ((hintAt s₀.mem (Hp s₀) 1).headD (Vector.replicate n false))
    (polyAt s₀.mem (Rp s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Hp s₀), pR (Rp s₀)]
  wr : s₀.wr = [pR (O s₀)]
  dh : (pR (Hp s₀)).Disjoint (pR (O s₀))
  dr : (pR (Rp s₀)).Disjoint (pR (O s₀))
  fitH : (Hp s₀).toNat + 1024 ≤ 2 ^ 64
  fitR : (Rp s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  red : Reduced s₀.mem (Rp s₀)

/-- After `i` iterations. -/
structure Inv (g : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = Hp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = Rp s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .r6 = O s₀ + BitVec.ofNat 64 (4 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (256 - i)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (2 * g)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (O s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ g)[j]!

theorem out_lt {g : Nat} (hg : g ∈ gamma2s) (s₀ : State) {i : Nat} (hi : i < 256) : (outs s₀ g)[i]! < 64 := by
  rw [outs, zipWith_get _ _ _ hi, useHint_eq hg, Int.toNat_natCast]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide))
    (by rcases mem_gamma2s hg with rfl | rfl <;> decide)

theorem out_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (uhv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64) ((coeffAt s₀.mem (Hp s₀) i).setWidth 64)).setWidth 32 =
      BitVec.ofNat 32 (outs s₀ g)[i]! := by
  obtain ⟨ea, ha⟩ := HighLow.load_toNat hp.red hi
  have hw : ((coeffAt s₀.mem (Hp s₀) i).setWidth 64).toNat = (coeffAt s₀.mem (Hp s₀) i).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Hp s₀) i).isLt; omega)
  have e := uh_val hg ha (by rw [hw]; exact (coeffAt s₀.mem (Hp s₀) i).isLt)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, e, BitVec.toNat_ofNat, outs, zipWith_get _ _ _ hi, useHint_eq hg,
    Int.toNat_natCast, hintAt_get _ _ hi, ea, hw, uhNat]
  have hb : decide ((coeffAt s₀.mem (Hp s₀) i).toNat ≠ 0) = decide (coeffAt s₀.mem (Hp s₀) i ≠ 0) :=
    decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl),
      fun h e => h (BitVec.eq_of_toNat_eq (by simpa using e))⟩
  rw [hb]

theorem inv_step {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv g s₀ i s) :
    WP isa (.block (uhBody g)) s fun s' => Inv g s₀ (i + 1) s' ∧ (s'.gpr .r7 != 0) = decide (i + 1 ≠ 256) := by
  have cH := coeff_contains (Hp s₀) (i := i) hi
  have cR := coeff_contains (Rp s₀) (i := i) hi
  have cO := coeff_contains (O s₀) (i := i) hi
  have hd : ∀ {p : Addr}, (pR p).Disjoint (pR (O s₀)) → ∀ r ∈ [pR (O s₀)], (pR p).Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  have eR : s.mem.readW (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i :=
    coeffAt_frame h.frame (hd hp.dr) hi
  have eH : s.mem.readW (Hp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Hp s₀) i :=
    coeffAt_frame h.frame (hd hp.dh) hi
  have hv := out_val hg hp hi
  rw [← eR, ← eH] at hv
  refine WP.mono (body_ok h.r3 h.r4 h.r6 h.r7 h.r5 h.r10 h.r11 h.r12 ?_ ?_ ?_)
    fun s' ⟨r3, r4, r6, r7, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
      (kp .r5 (by simp)).trans h.r5, (kp .r10 (by simp)).trans h.r10, (kp .r11 (by simp)).trans h.r11,
      (kp .r12 (by simp)).trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cO⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r7]; exact count_sub hi
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cO
  · intro j hj hji
    rw [m, hv, show O s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (O s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact h.coeff j hj (by omega)
  · rw [r7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-! ## The function -/

/-- What the function leaves. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    ∀ j < 256, coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ (G s₀).toNat)[j]!

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa useHint s₀ (Post s₀) := by
  refine sel_ok' (rg := .r5) (by decide) hp.g fun g hg hG s hgpr hm hrd hwr hsp hlr => ?_
  have e : (if g = g32 then uhLoop g32 else uhLoop g88) = uhLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e]
  have b2 : 2 * g < 2 ^ 31 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  refine WP.seq (consts_ok (WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_li (by decide)) (wp_nil ?_)))))
  refine WP.mono (wp_loop_nz (Inv g s₀) (N := 256) (by decide) (fun i hi s h => inv_step hg hp hi h)
    (fun _ h => h) ?_) fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => hG ▸ h'.coeff j hj hj⟩
  have e5 := VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val b2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrd, hwr, hsp, hlr, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega)⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e5
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · have : r ≠ .r0 ∧ r ≠ .r5 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.useHintContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 95232 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified PPC64LE.target useHint (Proof.MlDsa.useHintContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .r5) (by decide) [.r3, .r4, .r6] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, PPC64LE.abi, PPC64LE.argRegs]
    refine natPolyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (out_lt hp.g s hj) (by decide))
  · sig_pub [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, PPC64LE.abi, PPC64LE.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.2
    · exact h.2.2.2.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.UseHint
