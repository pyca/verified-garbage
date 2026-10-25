module


import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainMath
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Accumulate the full diagonal with its high carry accounted for. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.Square
open VG.Proof.MlKem.AArch64 (Keep)

structure DiagInv (s₀ : State) (B : Addr) (Z A eb i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (A+16*i)
  x11 : t.gpr .x11 = off B (eb+8*i)
  out : Outside B A (16*i) s₀.mem t.mem
  val : wv t.mem B A (2*i) + 2 ^ (128*i)*carry t =
    2*wv s₀.mem B A (2*i) + diagonalValue s₀.mem B eb i

structure TileInv (s₀ : State) (B : Addr) (Z A eb i j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (A+16*i)
  x11 : t.gpr .x11 = off B (eb+8*i)
  out : Outside B A (16*(i+j)) s₀.mem t.mem
  val : wv t.mem B A (2*(i+j)) + 2 ^ (128*(i+j))*carry t =
    2*wv s₀.mem B A (2*(i+j)) + diagonalValue s₀.mem B eb (i+j)

theorem diagStep_ok {s₀ t : State} {B : Addr} {Z A eb w i j : Nat}
    (h7 : s₀.gpr .x7 = 0) (hi : i+j < w) (hj : j < 4) (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sb : eb+8*w ≤ A ∨ A+16*w ≤ eb) (hI : TileInv s₀ B Z A eb i j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.DiagonalChain.step j)) t fun u =>
        TileInv s₀ B Z A eb i (j+1) u := by
  have hn := hI.scr.nowrap
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.mono (diagonalStep_ok hI.scr hI.x16 hI.x11 t7 (by omega_arith) hj (by omega_arith))
    fun u ⟨⟨lo, hiw, hm, hv, _⟩, ku⟩ => ?_
  simp only [show A + 16*i + 16*j = A + 16*(i+j) by omega_arith,
    show eb + 8*i + 8*j = eb + 8*(i+j) by omega_arith] at hm hv
  have ho : Outside B (A+16*(i+j)) 16 t.mem u.mem := by
    rw [hm]
    exact ((writeW_outside t.mem B lo (d := A+16*(i+j)) (by omega_arith)).mono
      (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside (t.mem.writeW (off B (A+16*(i+j))) lo) B hiw
        (d := A+16*(i+j)+8) (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have rT : wv t.mem B (A+16*(i+j)) 2 = wv s₀.mem B (A+16*(i+j)) 2 :=
    hI.out.wv (by omega_arith) (by omega_arith)
  have rX : word t.mem B (eb+8*(i+j)) = word s₀.mem B (eb+8*(i+j)) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have rL : wv u.mem B A (2*(i+j)) = wv t.mem B A (2*(i+j)) :=
    ho.wv (by omega_arith) (by omega_arith)
  have newPair : wv u.mem B (A+16*(i+j)) 2 = lo.toNat + 2 ^ 64*hiw.toNat := by
    rw [hm, wv_writeW_top _ B (A+16*(i+j)) 1 hiw (by omega_arith)]
    have hlo := wv_writeW_top t.mem B (A+16*(i+j)) 0 lo (by omega_arith)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, wv, Nat.zero_add] at hlo
    simp [wv, hlo]
  have pairOld : (word t.mem B (A+16*(i+j))).toNat + 2 ^ 64*(word t.mem B (A+16*(i+j)+8)).toNat =
      wv s₀.mem B (A+16*(i+j)) 2 := by rw [← rT]; simp [wv, Nat.mul_comm]
  rw [pairOld, rX] at hv
  refine ⟨hI.scr.congr ku.wr, (hI.keep.trans ku).mono (by decide),
    (ku.gpr _ (by decide)).trans hI.x16, (ku.gpr _ (by decide)).trans hI.x11, ?_, ?_⟩
  · exact (hI.out.mono (o' := A) (n' := 16*(i+(j+1))) (Nat.le_refl _) (by omega_arith)).trans
      (ho.mono (o' := A) (n' := 16*(i+(j+1))) (by omega_arith) (by omega_arith))
  · have hold := hI.val
    rw [show 2*(i+(j+1)) = 2*(i+j)+2 by omega_arith, wv_add, wv_add s₀.mem B A, rL,
      show A+8*(2*(i+j)) = A+16*(i+j) by omega_arith, newPair,
      show 64*(2*(i+j)) = 128*(i+j) by omega_arith,
      show 128*(i+(j+1)) = 128*(i+j)+128 by omega_arith, Nat.pow_add,
      show i+(j+1) = (i+j)+1 by omega_arith, diagonalValue_succ]
    grind

def diagonalPrefix (n : Nat) : List Instr :=
  (List.range n).flatMap VG.Impl.Bignum.AArch64.DiagonalChain.step

theorem diagonalPrefix_ok {s₀ t : State} {B : Addr} {Z A eb w i n : Nat}
    (h7 : s₀.gpr .x7 = 0) (hn : n ≤ 4) (hw : i+n ≤ w)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z) (sb : eb+8*w ≤ A ∨ A+16*w ≤ eb)
    (hI : TileInv s₀ B Z A eb i 0 t) :
    WP isa (.block (diagonalPrefix n)) t (TileInv s₀ B Z A eb i n) := by
  induction n with
  | zero => exact WP.block_nil hI
  | succ n ih =>
    rw [diagonalPrefix, List.range_succ, List.flatMap_append]
    apply WP.block_append
    refine WP.mono (ih (by omega_arith) (by omega_arith)) fun u hu => ?_
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      diagStep_ok h7 (by omega_arith) (by omega_arith) hA hb sb hu

def diagonalAdvance : List Instr :=
  [.addImm .x .x16 .x16 64, .addImm .x .x11 .x11 32]

theorem diagonalAdvance_ok {s : State} {B : Addr} {A eb i : Nat}
    (h16 : s.gpr .x16 = off B (A+16*i)) (h11 : s.gpr .x11 = off B (eb+8*i)) :
    WP isa (.block diagonalAdvance) s fun t =>
      (t.gpr .x16 = off B (A+16*(i+4)) ∧ t.gpr .x11 = off B (eb+8*(i+4)) ∧ t.mem = s.mem ∧ t.c = s.c) ∧
        Keep [.x16, .x11] s t := by
  refine WP.keep [.x16, .x11] ?_ rfl rfl rfl
  unfold diagonalAdvance
  brun [h16, h11, show A+16*i+64 = A+16*(i+4) by omega_arith,
    show eb+8*i+32 = eb+8*(i+4) by omega_arith]

theorem diagonalBlockStep_ok {s₀ t : State} {B : Addr} {Z A eb k j : Nat}
    (h7 : s₀.gpr .x7 = 0) (hj : j < k) (hA : A+16*(4*k) ≤ Z) (hb : eb+8*(4*k) ≤ Z)
    (sb : eb+8*(4*k) ≤ A ∨ A+16*(4*k) ≤ eb) (hI : DiagInv s₀ B Z A eb (4*j) t) :
    WP isa (.block ((diagonalPrefix 4 ++ diagonalAdvance) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
        DiagInv s₀ B Z A eb (4*(j+1)) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have h0 : TileInv s₀ B Z A eb (4*j) 0 t :=
    ⟨hI.scr, hI.keep, hI.x16, hI.x11, by simpa using hI.out, by simpa using hI.val⟩
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x6]
    (diagonalPrefix_ok h7 (by decide) (by omega_arith) hA hb sb h0)
    (by decide) (by decide) (by decide)) fun v ⟨hv, kp⟩ => ?_
  apply WP.block_append
  refine WP.mono (diagonalAdvance_ok hv.x16 hv.x11) fun a ⟨⟨ha16, ha11, ham, hac⟩, ka⟩ => ?_
  refine WP.mono (dec_ok a .x14) fun u ⟨⟨hu14, hum, huc⟩, ku⟩ => ?_
  have hmem := hum.trans ham
  refine ⟨⟨hv.scr.congr (ku.wr.trans ka.wr),
    ((hv.keep.trans ka).trans ku).mono (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ((ku.gpr _ (by decide)).trans ha16).trans (congrArg (off B) (by omega_arith))
  · exact ((ku.gpr _ (by decide)).trans ha11).trans (congrArg (off B) (by omega_arith))
  · rw [hmem]
    simpa only [show 4*j+4 = 4*(j+1) by omega_arith] using hv.out
  · have hc : carry u = carry v := by
      unfold carry; rw [ku.gpr .x5 (by decide), ka.gpr .x5 (by decide), huc, hac]
    rw [hmem, hc]
    simpa only [show 4*j+4 = 4*(j+1) by omega_arith] using hv.val
  · rw [hu14, ka.gpr .x14 (by decide)]
    rw [kp.gpr .x14 (by decide)]

end VG.Proof.Bignum.AArch64.DiagonalChain
