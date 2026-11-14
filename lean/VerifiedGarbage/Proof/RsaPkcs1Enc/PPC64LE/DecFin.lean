module

import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecSel
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select

/-! ### `RsaPkcs1Enc.PPC64LE.DecOut`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: writing the output

`*msg_len` (`outInit`) and the output, byte by byte (`selBody_ok`,
`selLoop_ok`): byte `i` of `out` is `outByte v ok kl i EM[i] AM[i]`; then the
result and our return address (`selPart_ok`, into `Fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

/-- After the private-key operation's output is read: the frame, the slots
and the result `R` in its slot, memory changed only in our stack, `out`,
`*msg_len` and `scratch`. -/
structure Fr3 (s : State) (R : BitVec 64) (u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ preserved, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, mlR s, sR s] s.mem u.mem
  sl : Slots s u.mem
  r : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R

theorem Post.fr3 {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t) : Fr3 s R t :=
  ⟨hc.sp, hc.rd, hc.wr, hc.hi, hc.mem.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩, hc.sl, hc.r⟩

/-- A store to `out` or `*msg_len`. -/
theorem Fr3.store {s : State} (h : DPre pc s) {R : BitVec 64} {t u : State} (hc : Fr3 s R t) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (hsp : u.sp = t.sp) (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) {X : Region}
    (hX : X = oR s ∨ X = mlR s) {Y : Region} (hY : Region.Sub Y X) (hf : Frame [Y] t.mem u.mem) :
    Fr3 s R u := by
  have hk : Region.Disjoint (kR s) Y := by
    rcases hX with rfl | rfl
    · exact h.ko.sub_right hY
    · exact h.km.sub_right hY
  refine ⟨hsp.trans hc.sp, hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hg r hr).trans (hc.hi r hr),
    hc.mem.trans (hf.sub fun r hr => ?_), hc.sl.words hf fun r hr d _ hn => ?_, ?_⟩
  · rw [List.mem_singleton.mp hr]
    rcases hX with rfl | rfl
    · exact ⟨_, by simp, hY⟩
    · exact ⟨_, by simp, hY⟩
  · rw [List.mem_singleton.mp hr]; exact hk.sub_left (frame_sub s hn)
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hk.sub_left (frame_sub s (by decide))) (by decide)]
    exact hc.r

/-! ## A byte of the output -/

/-- The first part of `selBody`: the byte, in `r6`. -/
def selA : List Instr :=
  [.lbz .r6 .r11 0, .lbz .r12 .r10 0, .logic .xor .r6 .r6 .r12, .logic .and .r6 .r6 .r5,
    .logic .xor .r6 .r6 .r12, .sub .r12 .r9 .r3, .lsr .d .r12 .r12 63, .sub .r12 .r0 .r12,
    .logic .xor .r12 .r12 .r8, .logic .and .r12 .r12 .r4, .logic .and .r6 .r6 .r12]

/-- The rest: its store, and the pointers and counter advanced. -/
def selB : List Instr :=
  [.stb .r6 .r11 0, .addi .r9 .r9 1, .addi .r11 .r11 1, .addi .r10 .r10 1, .subi .r7 .r7 1]

theorem selBody_eq : selBody = selA ++ selB := rfl

theorem outB_eq (v ok : Bool) {kl i : Nat} (hkl : kl < 2 ^ 63) (hi : i < 2 ^ 63) (e a : Byte) :
    ((((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64) &&&
      ((((0 : BitVec 64) - ((BitVec.ofNat 64 i - BitVec.ofNat 64 kl) >>> 63)) ^^^ BitVec.allOnes 64) &&& bm ok)).setWidth 8 =
      outByte v ok kl i e a := by
  have sel : ((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64 = (if v then e else a).setWidth 64 := by
    cases v
    · simp [bm]
    · simp only [bm, ite_true, BitVec.and_allOnes]
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [sel, borrow _ _ hi hkl]
  simp only [outByte]
  by_cases hk : kl ≤ i
  · cases ok
    · simp only [hk, ↓reduceIte, bm, Bool.false_eq_true, and_false]
      apply BitVec.eq_of_toNat_eq; simp
    · simp only [hk, ↓reduceIte, bm, and_self]
      rw [show ((0 : BitVec 64) - BitVec.ofNat 64 0) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 by decide,
        BitVec.and_allOnes, BitVec.and_allOnes, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [hk, ↓reduceIte, false_and]
    rw [show ((0 : BitVec 64) - BitVec.ofNat 64 1) ^^^ BitVec.allOnes 64 = 0 by decide]
    apply BitVec.eq_of_toNat_eq; simp

theorem selA_ok {t : State} (he : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (ha : InRegions (t.rd ++ t.wr) (t.gpr .r10 + BitVec.ofNat 64 0) 1) (h0 : t.gpr .r0 = 0) :
    WP isa (.block selA) t fun u => (u.mem = t.mem ∧
      u.gpr .r6 = ((((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 ^^^
          (t.mem (t.gpr .r10 + BitVec.ofNat 64 0)).setWidth 64) &&& t.gpr .r5) ^^^
          (t.mem (t.gpr .r10 + BitVec.ofNat 64 0)).setWidth 64) &&&
        ((((0 : BitVec 64) - ((t.gpr .r9 - t.gpr .r3) >>> 63)) ^^^ t.gpr .r8) &&& t.gpr .r4)) ∧
      Keep [.r6, .r12] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  unfold selA
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 he,
    exec_lbz (s := t.write .r6 ((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64))
      (show Reg.r10 ≠ .r0 by decide) c0 (by exact ha), h0]
  simp only [read1_64]

theorem selB_ok {t : State} (hw : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block selB) t fun u => (u.mem = t.mem.write (t.gpr .r11 + BitVec.ofNat 64 0) 1 ((t.gpr .r6).setWidth 8) ∧
      u.gpr .r9 = t.gpr .r9 + BitVec.ofNat 64 1 ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
      u.gpr .r10 = t.gpr .r10 + BitVec.ofNat 64 1 ∧ u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1) ∧
      Keep [.r9, .r11, .r10, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold selB
  prun [exec_stb (show Reg.r11 ≠ .r0 by decide) c0 hw, exec_addi (show Reg.r9 ≠ .r0 by decide) c1,
    exec_addi (show Reg.r11 ≠ .r0 by decide) c1, exec_addi (show Reg.r10 ≠ .r0 by decide) c1]

/-! ## The loop -/

/-- After `i` bytes of the output. -/
structure OInv (s : State) (R MLV : BitVec 64) (EM AM : List Byte) (v ok : Bool) (kl : Nat) (i : Nat) (t : State) :
    Prop where
  fr : Fr3 s R t
  ml : t.mem.readW (s.gpr .r5) 64 = MLV
  r9 : t.gpr .r9 = BitVec.ofNat 64 i
  r11 : t.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 i
  r10 : t.gpr .r10 = scA s sAM + BitVec.ofNat 64 i
  r4 : t.gpr .r4 = bm ok
  r5 : t.gpr .r5 = bm v
  r3 : t.gpr .r3 = BitVec.ofNat 64 kl
  r0 : t.gpr .r0 = 0
  r8 : t.gpr .r8 = BitVec.allOnes 64
  done : ∀ j < i, t.mem (s.gpr .r3 + BitVec.ofNat 64 j) = outByte v ok kl j (EM.getD j 1) (AM.getD j 0)
  todo : ∀ j, i ≤ j → j < (s.gpr .r7).toNat → t.mem (s.gpr .r3 + BitVec.ofNat 64 j) = EM.getD j 1
  am : ∀ j < (s.gpr .r7).toNat, t.mem (scA s sAM + BitVec.ofNat 64 j) = AM.getD j 0

section
variable {s : State} (h : DPre pc s)
include h

theorem outW {t : State} (hwr : t.wr = fr s :: s.wr) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions t.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hwr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem selLoop_ok {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 63) {t : State} (h0 : OInv s R MLV EM AM v ok kl 0 t) (h7 : t.gpr .r7 = s.gpr .r7) :
    WP isa selLoop t (OInv s R MLV EM AM v ok kl (s.gpr .r7).toNat) := by
  have hk := h.k2
  have hk64 := h.k1
  have hwo := h.wo
  rw [h.h4] at hwo
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (by omega_using []) (by omega_using [hk64]) (OInv s R MLV EM AM v ok kl)
    (fun i hi u hu _ => ?_) h0 (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hc := hu.fr
  have he : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r11, BitVec.add_zero]
    obtain ⟨r, hr, hcr⟩ := outW h hc.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r10, BitVec.add_zero, Offset.add_add]
    exact scInR h hc.wr (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega_using [hk, hi])
  rw [selBody_eq, WP.block_append_iff]
  refine WP.mono (selA_ok he ha hu.r0) fun w ⟨⟨wm, w6⟩, kw⟩ => ?_
  have hw : InRegions w.wr (w.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [kw.wr, kw.gpr _ (by decide), hu.r11, BitVec.add_zero]; exact outW h hc.wr hi
  refine WP.mono (selB_ok hw) fun x ⟨⟨xm, x9, x11, x10, x7⟩, kx⟩ => ⟨?_, ?_⟩
  · have hb : (w.gpr .r6).setWidth 8 = outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
      rw [w6, hu.r5, hu.r4, hu.r9, hu.r3, hu.r8, hu.r11, hu.r10, BitVec.add_zero, BitVec.add_zero,
        hu.todo i (Nat.le_refl _) hi, hu.am i hi, outB_eq _ _ hkl (by omega_using [hk, hi])]
    rw [hb, kw.gpr _ (by decide), hu.r11, BitVec.add_zero, wm] at xm
    have hf : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsub : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]; exact Offset.sub_base _ (by omega_using [hi])
    have hne : ∀ j, j ≠ i → j < (s.gpr .r7).toNat → s.gpr .r3 + BitVec.ofNat 64 j ≠ s.gpr .r3 + BitVec.ofNat 64 i :=
      fun j hj hjk => Offset.add_ofNat_ne _ (by omega_using [hjk]) (by omega_using [hi]) hj
    have kk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] u x :=
      (kw.mono (by decide)).trans' (kx.mono (by decide))
    have g : ∀ r, r ∉ [Reg.r9, .r11, .r10, .r7] → r ∉ [Reg.r6, .r12] → x.gpr r = u.gpr r := fun r h₁ h₂ =>
      (kx.gpr r h₁).trans (kw.gpr r h₂)
    refine ⟨hc.store h kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r; decide)) (.inl rfl) hsub hf, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
        rw [List.mem_singleton.mp hX]; exact (h.om.sub_left hsub).symm) (by decide), hu.ml]
    · rw [x9, kw.gpr _ (by decide), hu.r9, ← BitVec.ofNat_add]
    · rw [x11, kw.gpr _ (by decide), hu.r11, Offset.add_add]
    · rw [x10, kw.gpr _ (by decide), hu.r10, Offset.add_add]
    · rw [g _ (by decide) (by decide), hu.r4]
    · rw [g _ (by decide) (by decide), hu.r5]
    · rw [g _ (by decide) (by decide), hu.r3]
    · rw [g _ (by decide) (by decide), hu.r0]
    · rw [g _ (by decide) (by decide), hu.r8]
    · intro j hj
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [write1_ne' _ _ (hne j (by omega_using [hj]) (by omega_arith)), hu.done j hj]
      · exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _
    · intro j hj hjk
      rw [xm, write1_ne' _ _ (hne j (by omega_using [hj]) hjk), hu.todo j (by omega_using [hj]) hjk]
    · intro j hj
      rw [hf.bytes (R := ⟨scA s sAM, (s.gpr .r7).toNat⟩) (fun X hX => by
        rw [List.mem_singleton.mp hX]
        exact ((h.os.sub_left hsub).sub_right (sc_sub h)).symm.sub_left (scSub (by unfold sAM scrBytes; omega_using [hk])))
        (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega_using []) hj, hu.am j hj]
  · rw [x7, kw.gpr _ (by decide)]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the selection

The validity and `*msg_len` (`selInit_ok`), the output's loop, and the
result and our return address (`finish_ok`): `selPart_ok`, from `SCN` to
`Fin`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

/-- `AM`. -/
abbrev amOf (s : State) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .r7).toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (s : State) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM (s.gpr .r7).toNat

/-- The selected length. -/
abbrev lenOf (s : State) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM s EM) ((firstZero EM (s.gpr .r7).toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd)) (s.gpr .r7).toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega_using [hk]
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- At the end of the body: the output and `*msg_len` written, the result in
`r3` and our return address in the link register. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (len : Nat) (u : State) : Prop
    extends Fr3 s R u where
  r3 : u.gpr .r3 = R
  lr : u.lr = s.lr
  out : ∀ i < (s.gpr .r7).toNat, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
    outByte v ok ((s.gpr .r7).toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : u.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 len &&& bm ok

section
variable {s : State} (h : DPre pc s) {R : BitVec 64}
include h

theorem outInit_ok {t : State} (hc : Fr3 s R t) (h12 : t.gpr .r12 = fb s) :
    WP isa (.block outInit) t fun u => (u.mem = t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) (t.gpr .r6) ∧
      u.gpr .r10 = scA s sAM ∧ u.gpr .r9 = 0) ∧ Keep [.r10, .r9] t u := by
  have c1 : oML < 2 ^ 15 ∧ oML % 4 = 0 := by decide
  have c2 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c3 : sAM < 2 ^ 15 := by decide
  have i1 := slotIn (u := t) hc.wr (d := oML) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oScr) (by decide) (by decide)
  have hw : InRegions t.wr (s.gpr .r5 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, hc.wr, h.hwr]; exact ⟨mlR s, by simp, Region.contains_self _ _⟩
  have rS : ∀ v : BitVec 64, (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v).readW (fb s + BitVec.ofNat 64 oScr) 64 =
      stackArg s 13 := fun v => by
    have hf : Frame [mlR s] t.mem (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by rw [BitVec.add_zero]; exact Region.contains_self _ _)
    rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.km.sub_left (frame_sub s (by decide))) (by decide)]
    exact hc.sl.scr
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold outInit scr
  prun [h12, c1, c2, c3, i1, i2, hc.sl.ml, hw, rS, exec_addi (show Reg.r10 ≠ .r0 by decide) c3]
  rfl

omit h in
theorem finish_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block finish) t fun u => u.gpr .r3 = R ∧ u.lr = s.lr ∧ u.mem = t.mem ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  have c1 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 ∧ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have c2 : oLr < 2 ^ 15 ∧ oLr % 4 = 0 := by decide
  have i1 := slotIn (u := t) hc.wr (d := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oLr) (by decide) (by decide)
  unfold finish
  prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.r, hc.sl.lr, exec_mtlr]
  intro r hr
  have : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r12 := by revert r; decide
  simp only [this, ↓reduceIte]

/-- The selection: the validity, `*msg_len`, the output and the end. -/
theorem selPart_ok {EM kd : List Byte} {t : State} (hs : SCN s R EM kd t)
    (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa selPart t (Fin s R EM (amOf s kd) (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) (lenOf s EM kd)) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hs.amr.post
  have hsep := sep_lt EM (k := (s.gpr .r7).toNat) (by omega_using [hk64])
  have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
  refine WP.seq (WP.mono (validBlock_ok hc (outIn h hc (by omega_using [hk64])) (outIn h hc (by omega_using [hk64])) hs.r5 hs.r3 hs.al hs.r0 hs.r8
    (by omega_using [hk, hsep]) hR) fun t₁ ⟨⟨m₁, x11, x7, x5, x4, x6, x3, x12⟩, k₁⟩ => ?_)
  -- The values the block computed.
  have e0 : t.mem (s.gpr .r3 + BitVec.ofNat 64 0) = EM.getD 0 1 := by rw [← hc.em, bytes_getD' _ _ (by omega_using [hk64])]
  have e1 : t.mem (s.gpr .r3 + BitVec.ofNat 64 1) = EM.getD 1 1 := by rw [← hc.em, bytes_getD' _ _ (by omega_using [hk64])]
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM (s.gpr .r7).toNat).isSome
      ((firstZero EM (s.gpr .r7).toNat).getD 0) then s.gpr .r7 - BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0) -
        BitVec.ofNat 64 1 else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))) =
      BitVec.ofNat 64 (lenOf s EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat]; omega_using [hsep]),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hsep]
    · rfl
  have hlen : lenOf s EM kd ≤ (s.gpr .r7).toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega_arith
  simp only [e0, e1] at x5 x6 x3
  rw [eL] at x6 x3
  rw [show s.gpr .r7 - BitVec.ofNat 64 (lenOf s EM kd) = BitVec.ofNat 64 ((s.gpr .r7).toNat - lenOf s EM kd) by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hlen]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega_using [hlen]] at x3
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  -- `*msg_len`.
  refine WP.seq (WP.mono (outInit_ok h hc₁.fr3 x12) fun t₂ ⟨⟨m₂, x10, x9⟩, k₂⟩ => ?_)
  rw [x6] at m₂
  have hY : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩ (mlR s) := by rw [BitVec.add_zero]; exact fun _ h => h
  have F₂ : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₂ : Fr3 s R t₂ := hc₁.fr3.store h k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by revert r; decide)) (.inr rfl) hY F₂
  have bk : ∀ (X : Region), X.Disjoint (mlR s) → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY' => by rw [List.mem_singleton.mp hY']; exact hX.sub_right hY) hl hi, m₁]
  have hwo := h.wo; have h4 := h.h4
  have g : ∀ r, r ∉ [Reg.r10, .r9] → r ∉ [Reg.r12, .r11, .r7, .r10, .r9, .r4, .r5, .r6, .r3] → t₂.gpr r = t.gpr r :=
    fun r h₁ h₂ => (k₂.gpr r h₁).trans (k₁.gpr r h₂)
  have h0 : OInv s R (BitVec.ofNat 64 (lenOf s EM kd) &&& bm (decide (R ^^^ BitVec.ofNat 64 1 = 0))) EM (amOf s kd)
      (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ((s.gpr .r7).toNat - lenOf s EM kd) 0 t₂ :=
    { fr := hc₂
      ml := by rw [m₂, BitVec.add_zero, Mem.readW_writeW_self64]
      r9 := by rw [x9]; rfl
      r11 := by rw [k₂.gpr _ (by decide), x11, BitVec.add_zero]
      r10 := by rw [x10, BitVec.add_zero]
      r4 := by rw [k₂.gpr _ (by decide), x4]
      r5 := by rw [k₂.gpr _ (by decide), x5]
      r3 := by rw [k₂.gpr _ (by decide), x3]
      r0 := by rw [g _ (by decide) (by decide), hs.r0]
      r8 := by rw [g _ (by decide) (by decide), hs.r8]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [show s.gpr .r3 = (oR s).base from rfl, bk (oR s) h.om (by show (s.gpr .r4).toNat ≤ 2 ^ 64; omega_using []) j
          (by show j < (s.gpr .r4).toNat; omega_using [h4, hj]), show (oR s).base = s.gpr .r3 from rfl, ← hc.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [show scA s sAM = (⟨scA s sAM, (s.gpr .r7).toNat⟩ : Region).base from rfl,
          bk ⟨scA s sAM, (s.gpr .r7).toNat⟩ ((h.ms.symm.sub_left (sub_trans (scSub (by unfold sAM scrBytes; omega_using [hk]))
            (sc_sub h)))) (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega_using []) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .r7).toNat = amOf s kd := hs.amr.am
        rw [← ham, bytes_getD' _ _ hj] }
  refine WP.seq (WP.mono (selLoop_ok h (by omega_using [hk]) h0 (by rw [k₂.gpr _ (by decide), x7])) fun t₃ h₃ => ?_)
  refine WP.mono (finish_ok h₃.fr) fun u ⟨u3, ul, um, usp, urd, uwr, uh⟩ => ?_
  have hc₃ := h₃.fr
  exact ⟨⟨usp.trans hc₃.sp, urd.trans hc₃.rd, uwr.trans hc₃.wr, fun r hr => (uh r hr).trans (hc₃.hi r hr),
    um ▸ hc₃.mem, um ▸ hc₃.sl, um ▸ hc₃.r⟩, u3, ul, fun i hi => by rw [um]; exact h₃.done i hi,
    by rw [um]; exact h₃.ml⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
