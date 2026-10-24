module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecSel
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
theorem Fr3.store {s : State} (h : DPre s) {R : BitVec 64} {t u : State} (hc : Fr3 s R t) (hrd : u.rd = t.rd)
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

theorem Fr3.regs {s : State} {R : BitVec 64} {t u : State} (hc : Fr3 s R t) (hk : Keep [.r0, .r3, .r4, .r5, .r6,
    .r7, .r8, .r9, .r10, .r11, .r12] t u) (hm : u.mem = t.mem) : Fr3 s R u :=
  ⟨hk.sp.trans hc.sp, hk.rd.trans hc.rd, hk.wr.trans hc.wr,
    fun r hr => (hk.gpr r (by revert r; decide)).trans (hc.hi r hr), hm ▸ hc.mem, hm ▸ hc.sl, hm ▸ hc.r⟩

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
variable {s : State} (h : DPre s)
include h

theorem outW {t : State} (hwr : t.wr = fr s :: s.wr) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions t.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hwr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega) (by omega)⟩

theorem selLoop_ok {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 63) {t : State} (h0 : OInv s R MLV EM AM v ok kl 0 t) (h7 : t.gpr .r7 = s.gpr .r7) :
    WP isa selLoop t (OInv s R MLV EM AM v ok kl (s.gpr .r7).toNat) := by
  have hk := h.k2
  have hk64 := h.k1
  have hwo := h.wo
  rw [h.h4] at hwo
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (by omega) (by omega) (OInv s R MLV EM AM v ok kl)
    (fun i hi u hu _ => ?_) h0 (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hc := hu.fr
  have he : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r11, BitVec.add_zero]
    obtain ⟨r, hr, hcr⟩ := outW h hc.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r10, BitVec.add_zero, Offset.add_add]
    exact scInR h hc.wr (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega)
  rw [selBody_eq, WP.block_append_iff]
  refine WP.mono (selA_ok he ha hu.r0) fun w ⟨⟨wm, w6⟩, kw⟩ => ?_
  have hw : InRegions w.wr (w.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [kw.wr, kw.gpr _ (by decide), hu.r11, BitVec.add_zero]; exact outW h hc.wr hi
  refine WP.mono (selB_ok hw) fun x ⟨⟨xm, x9, x11, x10, x7⟩, kx⟩ => ⟨?_, ?_⟩
  · have hb : (w.gpr .r6).setWidth 8 = outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
      rw [w6, hu.r5, hu.r4, hu.r9, hu.r3, hu.r8, hu.r11, hu.r10, BitVec.add_zero, BitVec.add_zero,
        hu.todo i (Nat.le_refl _) hi, hu.am i hi, outB_eq _ _ hkl (by omega)]
    rw [hb, kw.gpr _ (by decide), hu.r11, BitVec.add_zero, wm] at xm
    have hf : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsub : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]; exact Offset.sub_base _ (by omega)
    have hne : ∀ j, j ≠ i → j < (s.gpr .r7).toNat → s.gpr .r3 + BitVec.ofNat 64 j ≠ s.gpr .r3 + BitVec.ofNat 64 i :=
      fun j hj hjk => Offset.add_ofNat_ne _ (by omega) (by omega) hj
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
      · rw [write1_ne' _ _ (hne j (by omega) (by omega)), hu.done j hj]
      · exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _
    · intro j hj hjk
      rw [xm, write1_ne' _ _ (hne j (by omega) hjk), hu.todo j (by omega) hjk]
    · intro j hj
      rw [hf.bytes (R := ⟨scA s sAM, (s.gpr .r7).toNat⟩) (fun X hX => by
        rw [List.mem_singleton.mp hX]
        exact ((h.os.sub_left hsub).sub_right (sc_sub h)).symm.sub_left (scSub (by unfold sAM scrBytes; omega)))
        (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega) hj, hu.am j hj]
  · rw [x7, kw.gpr _ (by decide)]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
