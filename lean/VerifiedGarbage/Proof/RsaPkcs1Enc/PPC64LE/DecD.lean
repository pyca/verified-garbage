module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecPost
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: `D = I2OSP(d, k)`

The result of the private-key operation to its slot (`dPtrs₁`), `k` zeros at
`scratch + sD` (`zeroLoop`), and `d` copied to their end (`dPtrs₂`,
`copyLoop`): `dBuild_ok`, from `AtD` to `DB`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

/-- The result's 32 bits, zero-extended. -/
def rOf (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem rOf_lt (x : BitVec 64) : (rOf x ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  have : (rOf x).toNat < 2 ^ 32 := by simp only [rOf, BitVec.toNat_setWidth]; omega
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 32) this (by decide)) (by decide)

/-- After `j` zeros of `D`. -/
structure ZInv (s : State) (R : BitVec 64) (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post s R EM t
  r12 : t.gpr .r12 = fb s
  r11 : t.gpr .r11 = scA s (sD + j)
  r0 : t.gpr .r0 = 0
  z : ∀ i < j, t.mem (scA s (sD + i)) = 0

theorem write1_ne' (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by bv_omega)

theorem readW_oR {s : State} {m : Mem} (v : BitVec 64) {d : Nat}
    (hd : d + 8 ≤ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR ∨ oLr ≤ d) (hn : d + 8 ≤ frameBytes) :
    (m.writeW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) v).readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ (hd.imp id fun h' => by unfold oLr Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR at *; omega)
    (by unfold frameBytes at hn; omega) (by decide)) (by decide)

/-- The private-key operation's result to its slot, the zeros' address and `k`. -/
theorem dPtrs₁_inv {s u : State} (h : DPre s) (A : AtD s u) :
    WP isa (.block dPtrs₁) u fun t =>
      ZInv s (rOf (u.gpr .r3)) (Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat) 0 t ∧ t.gpr .r9 = s.gpr .r7 := by
  have hsp : u.sp = fb s := A.sp
  have hR : InRegions u.wr (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 8 :=
    slotOut A.wr (by decide) (by decide)
  have hS : InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 oScr) 8 := slotIn A.wr (by decide) (by decide)
  have hK : InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 oK) 8 := slotIn A.wr (by decide) (by decide)
  have rS := fun v => (readW_oR (s := s) (m := u.mem) v (d := oScr) (.inl (by decide)) (by decide)).trans A.sl.scr
  have rK := fun v => (readW_oR (s := s) (m := u.mem) v (d := oK) (.inl (by decide)) (by decide)).trans A.sl.k
  have c1 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 := by decide
  have c2 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have c3 : oScr < 2 ^ 15 := by decide
  have c4 : oScr % 4 = 0 := by decide
  have c5 : oK < 2 ^ 15 := by decide
  have c6 : oK % 4 = 0 := by decide
  have c7 : sD < 2 ^ 15 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r12, .r11, .r9, .r0] (Q := fun t =>
    t.mem = u.mem.writeW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (rOf (u.gpr .r3)) ∧
      t.gpr .r12 = fb s ∧ t.gpr .r11 = scA s sD ∧ t.gpr .r9 = s.gpr .r7 ∧ t.gpr .r0 = 0) ?_ rfl)
    fun t ⟨⟨tm, t12, t11, t9, t0⟩, kt⟩ => ?_
  · unfold dPtrs₁ scr
    prun [fp, exec_addSp0, hsp, BitVec.ushiftRight_zero, c1, c2, c3, c4, c5, c6, c7, hR, hS, hK, rS, rK,
      exec_addi (show Reg.r11 ≠ .r0 by decide) c7]
    exact ⟨rfl, rfl⟩
  have hf : Frame [⟨fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR, 8⟩] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hO : Region.Disjoint (outR s) ⟨fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR, 8⟩ := by
    rw [outR_eq h]; exact h.ko.symm.sub_right (frame_sub s (by decide))
  refine ⟨⟨⟨⟨kt.sp.trans hsp, kt.rd.trans A.rd, kt.wr.trans A.wr,
    fun r hr => (kt.gpr r (by revert r; decide)).trans (A.hi r hr), A.mem.trans (hf.sub fun r hr => ?_),
    A.sl.words hf fun r hr d hd hn => ?_⟩, ?_, ?_, rOf_lt _⟩, t12, ?_, t0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, t9⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s (by decide)⟩
  · rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (hd.imp id fun h' => by unfold oLr Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR at *; omega)
      (by unfold frameBytes at hn; omega) (by decide)
  · rw [tm, Mem.readW_writeW_self64]
  · exact bytes_of_frame (s := u) hf (fun X hX => by rw [List.mem_singleton.mp hX]; exact hO)
      (by have := h.wo; rw [h.h4] at this; omega)
  · rw [t11, Nat.add_zero]

theorem zBody_ok {t : State} (hw : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.stb .r0 .r11 0, .addi .r11 .r11 1, .subi .r9 .r9 1]) t fun u =>
      (u.mem = t.mem.write (t.gpr .r11 + BitVec.ofNat 64 0) 1 ((t.gpr .r0).setWidth 8) ∧
        u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧ u.gpr .r9 = t.gpr .r9 - BitVec.ofNat 64 1) ∧
      Keep [.r11, .r9] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c : (0 : Nat) < 2 ^ 15 := by decide
  prun [exec_stb (show Reg.r11 ≠ .r0 by decide) c hw, exec_addi (show Reg.r11 ≠ .r0 by decide) (show 1 < 2 ^ 15 by decide)]

theorem zeroLoop_ok {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hz : ZInv s R EM 0 t)
    (h9 : t.gpr .r9 = s.gpr .r7) : WP isa zeroLoop t (ZInv s R EM (s.gpr .r7).toNat) := by
  have hk := h.k2
  have hk1 := h.k1
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r9) (by omega) (by omega) (ZInv s R EM)
    (fun j hj u hu _ => ?_) hz (by rw [h9, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hin : InRegions u.wr (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r11, BitVec.add_zero]
    exact scIn h hu.post.wr (by unfold sD scrBytes; omega)
  refine WP.mono (zBody_ok hin) fun w ⟨⟨hm, h11, h9'⟩, kw⟩ => ⟨?_, h9'⟩
  have hm' : w.mem = u.mem.write (scA s (sD + j)) 1 0 := by rw [hm, hu.r11, hu.r0, BitVec.add_zero]; rfl
  have hf : Frame [⟨scA s (sD + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hu.post.step h kw.rd kw.wr kw.sp (fun r hr => kw.gpr r (by revert r; decide)) hf fun r hr => ?_,
    (kw.gpr _ (by decide)).trans hu.r12, ?_, (kw.gpr _ (by decide)).trans hu.r0, fun i hi => ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega))
  · rw [h11, hu.r11, Offset.add_add, Nat.add_assoc]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have := h.ws; have := scr_le h
      rw [write1_ne' _ _ (Offset.add_ofNat_ne _ (by unfold sD scrBytes at *; omega)
        (by unfold sD scrBytes at *; omega) (by omega)), hu.z i hi]
    · exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _

theorem x11_eq (p : Addr) (a : Nat) (k dl : BitVec 64) (h : dl.toNat ≤ k.toNat) :
    p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 (a + (k.toNat - dl.toNat)) := by
  have ek : k = BitVec.ofNat 64 k.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ed : dl = BitVec.ofNat 64 dl.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 a + BitVec.ofNat 64 k.toNat -
    BitVec.ofNat 64 dl.toNat by rw [← ek, ← ed], Offset.add_add, Offset.add_ofNat_sub _ (by omega),
    Nat.add_sub_assoc h]

/-- After the zeros of `D` and `j` bytes of `d`. -/
structure CInv (s : State) (R : BitVec 64) (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post s R EM t
  r12 : t.gpr .r12 = fb s
  r10 : t.gpr .r10 = s.gpr .r10 + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = scA s (sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + j)
  z : ∀ i < (s.gpr .r7).toNat - (stackArg s 0).toNat, t.mem (scA s (sD + i)) = 0
  c : ∀ i < j, t.mem (scA s (sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + i)) = s.mem (s.gpr .r10 + BitVec.ofNat 64 i)

theorem dPtrs₂_inv {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {t : State}
    (hz : ZInv s R EM (s.gpr .r7).toNat t) :
    WP isa (.block dPtrs₂) t fun u => CInv s R EM 0 u ∧ u.gpr .r9 = stackArg s 0 := by
  have hc := hz.post
  have c1 : oD < 2 ^ 15 ∧ oD % 4 = 0 := by decide
  have c2 : oDl < 2 ^ 15 ∧ oDl % 4 = 0 := by decide
  have c3 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c4 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c5 : sD < 2 ^ 15 := by decide
  have i1 : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oD) 8 := slotIn hc.wr (by decide) (by decide)
  have i2 : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oDl) 8 := slotIn hc.wr (by decide) (by decide)
  have i3 : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oScr) 8 := slotIn hc.wr (by decide) (by decide)
  have i4 : InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 oK) 8 := slotIn hc.wr (by decide) (by decide)
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r10, .r9, .r11, .r8] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r10 = s.gpr .r10 ∧ u.gpr .r9 = stackArg s 0 ∧
      u.gpr .r11 = stackArg s 13 + BitVec.ofNat 64 sD + s.gpr .r7 - stackArg s 0) ?_ rfl)
    fun u ⟨⟨um, u10, u9, u11⟩, ku⟩ => ?_
  · unfold dPtrs₂ scr
    prun [hz.r12, c1, c2, c3, c4, i1, i2, i3, i4, hc.sl.d, hc.sl.dl, hc.sl.scr, hc.sl.k,
      exec_addi (show Reg.r11 ≠ .r0 by decide) c5]
  refine ⟨⟨hc.regs ku.rd ku.wr ku.sp um fun r hr => ku.gpr r (by revert r; decide),
    (ku.gpr _ (by decide)).trans hz.r12, by rw [u10, BitVec.add_zero], ?_, fun i hi => ?_,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩, u9⟩
  · rw [u11, x11_eq _ _ _ _ (h.d2), Nat.add_zero]
  · rw [um]; exact hz.z i (by omega)

theorem cBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .r10 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.lbz .r0 .r10 0, .stb .r0 .r11 0, .addi .r10 .r10 1, .addi .r11 .r11 1, .subi .r9 .r9 1]) t
      fun u => (u.mem = t.mem.write (t.gpr .r11 + BitVec.ofNat 64 0) 1 (t.mem (t.gpr .r10 + BitVec.ofNat 64 0)) ∧
        u.gpr .r10 = t.gpr .r10 + BitVec.ofNat 64 1 ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
        u.gpr .r9 = t.gpr .r9 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r10, .r11, .r9] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  prun [exec_lbz (show Reg.r10 ≠ .r0 by decide) c hr,
    exec_stb (s := t.write .r0 ((t.mem.read (t.gpr .r10 + BitVec.ofNat 64 0) 1).setWidth 64))
      (show Reg.r11 ≠ .r0 by decide) c (by exact hw),
    exec_addi (show Reg.r10 ≠ .r0 by decide) c1, exec_addi (show Reg.r11 ≠ .r0 by decide) c1,
    VG.Proof.Bignum.PPC64LE.read_one']

theorem copyLoop_ok {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : CInv s R EM 0 t)
    (h9 : t.gpr .r9 = stackArg s 0) : WP isa copyLoop t (CInv s R EM ((stackArg s 0).toNat)) := by
  have hk := h.k2
  have hdk := h.d2
  have hd1 := h.d1
  have hwd := h.wd
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r9) (by omega) (by omega) (CInv s R EM)
    (fun j hj u hu _ => ?_) hc (by rw [h9, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hin : InRegions u.wr (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r11, BitVec.add_zero]
    exact scIn h hu.post.wr (by unfold sD scrBytes; omega)
  have hrd : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [hu.r10, BitVec.add_zero]
    exact ⟨dR s, by rw [hu.post.rd, h.hrd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hb : u.mem (s.gpr .r10 + BitVec.ofNat 64 j) = s.mem (s.gpr .r10 + BitVec.ofNat 64 j) :=
    hu.post.mem.bytes (R := dR s) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.kd.symm
      · exact h.od.symm
      · exact h.ds) (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega) hj
  refine WP.mono (cBody_ok hrd hin) fun w ⟨⟨hm, h10, h11, h9'⟩, kw⟩ => ⟨?_, h9'⟩
  have hm' : w.mem = u.mem.write (scA s (sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + j)) 1 (s.mem (s.gpr .r10 + BitVec.ofNat 64 j)) := by
    rw [hm, hu.r11, hu.r10, BitVec.add_zero, BitVec.add_zero, hb]
  have hf : Frame [⟨scA s (sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hne : ∀ a, a < sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + j → scA s a ≠ scA s (sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + j) := fun a ha =>
    Offset.add_ofNat_ne _ (by unfold sD scrBytes at *; omega) (by unfold sD scrBytes at *; omega) (by omega)
  refine ⟨hu.post.step h kw.rd kw.wr kw.sp (fun r hr => kw.gpr r (by revert r; decide)) hf fun r hr => ?_,
    (kw.gpr _ (by decide)).trans hu.r12, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega))
  · rw [h10, hu.r10, Offset.add_add]
  · rw [h11, hu.r11, Offset.add_add, Nat.add_assoc]
  · rw [hm', write1_ne' _ _ (hne _ (by omega)), hu.z i hi]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write1_ne' _ _ (hne _ (by omega)), hu.c i hi]
    · exact VG.Proof.Bignum.PPC64LE.write1_self _ _ _

/-- After `dBuild`: `R` in its slot, `EM` in `out`, and `D = I2OSP(d, k)` at `scratch + sD`. -/
structure DB (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  post : Post s R EM t
  D : Spec.Rsa.bytesAt t.mem (scA s sD) (s.gpr .r7).toNat =
    Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r10) ((stackArg s 0).toNat))) (s.gpr .r7).toNat

theorem cinv_db {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {u : State}
    (hu : CInv s R EM ((stackArg s 0).toNat) u) : DB s R EM u := by
  refine ⟨hu.post, ?_⟩
  have hdk := h.d2
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by simp [Spec.Rsa.bytesAt]; exact hdk)]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine List.ext_getElem (by simp; omega) fun i h₁ _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < (s.gpr .r7).toNat - (stackArg s 0).toNat
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate, Offset.add_add, hu.z i hi]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem_map, List.getElem_range]
    have := hu.c (i - ((s.gpr .r7).toNat - (stackArg s 0).toNat)) (by simp at h₁; omega)
    rw [Offset.add_add, show sD + i = sD + ((s.gpr .r7).toNat - (stackArg s 0).toNat) + (i - ((s.gpr .r7).toNat - (stackArg s 0).toNat)) by omega, this]

theorem dBuild_ok {s u : State} (h : DPre s) (A : AtD s u) :
    WP isa dBuild u (DB s (rOf (u.gpr .r3)) (Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat)) := by
  refine WP.seq (WP.mono (dPtrs₁_inv h A) fun _ ⟨h₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok h h₁ e₁) fun _ h₂ => ?_)
  refine WP.seq (WP.mono (dPtrs₂_inv h h₂) fun _ ⟨h₃, e₃⟩ => ?_)
  exact WP.mono (copyLoop_ok h h₃ e₃) fun _ hu => cinv_db h hu

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
