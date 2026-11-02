module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Sel
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: writing the output

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecOut.lean`): the output, byte by byte
(`selBody_ok`, `selLoop_ok`): byte `i` of `out` is
`outByte v ok kl i EM[i] AM[i]`, with `Fr3` (`Mid` with `out`, `*msg_len` and
`scratch` written, and the result in `s7`) kept.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

theorem write1_ne' (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by bv_omega)

/-- After the scan: `Mid` with `out`, `*msg_len` and `scratch` written, and the
result `R` in `s7`. -/
structure Fr3 (s : State) (R : BitVec 64) (u : State) : Prop extends Mid [oR s, mlR s, sR s] s u where
  r : u.gpr .s7 = R

theorem Post.fr3 {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hp : Post s R EM t) : Fr3 s R t :=
  ⟨hp.toMid.of (fun _ _ => rfl) rfl rfl rfl (hp.mem.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩) hp.sv, hp.r⟩

section
variable {s : State} (h : DPre s) {R : BitVec 64}
include h

/-- Writes of `out` or `*msg_len`, and of registers `Fr3` does not keep. -/
theorem Fr3.store {t u : State} (hc : Fr3 s R t) {rs : List Reg} (o : Kept rs t u) {X : Region}
    (hX : X = oR s ∨ X = mlR s) {Y : Region} (hY : Region.Sub Y X) (hf : Frame [Y] t.mem u.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Fr3 s R u := by
  have hk : Region.Disjoint (kR s) Y := by
    rcases hX with rfl | rfl
    · exact h.ko.sub_right hY
    · exact h.km.sub_right hY
  refine ⟨hc.toMid.keep o (hc.mem.trans (hf.sub fun r hr => ?_)) (hc.sv.frame hf fun p hp r hr => ?_) hrs,
    (o.gpr _ h7).trans hc.r⟩
  · rw [List.mem_singleton.mp hr]
    rcases hX with rfl | rfl
    · exact ⟨_, by simp, hY⟩
    · exact ⟨_, by simp, hY⟩
  · rw [List.mem_singleton.mp hr]
    have := saved_offs p hp
    exact hk.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega))

omit h in
theorem Fr3.only {t u : State} (hc : Fr3 s R t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Fr3 s R u :=
  ⟨hc.toMid.only o hrs, (o.get _ h7).trans hc.r⟩

end

/-! ## A byte of the output -/

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

/-- The byte `selBody` writes. -/
abbrev selByte (t : State) : Byte :=
  ((((t.mem (t.gpr .t1)).setWidth 64 ^^^ (t.mem (t.gpr .a0)).setWidth 64) &&& t.gpr .a4) ^^^
      (t.mem (t.gpr .a0)).setWidth 64) &&&
    ((((0 : BitVec 64) - ((t.gpr .a1 - t.gpr .a5) >>> 63)) ^^^ t.gpr .a7) &&& t.gpr .a3) |>.setWidth 8

theorem selBody_ok {t : State} (he : InRegions (t.rd ++ t.wr) (t.gpr .t1) 1)
    (ha : InRegions (t.rd ++ t.wr) (t.gpr .a0) 1) (hw : InRegions t.wr (t.gpr .t1) 1) (h6 : t.gpr .a6 = 0) :
    WP isa (.block selBody) t fun u => (u.mem = t.mem.write (t.gpr .t1) 1 (selByte t) ∧
      u.gpr .a1 = t.gpr .a1 + BitVec.ofNat 64 1 ∧ u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 1 ∧
      u.gpr .a0 = t.gpr .a0 + BitVec.ofNat 64 1 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1) ∧
      Kept [.t6, .a2, .a1, .t1, .a0, .t2] t u := by
  unfold selBody
  mrun [he, ha, hw, h6]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  obtain ⟨a, b, c, d, e, f⟩ : r ≠ .t6 ∧ r ≠ .a2 ∧ r ≠ .a1 ∧ r ≠ .t1 ∧ r ≠ .a0 ∧ r ≠ .t2 := by simpa using hr
  simp only [a, b, c, d, e, f, ite_false]

/-! ## The loop -/

/-- After `i` bytes of the output. -/
structure OInv (s : State) (R MLV : BitVec 64) (EM AM : List Byte) (v ok : Bool) (kl : Nat) (i : Nat) (t : State) :
    Prop extends Fr3 s R t where
  ml : t.mem.readW (s.gpr .a2) 64 = MLV
  a1 : t.gpr .a1 = BitVec.ofNat 64 i
  t1 : t.gpr .t1 = s.gpr .a0 + BitVec.ofNat 64 i
  a0 : t.gpr .a0 = scA s sAM + BitVec.ofNat 64 i
  a3 : t.gpr .a3 = bm ok
  a4 : t.gpr .a4 = bm v
  a5 : t.gpr .a5 = BitVec.ofNat 64 kl
  a6 : t.gpr .a6 = 0
  a7 : t.gpr .a7 = BitVec.allOnes 64
  done : ∀ j < i, t.mem (s.gpr .a0 + BitVec.ofNat 64 j) = outByte v ok kl j (EM.getD j 1) (AM.getD j 0)
  todo : ∀ j, i ≤ j → j < (s.gpr .a4).toNat → t.mem (s.gpr .a0 + BitVec.ofNat 64 j) = EM.getD j 1
  am : ∀ j < (s.gpr .a4).toNat, t.mem (scA s sAM + BitVec.ofNat 64 j) = AM.getD j 0

section
variable {s : State} (h : DPre s)
include h

theorem outW {t : State} (hwr : t.wr = frR s :: s.wr) {i : Nat} (hi : i < (s.gpr .a4).toNat) :
    InRegions t.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h1] at this
  exact ⟨oR s, by rw [hwr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]
    exact Offset.contains_base _ (by omega) (by omega)⟩

theorem selLoop_ok {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 63) {t : State} (h0 : OInv s R MLV EM AM v ok kl 0 t) (h2 : t.gpr .t2 = s.gpr .a4) :
    WP isa selLoop t (OInv s R MLV EM AM v ok kl (s.gpr .a4).toNat) := by
  have hk := h.k2
  have hk64 := h.k1
  have hwo := h.wo
  rw [h.h1] at hwo
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (by omega) (by omega) (OInv s R MLV EM AM v ok kl)
    (fun i hi u hu _ => ?_) h0 (by rw [h2, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have he : InRegions (u.rd ++ u.wr) (u.gpr .t1) 1 := by
    rw [hu.t1]
    obtain ⟨r, hr, hcr⟩ := outW h hu.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .a0) 1 := by
    rw [hu.a0, Offset.add_add]
    obtain ⟨r, hr, hcr⟩ := scIn h hu.wr (a := sAM + i) (l := 1) (by unfold sAM scrBytes; omega)
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have hw : InRegions u.wr (u.gpr .t1) 1 := by rw [hu.t1]; exact outW h hu.wr hi
  refine WP.mono (selBody_ok he ha hw hu.a6) fun x ⟨⟨xm, x1, xt1, x0, x2⟩, kx⟩ => ⟨?_, ?_⟩
  · have hb : selByte u = outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
      unfold selByte
      rw [hu.a4, hu.a3, hu.a1, hu.a5, hu.a7, hu.t1, hu.a0, hu.todo i (Nat.le_refl _) hi, hu.am i hi,
        outB_eq _ _ hkl (by omega)]
    rw [hb, hu.t1] at xm
    have hf : Frame [⟨s.gpr .a0 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsub : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]; exact Offset.sub_base _ (by omega)
    have hne : ∀ j, j ≠ i → j < (s.gpr .a4).toNat → s.gpr .a0 + BitVec.ofNat 64 j ≠ s.gpr .a0 + BitVec.ofNat 64 i :=
      fun j hj hjk => Offset.add_ofNat_ne _ (by omega) (by omega) hj
    refine ⟨hu.toFr3.store h kx (.inl rfl) hsub hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
        rw [List.mem_singleton.mp hX]; exact (h.om.sub_left hsub).symm) (by decide), hu.ml]
    · rw [x1, hu.a1, ← BitVec.ofNat_add]
    · rw [xt1, hu.t1, Offset.add_add]
    · rw [x0, hu.a0, Offset.add_add]
    · rw [kx.gpr _ (by decide), hu.a3]
    · rw [kx.gpr _ (by decide), hu.a4]
    · rw [kx.gpr _ (by decide), hu.a5]
    · rw [kx.gpr _ (by decide), hu.a6]
    · rw [kx.gpr _ (by decide), hu.a7]
    · intro j hj
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [write1_ne' _ _ (hne j (by omega) (by omega)), hu.done j hj]
      · exact VG.Proof.Bignum.RISCV64.write1_self _ _ _
    · intro j hj hjk
      rw [xm, write1_ne' _ _ (hne j (by omega) hjk), hu.todo j (by omega) hjk]
    · intro j hj
      rw [hf.bytes (R := ⟨scA s sAM, (s.gpr .a4).toNat⟩) (fun X hX => by
        rw [List.mem_singleton.mp hX]
        exact (h.os.sub_left hsub).symm.sub_left (scSub h (by unfold sAM scrBytes; omega)))
        (by show (s.gpr .a4).toNat ≤ 2 ^ 64; omega) hj, hu.am j hj]
  · rw [x2]

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
