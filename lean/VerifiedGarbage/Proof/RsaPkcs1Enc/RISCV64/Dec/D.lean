module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Call
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: `D = I2OSP(d, k)`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecD.lean`): from the call on, `Post s R EM`
holds: `Mid` with `out` and `scratch` written, `R` (the private-key
operation's result, zero-extended) in `s7` and `EM` in `out`, which the
result relates to the private-key operation (`PrivRel`, `privRel_of`).
`dBuild_ok`: `k` zeros at `scratch + sD`, then `d` at their end, which is
`I2OSP(OS2IP(d), k)` (`DB`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## `scratch` -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `scratch + a`. -/
abbrev scA (s : State) (a : Nat) : Addr := stackArg s 13 + BitVec.ofNat 64 a

/-- The bytes of `scratch` the function uses after the call. -/
def scrBytes : Nat := 2576

section
variable {s : State} (h : DPre s)
include h

theorem scr_le : scrBytes ≤ (stackArg s 14).toNat * 8 := by
  have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords scrBytes at *; omega

theorem scSub {a l : Nat} (ha : a + l ≤ scrBytes) : Region.Sub ⟨scA s a, l⟩ (sR s) :=
  Offset.sub_base _ (by have := scr_le h; omega)

theorem scContains {a l : Nat} (ha : a + l ≤ scrBytes) : (sR s).Contains (scA s a) l :=
  Offset.contains_base _ (by have := scr_le h; omega) (by unfold scrBytes at ha; omega)

theorem scIn {t : State} (hwr : t.wr = frR s :: s.wr) {a l : Nat} (ha : a + l ≤ scrBytes) :
    InRegions t.wr (scA s a) l := by
  rw [hwr, h.hwr]; exact ⟨sR s, by simp, scContains h ha⟩

theorem scCov {t : State} (hwr : t.wr = frR s :: s.wr) {a l : Nat} (ha : a + l ≤ scrBytes) :
    Covers [⟨scA s a, l⟩] t.wr :=
  Covers.one (scIn h hwr ha)

theorem scByte {t : State} (hwr : t.wr = frR s :: s.wr) {a n : Nat} (ha : a + n ≤ scrBytes) :
    ∀ i < n, InRegions t.wr (scA s a + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact scIn h hwr (by omega)

end

/-! ## After the call -/

/-- The result of the private-key operation `o`, zero-extended to `R`, with
`EM` in `out`. -/
def PrivRel (k : Nat) (o : Spec.Rsa.Outcome) (R : BitVec 64) (EM : List Byte) : Prop :=
  match o with
  | .ok y => R = 1 ∧ EM = y
  | .invalid => R = 0 ∧ EM = List.replicate k 0
  | .fault => R = 2 ∧ EM = List.replicate k 0

/-- The private-key operation of the input. -/
abbrev privOp (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)

/-- The low word of `x`, zero-extended. -/
abbrev zx (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = zx x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  omega

theorem privRel_of {s u : State} (A : AtRet s u) :
    PrivRel (s.gpr .a4).toNat (privOp s) (zx (u.gpr .a0)) (Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat) := by
  have := A.out
  change Spec.Rsa.writtenOutcome _ _ _ _ (privOp s) at this
  unfold PrivRel
  cases hc : privOp s <;> rw [hc] at this <;> exact ⟨by unfold zx; rw [this.1]; rfl, this.2⟩

/-- From the call on: `Mid` with `out` and `scratch` written, `R` in `s7` and
`EM` in `out`. -/
structure Post (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Mid [oR s, sR s] s t where
  r : t.gpr .s7 = R
  em : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat = EM

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

/-- `out` misses `scratch`. -/
theorem oSc {a l : Nat} (ha : a + l ≤ scrBytes) :
    Region.Disjoint ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ ⟨scA s a, l⟩ := by
  have := h.os.sub_right (scSub h ha); simp only [oR, h.h1] at this; exact this

/-- The callees' frames, below ours. -/
abbrev lowR (s : State) : Region :=
  ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩

omit h in
theorem slot_low (s : State) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ (lowR s) := by
  simp only [lowR]
  rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)

/-- `Post` is kept by code writing registers `Mid` does not keep but `s7`,
`scratch` and the callees' frames. -/
theorem Post.keep {t w : State} (hp : Post s R EM t) {rs : List Reg} (o : Kept rs t w) {ws : List Region}
    (hf : Frame ws t.mem w.mem) (hs : ∀ r ∈ ws, Region.Sub r (sR s) ∨ Region.Sub r (lowR s))
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Post s R EM w := by
  have cs := callee_sub s
  refine ⟨hp.toMid.keep o (hp.mem.trans (hf.sub fun r hr => ?_)) (hp.sv.frame hf fun q hq r hr => ?_) hrs,
    (o.gpr _ h7).trans hp.r, ?_⟩
  · rcases hs r hr with hr' | hr'
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), hr'⟩
    · exact ⟨_, List.mem_cons_self .., sub_trans hr' cs⟩
  · have := saved_offs q hq
    rcases hs r hr with hr' | hr'
    · exact (h.ks.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega))).sub_right hr'
    · exact (slot_low s (by unfold oEnd frameBytes at *; omega)).sub_right hr'
  · rw [← hp.em]
    exact bytes_of_frame (s := t) hf (fun r hr => by
      rcases hs r hr with hr' | hr'
      · have := h.os.sub_right hr'; simp only [oR, h.h1] at this; exact this
      · have := (h.ko.symm.sub_right cs).sub_right hr'; simp only [oR, h.h1] at this; exact this)
      (by have := h.wo; have := h.h1; omega)


/-! ## `D` -/

omit h in
theorem W_nil (s : State) : W s [] s :=
  ⟨Kept.refl _ _, (writeBytes_nil _ _).symm, by rw [List.length_nil, BitVec.add_zero]⟩

omit h in
theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

omit h in
/-- Writing over the same bytes. -/
theorem writeBytes_writeBytes (m : Mem) (q : Addr) {xs ys : List Byte} (hl : xs.length = ys.length) :
    writeBytes (writeBytes m q xs) q ys = writeBytes m q ys := by
  funext a
  simp only [writeBytes]
  by_cases h1 : (a - q).toNat < ys.length
  · simp only [h1, ite_true]
  · simp only [h1, ite_false, hl]

omit h in
/-- `k` zeros, then `ys` written over their end. -/
theorem zeros_then (m : Mem) (q : Addr) {k : Nat} {ys : List Byte} (hl : ys.length ≤ k) (hk : k < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes m q (List.replicate k 0))
      (q + BitVec.ofNat 64 (k - ys.length)) ys) q k = List.replicate (k - ys.length) 0 ++ ys := by
  have e : List.replicate k (0 : Byte) = List.replicate (k - ys.length) 0 ++ List.replicate ys.length 0 := by
    rw [List.replicate_append_replicate, Nat.sub_add_cancel hl]
  have e2 : writeBytes m q (List.replicate k 0) = writeBytes (writeBytes m q (List.replicate (k - ys.length) 0))
      (q + BitVec.ofNat 64 (k - ys.length)) (List.replicate ys.length 0) := by
    have := writeBytes_append m q (List.replicate (k - ys.length) (0 : Byte)) (List.replicate ys.length 0)
      (by simp; omega)
    rw [List.length_replicate] at this
    rw [e, ← this]
  have e3 : writeBytes (writeBytes m q (List.replicate (k - ys.length) 0)) (q + BitVec.ofNat 64 (k - ys.length)) ys =
      writeBytes m q (List.replicate (k - ys.length) 0 ++ ys) := by
    have := writeBytes_append m q (List.replicate (k - ys.length) (0 : Byte)) ys (by simp; omega)
    rwa [List.length_replicate] at this
  rw [e2, writeBytes_writeBytes _ _ (by simp), e3]
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes m q (List.replicate (k - ys.length) 0 ++ ys) (by simp; omega)
  rwa [List.length_append, List.length_replicate, Nat.sub_add_cancel hl] at this

/-- The private exponent's bytes. -/
abbrev dBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat

/-- After `dBuild`: `D` at `scratch + sD`. -/
structure DB (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Post s R EM t where
  D : Spec.Rsa.bytesAt t.mem (scA s sD) (s.gpr .a4).toNat = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dBytes s)) (s.gpr .a4).toNat

theorem dBuild_ok {u : State} (A : AtRet s u) :
    WP isa dBuild u (DB s (zx (u.gpr .a0)) (Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat)) := by
  have hk := h.k2
  have hk1 := h.k1
  have hd1 := h.d1
  have hd2 := h.d2
  unfold dBuild dZeros
  refine WP.seq (wp_sll fun u₁ o₁ e₁ => wp_srl fun u₂ o₂ e₂ => wp_addi (imm := sD) (fun u₃ o₃ e₃ =>
    wp_mov fun u₄ o₄ e₄ => wp_li (imm := 0) (by decide) fun w o₅ e₅ => wp_nil ?_) (by decide))
  have O : Only [.s7, .a1, .t5, .t0] u w := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have P : Post s (zx (u.gpr .a0)) (Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat) w :=
    ⟨A.toMid.only O, by rw [o₅.get .s7, o₄.get .s7, o₃.get .s7, e₂, e₁, zext_eq], by rw [O.mem]⟩
  have w1 : w.gpr .a1 = scA s sD := by rw [o₅.get .a1, o₄.get .a1, e₃, o₂.get .s0, o₁.get .s0, A.s0]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a4).toNat := by
    rw [o₅.get .t5, e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, A.s1, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a4).toNat := fun i hi => by
    rw [w1]; exact scByte h P.wr (a := sD) (n := (s.gpr .a4).toNat) (by unfold sD scrBytes; omega) i hi
  refine WP.seq (WP.mono (fillLoop_ok hb (by omega) (acc := []) (by omega) (by simp) (W_nil w) 0
    (by rw [e₅]; rfl) w5) fun t₁ ⟨⟨K₁, m₁, _⟩, _⟩ => ?_)
  rw [List.nil_append, w1] at m₁
  have P₁ := P.keep h K₁ (ws := [⟨scA s sD, (List.replicate (s.gpr .a4).toNat (0 : Byte)).length⟩])
    (by rw [m₁]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact .inl (scSub h (by unfold sD scrBytes; omega)))
  unfold dCopy
  refine WP.seq (wp_mov fun v₁ p₁ f₁ => wp_mov fun v₂ p₂ f₂ => wp_addi (imm := sD) (fun v₃ p₃ f₃ =>
    wp_add fun v₄ p₄ f₄ => wp_sub fun w₂ p₅ f₅ => wp_nil ?_) (by decide))
  have Q : Only [.a4, .a5, .a1] t₁ w₂ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  have P₂ := P₁.keep h Q.keep (ws := []) (by rw [Q.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
  have x4 : w₂.gpr .a4 = s.gpr .a7 := by rw [p₅.get .a4, p₄.get .a4, p₃.get .a4, p₂.get .a4, f₁, P₁.s4]
  have x5 : w₂.gpr .a5 = BitVec.ofNat 64 (stackArg s 0).toNat := by
    rw [p₅.get .a5, p₄.get .a5, p₃.get .a5, f₂, p₁.get .s5, P₁.s5, ← gpr_ofNat]
  have x1 : w₂.gpr .a1 = scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) := by
    rw [f₅, f₄, f₃, p₂.get .s0, p₁.get .s0, P₁.s0, p₃.get .s1, p₂.get .s1, p₁.get .s1, P₁.s1,
      p₄.get .s5, p₃.get .s5, p₂.get .s5, p₁.get .s5, P₁.s5]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (stackArg s 13).isLt; have := (s.gpr .a4).isLt; have := (stackArg s 0).isLt
    unfold sD; omega
  have hb₂ : Buf w₂ (stackArg s 0).toNat := fun i hi => by
    rw [x1]
    exact scByte h P₂.wr (a := sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) (n := (stackArg s 0).toNat)
      (by unfold sD scrBytes; omega) i hi
  have hr : ∀ j < (stackArg s 0).toNat, InRegions (w₂.rd ++ w₂.wr) (w₂.gpr .a4 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [x4, P₂.rd, h.hrd]
      exact ⟨dR s, List.mem_append_left _ (by simp), Offset.contains_base _ (by omega) (by have := h.wd; omega)⟩
  have hdd : ∀ j < (stackArg s 0).toNat, ∀ i < (stackArg s 0).toNat,
      w₂.gpr .a4 + BitVec.ofNat 64 j ≠ w₂.gpr .a1 + BitVec.ofNat 64 i := fun j hj i hi e => by
    rw [x4, x1, BitVec.add_assoc, BitVec.ofNat_add_ofNat] at e
    have c1 : (dR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega) (by have := h.wd; omega)
    have c2 : (sR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 := by
      rw [e]; exact scContains h (by unfold sD scrBytes; omega)
    exact h.ds _ c1 c2
  refine WP.mono (copyLoop_ok hb₂ (by omega) (acc := []) (n := (stackArg s 0).toNat) h.d1 (by simp) (W_nil w₂)
    rfl x5 hr hdd) fun t ⟨K, m, _⟩ => ?_
  rw [List.nil_append, x1, x4] at m
  have hD : Spec.Rsa.bytesAt w₂.mem (s.gpr .a7) (stackArg s 0).toNat = dBytes s := by
    exact bytes_of_frame (s := s) P₂.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.kd.symm
      · exact h.od.symm
      · exact h.ds) (by have := h.wd; omega)
  rw [hD] at m
  have hl : (dBytes s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
  refine ⟨P₂.keep h K (ws := [⟨scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat), (dBytes s).length⟩])
    (by rw [m]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, hl]; exact .inl (scSub h (by unfold sD scrBytes; omega))), ?_⟩
  rw [m, Q.mem, m₁, Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [hl]; omega)]
  have e : scA s (sD + (s.gpr .a4).toNat - (stackArg s 0).toNat) =
      scA s sD + BitVec.ofNat 64 ((s.gpr .a4).toNat - (dBytes s).length) := by
    rw [hl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
  rw [e]
  exact zeros_then _ _ (by rw [hl]; omega) (by omega)

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
