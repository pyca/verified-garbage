module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Frame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: the setup and the encoding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignSetup.lean`, `SignEnc.lean`): the saves and
`encode`'s arguments (`setup_ok`, into `AtEnc`), and the encoding of the hash
value into `EM` in the frame, with 1 in `a0`, or 0 if it fails
(`enc_ok`, into `AtAft`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign
open VG.Proof.RsaPkcs1Sig.RISCV64 (EPre EPost EOut encodeId encode_ok)

/-- `out`, `n`, `k`, `e` and `e_len`, which `s1`–`s5` keep. -/
abbrev SMid (S : List Region) (s t : State) : Prop :=
  Mid S s (s.gpr .a0) (s.gpr .a2) (s.gpr .a3) (s.gpr .a4) (s.gpr .a5) t

/-- The hash function's number. -/
abbrev hid (s : State) : Nat := ((s.gpr .a6).setWidth 32).toNat

/-- The hash value. -/
abbrev hashOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat

/-- The encoding of the hash value, if it succeeds. -/
abbrev encOut (s : State) : Option (List Byte) := encodeId (hid s) (hashOf s) (s.gpr .a3).toNat

/-- `EM`, in the frame. -/
abbrev emR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .a3).toNat⟩

theorem em_sub {s : State} (h : SPre s) : Region.Sub (emR s) (kR s) :=
  frame_sub s (by have := h.k2; unfold oEM frameBytes; omega)

theorem zext_toNat (x : BitVec 64) : (x <<< 32 >>> 32).toNat = (x.setWidth 32).toNat := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  omega

/-- At `encode`. -/
structure AtEnc (s t : State) : Prop extends SMid [] s t where
  a1 : t.gpr .a1 = fb s + BitVec.ofNat 64 oEM
  a2 : t.gpr .a2 = s.gpr .a3
  a3 : (t.gpr .a3).toNat = hid s
  a4 : t.gpr .a4 = s.gpr .a7
  a5 : t.gpr .a5 = stackArg s 0
  t6 : t.gpr .t6 = stackArgAddr s 0

/-- Our stack argument `j`, in memory changed only in the stack. -/
theorem arg_frame {s : State} (h : SPre s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 13) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : SPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 13) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

theorem arg_al {s : State} (h : SPre s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := s.sp.isLt; have := h.sp16
  omega

theorem setup_ok {s : State} (h : SPre s) :
    WP isa (.block (save ++ encArgs)) (allocd frameBytes s) (AtEnc s) := by
  have hfa := fb_al h
  rw [save_eq, List.append_assoc]
  refine save_ok (s := s) (u := allocd frameBytes s) rfl rfl (by omega) (Frame.refl _ _) (fun _ _ => rfl) fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => kv.gpr r hr
  simp only [moves, encArgs, argBase, List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_addSp (imm := frameBytes) (fun v₆ o₆ e₆ => wp_addi (imm := oEM) fun v₇ o₇ e₇ =>
    wp_mov fun v₈ o₈ e₈ => wp_sll fun v₉ o₉ e₉ => wp_srl fun v₁₀ o₁₀ e₁₀ => wp_mov fun v₁₁ o₁₁ e₁₁ => ?_)
    (by decide)
  have O : Only [.s1, .s2, .s3, .s4, .s5, .t6, .a1, .a2, .a3, .a3, .a4] v v₁₁ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans
      (o₁₀.trans o₁₁)))))))))).mono
  have sp₅ : v₅.sp = fb s := by rw [(o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).sp, kv.sp]; rfl
  have t6₁₁ : v₁₁.gpr .t6 = stackArgAddr s 0 := by
    rw [o₁₁.get .t6, o₁₀.get .t6, o₉.get .t6, o₈.get .t6, o₇.get .t6, e₆, sp₅, stackArgAddr_fb]; rfl
  have rd₁₁ : v₁₁.rd = s.rd := by rw [O.rd, kv.rd]; rfl
  refine wp_ld (a := stackArgAddr s 0) (by rw [t6₁₁, BitVec.add_zero]) (arg_al h 0)
    (arg_in h rd₁₁ (j := 0) (by decide)) fun w o e => wp_nil ?_
  rw [O.mem, arg_frame h fv (j := 0) (by decide)] at e
  have P : Only [.s1, .s2, .s3, .s4, .s5, .t6, .a1, .a2, .a3, .a4, .a5] v w := (O.trans o).mono
  exact {
    sp := by rw [P.sp, kv.sp]; rfl
    rd := by rw [P.rd, kv.rd]; rfl
    wr := by rw [P.wr, kv.wr]; rfl
    s1 := by
      rw [o.get .s1, o₁₁.get .s1, o₁₀.get .s1, o₉.get .s1, o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1,
        o₄.get .s1, o₃.get .s1, o₂.get .s1, e₁, gv .a0 (by decide)]
    s2 := by
      rw [o.get .s2, o₁₁.get .s2, o₁₀.get .s2, o₉.get .s2, o₈.get .s2, o₇.get .s2, o₆.get .s2, o₅.get .s2,
        o₄.get .s2, o₃.get .s2, e₂, o₁.get .a2, gv .a2 (by decide)]
    s3 := by
      rw [o.get .s3, o₁₁.get .s3, o₁₀.get .s3, o₉.get .s3, o₈.get .s3, o₇.get .s3, o₆.get .s3, o₅.get .s3,
        o₄.get .s3, e₃, o₂.get .a3, o₁.get .a3, gv .a3 (by decide)]
    s4 := by
      rw [o.get .s4, o₁₁.get .s4, o₁₀.get .s4, o₉.get .s4, o₈.get .s4, o₇.get .s4, o₆.get .s4, o₅.get .s4,
        e₄, o₃.get .a4, o₂.get .a4, o₁.get .a4, gv .a4 (by decide)]
    s5 := by
      rw [o.get .s5, o₁₁.get .s5, o₁₀.get .s5, o₉.get .s5, o₈.get .s5, o₇.get .s5, o₆.get .s5, e₅,
        o₄.get .a5, o₃.get .a5, o₂.get .a5, o₁.get .a5, gv .a5 (by decide)]
    hi := fun r hr => by rw [P.gpr r (by revert r; decide), gv r (by revert r; decide)]
    mem := by rw [P.mem]; exact fv
    sv := by rw [P.mem]; exact sv
    a1 := by
      rw [o.get .a1, o₁₁.get .a1, o₁₀.get .a1, o₉.get .a1, o₈.get .a1, e₇, o₆.get .t0, o₅.get .t0, o₄.get .t0,
        o₃.get .t0, o₂.get .t0, o₁.get .t0, v0]
    a2 := by
      rw [o.get .a2, o₁₁.get .a2, o₁₀.get .a2, o₉.get .a2, e₈, o₇.get .s3, o₆.get .s3, o₅.get .s3, o₄.get .s3,
        e₃, o₂.get .a3, o₁.get .a3, gv .a3 (by decide)]
    a3 := by
      rw [o.get .a3, o₁₁.get .a3, e₁₀, e₉, o₈.get .a6, o₇.get .a6, o₆.get .a6, o₅.get .a6, o₄.get .a6,
        o₃.get .a6, o₂.get .a6, o₁.get .a6, gv .a6 (by decide), zext_toNat]
    a4 := by
      rw [o.get .a4, e₁₁, o₁₀.get .a7, o₉.get .a7, o₈.get .a7, o₇.get .a7, o₆.get .a7, o₅.get .a7, o₄.get .a7,
        o₃.get .a7, o₂.get .a7, o₁.get .a7, gv .a7 (by decide)]
    a5 := e
    t6 := by rw [o.get .t6, t6₁₁] }

/-- A byte of `EM` is in our frame. -/
theorem em_in {s : State} (h : SPre s) (rs : List Region) {i : Nat} (hi : i < (s.gpr .a3).toNat) :
    InRegions (frR s :: rs) (fb s + BitVec.ofNat 64 oEM + BitVec.ofNat 64 i) 1 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact in_fr s rs (by have := h.k2; unfold oEM frameBytes; omega)

theorem AtEnc.epre {s t : State} (h : SPre s) (A : AtEnc s t) : EPre t (hid s) (s.gpr .a3).toNat := by
  refine ⟨A.a3, by rw [A.a2], h.k2, fun i hi => ?_, fun j hj => ?_, fun j hj i hi e => ?_⟩
  · rw [A.a1, A.wr]; exact em_in h _ hi
  · rw [A.a4, A.rd, h.hrd]
    rw [A.a5] at hj
    exact ⟨dR s, List.mem_append_left _ (by simp), Offset.contains_base _ (by omega) (by have := h.wd; omega)⟩
  · rw [A.a5] at hj
    rw [A.a4, A.a1] at e
    have c1 : (dR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega) (by have := h.wd; omega)
    have c2 : (kR s).Contains (s.gpr .a7 + BitVec.ofNat 64 j) 1 := by
      rw [e, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact frame_contains s (by have := h.k2; unfold oEM frameBytes; omega)
    exact h.kd _ c2 c1

theorem encodeId_len {x : Nat} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After `encode`. -/
structure AtAft (s u : State) : Prop extends SMid [] s u where
  t6 : u.gpr .t6 = stackArgAddr s 0
  enc : match encOut s with
    | some em => u.gpr .a0 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .a3).toNat = em
    | none => u.gpr .a0 = 0

theorem enc_ok {s t : State} (h : SPre s) (A : AtEnc s t) :
    WP isa Impl.RsaPkcs1Sig.RISCV64.encode t (AtAft s) := by
  have hk := h.k2
  have hH : Spec.Rsa.bytesAt t.mem (t.gpr .a4) (t.gpr .a5).toNat = hashOf s := by
    rw [A.a4, A.a5]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kd.symm)
      (by have := h.wd; omega)
  refine WP.mono (encode_ok (A.epre h)) fun u ⟨kp, eo⟩ => ?_
  rw [hH] at eo
  have hf : Frame [emR s] t.mem u.mem ∧ (match encOut s with
      | some em => u.gpr .a0 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .a3).toNat = em
      | none => u.gpr .a0 = 0) := by
    show Frame _ _ _ ∧ match encOut s with | some em => _ | none => _
    unfold encOut
    revert eo
    cases he : encodeId (hid s) (hashOf s) (s.gpr .a3).toNat with
    | none => intro eo; simp only [EOut] at eo; exact ⟨eo.2 ▸ Frame.refl _ _, eo.1⟩
    | some em =>
      intro eo
      have hl := encodeId_len he
      simp only [EOut] at eo
      rw [A.a1] at eo
      refine ⟨by rw [eo.2]; show Frame [⟨_, _⟩] _ _; rw [← hl]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _,
        eo.1, ?_⟩
      rw [eo.2, ← hl]; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ (by omega)
  obtain ⟨hf, he⟩ := hf
  have hm := A.frameMem (f := oEM) (n := (s.gpr .a3).toNat) (by decide) (by unfold oEM frameBytes; omega) hf
  exact ⟨A.keep kp hm.1 hm.2, (kp.get .t6).trans A.t6, he⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
