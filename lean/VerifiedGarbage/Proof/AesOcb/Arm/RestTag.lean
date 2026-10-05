import VerifiedGarbage.Proof.AesOcb.Arm.Whole
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-OCB on ARMv7: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`, XORs the last
`r` bytes of the data with it (`xorLoop`) and adds their padding to the
checksum (`padCk`), before the XOR for `seal` and after it for `open`
(`rest_ok`); `tag d` writes `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ Sum` to
`W + d` (`tag_ok`), as on AArch64 (`Proof.AesOcb.AArch64.rest_ok`,
`Proof.AesOcb.AArch64.tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz pad)
open VG.Proof.Ocb (offAt blockAtMem_frame length_bytesAt)
open VG.Proof.AesGcm.Arm (below xorLoop_ok xorBytes LoopPre)

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    Proof.Ocb.bytesAt_append, xor_append_right _ _ _ (by rw [hl, length_bytesAt])]

/-- The last `r` bytes of the data, from offset `a`. -/
structure Tail (p : Prm) (a r : Nat) : Prop where
  fit : a + r ≤ p.n
  pos : 0 < r
  lt : r < 16

namespace Tail

variable {p : Prm} (L : Lay p) {a r : Nat} (T : Tail p a r)
include L T

theorem addr : State.addr (p.D + BitVec.ofNat 32 a) = State.addr p.D + BitVec.ofNat 64 a :=
  addr_add (by have := L.dw; have := T.fit; have := T.pos; omega)

theorem toNat : (p.D + BitVec.ofNat 32 a).toNat = p.D.toNat + a := by
  have := L.dw; have := T.fit; have := T.pos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (by omega)]

omit L in
theorem sub : Region.Sub ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ ⟨State.addr p.D, p.n⟩ :=
  Offset.sub_base _ T.fit

theorem w {d k : Nat} (h : d + k ≤ 2560) :
    (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
  (L.d_w' h).sub_left T.sub

end Tail

/-- What the head of `rest` leaves: `Offset_*` at `W + ofsO` and `Pad` at
`W + tmpO`. -/
structure RestHead (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem
  tmp : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
    ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem)
  saved : ∀ r ∈ keptRegs, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.seq (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO)) (encOne tmpO)) t
      (RestHead p t) := by
  have fw := L.ww
  have fk := L.kw
  refine WP.seq (WP.block_append (WP.mono (xorB_wp (s := t) (pb := .r11) (qb := .r10) (cb := .r11) (pd := ofsO)
    (qd := 240) (cd := ofsO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E.r11]; simp only [ofsO]; omega) (by rw [E.r10]; omega)
    (by rw [E.r11]; simp only [ofsO]; omega) (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [E.r10]; exact E.perm.kC (by decide)) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_))
  rw [E.r11, E.r10] at R₁
  have E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (copy16_wp (t := t₁) (W := State.addr p.W) (sO := ofsO) (dO := tmpO) (by rw [E₁.r11])
    (by decide) (by decide) (by rw [E₁.r11]; omega) (by decide) (by decide) (E₁.perm.wCR (by decide))
    (E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  have E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have kOW : (⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint ⟨State.addr p.K + BitVec.ofNat 64 240, 16⟩ :=
    (L.k_w' (by decide)).symm.sub_right (Offset.sub_base _ (by decide))
  have ofs₁ : blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem := by
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint kOW)]; rfl
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem, R₁.mem]
    exact ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp)).trans ((copyMem_frame _ _ _).mono (by simp))
  have tmp₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem := by
    rw [R₂.mem, blockAtMem_copy, ofs₁]
  refine WP.mono (encOne_ok L E₂ (d := tmpO) (by decide) (by decide)) fun t₃ C₃ => ?_
  have hs : sched p t₂.mem = sched p t.mem :=
    sched_mut L (fr₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact w_mut L (.inl (by decide)))
  refine ⟨C₃.env E₂, ?_, ?_, ?_, fun r hr => ?_, by rw [C₃.rd, R₂.rd, R₁.rd], by rw [C₃.wr, R₂.wr, R₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (C₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [blockAtMem_frame C₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm), R₂.mem, blockAtMem_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      ofs₁]
  · have := C₃.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, encF_ciph, tmp₂, hs]
  · rw [C₃.saved r hr, R₂.gpr r (fun h => by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h),
      R₁.gpr r (fun h => by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h)]

/-- `W + d ← (W + d) ⊕ (W + s)`. -/
theorem xorW_wp {p : Prm} (L : Lay p) {t : State} (E : Env p t) {s d : Nat} (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) :
    WP isa (.block (xorW s d)) t (Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.W + BitVec.ofNat 64 d)
      (State.addr p.W + BitVec.ofNat 64 d) (State.addr p.W + BitVec.ofNat 64 s)) t) := by
  have fw := L.ww
  have := xorB_wp (s := t) (pb := .r11) (qb := .r11) (cb := .r11) (pd := d) (qd := s) (cd := d) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (by rw [E.r11]; omega) (by rw [E.r11]; omega) (by rw [E.r11]; omega) (by rw [E.r11]; exact E.perm.wCR hd)
    (by rw [E.r11]; exact E.perm.wCR hs) (by rw [E.r11]; exact E.perm.wC hd)
  rw [E.r11] at this
  exact this

theorem xorW_val {p : Prm} (L : Lay p) (m : Mem) {s d : Nat} (h : s + 16 ≤ d ∨ d + 16 ≤ s) (hs : s + 16 ≤ 2560)
    (hd : d + 16 ≤ 2560) :
    blockAtMem (Proof.Cmac.xor4Mem m (State.addr p.W + BitVec.ofNat 64 d) (State.addr p.W + BitVec.ofNat 64 d)
      (State.addr p.W + BitVec.ofNat 64 s)) (State.addr p.W + BitVec.ofNat 64 d) =
      blockAtMem m (State.addr p.W + BitVec.ofNat 64 d) ^^^ blockAtMem m (State.addr p.W + BitVec.ofNat 64 s) :=
  blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (L.w_w (by omega) hd hs))

/-- `padCk`: the checksum with the padded `r` bytes at `D + a`. -/
theorem padCk_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {a r : Nat} (T : Tail p a r)
    (h4 : s.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : s.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa padCk s fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        pad (bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 a) r) ∧
      Others padRegs s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have := L.dw; have := T.fit; have := L.n_lt
  unfold padCk
  refine WP.seq (WP.mono (padTo_ok L E (S := p.D + BitVec.ofNat 32 a) (n := r) (d := t2O) T.pos T.lt (by decide)
    (by decide) h4 h5 (by rw [T.toNat L]; omega)
    (by rw [T.addr L]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d T.fit (by omega)))
    (by rw [T.addr L]; exact T.w L (by decide))) fun t₁ ⟨fr₁, b₁, O₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ := E.of_others O₁ sp₁ rd₁ wr₁
  refine WP.mono (xorW_wp L E₁ (s := t2O) (d := ckO) (by decide) (by decide)) fun t₂ R₂ => ?_
  refine ⟨?_, ?_, fun r hr => ?_, by rw [R₂.sp, sp₁], by rw [R₂.rd, rd₁], by rw [R₂.wr, wr₁]⟩
  · rw [R₂.mem]; exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  · rw [R₂.mem, xorW_val L _ (by decide) (by decide) (by decide), b₁, blockAtMem_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      T.addr L]
  · rw [R₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl <;> simp)), O₁ r hr]

/-- `xorPad`: the `r` bytes at `D + a` XORed with the first `r` bytes at
`W + tmpO`. -/
theorem xorPad_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {a r : Nat} (T : Tail p a r)
    (h4 : s.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : s.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem (State.addr p.D + BitVec.ofNat 64 a)
        (Spec.Ocb.xor (bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 a) r)
          (bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 tmpO) r)) ∧
      Others [.r0, .r1, .r2, .r3, .r12] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww; have := L.dw; have := T.fit; have := L.n_lt; have := T.lt
  have he : encodable (BitVec.ofNat 32 112) = true := by decide
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨_, by orun [he, E.r11, h4, h5], ?_⟩)
  refine WP.mono (xorLoop_ok _ (S := p.W + BitVec.ofNat 32 tmpO) (D := p.D + BitVec.ofNat 32 a) (n := r)
    ⟨by simp [gpr_setReg, tmpO], by simp [gpr_setReg, h4], by simp [gpr_setReg, h5], T.pos, by omega,
      by rw [L.wN (by decide)]; simp only [tmpO]; omega, by rw [T.toNat L]; omega,
      by simp only [rd_setReg, wr_setReg, L.wA (show tmpO < 2560 by decide)]; exact E.perm.wCR (by simp only [tmpO]; omega),
      by simp only [wr_setReg, T.addr L]; exact Proof.AesGcm.Arm.covers_off E.perm.d T.fit (by omega),
      by rw [T.addr L, L.wA (by decide)]; exact (T.w L (by simp only [tmpO]; omega)).symm⟩) fun t ⟨m, O⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [O.sp]; rfl, by rw [O.rd]; rfl, by rw [O.wr]; rfl⟩
  · rw [m]; simp only [mem_setReg, T.addr L, L.wA (show tmpO < 2560 by decide)]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [O.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_setReg, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (p : Prm) (a r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem
  out : bytesAt t'.mem (State.addr p.D + BitVec.ofNat 64 a) r = Spec.Ocb.xor
    (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r)
    (Spec.Ocb.toBytes (ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem)))
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (State.addr p.D + BitVec.ofNat 64 a) r)
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {a r : Nat} (T : Tail p a r)
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 a) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa (rest enc) t (RestPost enc p a r t) := by
  have := T.lt
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (restHead_ok L E) fun t₃ H => ?_))
  have h4₃ : t₃.gpr .r4 = p.D + BitVec.ofNat 32 a := by rw [H.saved _ (by decide), h4]
  have h5₃ : t₃.gpr .r5 = BitVec.ofNat 32 r := by rw [H.saved _ (by decide), h5]
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => T.w L h
  have dH : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact (L.bd.sub_right T.sub).symm
  have dT : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
    Proof.Cmac.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r) (Spec.Ocb.toBytes ys)).length = r :=
    fun ys => by simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r →
      Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] m (writeBytes m (State.addr p.D + BitVec.ofNat 64 a) xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have xP : ∀ u : State, bytesAt u.mem (State.addr p.D + BitVec.ofNat 64 a) r =
        bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r →
      blockAtMem u.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
        blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem (State.addr p.D + BitVec.ofNat 64 a)
        (Spec.Ocb.xor (bytesAt u.mem (State.addr p.D + BitVec.ofNat 64 a) r)
          (bytesAt u.mem (State.addr p.W + BitVec.ofNat 64 tmpO) r))) (State.addr p.D + BitVec.ofNat 64 a) r =
        Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r) (Spec.Ocb.toBytes
          (ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega), ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  have ck₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok L E₃ T h4₃ h5₃) fun t₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.of_others g₄ sp₄ rd₄ wr₄
    have fr₄ : Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t₃.mem t₄.mem := by
      rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄ T (by rw [g₄ _ (by decide), h4₃]) (by rw [g₄ _ (by decide), h5₃]))
      fun t₅ ⟨fr₅, ck₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
      Proof.Cmac.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.of_others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L E₃ T h4₃ h5₃) fun t₄ ⟨fr₄, ck₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.of_others g₄ sp₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 a) r = bytesAt t₃.mem (State.addr p.D + BitVec.ofNat 64 a) r :=
      Proof.Cmac.bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (xorPad_ok L E₄ T (by rw [g₄ _ (by decide), h4₃]) (by rw [g₄ _ (by decide), h5₃]))
      fun t₅ ⟨m₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t₄.mem t₅.mem := by
      rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.of_others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (p : Prm) (d : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] t.mem t'.mem
  val : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 d) =
    ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO)
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag d) t (TagPost p d t) := by
  have fw := L.ww
  have hd' : d = 0 ∨ d = 176 := hd
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region)],
        (⟨State.addr p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  unfold tag
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (copy16_wp (t := t) (W := State.addr p.W) (sO := ckO)
    (dO := tmpO) (by rw [E.r11]) (by decide) (by decide) (by rw [E.r11]; omega) (by decide) (by decide)
    (E.perm.wCR (by decide)) (E.perm.wC (by decide))) fun t₁ R₁ => ?_)))
  have E₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (xorW_wp L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)) fun t₂ R₂ => ?_
  have E₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  refine WP.mono (xorW_wp L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)) fun t₃ R₃ => ?_
  have E₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact copyMem_frame _ _ _
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem := by
    rw [R₂.mem]; exact fr₁.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  have fr₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := by
    rw [R₃.mem]; exact fr₂.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  have tmp₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO) := by
    rw [R₃.mem, xorW_val L _ (by decide) (by decide) (by decide), R₂.mem, xorW_val L _ (by decide) (by decide)
      (by decide), ← R₂.mem, blockAtMem_frame fr₂ (tW (by decide) (by decide)), R₁.mem, blockAtMem_copy, ← R₁.mem,
      blockAtMem_frame fr₁ (tW (by decide) (by decide))]
  have hs : sched p t₃.mem = sched p t.mem :=
    sched_mut L (fr₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_mut L (.inl (by decide)))
  refine WP.seq (WP.mono (encOne_ok L E₃ (d := tmpO) (by decide) (by decide)) fun t₄ C₄ => ?_)
  have E₄ := C₄.env E₃
  refine WP.block_append (WP.mono (copy16_wp (t := t₄) (W := State.addr p.W) (sO := tmpO) (dO := d)
    (by rw [E₄.r11]) (by decide) (by omega) (by rw [E₄.r11]; omega) (by decide) (by omega) (E₄.perm.wCR (by decide))
    (E₄.perm.wC (by omega))) fun t₅ R₅ => ?_)
  have E₅ := E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr
  refine WP.mono (xorW_wp L E₅ (s := sumO) (d := d) (by decide) (by omega)) fun t₆ R₆ => ?_
  have tmp₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ldO)) := by
    have := C₄.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, encF_ciph, tmp₃, hs]
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (by simp only [sumO]; omega) (by decide) (by omega)
  have dCall : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP],
      (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  refine ⟨E₅.of_others R₆.gpr R₆.sp R₆.rd R₆.wr, ?_, ?_,
    by rw [R₆.rd, R₅.rd, C₄.rd, R₃.rd, R₂.rd, R₁.rd], by rw [R₆.wr, R₅.wr, C₄.wr, R₃.wr, R₂.wr, R₁.wr]⟩
  · rw [R₆.mem, R₅.mem]
    refine (((fr₃.mono (by simp)).trans (C₄.frame.sub fun r hr => ?_)).trans
      ((copyMem_frame _ _ _).mono (by simp))).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [R₆.mem, xorW_val L _ (by simp only [sumO]; omega) (by decide) (by omega), R₅.mem, blockAtMem_copy, tmp₄,
      blockAtMem_frame (copyMem_frame _ _ _) dD, blockAtMem_frame C₄.frame dCall,
      blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.Arm
