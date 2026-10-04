import VerifiedGarbage.Proof.AesOcb.AArch64.XorPad

/-!
# AES-OCB on AArch64: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`
(`restHead_ok`), XORs the last bytes with `Pad` (`xorPad_ok`) and adds the
padded plaintext to the checksum (`padCk_ok`), in the order of `seal` or
`open` (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.Ocb (length_bytesAt blockAtMem_frame)

/-- The callee-saved registers but `x30` are unchanged. -/
abbrev Saved (t t' : State) : Prop := ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r

theorem saved_of {t t' : State} {rs : List Reg} (h : ∀ r, r ∉ rs → t'.gpr r = t.gpr r)
    (hd : ∀ r ∈ rs, r ∉ preserved := by decide) : Saved t t' :=
  fun r hr _ => h r fun h' => hd r h' hr

theorem Saved.trans {t₁ t₂ t₃ : State} (h₁ : Saved t₁ t₂) (h₂ : Saved t₂ t₃) : Saved t₁ t₃ :=
  fun r hr h30 => (h₂ r hr h30).trans (h₁ r hr h30)

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `x23`. -/
theorem padCk_ok {K W : Addr} (L : Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {S : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (h23 : s.gpr .x23 = S) (h24 : s.gpr .x24 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (padTo_ok h19 hw hr hr' (by decide) h23 h24 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ ⟨fr₁, pad₁, g₁, sp₁, rd₁, wr₁⟩ => ?_)
  have h19₁ : t₁.gpr .x19 = W := by rw [g₁ _ (by decide), h19]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [wr₁]; exact Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := t2O) (d := ckO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (by rw [rd₁]; exact Proof.AesGcm.AArch64.in_left (ww (by decide)))
    (by rw [rd₁]; exact Proof.AesGcm.AArch64.in_left (ww (by decide))) (ww (by decide)) (ww (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_,
    fun q hq => ?_, by rw [B₂.sp, sp₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [B₂.val, pad₁, blockAtMem_frame fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [B₂.gpr q (by simp [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]),
      g₁ q (by simp [padRegs, hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2])]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (K W D : Addr) (R n : Nat) (SP : Addr) (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
    t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  tmp : blockAtMem t'.mem (W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State}
    (E : Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.seq (.block (xor16 .x20 240 ofsO ++ copy16 ofsO tmpO)) (callBlocks (callees v).enc (oneBlock tmpO))) t
      (RestHead K W D R n SP t) := by
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .x20) (a := 240) (d := ofsO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) (by decide) (by decide) E₁.x19
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₂.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega)]
  refine WP.seq (WP.of_runBlock ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₂ hR
    (oneBlock_ok E₂.x19 tmpO (by decide)) (dstW L E₂.perm (d := tmpO) (n := 1) (by decide))) fun t₃ P₃ => ?_
  refine ⟨E₂.of_saved P₃.saved P₃.sp P₃.rd P₃.wr, ?_, ?_, ?_, ?_, by rw [P₃.rd, B₂.rd, B₁.rd],
    by rw [P₃.wr, B₂.wr, B₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · rw [P₃.enc0, B₂.val, B₁.val]
    show ctxCiph t₂.mem K R _ = _
    rw [cK]; rfl
  · exact (saved_of B₁.gpr).trans ((saved_of B₂.gpr).trans P₃.saved)

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    Proof.Ocb.bytesAt_append, xor_append_right _ _ _ (by rw [hl, length_bytesAt])]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (K W D : Addr) (R n : Nat) (SP : Addr) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)))
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State}
    (E : Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16)
    (h23 : t.gpr .x23 = P) (h24 : t.gpr .x24 = BitVec.ofNat 64 r) (hP : DBuf K W t P r) :
    WP isa (rest (callees v) enc) t (RestPost enc K W D R n SP P r t) := by
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (restHead_ok v L E hR) fun t₃ H => ?_))
  have h23₃ : t₃.gpr .x23 = P := by rw [H.saved _ (by decide) (by decide), h23]
  have h24₃ : t₃.gpr .x24 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide) (by decide), h24]
  have hP₃ : DBuf K W t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact dW (by decide)
  have dT : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := Proof.Cmac.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (W + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes
          (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have ck₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok E₃.x19 E₃.perm.w hr hr' h23₃ h24₃ hP₃) fun t₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄.x19 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h23₃])
      (by rw [g₄ _ (by decide), h24₃]) (by rw [rd₄, wr₄]; exact hS₃) hP.w) fun t₅ ⟨fr₅, ck₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := Proof.Cmac.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((saved_of g₄).trans (saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L E₃.x19 E₃.perm.w hr hr' h23₃ h24₃ hS₃ hP.w)
      fun t₄ ⟨fr₄, ck₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := Proof.Cmac.bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (xorPad_ok E₄.x19 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h23₃])
      (by rw [g₄ _ (by decide), h24₃]) (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((saved_of g₄).trans (saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (K W D : Addr) (R n : Nat) (SP : Addr) (d : Nat) (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
    t.mem t'.mem
  val : blockAtMem t'.mem (W + BitVec.ofNat 64 d) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 sumO)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State}
    (E : Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (callees v) d) t (TagPost K W D R n SP d t) := by
  have hd' : d = 0 ∨ d = 128 := hd
  have hd8 : d % 8 = 0 ∧ d + 8 < 32768 := by omega
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := t) (a := ckO) (d := tmpO) (by decide) (by decide) E.x19
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := ofsO) (d := tmpO) (by decide) (by decide) E₁.x19
    E₁.x19 (by decide) (by decide) (by decide) (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide))
    (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .x19) (a := ldO) (d := tmpO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  have tmp₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₃.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₃ hR
    (oneBlock_ok E₃.x19 tmpO (by decide)) (dstW L E₃.perm (d := tmpO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ := E₃.of_saved P₄.saved P₄.sp P₄.rd P₄.wr
  have tmp₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) := by
    rw [P₄.enc0, tmp₃, ← cK]; rfl
  obtain ⟨t₅, run₅, B₅⟩ := copy16_ok (s := t₄) (a := tmpO) (d := d) (by decide) hd8 E₄.x19
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega)) (E₄.perm.wW (by omega))
  have E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  obtain ⟨t₆, run₆, B₆⟩ := xor16_ok (s := t₅) (b := .x19) (a := sumO) (d := d) (by decide) hd8 E₅.x19 E₅.x19
    (by decide) (by decide) (by decide) (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega))
    (E₅.perm.wW (by omega))
  refine WP.of_runBlock ⟨t₆, by rw [runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega)
  have dCall : ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨W + BitVec.ofNat 64 512, 2048⟩],
      (⟨W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨E₅.others B₆.gpr B₆.sp B₆.rd B₆.wr, ?_, ?_,
    (saved_of B₁.gpr).trans ((saved_of B₂.gpr).trans ((saved_of B₃.gpr).trans (Saved.trans P₄.saved
      ((saved_of B₅.gpr).trans (saved_of B₆.gpr))))),
    by rw [B₆.rd, B₅.rd, P₄.rd, B₃.rd, B₂.rd, B₁.rd], by rw [B₆.wr, B₅.wr, P₄.wr, B₃.wr, B₂.wr, B₁.wr]⟩
  · refine (((fr₃.mono (by simp)).trans (P₄.frame.sub fun r hr => ?_)).trans (B₅.frame.mono (by simp))).trans
      (B₆.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [B₆.val, B₅.val, tmp₄, blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega) (by decide)),
      blockAtMem_frame P₄.frame dCall, blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.AArch64
