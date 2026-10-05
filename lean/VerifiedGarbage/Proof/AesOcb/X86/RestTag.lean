import VerifiedGarbage.Proof.AesOcb.X86.Whole

/-!
# AES-OCB on x86: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum (`padCk_ok`) and XORs `P_*`
with `Pad` (`xorPad_ok`), and for `open` XORs `C_*` with `Pad` and adds the
padded result to the checksum (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph ctxLstar)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot xorLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32 length_bytesAt XorPre XorPost xorLoop_ok)

/-- `r` bytes of the data at `P` (in `esi`), `0 < r < 16`. -/
structure RBuf (p : Prm) (s : State) (P : BitVec 32) (r : Nat) : Prop where
  fit : P.toNat + r ≤ 2 ^ 32
  w : (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  stk : (stk p).Disjoint ⟨w64 P, r⟩
  wr : Covers [⟨w64 P, r⟩] s.wr
  inm : InMut p [⟨w64 P, r⟩]

theorem RBuf.of_eq {p : Prm} {s s' : State} {P : BitVec 32} {r : Nat} (h : RBuf p s P r) (hwr : s'.wr = s.wr) :
    RBuf p s' P r := ⟨h.fit, h.w, h.stk, by rw [hwr]; exact h.wr, h.inm⟩

theorem RBuf.sbuf {p : Prm} {s : State} {P : BitVec 32} {r : Nat} (h : RBuf p s P r) : SBuf p s P r :=
  ⟨h.fit, h.w, Proof.AesGcm.X86.covers_left h.wr⟩

/-- `xorPad`: the `r` bytes at `P` (in `esi`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {P : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (hsi : s.gpr .esi = P) (hcnt : slotv s.mem p.W restO = BitVec.ofNat 32 r) (hP : RBuf p s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem (w64 P)
        (Spec.Ocb.xor (bytesAt s.mem (w64 P) r) (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 tmpO) r)) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  simp only [slotv_eq] at hcnt
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .edi (.reg .esi), .mov .edx (.reg .ebp),
      .alu .add .edx (imm tmpO), .mov .ecx (slot restO)] s = some s₁ ∧ s₁.gpr .edi = P ∧
      s₁.gpr .edx = p.W + BitVec.ofNat 32 tmpO ∧ s₁.gpr .ecx = BitVec.ofNat 32 r ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hsi, hcnt], by gregs [hsi], by gregs [E.ebp], by gregs [hcnt],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have xp : XorPre s₁ (p.W + BitVec.ofNat 32 tmpO) P r := by
    refine ⟨dx₁, di₁, cx₁, hr, by omega, ?_, hP.fit, ?_, by rw [wr₁]; exact hP.wr, ?_⟩
    · rw [L.nW (by decide)]; have := L.ww; simp only [tmpO]; omega
    · rw [aT, rd₁, wr₁]; exact E.perm.wCR (d := tmpO) (n := r) (by simp only [tmpO]; omega)
    · rw [aT]; exact (hP.w.sub_right (Lay.wSub (by simp only [tmpO]; omega))).symm
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (xorLoop_ok s₁ xp) fun t P' => ⟨by rw [P'.mem, m₁, aT]; rfl, fun r h₁ h₂ h₃ h₄ h₅ => by
    rw [P'.other r h₁ h₂ h₅ h₄ h₃, g₁ r h₃ h₄ h₅], by rw [P'.rd, rd₁], by rw [P'.wr, wr₁]⟩

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `esi`. -/
theorem padCk_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {S : BitVec 32} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W restO = BitVec.ofNat 32 r) (hS : SBuf p s S r) :
    WP isa padCk s fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) =
        blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem (w64 S) r) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (padTo_ok L E (d := t2O) (cO := restO) hr hr' (by decide) (by decide) (.inr (by decide))
    hsi hcnt hS) fun t₁ ⟨fr₁, pad₁, g₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (frame_toMut fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := t2O) (d := ckO) (by decide) (by decide)
    (.inr (by decide))
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (xorMem16_frame _ _ _ _ _).mono (by simp)
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans f₂, ?_,
    fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁, g₁ r h₁ h₂ h₃ h₄], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [m₂, xorMem16_block, pad₁, Proof.Ocb.blockAtMem_frame fr₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] t.mem t'.mem
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
  tmp : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.seq (.block ([.mov .ebx (slot ctxO)] ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO))
      (callBlocks (callees v).enc (oneBlock tmpO))) t (RestHead p t) := by
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  have E₁ : Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ofsO) (by decide) (by decide)
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  have E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := copy16_ok L E₂ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact copyMem16_frame _ _ _ _ _
  have E₃ : Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide), E₂.ebp]) (by rw [g₃ _ (by decide), E₂.esp]) rd₃ wr₃
    (frame_toMut f₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := by
    rw [← m₁]; exact (f₂.mono (by simp)).trans (f₃.mono (by simp))
  have ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [m₂, xorMem16_block, m₁]; rfl
  have ofs₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [Proof.Ocb.blockAtMem_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_⟩)
  refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  refine ⟨P₄.env, (fr₃.mono (by simp)).trans ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [P₄.rd, rd₃, rd₂, rd₁],
    by rw [P₄.wr, wr₃, wr₂, wr₁]⟩
  · have F := P₄.frame
    rw [aT, show 16 * 1 = 16 from rfl] at F
    exact F.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  · rw [Proof.Ocb.blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm), ofs₃]
  · have := P₄.enc (i := 0) (by decide)
    rw [aT, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, ctxCiph_mut L (frame_toMut fr₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact inMut_w p (.inl (by decide))), m₃, copyMem16_block, ofs₂]
  · rw [P₄.gpr r h₁ h₂ h₃ h₄, g₃ r h₁, g₂ r h₁, g₁ r h₂]

/-- What `rest` writes. -/
abbrev restR (p : Prm) (P : BitVec 32) (r : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p, ⟨w64 P, r⟩]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (p : Prm) (P : BitVec 32) (r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (restR p P r) t.mem t'.mem
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
  out : bytesAt t'.mem (w64 P) r = Spec.Ocb.xor (bytesAt t.mem (w64 P) r)
    (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
      (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))))
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) (w64 P) r)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (hsi : t.gpr .esi = P) (hcnt : slotv t.mem p.W restO = BitVec.ofNat 32 r)
    (hP : RBuf p t P r) :
    WP isa (rest (callees v) enc) t (RestPost enc p P r t) := by
  unfold rest
  refine seq_assoc (WP.seq (WP.mono (restHead_ok v L E) fun t₃ H => ?_))
  have si₃ : t₃.gpr .esi = P := by rw [H.gpr _ (by decide) (by decide) (by decide) (by decide), hsi]
  have hP₃ : RBuf p t₃ P r := hP.of_eq H.wr
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p], (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
  have dT : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dWW : ∀ {a d : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 → d + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h₁ h₂ q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h₁ h₂
  have dTW : ∀ {a : Nat}, (a + 16 ≤ t2O ∨ t2O + 16 ≤ a) → (a + 16 ≤ ckO ∨ ckO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
        (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q := fun h₁ h₂ h q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Lay.w_w h₁ h (by decide)
    · exact Lay.w_w h₂ h (by decide)
  have pP₃ : bytesAt t₃.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem (w64 P) r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨w64 P, r⟩] m (writeBytes m (w64 P) xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have cnt₃ : slotv t₃.mem p.W restO = BitVec.ofNat 32 r := by
    rw [← hcnt]
    exact H.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- What `xorPad` writes, from the state it starts in.
  have xP : ∀ u : State, bytesAt u.mem (w64 P) r = bytesAt t.mem (w64 P) r →
      blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem (w64 P) (Spec.Ocb.xor (bytesAt u.mem (w64 P) r)
        (bytesAt u.mem (w64 p.W + BitVec.ofNat 64 tmpO) r))) (w64 P) r =
        Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
          (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)))) := by
    intro u hu ht
    rw [hu, Proof.Ocb.xor_bytesAt_block _ _ _ hl (by omega), ht, H.tmp,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have ck₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) :=
    Proof.Ocb.blockAtMem_frame H.frame fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨w64 P, r⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have mP : InMut p [⟨w64 P, r⟩] := hP.inm
  have mT : InMut p [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    · exact inMut_w p (.inl (by decide))
  have fR : ∀ {m₀ m₁ m₂ : Mem} {rs : List Region}, Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m₀ m₁ →
      Frame rs m₁ m₂ → (∀ q ∈ rs, q ∈ restR p P r) → Frame (restR p P r) m₀ m₂ := fun h₁ h₂ hs =>
    (h₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> simp).trans
      (h₂.mono hs)
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok L H.env hr hr' si₃ cnt₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    have fr₄ : Frame [⟨w64 P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    have E₄ : Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      H.env.ebp]) (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄
      (frame_toMut fr₄ mP)
    have cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (dW (by decide)).symm) (by decide)
    refine WP.mono (padCk_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), si₃])
      cnt₄ (hP₃.of_eq wr₄).sbuf) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem (w64 P) r = bytesAt t₄.mem (w64 P) r :=
      Proof.AesGcm.X86.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.mut L (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), E₄.ebp])
      (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), E₄.esp]) rd₅ wr₅ (frame_toMut fr₅ mT),
      fR H.frame (rs := [⟨w64 P, r⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩])
        ((fr₄.mono (by simp)).trans (fr₅.mono (by simp))) (by simp), ?_, ?_, ?_,
      fun q h₁ h₂ h₃ h₄ h₅ => by rw [g₅ q h₁ h₃ h₄ h₅, g₄ q h₁ h₂ h₃ h₄ h₅, H.gpr q h₁ h₂ h₃ h₄],
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [Proof.Ocb.blockAtMem_frame fr₅ (dTW (.inl (by decide)) (.inl (by decide)) (by decide)),
        Proof.Ocb.blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, Proof.Ocb.blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L H.env hr hr' si₃ cnt₃ hP₃.sbuf) fun t₄ ⟨fr₄, ck₄, g₄, rd₄, wr₄⟩ => ?_)
    have E₄ : Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄ (frame_toMut fr₄ mT)
    have p₄ : bytesAt t₄.mem (w64 P) r = bytesAt t₃.mem (w64 P) r := Proof.AesGcm.X86.bytesAt_frame fr₄ dT (by omega)
    have cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    refine WP.mono (xorPad_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), si₃]) cnt₄
      (hP₃.of_eq wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨w64 P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.mut L (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₄.ebp])
      (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₄.esp]) rd₅ wr₅ (frame_toMut fr₅ mP),
      fR H.frame (rs := [⟨w64 P, r⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩])
        ((fr₄.mono (by simp)).trans (fr₅.mono (by simp))) (by simp), ?_, ?_, ?_,
      fun q h₁ h₂ h₃ h₄ h₅ => by rw [g₅ q h₁ h₂ h₃ h₄ h₅, g₄ q h₁ h₃ h₄ h₅, H.gpr q h₁ h₂ h₃ h₄],
      by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [Proof.Ocb.blockAtMem_frame fr₅ (pW (by decide)),
        Proof.Ocb.blockAtMem_frame fr₄ (dTW (.inl (by decide)) (.inl (by decide)) (by decide)), H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (Proof.Ocb.blockAtMem_frame fr₄
        (dTW (.inl (by decide)) (.inr (by decide)) (by decide)))]
    · simp only [↓reduceIte]
      rw [Proof.Ocb.blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (p : Prm) (d : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] t.mem t'.mem
  val : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) =
    ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO)
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (callees v) d) t (TagPost p d t) := by
  have hd' : d = 0 ∨ d = 144 := hd
  have mW : ∀ {a : Nat}, a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176 → InMut p [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      rcases h with h | h
      · exact inMut_w p (.inl h)
      · exact inMut_w p (.inr (.inl h))
  have step : ∀ {u u' : State} {a : Nat}, Env p u → (a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176) →
      Frame [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] u.mem u'.mem → (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) →
      u'.rd = u.rd → u'.wr = u.wr → Env p u' := fun Eu ha f g rd wr =>
    Eu.mut L (by rw [g _ (by decide), Eu.ebp]) (by rw [g _ (by decide), Eu.esp]) rd wr (frame_toMut f (mW ha))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := ckO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact copyMem16_frame _ _ _ _ _
  have E₁ := step E (.inl (by decide)) f₁ g₁ rd₁ wr₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  have E₂ := step E₁ (.inl (by decide)) f₂ g₂ rd₂ wr₂
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xor16W_ok L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact xorMem16_frame _ _ _ _ _
  have E₃ := step E₂ (.inl (by decide)) f₃ g₃ rd₃ wr₃
  have fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := (f₁.trans f₂).trans f₃
  have tW : ∀ {a : Nat}, (a + 16 ≤ tmpO ∨ tmpO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h' (by decide)
  have tmp₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO) := by
    have ofs₁ := Proof.Ocb.blockAtMem_frame f₁ (tW (a := ofsO) (.inl (by decide)) (by decide))
    have ld₂ := Proof.Ocb.blockAtMem_frame (f₁.trans f₂) (tW (a := ldO) (.inl (by decide)) (by decide))
    rw [m₃, xorMem16_block, ld₂, m₂, xorMem16_block, ofs₁, m₁, copyMem16_block]
  have cK : ctxCiph t₃.mem (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R :=
    ctxCiph_mut L (frame_toMut fr₃ (mW (.inl (by decide))))
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_)
  have aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  have tmp₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [aT, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, tmp₃, cK]
  have mD : d + 16 ≤ 128 ∨ 144 ≤ d ∧ d + 16 ≤ 176 := by omega
  have dT : (d + 16 ≤ tmpO ∨ tmpO + 16 ≤ d) := by simp only [tmpO]; omega
  obtain ⟨t₅, run₅, m₅, g₅, rd₅, wr₅⟩ := copy16_ok L P₄.env (s := tmpO) (d := d) (by decide) (by omega)
    (by simp only [tmpO]; omega)
  have f₅ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₄.mem t₅.mem := by rw [m₅]; exact copyMem16_frame _ _ _ _ _
  have E₅ := step P₄.env mD f₅ g₅ rd₅ wr₅
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := xor16W_ok L E₅ (s := sumO) (d := d) (by decide) (by omega)
    (by simp only [sumO]; omega)
  have f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₅.mem t₆.mem := by rw [m₆]; exact xorMem16_frame _ _ _ _ _
  refine WP.of_runBlock ⟨t₆, runBlock_app_of run₅ run₆, step E₅ mD f₆ g₆ rd₆ wr₆, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ => by rw [g₆ r h₁, g₅ r h₁, P₄.gpr r h₁ h₂ h₃ h₄, g₃ r h₁, g₂ r h₁, g₁ r h₁],
    by rw [rd₆, rd₅, P₄.rd, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, P₄.wr, wr₃, wr₂, wr₁]⟩
  · have F₄ := P₄.frame
    rw [aT, show 16 * 1 = 16 from rfl] at F₄
    exact (((fr₃.mono (by simp)).trans (F₄.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> simp)).trans
      (f₅.mono (by simp))).trans (f₆.mono (by simp))
  · have sum₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 sumO) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 sumO) := by
      rw [Proof.Ocb.blockAtMem_frame P₄.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [aT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm), Proof.Ocb.blockAtMem_frame fr₃ (tW (.inl (by decide)) (by decide))]
    rw [m₆, xorMem16_block, m₅, copyMem16_block, Proof.Ocb.blockAtMem_frame (copyMem16_frame _ _ _ _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (by simp only [sumO]; omega) (by decide) (by omega)),
      tmp₄, sum₄]

end VG.Proof.AesOcb.X86
