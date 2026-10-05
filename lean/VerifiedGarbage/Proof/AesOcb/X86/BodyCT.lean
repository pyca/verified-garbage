import VerifiedGarbage.Proof.AesOcb.X86.HashCT

/-!
# AES-OCB on x86: the data and the tag in constant time

Untrusted: everything here is checked by Lean. A pass over the whole blocks
runs for their number, public, each block's offset by `lNtz` (`pass_ct`);
`whole` is two passes around a call (`whole_ct`); the rest addresses the
data's end and `W` (`rest_ct`); `body` branches on the data's length
(`body_ct`); the tag addresses only `W` (`tag_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq xorLoop_ct runBlock_app_of)

/-! ## A pass -/

/-- Checksums by `fC` from `c0`. -/
def ckRec (fC : Block → Block → Block → Block) (O0 l : Block) (X : Nat → Block) (c0 : Block) : Nat → Block
  | 0 => c0
  | k + 1 => fC (ckRec fC O0 l X c0 k) (X k) (offAt O0 l (k + 1))

/-- A pass's state after `i` of its `m` blocks, for some offset, `L_*`,
blocks and checksums. -/
def PassI (p : Prm) (fC : Block → Block → Block → Block) (m i : Nat) (t : State) : Prop :=
  ∃ O0 l X ckF t₀, (∀ k < m, ckF (k + 1) = fC (ckF k) (X k) (offAt O0 l (k + 1))) ∧
    PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i

theorem PassI.start {p : Prm} {fC : Block → Block → Block → Block} {m : Nat} {t : State} (E : Env p t)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0)) (hdi : t.gpr .edi = BitVec.ofNat 32 (0 + 1))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 0)) {l : Block}
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) : PassI p fC m 0 t :=
  ⟨_, l, fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)),
    ckRec fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) l
      (fun k => blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)),
    t, fun _ _ => rfl,
    { env := E, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := hsi, edi := hdi, ebx := hbx, ofs := rfl,
      ck := rfl, blk := fun k _ => by simp, l0 := hl0, gpr := fun _ _ _ _ _ _ _ => rfl }⟩

/-- A pass of `body` over the `m` whole blocks; `body ++ nextBlock` is
constant time from `ebp` and `esi` (`hct`). -/
theorem pass_ct {p : Prm} (L : Lay p) {body : List Instr} {fC : Block → Block → Block → Block}
    (hB : BodyOk p body (fun b o => b ^^^ o) fC)
    (hct : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (body ++ nextBlock)))
    {m : Nat} (hm0 : 0 < m) (hmn : 16 * m ≤ p.n) : CT (PassI p fC m 0) (pass body) := by
  have hn := L.n32
  unfold pass
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ m ∧ PassI p fC m (m - n) t) (fun n => ?_)
    (fun n t ⟨hn0, hnm, _, _, _, _, _, hck, P⟩ => WP.mono (pass_step L hB hck hmn (by omega) P) fun t' ⟨P', zf'⟩ =>
      ⟨hn0, by rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega,
        fun h1 => ⟨by omega, by omega, _, _, _, _, _, hck, by
          rw [show m - (n - 1) = m - n + 1 by omega]; exact P'⟩⟩) m).mono
    fun t h => ⟨hm0, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  by_cases hn : 0 < n ∧ n ≤ m
  swap
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩
  unfold nextOffset
  have hw : ∀ t, (0 < n ∧ n ≤ m ∧ PassI p fC m (m - n) t) → WP isa lNtz t fun t' =>
      Env p t' ∧ t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)) := fun t ⟨_, _, _, _, _, _, _, _, P⟩ =>
    WP.mono (lNtz_ok L P.env (by omega) (by omega) P.edi P.l0) fun t₁ P₁ =>
      ⟨P₁.env L P.env, by rw [P₁.gpr _ (by decide) (by decide) (by decide), P.esi]⟩
  refine CT.seq (J := fun t => t.gpr .ebp = p.W ∧ t.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)))
    (CT.seq (J := fun t => Env p t ∧ t.gpr .esi = p.D + BitVec.ofNat 32 (16 * (m - n)))
      (lNtz_ct L (i := m - n + 1) (by omega) (by omega) fun t ⟨_, _, _, _, _, _, _, _, P⟩ => ⟨P.env, P.edi⟩) hw
      (CT.taint [.ebp] (pin_ebp fun t h => h.1.ebp) (by taint_decide)))
    (fun t h => WP.seq (WP.mono (hw t h) fun t₁ ⟨E₁, si₁⟩ => ?_)) (hct fun _ h => h)
  obtain ⟨t₂, run₂, -, g₂, -⟩ := xor16W_ok L E₁ (s := lO) (d := ofsO) (by decide) (by decide) (.inr (by decide))
  exact WP.of_runBlock ⟨t₂, run₂, by rw [g₂ _ (by decide), E₁.ebp], by rw [g₂ _ (by decide), si₁]⟩

/-! ## The whole blocks -/

/-- What `whole` needs. -/
def WhI (p : Prm) (m : Nat) (t : State) : Prop :=
  Env p t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m ∧ ∃ l, blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0

theorem whole_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} (L : Lay p) {pre post : List Instr}
    {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    (hct1 : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (pre ++ nextBlock)))
    (hct2 : ∀ {J : State → Prop} {B : BitVec 32}, (∀ s, J s → s.gpr .ebp = p.W ∧ s.gpr .esi = B) →
      CT J (.block (post ++ nextBlock)))
    {m : Nat} (hm0 : 0 < m) (hmn : 16 * m ≤ p.n) : CT (WhI p m) (whole fn pre post) := by
  have hn := L.n32
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- What a pass keeps.
  have kP : ∀ {d k : Nat} {m' : Mem} {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t : State} {i : Nat},
      PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → d + k ≤ 2560 →
      (d + k ≤ ofsO ∨ (48 ≤ d ∧ d + k ≤ lO) ∨ (112 ≤ d ∧ d + k ≤ kO) ∨ 224 ≤ d) → t₀.mem = m' →
      ∀ r ∈ [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun _ h₁ h₂ _ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₂ ⊢; omega) h₁ (by decide)
    · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₂ ⊢; omega) h₁ (by decide)
    · exact dW h₁
  -- What a call keeps.
  have kC : ∀ {d k : Nat}, d + k ≤ scrO → ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p],
      (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dW (by simp only [scrO] at h; omega)
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega)).symm
  have start : ∀ {fC : Block → Block → Block → Block} t, WhI p m t → ∃ t', runBlock isa passStart t = some t' ∧
      PassI p fC m 0 t' := fun t ⟨E, nb, l, hl0⟩ => by
    obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E nb
    exact ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
      (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0)⟩
  -- `nbO` and `l0O`, across a pass.
  have nbP : ∀ {O0 l : Block} {X : Nat → Block} {ckF : Nat → Block} {t₀ t t' : State} {i i' : Nat},
      PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t i → PassInv p m O0 l X (fun b o => b ^^^ o) ckF t₀ t' i' →
      slotv t'.mem p.W nbO = slotv t.mem p.W nbO := fun P P' => by
    rw [slotv_eq, slotv_eq, P'.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P' (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide),
      P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kP P (by decide) (.inr (.inr (.inr (by decide)))) rfl) (by decide)]
  have hargs : ∀ t, WhI p m t → ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] t = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨E, nb, _⟩ => by
    have hD := E.slots.data
    simp only [slotv_eq] at hD nb
    exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hD, nb], by gregs [hD], by gregs [nb],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  unfold whole
  -- The first pass.
  refine CT.seq (J := fun t => PassI p fC1 m 0 t ∧ slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0⟩ => by
      obtain ⟨t₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E nb
      exact WP.of_runBlock ⟨t₁, run₁, PassI.start (E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
        (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁) si₁ di₁ bx₁ (by rw [m₁]; exact hl0),
        by rw [m₁]; exact nb⟩) ?_
  refine CT.seq (J := WhI p m) ((pass_ct L hB1 hct1 hm0 hmn).mono fun _ h => h.1)
    (fun t ⟨⟨_, _, _, _, _, hck, P⟩, nb⟩ => WP.mono (pass_ok L hB1 hck hmn hm0 P) fun t' P' =>
      ⟨P'.env, by rw [nbP P P', nb], _, P'.l0⟩) ?_
  -- The call.
  refine CT.seq (J := WhI p m) (callBlocks_ct ok ct nosp stack L
      (fun t h => ⟨h.1, DReg.d L h.1 hmn, hargs t h⟩) fun hJ => by exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide))
    (fun t h => WP.mono (callBlocks_ok ok nosp stack L h.1 (hargs t h) (DReg.d L h.1 hmn)) fun t' P => ?_) ?_
  · obtain ⟨E, nb, l, hl0⟩ := h
    refine ⟨P.env, ?_, l, ?_⟩
    · rw [← nb]
      exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (kC (by decide))
        (by decide)
    · rw [Proof.Ocb.blockAtMem_frame P.frame (kC (by decide)), hl0]
  -- `Offset_0` again, and the second pass.
  refine CT.seq (J := PassI p fC2 m 0) (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide))
    (fun t ⟨E, nb, l, hl0⟩ => ?_) ((pass_ct L hB2 hct2 hm0 hmn))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₁.mem := by
    rw [m₁]; exact copyMem16_frame _ _ _ _ _
  have k₁ : ∀ {d k : Nat}, (d + k ≤ ofsO ∨ ofsO + 16 ≤ d) → d + k ≤ 2560 →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun h h' r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h h' (by decide)
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  have nb₁ : slotv t₁.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← nb]
    exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (k₁ (.inr (by decide)) (by decide)) (by decide)
  have l0₁ : blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0 := by
    rw [Proof.Ocb.blockAtMem_frame f₁ (k₁ (.inr (by decide)) (by decide)), hl0]
  obtain ⟨t', run', P⟩ := start (fC := fC2) t₁ ⟨E₁, nb₁, l, l0₁⟩
  exact WP.of_runBlock ⟨t', runBlock_app_of run₁ run', P⟩

end VG.Proof.AesOcb.X86
