import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp

/-!
# AES-GCM-SIV on x86: the tag in and out

Untrusted: everything here is checked by Lean. `open` copies the received
tag from `tag` to `W` (`recvTag_ok`), and `seal` copies the tag it computed
at `W` out to `tag` (`tagOut_ok`): both load the pointer from its slot, then
all four words, then store them, so constant time from `ebp`, then from the
pointer (`recvTag_ct`, `tagOut_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq w64_add in_off in_left)

/-- The pointer to the tag, loaded. -/
theorem tagPtr_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t', runBlock isa [.mov .edi (slot tpO)] t = some t' ∧ t'.gpr .edi = p.T ∧ t'.mem = t.mem ∧
      (∀ r, r ≠ .edi → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hT := E.slots.tp
  simp only [slotv_eq, tpO] at hT
  exact ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], by gregs [hT], by gmems [], fun r h => by gregs [h], by gmems [],
    by gmems []⟩

theorem recvTag_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa recvTag t fun t' => Env p t' ∧ bytesAt t'.mem (w64 p.W) 16 = bytesAt t.mem (w64 p.T) 16 ∧
      Frame [⟨w64 p.W, 16⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, di₁, m₁, g₁, rd₁, wr₁⟩ := tagPtr_ok L E
  have aT : ∀ {k}, k < 16 → w64 (p.T + BitVec.ofNat 32 k) = w64 p.T + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := L.tw; omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions (t₁.rd ++ t₁.wr) (w64 p.T + BitVec.ofNat 64 k) 4 := fun hk => by
    rw [rd₁, wr₁]; exact in_off E.perm.t hk (by decide)
  have bp₁ : t₁.gpr .ebp = p.W := by rw [g₁ _ (by decide), E.ebp]
  have wIn : ∀ {d}, d + 4 ≤ 2816 → InRegions t₁.wr (w64 p.W + BitVec.ofNat 64 d) 4 := fun hd => by
    rw [wr₁]; exact E.perm.wW hd
  have hs := Proof.AesGcm.X86.store4_eq t₁.mem p.W 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain ⟨t₂, run₂, hm₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
        .mov .ebx (.mem (at_ .edi 12)), .store (at_ .ebp tagO) .eax, .store (at_ .ebp (tagO + 4)) .ecx,
        .store (at_ .ebp (tagO + 8)) .edx, .store (at_ .ebp (tagO + 12)) .ebx] t₁ = some t₂ ∧
      t₂.mem = Cmac.store4 t₁.mem (w64 p.W + BitVec.ofNat 64 0) (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 0) 32)
        (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 4) 32) (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 8) 32)
        (t₁.mem.readW (w64 p.T + BitVec.ofNat 64 12) 32) ∧
      t₂.gpr .ebp = p.W ∧ t₂.gpr .esp = p.SP ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr :=
    ⟨_, by grun [di₁, aT, tIn, bp₁, L.aW, wIn], by gmems [di₁, bp₁, aT, L.aW, hs], by gregs [bp₁],
      by gregs [g₁ _ (by decide : Reg.esp ≠ .edi), E.esp], by gmems [rd₁], by gmems [wr₁]⟩
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have f : Frame [⟨w64 p.W, 16⟩] t.mem t₂.mem := by
    rw [hm₂, m₁, BitVec.add_zero]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨E.mut L bp₂ sp₂ rd₂ wr₂ (frame_toMut f fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; simpa using inMut_w p (d := 0) (k := 16) (.inl (by decide))),
    ?_, f, rd₂, wr₂⟩
  rw [hm₂, m₁, BitVec.add_zero, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW,
    Cmac.le4_readW, Cmac.le4_readW, BitVec.add_zero]

theorem recvTag_ct {p : Prm} (L : Lay p) : CT (Env p) recvTag :=
  CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .edi = p.T)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => let ⟨t₁, run₁, di₁, _, g₁, _⟩ := tagPtr_ok L E
      WP.of_runBlock ⟨t₁, run₁, by rw [g₁ _ (by decide), E.ebp], di₁⟩)
    (CT.taint [.ebp, .edi] (pin2 fun _ h => h) (by taint_decide))

theorem tagOut_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (tW : Covers [⟨w64 p.T, 16⟩] t.wr) :
    WP isa tagOut t fun t' => bytesAt t'.mem (w64 p.T) 16 = bytesAt t.mem (w64 p.W) 16 ∧
      Frame [⟨w64 p.T, 16⟩] t.mem t'.mem ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.gpr .eax = t.mem.readW
        (w64 p.W) 32 ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hT := E.slots.tp
  simp only [slotv_eq, tpO] at hT
  have aT : ∀ {k}, k < 16 → w64 (p.T + BitVec.ofNat 32 k) = w64 p.T + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := L.tw; omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions t.wr (w64 p.T + BitVec.ofNat 64 k) 4 := fun hk => in_off tW hk (by decide)
  have hs := Proof.AesGcm.X86.store4_eq t.mem p.T 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], ?_⟩)
  refine WP.of_runBlock ⟨_, by grun [aT, tIn, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hs, hT]
    rw [BitVec.add_zero, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW,
      Cmac.le4_readW, BitVec.add_zero]
  · gmems [hs, hT]
    rw [BitVec.add_zero]
    exact Cmac.frame_store4 _ _ _ _ _
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []; rw [BitVec.add_zero]
  · gmems []
  · gmems []

theorem tagOut_ct {p : Prm} (L : Lay p) : CT (Env p) tagOut :=
  CT.seq (J := fun s => s.gpr .edi = p.T) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => by
      have hT := E.slots.tp
      simp only [slotv_eq, tpO] at hT
      exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hT], by gregs [hT]⟩)
    (CT.taint [.edi] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

/-! ## Writes to the tag -/

/-- A part of `W` misses the tag. -/
theorem w_t {p : Prm} (L : Lay p) {d k : Nat} (h : d + k ≤ 2816) :
    ∀ r ∈ [(⟨w64 p.T, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w.sub_right (Lay.wSub h)).symm

/-- An environment, after code that writes only the tag. -/
theorem Env.tag {p : Prm} (L : Lay p) {s s' : State} (h : Env p s) (hbp : s'.gpr .ebp = p.W)
    (hsp : s'.gpr .esp = p.SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨w64 p.T, 16⟩] s.mem s'.mem) : Env p s' := by
  have k : ∀ o, o + 4 ≤ 2816 → slotv s'.mem p.W o = slotv s.mem p.W o := fun o ho =>
    hf.readW (r := ⟨w64 p.W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (w_t L ho) (by decide)
  have S := h.slots
  exact ⟨hbp, hsp, h.perm.of_eq hrd hwr, by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.aad,
    by rw [k _ (by decide)]; exact S.alen, by rw [k _ (by decide)]; exact S.data,
    by rw [k _ (by decide)]; exact S.len, by rw [k _ (by decide)]; exact S.tp⟩

end VG.Proof.AesGcmSiv.X86
