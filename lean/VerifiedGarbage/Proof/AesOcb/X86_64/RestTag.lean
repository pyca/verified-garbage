import VerifiedGarbage.Proof.AesOcb.X86_64.XorPad

/-!
# AES-OCB on x86-64: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum and XORs `P_*` with `Pad`
(`restSeal_ok`), and for `open` XORs `C_*` with `Pad` and adds the padded
result to the checksum (`restOpen_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt length_bytesAt bytesAt_frame)

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `rbx`. -/
theorem padCk_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {S : Addr} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (h3 : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (padTo_ok E hr hr' (by decide) h3 h12 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ ⟨fr₁, pad₁, g₁, rd₁, wr₁⟩ => ?_)
  have h15₁ : t₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := t2O) (d := ckO) h15₁ h15₁ (by decide) (by decide)
    (by rw [rd₁, wr₁]; exact E.perm.wR (by decide)) (by rw [rd₁, wr₁]; exact E.perm.wR (by decide))
    (by rw [wr₁]; exact E.perm.wW (by decide)) (by rw [wr₁]; exact E.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_,
    fun r h1 h2 h3 h4 => by rw [B₂.gpr r (by simp [h1, h4]), g₁ r h1 h2 h3], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  rw [B₂.val, pad₁, blockAtMem_frame fr₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (K W SP : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  tmp : blockAtMem t'.mem (W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R) :
    WP isa (.seq (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) (callBlocks (callees v).enc (oneBlock tmpO))) t
      (RestHead K W SP R t) := by
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ofsO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : t₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) h15₁
    (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)) (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide))
    (by rw [B₁.wr]; exact E.perm.wW (by decide)) (by rw [B₁.wr]; exact E.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    rw [B₂.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide),
      B₁.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)]) (by rw [B₂.rd, B₁.rd]) (by rw [B₂.wr, B₁.wr])
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have hrnd₂ : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₂.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hrnd]
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₂.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega)]
  refine WP.seq (WP.of_runBlock ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₂ hR hrnd₂
    (oneBlock_ok E₂.r15 tmpO (by decide)) (dstW L E₂.perm (d := tmpO) (n := 1) (by decide))) fun t₃ P₃ => ?_
  refine ⟨E₂.of_saved P₃.saved P₃.rd P₃.wr, ?_, ?_, ?_, fun r hr => ?_, by rw [P₃.rd, B₂.rd, B₁.rd],
    by rw [P₃.wr, B₂.wr, B₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [E₂.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₂.rsp]; exact (L.stk_w' (by decide)).symm), ofs₂]
  · have := P₃.enc (i := 0) (by decide)
    rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    rw [this, B₂.val, B₁.val]
    show ctxCiph t₂.mem K R _ = _
    rw [cK]; rfl
  · have hr' : r ≠ .rax ∧ r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn : r ∉ [Reg.rax, .rdx] := by simp [hr'.1, hr'.2]
    rw [P₃.saved r hr, B₂.gpr r hn, B₁.gpr r hn]

end VG.Proof.AesOcb.X86_64
