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

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

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
structure RestPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)))
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (h3 : t.gpr .rbx = P) (h12 : t.gpr .r12 = BitVec.ofNat 64 r)
    (hP : DBuf K W SP t P r) :
    WP isa (rest (callees v) enc) t (RestPost enc K W SP R P r t) := by
  unfold rest
  refine wp_seq_assoc (WP.seq (WP.mono (restHead_ok v L E hR hrnd) fun t₃ H => ?_))
  have h3₃ : t₃.gpr .rbx = P := by rw [H.saved _ (by decide), h3]
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide), h12]
  have hP₃ : DBuf K W SP t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  -- `P` is apart from what the pieces write in `W` and from the stack.
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
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
  have pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  -- What `xorPad` writes, from the state it starts in.
  have xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (W + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes
          (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have ck₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have g7 : ∀ {u u' : State} (a b c d : Reg), (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → u'.gpr r = u.gpr r) →
      a ∉ calleeSaved → b ∉ calleeSaved → c ∉ calleeSaved → d ∉ calleeSaved →
      ∀ r ∈ calleeSaved, u'.gpr r = u.gpr r :=
    fun a b c d g ha hb hc hd r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr)) (fun h => hc (h ▸ hr))
      (fun h => hd (h ▸ hr))
  have E' : ∀ {u : State}, (∀ r ∈ calleeSaved, u.gpr r = t₃.gpr r) → u.rd = t₃.rd → u.wr = t₃.wr → Env K W SP u :=
    fun g hrd hwr => H.env.of_saved g hrd hwr
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok H.env hr hr' h3₃ h12₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    have s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₄ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    have E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    have fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (by rw [rd₄, wr₄]; exact hS₃) hP.w) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    have s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rcx .rsi .rdx g₅ (by decide) (by decide) (by decide) (by decide)
    have p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := bytesAt_frame fr₅ dT (by omega)
    refine ⟨E' (fun r hr => by rw [s₅ r hr, s₄ r hr]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]),
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      fun r hr => by rw [s₅ r hr, s₄ r hr, H.saved r hr], by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L H.env hr hr' h3₃ h12₃ hS₃ hP.w) fun t₄ ⟨fr₄, ck₄, g₄, rd₄, wr₄⟩ => ?_)
    have s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rcx .rsi .rdx g₄ (by decide) (by decide) (by decide) (by decide)
    have E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (xorPad_ok E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    have s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₅ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    have fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E' (fun r hr => by rw [s₅ r hr, s₄ r hr]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]),
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      fun r hr => by rw [s₅ r hr, s₄ r hr, H.saved r hr], by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (K W SP : Addr) (R d : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, wC W, below SP 8] t.mem t'.mem
  val : blockAtMem t'.mem (W + BitVec.ofNat 64 d) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 sumO)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (callees v) d) t (TagPost K W SP R d t) := by
  have hd' : d = 0 ∨ d = 128 := hd
  have nr : ∀ r ∈ calleeSaved, r ∉ [Reg.rax, .rdx] := by decide
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := t) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  have hrnd₃ : t₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hrnd]
  have tmp₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₃.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₃ hR
    hrnd₃ (oneBlock_ok E₃.r15 tmpO (by decide)) (dstW L E₃.perm (d := tmpO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ : Env K W SP t₄ := E₃.of_saved P₄.saved P₄.rd P₄.wr
  have tmp₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    rw [this, tmp₃, ← cK]; rfl
  obtain ⟨t₅, run₅, B₅⟩ := copy16_ok (s := t₄) (a := tmpO) (d := d) E₄.r15
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega)) (E₄.perm.wW (by omega))
  have E₅ : Env K W SP t₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨t₆, run₆, B₆⟩ := xor16_ok (s := t₅) (b := .r15) (a := sumO) (d := d) E₅.r15 E₅.r15 (by decide) (by decide)
    (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega)) (E₅.perm.wW (by omega))
  refine WP.of_runBlock ⟨t₆, by rw [runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega)
  have dCall : ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨W + BitVec.ofNat 64 512, 2048⟩,
      below (t₃.gpr .rsp) 8], (⟨W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [E₃.rsp]; exact (L.stk_w' (by decide)).symm
  refine ⟨E₅.keep (fun r hr => B₆.gpr r (nE r hr)) B₆.rd B₆.wr, ?_, ?_,
    fun r hr => by rw [B₆.gpr r (nr r hr), B₅.gpr r (nr r hr), P₄.saved r hr, B₃.gpr r (nr r hr),
      B₂.gpr r (nr r hr), B₁.gpr r (nr r hr)],
    by rw [B₆.rd, B₅.rd, P₄.rd, B₃.rd, B₂.rd, B₁.rd], by rw [B₆.wr, B₅.wr, P₄.wr, B₃.wr, B₂.wr, B₁.wr]⟩
  · refine (((fr₃.mono (by simp)).trans (P₄.frame.sub fun r hr => ?_)).trans (B₅.frame.mono (by simp))).trans
      (B₆.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [E₃.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  · rw [B₆.val, B₅.val, tmp₄, blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega) (by decide)),
      blockAtMem_frame P₄.frame dCall, blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.X86_64
