module

public import VerifiedGarbage.Proof.AesOcb.X86_64.Whole
public import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesOcb.X86_64.XorPad
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.AesOcb.X86_64.Words
import VerifiedGarbage.Proof.Ocb.Spec

/-! ### `AesOcb.X86_64.RestTag`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86-64: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum and XORs `P_*` with `Pad`
(`restSeal_ok`), and for `open` XORs `C_*` with `Pad` and adds the padded
result to the checksum (`restOpen_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

@[expose] public section

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
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 3584⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (padTo_ok E hr hr' (by decide) h3 h12 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ ⟨fr₁, pad₁, g₁, rd₁, wr₁⟩ => ?_)
  obtain h15₁ : t₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
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
  obtain h15₁ : t₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) h15₁
    (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)) (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide))
    (by rw [B₁.wr]; exact E.perm.wW (by decide)) (by rw [B₁.wr]; exact E.perm.wW (by decide))
  obtain E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    rw [B₂.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide),
      B₁.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)]) (by rw [B₂.rd, B₁.rd]) (by rw [B₂.wr, B₁.wr])
  obtain fr₂ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain hrnd₂ : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₂.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hrnd]
  obtain ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  obtain cK : ctxCiph t₂.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega_arith)]
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
    obtain hn : r ∉ [Reg.rax, .rdx] := by simp [hr'.1, hr'.2]
    rw [P₃.saved r hr, B₂.gpr r hn, B₁.gpr r hn]

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega_arith,
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
  obtain h3₃ : t₃.gpr .rbx = P := by rw [H.saved _ (by decide), h3]
  obtain h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide), h12]
  obtain hP₃ : DBuf K W SP t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  -- `P` is apart from what the pieces write in `W` and from the stack.
  obtain dW : ∀ {d k : Nat}, d + k ≤ 3584 → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  obtain dH : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
  obtain dT : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  obtain dTmp : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  obtain dOfs : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := bytesAt_frame H.frame dH (by omega_arith)
  obtain hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  obtain hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega_arith
  obtain fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  -- What `xorPad` writes, from the state it starts in.
  obtain xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (W + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes
          (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega_arith), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega_arith), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  obtain dCk : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  obtain ck₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  obtain pW : ∀ {d : Nat}, d + 16 ≤ 3584 → ∀ q ∈ [(⟨P, r⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  obtain g7 : ∀ {u u' : State} (a b c d : Reg), (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → u'.gpr r = u.gpr r) →
      a ∉ calleeSaved → b ∉ calleeSaved → c ∉ calleeSaved → d ∉ calleeSaved →
      ∀ r ∈ calleeSaved, u'.gpr r = u.gpr r :=
    fun a b c d g ha hb hc hd r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr)) (fun h => hc (h ▸ hr))
      (fun h => hd (h ▸ hr))
  obtain E' : ∀ {u : State}, (∀ r ∈ calleeSaved, u.gpr r = t₃.gpr r) → u.rd = t₃.rd → u.wr = t₃.wr → Env K W SP u :=
    fun g hrd hwr => H.env.of_saved g hrd hwr
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok H.env hr hr' h3₃ h12₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    obtain s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₄ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    obtain E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    obtain fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (by rw [rd₄, wr₄]; exact hS₃) hP.w) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    obtain s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rcx .rsi .rdx g₅ (by decide) (by decide) (by decide) (by decide)
    obtain p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := bytesAt_frame fr₅ dT (by omega_arith)
    refine ⟨E' (fun r hr => by rw [s₅ r hr, s₄ r hr]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]),
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      fun r hr => by rw [s₅ r hr, s₄ r hr, H.saved r hr], by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L H.env hr hr' h3₃ h12₃ hS₃ hP.w) fun t₄ ⟨fr₄, ck₄, g₄, rd₄, wr₄⟩ => ?_)
    obtain s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rcx .rsi .rdx g₄ (by decide) (by decide) (by decide) (by decide)
    obtain E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    obtain p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := bytesAt_frame fr₄ dT (by omega_arith)
    refine WP.mono (xorPad_ok E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    obtain s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₅ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    obtain fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
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
  obtain nr : ∀ r ∈ calleeSaved, r ∉ [Reg.rax, .rdx] := by decide
  obtain nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := t) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  obtain E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  obtain E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  obtain tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 3584 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  obtain fr₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  obtain hrnd₃ : t₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hrnd]
  obtain tmp₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  obtain cK : ctxCiph t₃.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega_arith)]
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₃ hR
    hrnd₃ (oneBlock_ok E₃.r15 tmpO (by decide)) (dstW L E₃.perm (d := tmpO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  obtain E₄ : Env K W SP t₄ := E₃.of_saved P₄.saved P₄.rd P₄.wr
  obtain tmp₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    rw [this, tmp₃, ← cK]; rfl
  obtain ⟨t₅, run₅, B₅⟩ := copy16_ok (s := t₄) (a := tmpO) (d := d) E₄.r15
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega_arith)) (E₄.perm.wW (by omega_arith))
  obtain E₅ : Env K W SP t₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨t₆, run₆, B₆⟩ := xor16_ok (s := t₅) (b := .r15) (a := sumO) (d := d) E₅.r15 E₅.r15 (by decide) (by decide)
    (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega_arith)) (E₅.perm.wW (by omega_arith))
  refine WP.of_runBlock ⟨t₆, by rw [runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  obtain dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 3584 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega_arith)
  obtain dCall : ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨W + BitVec.ofNat 64 512, 2048⟩,
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
  · rw [B₆.val, B₅.val, tmp₄, blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega_arith) (by decide)),
      blockAtMem_frame P₄.frame dCall, blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs `whole` on the
`m = len / 16` whole blocks if there are any (`wholeIte_ok`), then `rest` on
the `len mod 16` bytes after them if there are any (`restIte_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e length_bytesAt bytesAt_frame)

/-- The number of whole blocks, in `r13`. -/
theorem bodyHead_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {n : Nat} (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ s₁, runBlock isa [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)] s = some s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .r13 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  refine ⟨_, by orun [E.r15, r₁, hlen], ?_, ?_, ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn,
      Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega_arith)]
  · rfl
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
  all_goals rfl

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) {O0 l : Block}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hT : TblL W l n s.mem)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s
      (WholePost K W SP D (16 * (n / 16)) (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyHead_ok E hn hlen
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, fun k hk => absurd hk (by omega_arith),
      by rw [m₁, hofs, hm]; rfl, by rw [m₁, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    rw [← m₁]
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nosp depth hcall hB1 hB2 L E₁ hR (hD.take' (Nat.mul_div_le n 16) |>.of_eq rd₁ wr₁)
      (Nat.le_refl _) (by omega_arith) (by rw [m₁]; exact hdata) r13₁ (by rw [m₁]; exact hrnd)
      (by rw [m₁]; exact hofs) (by rw [m₁]; exact ho0) (by rw [m₁]; exact hck) (by rw [m₁]; exact hT)
      (fun i => by rw [m₁]; exact hckF1 i) hckF2₀ (fun i => by rw [m₁]; exact hckF2 i)) fun t P => ?_
    exact ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ t₁, runBlock isa [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)] t = some t₁ ∧
      t₁.gpr .rbx = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (n % 16) ∧
      t₁.zf = some (decide (n % 16 = 0)) ∧ t₁.mem = t.mem ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  have r₂ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesCcm.X86_64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega_arith]
  refine ⟨_, by orun [E.r15, r₁, r₂, hdata, hlen], ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn, hsub]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15,
      Proof.AesCcm.X86_64.and15', toNat_ofNat_of_lt hn,
      Proof.AesCcm.X86_64.and_self_beq (show n % 16 < 2 ^ 64 by omega_arith)]
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, ite_false]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP t D n)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (rest (callees v) enc))) t
      (TailPost enc K W SP R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok E hn hdata hlen
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega_arith
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega_arith
    have hP : DBuf K W SP t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)).of_eq rd₁ wr₁
    refine WP.mono (rest_ok v enc L E₁ hR (by rw [m₁]; exact hrnd) hr (Nat.mod_lt _ (by decide)) rbx₁ r12₁ hP)
      fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, wC W, below SP 8, ⟨D, n⟩]

theorem bodyR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W SP D n) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W SP D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env K W SP t
  frame : Frame (bodyR W SP D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_arith))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_arith)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_arith]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_arith]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W`, the stack and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W SP Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

/-- A buffer apart from `W`, the stack and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W SP Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W SP D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

theorem wholeR_sub {W SP D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W SP D k, ∃ r' ∈ bodyR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W SP D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W SP D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hT : TblL W (ctxLstar s.mem K) n s.mem) :
    WP isa (body (callees v) true) s (BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_arith)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_arith)).symm
  simp only [body, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNosp v.encDepth hcall_enc sealPre_ok xorOfs_ok L E hR hD hdata hlen hrnd hofs ho0 hck hT
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hrnd₁ := (kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (restIte_ok v true L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    bytesAt_frame Pw.frame (disj_whole hP.w hP.stk dDP.symm) (by omega_arith)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [bytesAt_frame Pt.frame (disj_tail hDm.w hDm.stk dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hT : TblL W (ctxLstar s.mem K) n s.mem) :
    WP isa (body (callees v) false) s (BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_arith)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_arith)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNosp v.decDepth hcall_dec xorOfs_ok openPost_ok L E hR hD hdata hlen hrnd hofs ho0 hck hT
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hrnd₁ := (kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (restIte_ok v false L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    bytesAt_frame Pw.frame (disj_whole hP.w hP.stk dDP.symm) (by omega_arith)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [bytesAt_frame Pt.frame (disj_tail hDm.w hDm.stk dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86_64
