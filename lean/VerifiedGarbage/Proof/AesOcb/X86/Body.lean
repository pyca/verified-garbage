module

public import VerifiedGarbage.Proof.AesOcb.X86.Calls
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesOcb.X86.Nonce
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesOcb.X86.Hash
import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.X86.Blk
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.AesOcb.X86.HashFill
import VerifiedGarbage.Proof.AesOcb.X86.LNtz
public import VerifiedGarbage.Proof.AesOcb.X86.PadTo
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `AesOcb.X86.RestTag`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum (`padCk_ok`) and XORs `P_*`
with `Pad` (`xorPad_ok`), and for `open` XORs `C_*` with `Pad` and adds the
padded result to the checksum (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

@[expose] public section

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
  obtain aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  obtain xp : XorPre s₁ (p.W + BitVec.ofNat 32 tmpO) P r := by
    refine ⟨dx₁, di₁, cx₁, hr, by omega_arith, ?_, hP.fit, ?_, by rw [wr₁]; exact hP.wr, ?_⟩
    · rw [L.nW (by decide)]; have := L.ww; simp only [tmpO]; omega_arith
    · rw [aT, rd₁, wr₁]; exact E.perm.wCR (d := tmpO) (n := r) (by simp only [tmpO]; omega_arith)
    · rw [aT]; exact (hP.w.sub_right (Lay.wSub (by simp only [tmpO]; omega_arith))).symm
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
  obtain E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (frame_toMut fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := t2O) (d := ckO) (by decide) (by decide)
    (.inr (by decide))
  obtain f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (xorMem16_frame _ _ _ _ _).mono (by simp)
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans f₂, ?_,
    fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁, g₁ r h₁ h₂ h₃ h₄], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [m₂, xorMem16_block, pad₁, Proof.Ocb.blockAtMem_frame fr₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)]

/-- The block of `rest`'s head: `Offset_* = Offset ⊕ L_*`, copied to
`W + tmpO`. -/
theorem restBlk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₃, runBlock isa (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO) t = some t₃ ∧
      Env p t₃ ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem ∧
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) ∧
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → t₃.gpr r = t.gpr r) ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  obtain E₁ : Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ofsO) (by decide) (by decide)
  obtain f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  obtain E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := copy16_ok L E₂ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  obtain f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact copyMem16_frame _ _ _ _ _
  obtain E₃ : Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide), E₂.ebp]) (by rw [g₃ _ (by decide), E₂.esp]) rd₃ wr₃
    (frame_toMut f₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := by
    rw [← m₁]; exact (f₂.mono (by simp)).trans (f₃.mono (by simp))
  obtain ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [m₂, xorMem16_block, m₁]; rfl
  obtain ofs₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K) := by
    rw [Proof.Ocb.blockAtMem_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  exact ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, E₃, fr₃, ofs₃, by rw [m₃, copyMem16_block, ofs₂],
    fun r h₁ h₂ => by rw [g₃ r h₁, g₂ r h₁, g₁ r h₂], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩

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
    WP isa (.seq (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO))
      (callBlocks (callees v).enc (oneBlock tmpO))) t (RestHead p t) := by
  obtain ⟨t₃, run₃, E₃, fr₃, ofs₃, tmp₃, g₃, rd₃, wr₃⟩ := restBlk_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_
  obtain aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  refine ⟨P₄.env, (fr₃.mono (by simp)).trans ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [P₄.rd, rd₃],
    by rw [P₄.wr, wr₃]⟩
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
      rcases hr with rfl | rfl <;> exact inMut_w p (.inl (by decide))), tmp₃]
  · rw [P₄.gpr r h₁ h₂ h₃ h₄, g₃ r h₁ h₂]

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
  obtain si₃ : t₃.gpr .esi = P := by rw [H.gpr _ (by decide) (by decide) (by decide) (by decide), hsi]
  obtain hP₃ : RBuf p t₃ P r := hP.of_eq H.wr
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 P, r⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  obtain dH : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p], (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
  obtain dT : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨w64 P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  obtain dWW : ∀ {a d : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 → d + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h₁ h₂ q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h₁ h₂
  obtain dTW : ∀ {a : Nat}, (a + 16 ≤ t2O ∨ t2O + 16 ≤ a) → (a + 16 ≤ ckO ∨ ckO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩],
        (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q := fun h₁ h₂ h q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Lay.w_w h₁ h (by decide)
    · exact Lay.w_w h₂ h (by decide)
  obtain pP₃ : bytesAt t₃.mem (w64 P) r = bytesAt t.mem (w64 P) r :=
    Proof.AesGcm.X86.bytesAt_frame H.frame dH (by omega_arith)
  obtain hl : (bytesAt t.mem (w64 P) r).length = r := length_bytesAt _ _ _
  obtain hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega_arith
  obtain fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨w64 P, r⟩] m (writeBytes m (w64 P) xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  obtain cnt₃ : slotv t₃.mem p.W restO = BitVec.ofNat 32 r := by
    rw [← hcnt]
    exact H.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- What `xorPad` writes, from the state it starts in.
  obtain xP : ∀ u : State, bytesAt u.mem (w64 P) r = bytesAt t.mem (w64 P) r →
      blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem (w64 P) (Spec.Ocb.xor (bytesAt u.mem (w64 P) r)
        (bytesAt u.mem (w64 p.W + BitVec.ofNat 64 tmpO) r))) (w64 P) r =
        Spec.Ocb.xor (bytesAt t.mem (w64 P) r) (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
          (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)))) := by
    intro u hu ht
    rw [hu, Proof.Ocb.xor_bytesAt_block _ _ _ hl (by omega_arith), ht, H.tmp,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega_arith), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  obtain ck₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) :=
    Proof.Ocb.blockAtMem_frame H.frame fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm
  obtain pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨w64 P, r⟩ : Region)],
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have mP : InMut p [⟨w64 P, r⟩] := hP.inm
  obtain mT : InMut p [⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
    · exact inMut_w p (.inl (by decide))
  obtain fR : ∀ {m₀ m₁ m₂ : Mem} {rs : List Region}, Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p] m₀ m₁ →
      Frame rs m₁ m₂ → (∀ q ∈ rs, q ∈ restR p P r) → Frame (restR p P r) m₀ m₂ := fun h₁ h₂ hs =>
    (h₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> simp).trans
      (h₂.mono hs)
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok L H.env hr hr' si₃ cnt₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    obtain fr₄ : Frame [⟨w64 P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    obtain E₄ : Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      H.env.ebp]) (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄
      (frame_toMut fr₄ mP)
    obtain cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (dW (by decide)).symm) (by decide)
    refine WP.mono (padCk_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), si₃])
      cnt₄ (hP₃.of_eq wr₄).sbuf) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    obtain p₅ : bytesAt t₅.mem (w64 P) r = bytesAt t₄.mem (w64 P) r :=
      Proof.AesGcm.X86.bytesAt_frame fr₅ dT (by omega_arith)
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
    obtain E₄ : Env p t₄ := H.env.mut L (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), H.env.esp]) rd₄ wr₄ (frame_toMut fr₄ mT)
    obtain p₄ : bytesAt t₄.mem (w64 P) r = bytesAt t₃.mem (w64 P) r := Proof.AesGcm.X86.bytesAt_frame fr₄ dT (by omega_arith)
    obtain cnt₄ : slotv t₄.mem p.W restO = BitVec.ofNat 32 r := by
      rw [← cnt₃]
      exact fr₄.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    refine WP.mono (xorPad_ok L E₄ hr hr' (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), si₃]) cnt₄
      (hP₃.of_eq wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    obtain fr₅ : Frame [⟨w64 P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
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
  obtain mW : ∀ {a : Nat}, a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176 → InMut p [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      rcases h with h | h
      · exact inMut_w p (.inl h)
      · exact inMut_w p (.inr (.inl h))
  obtain step : ∀ {u u' : State} {a : Nat}, Env p u → (a + 16 ≤ 128 ∨ 144 ≤ a ∧ a + 16 ≤ 176) →
      Frame [⟨w64 p.W + BitVec.ofNat 64 a, 16⟩] u.mem u'.mem → (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) →
      u'.rd = u.rd → u'.wr = u.wr → Env p u' := fun Eu ha f g rd wr =>
    Eu.mut L (by rw [g _ (by decide), Eu.ebp]) (by rw [g _ (by decide), Eu.esp]) rd wr (frame_toMut f (mW ha))
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := ckO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact copyMem16_frame _ _ _ _ _
  obtain E₁ := step E (.inl (by decide)) f₁ g₁ rd₁ wr₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := ofsO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  obtain f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  obtain E₂ := step E₁ (.inl (by decide)) f₂ g₂ rd₂ wr₂
  obtain ⟨t₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xor16W_ok L E₂ (s := ldO) (d := tmpO) (by decide) (by decide)
    (.inl (by decide))
  obtain f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t₂.mem t₃.mem := by rw [m₃]; exact xorMem16_frame _ _ _ _ _
  obtain E₃ := step E₂ (.inl (by decide)) f₃ g₃ rd₃ wr₃
  obtain fr₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem := (f₁.trans f₂).trans f₃
  obtain tW : ∀ {a : Nat}, (a + 16 ≤ tmpO ∨ tmpO + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨w64 p.W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w h h' (by decide)
  obtain tmp₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO) := by
    obtain ofs₁ := Proof.Ocb.blockAtMem_frame f₁ (tW (a := ofsO) (.inl (by decide)) (by decide))
    obtain ld₂ := Proof.Ocb.blockAtMem_frame (f₁.trans f₂) (tW (a := ldO) (.inl (by decide)) (by decide))
    rw [m₃, xorMem16_block, ld₂, m₂, xorMem16_block, ofs₁, m₁, copyMem16_block]
  obtain cK : ctxCiph t₃.mem (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R :=
    ctxCiph_mut L (frame_toMut fr₃ (mW (.inl (by decide))))
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₃ (oneBlock_ok E₃ tmpO)
    (DReg.w L E₃ (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun t₄ P₄ => ?_)
  obtain aT : w64 (p.W + BitVec.ofNat 32 tmpO) = w64 p.W + BitVec.ofNat 64 tmpO := L.aW (by decide)
  obtain tmp₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem (w64 p.K) p.R (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [aT, show w64 p.W + BitVec.ofNat 64 tmpO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 tmpO from
      BitVec.add_zero _] at this
    rw [this, tmp₃, cK]
  obtain mD : d + 16 ≤ 128 ∨ 144 ≤ d ∧ d + 16 ≤ 176 := by omega_arith
  obtain dT : (d + 16 ≤ tmpO ∨ tmpO + 16 ≤ d) := by simp only [tmpO]; omega_arith
  obtain ⟨t₅, run₅, m₅, g₅, rd₅, wr₅⟩ := copy16_ok L P₄.env (s := tmpO) (d := d) (by decide) (by omega_arith)
    (by simp only [tmpO]; omega_arith)
  obtain f₅ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₄.mem t₅.mem := by rw [m₅]; exact copyMem16_frame _ _ _ _ _
  obtain E₅ := step P₄.env mD f₅ g₅ rd₅ wr₅
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := xor16W_ok L E₅ (s := sumO) (d := d) (by decide) (by omega_arith)
    (by simp only [sumO]; omega_arith)
  obtain f₆ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] t₅.mem t₆.mem := by rw [m₆]; exact xorMem16_frame _ _ _ _ _
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
      simp only [List.mem_singleton] at hq; subst hq; exact Lay.w_w (by simp only [sumO]; omega_arith) (by decide) (by omega_arith)),
      tmp₄, sum₄]

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.Pass`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`, with the offset and the checksum in
`xmm0` and `xmm1` (`XInv`, OCB's blocks `rv` of the registers), loaded from
`W` before the blocks and stored back after them (`PassInv`). For block `i`
it finds `L_{ntz(i)}` (`lAddr_ok`: in the table `ltable` wrote, `Tbl`,
`ltable_ok`, which has `L_j` whenever `2^j` is at most the number of
blocks, `lt_tblLen`, by a walk on `i`'s trailing zero bits, or at `W + lO` by
`lNtz_ok` when `i` is a multiple of 64), XORs it into the offset
(`ofsDx_ok`, `OfsOk`), loads the block to `xmm3`, runs `body` on it, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`), and
stores it back (`blockStep_ok`). Four blocks at a time while four are left
(`quad_ok`: the first three have `ntz` 0, 1 and 0, so their `L_{ntz(i)}`
are the table's first two entries, `ofsAt_ok`), then one at a time
(`single_ok`); `pass_ok` gives the blocks, the offset and the checksum in
`W` after all `m`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-! ## Blocks in SSE registers -/

/-- OCB's block of the 16 bytes in an SSE register: a 16-byte load puts the
first byte in the least significant byte. -/
abbrev rv (x : BitVec 128) : Block := XBinOp.eval .pshufb x Proof.Gcm.X86.revMask

theorem blockAtMem_eq (m : Mem) (p : Addr) : blockAtMem m p = rv (m.readW p 128) :=
  Proof.Gcm.X86.blockAt_eq m p

theorem rv_xor (a b : BitVec 128) : rv (a ^^^ b) = rv a ^^^ rv b := Proof.Gcm.X86.pshufb_rev_xor a b

theorem blockAtMem_writeW (m : Mem) (p : Addr) (v : BitVec 128) : blockAtMem (m.writeW p v) p = rv v := by
  rw [blockAtMem_eq, Mem.readW_writeW_self m p 16 _ (by decide)]

/-- A block of `B` that the code may read and write, apart from `W`. -/
structure BBlk (p : Prm) (t : State) (B : BitVec 32) : Prop where
  fit : B.toNat + 16 ≤ 2 ^ 32
  w : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  wr : Covers [⟨w64 B, 16⟩] t.wr
  inm : InMut p [⟨w64 B, 16⟩]

/-- Block `i` of the data. -/
theorem dblk {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : 16 * (i + 1) ≤ p.n) :
    BBlk p t (p.D + BitVec.ofNat 32 (16 * i)) := by
  have hd := L.dw
  obtain a16 : w64 (p.D + BitVec.ofNat 32 (16 * i)) = w64 p.D + BitVec.ofNat 64 (16 * i) := w64_add (by omega_arith)
  obtain sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨by rw [toNat_add32 (by omega_arith)]; omega_arith, L.d_w.sub_left sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega_arith) (by omega_arith)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, sub⟩

/-! ## The table of `L_j` -/

/-- The first `n` entries of the table at `W + tblO` (of six at most): `L_j`
for `j < n`. -/
def TblN (p : Prm) (l : Block) (n : Nat) (m : Mem) : Prop :=
  ∀ j, j < n → j < 6 → blockAtMem m (w64 p.W + BitVec.ofNat 64 (tblO + 16 * j)) = lAt l j

/-- The entries `ltableFrom j k` leaves, for `m` blocks: up to the first
`L_i`, from `L_j` on, with `m < 2^{i+1}`, or all `j + k + 1`. -/
def tblLenFrom (m j : Nat) : Nat → Nat
  | 0 => j + 1
  | k + 1 => if m < 2 ^ (j + 1) then j + 1 else tblLenFrom m (j + 1) k

/-- The entries of the table for `m` blocks. -/
def tblLen (m : Nat) : Nat := tblLenFrom m 0 5

/-- The table for `m` blocks. -/
abbrev Tbl (p : Prm) (l : Block) (m : Nat) (mem : Mem) : Prop := TblN p l (tblLen m) mem

/-- The table has `L_n` whenever `2^n` is at most the number of blocks. -/
theorem lt_tblLenFrom {m n : Nat} (hn : n < 6) (h : 2 ^ n ≤ m) : ∀ k j, j + k = 5 → n < tblLenFrom m j k
  | 0, j, hjk => by
    rw [tblLenFrom]; omega_arith
  | k + 1, j, hjk => by
    rw [tblLenFrom]
    split
    · rename_i hlt
      by_contra hc
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.pow_le_pow_right (by decide)
        (show j + 1 ≤ n by omega_arith)) h) hlt) (Nat.lt_irrefl _)
    · exact lt_tblLenFrom hn h k (j + 1) (by omega_arith)

theorem lt_tblLen {m n : Nat} (hn : n < 6) (h : 2 ^ n ≤ m) : n < tblLen m := lt_tblLenFrom hn h 5 0 rfl

/-- The table's bytes. -/
abbrev tblR (p : Prm) : Region := ⟨w64 p.W + BitVec.ofNat 64 tblO, 96⟩

theorem inMut_tblR (p : Prm) : InMut p [tblR p] := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))

/-- The table, after code that writes elsewhere. -/
theorem TblN.frame {p : Prm} {l : Block} {n : Nat} {m m' : Mem} (h : TblN p l n m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (tblR p).Disjoint r) : TblN p l n m' :=
  fun j hj hj6 => by
    rw [Proof.Ocb.blockAtMem_frame hf fun r hr =>
      (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by omega_arith)), h j hj hj6]

/-- The table is apart from a part of `W` outside `[tblO, tblO + 96)`. -/
theorem tblR_w {p : Prm} {d k : Nat} (h : d + k ≤ tblO ∨ tblO + 96 ≤ d) (hd : d + k ≤ 2560) :
    (tblR p).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  Lay.w_w (by simp only [tblO] at h ⊢; omega_arith) (by decide) hd

/-- What `ltable` and its steps leave, from `t₀`: only the table written. -/
structure LtKeep (p : Prm) (t₀ t : State) : Prop where
  frame : Frame [tblR p] t₀.mem t.mem
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

theorem LtKeep.env {p : Prm} (L : Lay p) {t₀ t : State} (E : Env p t₀) (K : LtKeep p t₀ t) : Env p t :=
  E.mut L (by rw [K.gpr _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [K.gpr _ (by decide) (by decide) (by decide), E.esp]) K.rd K.wr (frame_toMut K.frame (inMut_tblR p))

/-- The number of blocks, kept in `W`, after the table is written. -/
theorem LtKeep.nb {p : Prm} {t₀ t : State} (K : LtKeep p t₀ t) :
    slotv t.mem p.W nbO = slotv t₀.mem p.W nbO :=
  K.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (tblR_w (.inl (by decide)) (by decide)).symm) (by decide)

/-- A level's test: CF set if the blocks are fewer than `2^{j+1}`. -/
theorem ltHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {m j : Nat} (hm : m < 2 ^ 32) (hj : j < 5)
    (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))] t = some t' ∧
      t'.cf = some (decide (m < 2 ^ (j + 1))) ∧ (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h32 : 2 ^ (j + 1) < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega_arith)
  simp only [slotv_eq] at hnb
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hnb], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
    by gmems []⟩
  gmems [hnb, toNat_ofNat32 hm, toNat_ofNat32 h32]

/-- `ltableFrom j k`, from a table with `L_0` to `L_j`. -/
theorem ltableFrom_ok {p : Prm} (L : Lay p) {l : Block} {m : Nat} (hm : m < 2 ^ 32) {t₀ : State} (E₀ : Env p t₀)
    (hnb : slotv t₀.mem p.W nbO = BitVec.ofNat 32 m) : ∀ k j, j + k = 5 → ∀ t, LtKeep p t₀ t →
    TblN p l (j + 1) t.mem →
    WP isa (ltableFrom j k) t fun t' => TblN p l (tblLenFrom m j k) t'.mem ∧ LtKeep p t₀ t'
  | 0, j, _, t, K, T => WP.block_nil ⟨T, K⟩
  | k + 1, j, hjk, t, K, T => by
    have h288 : tblO = 288 := rfl
    have E : Env p t := K.env L E₀
    obtain ⟨t₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := ltHead_ok L E hm (j := j) (by omega_arith) (by rw [K.nb, hnb])
    have K₁ : LtKeep p t₀ t₁ := ⟨by rw [m₁]; exact K.frame, fun r h₁ h₂ h₃ => by rw [g₁ r h₁, K.gpr r h₁ h₂ h₃],
      by rw [rd₁, K.rd], by rw [wr₁, K.wr]⟩
    rw [ltableFrom, tblLenFrom]
    refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
    refine WP.ite (decide (m < 2 ^ (j + 1))) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [ite_eq_left (of_decide_eq_true hb)]
      exact ⟨by rw [m₁]; exact T, K₁⟩
    rw [ite_eq_right (of_decide_eq_false hb)]
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dblW_ok L (K₁.env L E₀) (s := tblO + 16 * j) (d := tblO + 16 * (j + 1))
      (by omega_arith) (by omega_arith) (.inr (.inl (by omega_arith)))
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 (tblO + 16 * (j + 1)), 16⟩] t₁.mem t₂.mem := by
      rw [m₂]; exact dblMem_frame _ _ _ _ _
    refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
    refine ltableFrom_ok L hm E₀ hnb k (j + 1) (by omega_arith) t₂
      ⟨K₁.frame.trans (f₂.sub fun r hr => ?_), fun r h₁ h₂ h₃ => by rw [g₂ r h₁ h₂ h₃, K₁.gpr r h₁ h₂ h₃],
        by rw [rd₂, K₁.rd], by rw [wr₂, K₁.wr]⟩ fun i hi hi6 => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩
    · by_cases hij : i = j + 1
      · subst hij
        rw [m₂, dblMem_block, m₁, T j (by omega_arith) (by omega_arith)]; rfl
      · rw [Proof.Ocb.blockAtMem_frame f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), m₁,
          T i (by omega_arith) hi6]

/-- `ltable`: the table for the `m` blocks, from `L_0` at `W + l0O`. -/
theorem ltable_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {m : Nat} (hm : m < 2 ^ 32)
    (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa ltable t fun t' => Tbl p l m t'.mem ∧ LtKeep p t t' := by
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := copy16_ok L E (s := l0O) (d := tblO) (by decide) (by decide)
    (.inl (by decide))
  have f₁ : Frame [tblR p] t.mem t₁.mem := by
    rw [m₁]
    exact (copyMem16_frame _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (Nat.le_refl _) (by decide)⟩
  have T₁ : TblN p l (0 + 1) t₁.mem := fun j hj _ => by
    obtain rfl : j = 0 := by omega_arith
    rw [m₁, Nat.mul_zero, Nat.add_zero, copyMem16_block, hl0]
  unfold ltable
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  exact ltableFrom_ok L hm E hnb 5 0 rfl t₁ ⟨f₁, fun r h₁ _ _ => g₁ r h₁, rd₁, wr₁⟩ T₁

/-! ## `lAddr` -/

theorem and63_zf32 {v : Nat} (hv : v < 2 ^ 32) : (BitVec.ofNat 32 v &&& 63#32 == 0) = decide (v % 64 = 0) := by
  have : BitVec.ofNat 32 v &&& 63#32 = BitVec.ofNat 32 (v % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat32 hv, show (63#32).toNat = 2 ^ 6 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat32 (by omega_arith)]
  rw [this, beq_zero32 (by omega_arith)]

/-- An `i` that `2^j` divides is a multiple of 64 unless `j < 6`. -/
theorem lt6_of {i j : Nat} (h64 : ¬ i % 64 = 0) (hj : i % 2 ^ j = 0) : j < 6 := by
  by_contra h
  exact h64 (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 (show 6 ≤ j by omega_arith))
    (Nat.dvd_of_mod_eq_zero hj)))

/-- Where `lAddr` finds `L_{ntz(i)}`, as an offset into `W`: its entry in
the table, or `lO` when `i` is a multiple of 64. -/
def lOff (i : Nat) : Nat := if i % 64 = 0 then lO else tblO + 16 * ntz i

/-- The offset and the checksum's blocks of `W`, where `lAddr` keeps the
registers across `lNtz`. -/
abbrev spillR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩]

/-- What `lAddr` writes: `lNtz`'s block and count, and those two blocks. -/
abbrev lAddrR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩]

theorem inMut_lAddrR (p : Prm) : InMut p (lAddrR p) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inl (by decide))

/-- A part of `W` that `lAddr` does not write. -/
theorem lAddrR_w {p : Prm} {d k : Nat}
    (h : d + k ≤ ofsO ∨ (48 ≤ d ∧ d + k ≤ lO) ∨ (112 ≤ d ∧ d + k ≤ kO) ∨ 224 ≤ d) (hd : d + k ≤ 2560) :
    ∀ r ∈ lAddrR p, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    exact Lay.w_w (by simp only [ofsO, ckO, lO, kO] at h ⊢; omega_arith) hd (by decide)

/-- What `lAddr` leaves. -/
structure LAddrPost (p : Prm) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame (lAddrR p) s.mem s'.mem
  edx : s'.gpr .edx = p.W + BitVec.ofNat 32 (lOff i)
  le : lOff i + 16 ≤ 384
  val : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 (lOff i)) = lAt l (ntz i)
  x0 : s'.xmm .xmm0 = s.xmm .xmm0
  x1 : s'.xmm .xmm1 = s.xmm .xmm1
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LAddrPost.env {p : Prm} (L : Lay p) {l : Block} {i : Nat} {s s' : State} (E : Env p s)
    (h : LAddrPost p l i s s') : Env p s' :=
  E.mut L (by rw [h.gpr _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [h.gpr _ (by decide) (by decide) (by decide), E.esp]) h.rd h.wr (frame_toMut h.frame (inMut_lAddrR p))

/-- The head of `lAddr`: `i` in `eax`, and ZF set if it is a multiple of 64. -/
theorem lAddrHead_ok {s : State} {i : Nat} (hi' : i < 2 ^ 32) (hdi : s.gpr .edi = BitVec.ofNat 32 i) :
    ∃ s₁, runBlock isa [.mov .eax (.reg .edi), .alu .test .eax (imm 63)] s = some s₁ ∧
      s₁.gpr .eax = BitVec.ofNat 32 i ∧ s₁.zf = some (decide (i % 64 = 0)) ∧
      (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.xmm = s.xmm ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
  ⟨_, by grun [hdi], by gregs [hdi], by gmems [hdi, and63_zf32 hi'], fun r h => by gregs [h], by gmems [],
    by smems [], by gmems [], by gmems []⟩

/-- The offset and the checksum stored in `W`. -/
theorem spill_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa [.movdquStore (at_ .ebp ofsO) .xmm0, .movdquStore (at_ .ebp ckO) .xmm1] s = some s' ∧
      s'.mem = (s.mem.writeW (w64 p.W + BitVec.ofNat 64 ofsO) (s.xmm .xmm0)).writeW
        (w64 p.W + BitVec.ofNat 64 ckO) (s.xmm .xmm1) ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by srun [E.ebp, L.aW, E.perm.wW], by smems [], by smems [], by smems [], by smems [], by smems []⟩

theorem spill_frame (p : Prm) (m : Mem) (a b : BitVec 128) :
    Frame (spillR p) m ((m.writeW (w64 p.W + BitVec.ofNat 64 ofsO) a).writeW (w64 p.W + BitVec.ofNat 64 ckO) b) :=
  ((Frame.refl _ _).writeW (r := ⟨_, 16⟩) (by simp) a (Region.contains_self _ _)).writeW (r := ⟨_, 16⟩) (by simp) b
    (Region.contains_self _ _)

theorem inMut_spillR (p : Prm) : InMut p (spillR p) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact inMut_w p (.inl (by decide))

/-- The blocks stored, read back as blocks and as the registers'. -/
theorem spill_ofs (p : Prm) (m : Mem) (a b : BitVec 128) :
    ((m.writeW (w64 p.W + BitVec.ofNat 64 ofsO) a).writeW (w64 p.W + BitVec.ofNat 64 ckO) b).readW
      (w64 p.W + BitVec.ofNat 64 ofsO) 128 = a := by
  rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self _ _ 16 _ (by decide)]

theorem spill_ck (p : Prm) (m : Mem) (a b : BitVec 128) :
    ((m.writeW (w64 p.W + BitVec.ofNat 64 ofsO) a).writeW (w64 p.W + BitVec.ofNat 64 ckO) b).readW
      (w64 p.W + BitVec.ofNat 64 ckO) 128 = b :=
  Mem.readW_writeW_self _ _ 16 _ (by decide)

/-- The offset and the checksum loaded from `W`. -/
theorem unspill_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa [.movdquLoad .xmm0 (at_ .ebp ofsO), .movdquLoad .xmm1 (at_ .ebp ckO)] s = some s' ∧
      s'.xmm .xmm0 = s.mem.readW (w64 p.W + BitVec.ofNat 64 ofsO) 128 ∧
      s'.xmm .xmm1 = s.mem.readW (w64 p.W + BitVec.ofNat 64 ckO) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by srun [E.ebp, L.aW, E.perm.wR], by smems [E.ebp, L.aW], by smems [E.ebp, L.aW], by smems [], by smems [],
    by smems [], by smems []⟩

/-- `W + lO` in `edx`. -/
theorem lAddrSlow_ok {p : Prm} {s : State} (E : Env p s) :
    ∃ s', runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm lO)] s = some s' ∧
      s'.gpr .edx = p.W + BitVec.ofNat 32 lO ∧ (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by grun [], by gregs [E.ebp], fun r h => by gregs [h], by gmems [], by smems [], by gmems [], by gmems []⟩

/-- The start of the walk: the table in `edx`, and ZF set if `i` is even. -/
theorem lAddrFast_ok {p : Prm} {s : State} (E : Env p s) {i : Nat} (hi' : i < 2 ^ 32)
    (hax : s.gpr .eax = BitVec.ofNat 32 i) :
    ∃ s', runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm tblO), .alu .test .eax (imm 1)] s = some s' ∧
      s'.gpr .edx = p.W + BitVec.ofNat 32 (tblO + 16 * 0) ∧ s'.gpr .eax = BitVec.ofNat 32 (i / 2 ^ 0) ∧
      s'.zf = some (decide (i % 2 = 0)) ∧ (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by grun [], by gregs [E.ebp], by gregs [hax, Nat.pow_zero, Nat.div_one], by gmems [hax, even_zf32 hi'],
    fun r h => by gregs [h], by gmems [], by smems [], by gmems [], by gmems []⟩

/-- One step of the walk: an entry on, `i / 2^j` halved, and ZF set if what
is left is even. -/
theorem lAddrStep_ok {p : Prm} {t : State} {j k : Nat} (hk : k < 2 ^ 32) (hax : t.gpr .eax = BitVec.ofNat 32 k)
    (hdx : t.gpr .edx = p.W + BitVec.ofNat 32 (tblO + 16 * j)) :
    ∃ t', runBlock isa [.alu .add .edx (imm 16), .shift .shr .eax 1, .alu .test .eax (imm 1)] t = some t' ∧
      t'.gpr .edx = p.W + BitVec.ofNat 32 (tblO + 16 * (j + 1)) ∧ t'.gpr .eax = BitVec.ofNat 32 (k / 2) ∧
      t'.zf = some (decide (k / 2 % 2 = 0)) ∧ (∀ r, r ≠ .eax → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧
      t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [], ?_, by gregs [hax, shr1_32 hk], ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [],
    by smems [], by gmems [], by gmems []⟩
  · gregs [hdx]; rw [add_ofNat_assoc32]
    exact congrArg _ (congrArg _ (by omega_arith))
  · gmems [hax, shr1_32 hk, even_zf32 (show k / 2 < 2 ^ 32 by omega_arith)]

theorem lAddr_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {l : Block} {i M : Nat} (hi : 0 < i)
    (hi' : i < 2 ^ 32) (him : i ≤ M) (hdi : s.gpr .edi = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) (hT : Tbl p l M s.mem) :
    WP isa lAddr s (LAddrPost p l i s) := by
  obtain ⟨s₁, run₁, ax₁, zf₁, g₁, m₁, x₁, rd₁, wr₁⟩ := lAddrHead_ok hi' hdi
  have E₁ : Env p s₁ := E.keep (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ m₁
  unfold lAddr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (i % 64 = 0)) (eval_e zf₁) (fun hb => ?_) (fun hb => ?_)
  · -- a multiple of 64: `lNtz`, the registers kept in `W`
    have h64 : i % 64 = 0 := of_decide_eq_true hb
    obtain ⟨s₂, run₂, m₂, g₂, x₂, rd₂, wr₂⟩ := spill_ok L E₁
    have f₂ : Frame (spillR p) s₁.mem s₂.mem := by rw [m₂]; exact spill_frame p _ _ _
    have E₂ : Env p s₂ := E₁.mut L (by rw [g₂, E₁.ebp]) (by rw [g₂, E₁.esp]) rd₂ wr₂
      (frame_toMut f₂ (inMut_spillR p))
    have hl0₂ : blockAtMem s₂.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0 := by
      rw [Proof.Ocb.blockAtMem_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), m₁, hl0]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.seq (WP.mono (lNtz_ok L E₂ hi hi' (by rw [g₂, g₁ _ (by decide), hdi]) hl0₂) fun s₃ P₃ => ?_)
    have E₃ := P₃.env L E₂
    have rd128 : ∀ {d : Nat}, d = ofsO ∨ d = ckO →
        s₃.mem.readW (w64 p.W + BitVec.ofNat 64 d) 128 = s₂.mem.readW (w64 p.W + BitVec.ofNat 64 d) 128 :=
      fun {d} h => P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> rcases h with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide))
        (by decide)
    obtain ⟨s₄, run₄, x0₄, x1₄, g₄, m₄, rd₄, wr₄⟩ := unspill_ok L E₃
    have E₄ : Env p s₄ := E₃.keep (by rw [g₄]) (by rw [g₄]) rd₄ wr₄ m₄
    obtain ⟨s₅, run₅, dx₅, g₅, m₅, x₅, rd₅, wr₅⟩ := lAddrSlow_ok E₄
    refine WP.of_runBlock ⟨s₅, runBlock_app_of run₄ run₅, ?_⟩
    have e : lOff i = lO := by rw [lOff, ite_eq_left h64]
    refine ⟨?_, by rw [e, dx₅], by rw [e]; decide, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, by rw [rd₅, rd₄, P₃.rd, rd₂, rd₁],
      by rw [wr₅, wr₄, P₃.wr, wr₂, wr₁]⟩
    · rw [m₅, m₄, ← m₁]
      exact (f₂.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
        (P₃.frame.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
    · rw [e, m₅, m₄, P₃.val]
    · rw [x₅, x0₄, rd128 (.inl rfl), m₂, spill_ofs, x₁]
    · rw [x₅, x1₄, rd128 (.inr rfl), m₂, spill_ck, x₁]
    · rw [g₅ r h₃, g₄, P₃.gpr r h₁ h₂ h₃, g₂, g₁ r h₁]
  · -- in the table
    have h64 : ¬ i % 64 = 0 := of_decide_eq_false hb
    obtain ⟨s₂, run₂, dx₂, ax₂, zf₂, g₂, m₂, x₂, rd₂, wr₂⟩ := lAddrFast_ok E₁ hi' ax₁
    have post_of : ∀ (t : State) (j : Nat), ntz i = j → i % 2 ^ j = 0 →
        t.gpr .edx = p.W + BitVec.ofNat 32 (tblO + 16 * j) → (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) →
        t.mem = s.mem → t.xmm = s.xmm → t.rd = s.rd → t.wr = s.wr → LAddrPost p l i s t :=
      fun t j hj hd dx g m x rd wr => by
        have hj6 : j < 6 := lt6_of h64 hd
        have hjT : j < tblLen M := lt_tblLen hj6
          (Nat.le_trans (Nat.le_of_dvd hi (Nat.dvd_of_mod_eq_zero hd)) him)
        have e : lOff i = tblO + 16 * j := by rw [lOff, ite_eq_right h64, hj]
        have h288 : tblO = 288 := rfl
        exact ⟨by rw [m]; exact Frame.refl _ _, by rw [e, dx], by rw [e]; omega_arith,
          by rw [e, m, hT j hjT hj6, hj], by rw [x], by rw [x], fun r h₁ _ h₃ => g r h₁ h₃, rd, wr⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.ite (!decide (i % 2 = 0)) (eval_ne zf₂) (fun hb₂ => WP.block_nil ?_) (fun hb₂ => ?_)
    · have ho : i % 2 = 1 := by
        have : ¬ i % 2 = 0 := by simpa using hb₂
        omega_arith
      exact post_of s₂ 0 (Proof.Ocb.ntz_odd ho) (Nat.mod_one _) dx₂ (fun r h₁ h₂ => by rw [g₂ r h₂, g₁ r h₁])
        (by rw [m₂, m₁]) (by rw [x₂, x₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    have he : i % 2 = 0 := by simpa using hb₂
    refine WP.loop (M := isa) (c := .e)
      (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
        ntz i = j + ntz (i / 2 ^ j) ∧ i % 2 ^ j = 0 ∧ t.gpr .eax = BitVec.ofNat 32 (i / 2 ^ j) ∧
        t.gpr .edx = p.W + BitVec.ofNat 32 (tblO + 16 * j) ∧ (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.xmm = s.xmm ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
      ⟨0, rfl, by simpa using hi, by simpa using he, by simp, Nat.mod_one _, ax₂, dx₂,
        fun r h₁ h₂ => by rw [g₂ r h₂, g₁ r h₁], by rw [m₂, m₁], by rw [x₂, x₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    rintro k t ⟨j, rfl, hpos, hev, hntz, hdv, ax, dx, g, m, x, rd, wr⟩
    have hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
    have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    obtain ⟨t₂, runt, dx', ax', zf', g', m', x', rd', wr'⟩ := lAddrStep_ok (p := p) hv ax dx
    rw [← e] at ax' zf'
    refine WP.of_runBlock ⟨t₂, runt, ?_⟩
    have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
      rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega_using []
    have hdv' : i % 2 ^ (j + 1) = 0 := by rw [Nat.mod_pow_succ, hdv, hev, Nat.mul_zero]
    have gg : ∀ r, r ≠ .eax → r ≠ .edx → t₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
    by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
    · right
      exact ⟨(eval_e zf').trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega_using [hpos], j + 1, rfl,
        by rw [e]; omega_using [hpos, hev], hodd, hntz', hdv', ax', dx', gg, by rw [m', m], by rw [x', x],
        by rw [rd', rd], by rw [wr', wr]⟩
    · left
      refine ⟨(eval_e zf').trans (by simp [hodd]), post_of t₂ (j + 1) ?_ hdv' dx' gg (by rw [m', m]) (by rw [x', x])
        (by rw [rd', rd]) (by rw [wr', wr])⟩
      rw [hntz', Proof.Ocb.ntz_odd (by omega_using [hodd])]

/-! ## A block -/

/-- What a body does to the block in `xmm3` and the checksum in `xmm1`, with
the offset in `xmm0`: nothing else but to the other SSE registers. -/
def BodyOk (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ t : State, ∃ t', runBlock isa body t = some t' ∧
    rv (t'.xmm .xmm3) = fB (rv (t.xmm .xmm3)) (rv (t.xmm .xmm0)) ∧
    rv (t'.xmm .xmm1) = fC (rv (t.xmm .xmm1)) (rv (t.xmm .xmm3)) (rv (t.xmm .xmm0)) ∧
    t'.xmm .xmm0 = t.xmm .xmm0 ∧ t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok : BodyOk xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := fun t =>
  ⟨_, by srun [xorOfs], by smems [eval_pxor, rv_xor], by smems [], by smems [], by smems [], by smems [],
    by smems [], by smems []⟩

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok : BodyOk (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := fun t =>
  ⟨_, by srun [addCk, xorOfs], by smems [eval_pxor, rv_xor], by smems [eval_pxor, rv_xor], by smems [],
    by smems [], by smems [], by smems [], by smems []⟩

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok : BodyOk (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := fun t =>
  ⟨_, by srun [addCk, xorOfs], by smems [eval_pxor, rv_xor], by smems [eval_pxor, rv_xor], by smems [],
    by smems [], by smems [], by smems [], by smems []⟩

/-- What the code `ofs` does to the offset in `xmm0`, for block `i + 1`:
`⊕ L_{ntz(i+1)}`, changing `xmm2` at most besides. -/
def OfsOk (ofs : List Instr) (l : Block) (i : Nat) (t : State) : Prop :=
  ∃ u, runBlock isa ofs t = some u ∧ rv (u.xmm .xmm0) = rv (t.xmm .xmm0) ^^^ lAt l (ntz (i + 1)) ∧
    u.xmm .xmm1 = t.xmm .xmm1 ∧ u.gpr = t.gpr ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr

/-- `L_{ntz(i+1)}` at `edx`, a block of `W`. -/
theorem ofsDx_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {i a : Nat} (ha : a + 16 ≤ 2560)
    (hdx : t.gpr .edx = p.W + BitVec.ofNat 32 a)
    (hv : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 a) = lAt l (ntz (i + 1))) : OfsOk ofsDx l i t := by
  have a0 : w64 (p.W + BitVec.ofNat 32 a + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 a := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact L.aW (by omega_arith)
  have r : InRegions (t.rd ++ t.wr) (w64 p.W + BitVec.ofNat 64 a) 16 := E.perm.wR ha
  refine ⟨_, by srun [ofsDx, hdx, a0, r], ?_, by smems [], by smems [], by smems [], by smems [], by smems []⟩
  smems [hdx, a0, eval_pxor, rv_xor]
  rw [← blockAtMem_eq, hv]

/-- What a pass writes: `lAddr`'s parts of `W`, and the blocks. -/
abbrev passR (p : Prm) (m : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩]

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them, with the offset and the checksum in `W`. -/
structure PassInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (passR p m) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  esi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * i)
  edi : t.gpr .edi = BitVec.ofNat 32 (i + 1)
  ebx : t.gpr .ebx = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0
  tbl : Tbl p l m t.mem
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t.gpr r = t₀.gpr r

/-- The same, among the blocks: the offset and the checksum in `xmm0` and
`xmm1`. -/
structure XInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (passR p m) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  esi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * i)
  edi : t.gpr .edi = BitVec.ofNat 32 (i + 1)
  ofs : rv (t.xmm .xmm0) = offAt O0 l i
  ck : rv (t.xmm .xmm1) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0
  tbl : Tbl p l m t.mem
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t.gpr r = t₀.gpr r

/-- The data's blocks are apart from `W`. -/
theorem dataBlk_w {p : Prm} (L : Lay p) {k d n : Nat} (hk : 16 * k + 16 ≤ p.n) (hd : d + n ≤ 2560) :
    (⟨w64 p.D + BitVec.ofNat 64 (16 * k), 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, n⟩ :=
  (L.d_w.sub_left (Offset.sub_base _ hk)).sub_right (Lay.wSub hd)

/-- A state that differs in `ebx`, the flags and the other SSE registers. -/
theorem XInv.of_eq {p : Prm} {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {ckF : Nat → Block} {t₀ t t' : State} {i : Nat} (P : XInv p m O0 l X fB ckF t₀ t i)
    (hg : ∀ r, r ≠ .ebx → t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) (hx : t'.xmm = t.xmm) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) : XInv p m O0 l X fB ckF t₀ t' i :=
  ⟨P.env.keep (hg _ (by decide)) (hg _ (by decide)) hrd hwr hm, by rw [hm]; exact P.frame, by rw [hrd, P.rd],
    by rw [hwr, P.wr], by rw [hg _ (by decide), P.esi], by rw [hg _ (by decide), P.edi], by rw [hx]; exact P.ofs,
    by rw [hx]; exact P.ck, by rw [hm]; exact P.blk, by rw [hm]; exact P.l0, by rw [hm]; exact P.tbl,
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [hg r h₂, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]⟩

/-- Across `lAddr`. -/
theorem XInv.lAddr {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {ckF : Nat → Block} {t₀ t t' : State} {i j : Nat} (hm : 16 * m ≤ p.n) (P : XInv p m O0 l X fB ckF t₀ t i)
    (P₁ : LAddrPost p l j t t') : XInv p m O0 l X fB ckF t₀ t' i := by
  refine ⟨P₁.env L P.env, P.frame.trans (P₁.frame.mono fun r hr => ?_), by rw [P₁.rd, P.rd], by rw [P₁.wr, P.wr],
    by rw [P₁.gpr _ (by decide) (by decide) (by decide), P.esi],
    by rw [P₁.gpr _ (by decide) (by decide) (by decide), P.edi], by rw [P₁.x0]; exact P.ofs,
    by rw [P₁.x1]; exact P.ck, fun k hk => ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => by
      rw [P₁.gpr r h₁ h₃ h₄, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact dataBlk_w L (by omega_arith) (by decide)), P.blk k hk]
  · rw [Proof.Ocb.blockAtMem_frame P₁.frame (lAddrR_w (.inr (.inl ⟨by decide, by decide⟩)) (by decide)), P.l0]
  · exact P.tbl.frame P₁.frame (lAddrR_w (.inr (.inr (.inr (by decide)))) (by decide))

/-- One block, `i + 1`: its offset (`ofs`), then the block through `body`. -/
theorem blockStep_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body ofs : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i : Nat} (hi : i < m) (P : XInv p m O0 l X fB ckF t₀ t i)
    (hofs : OfsOk ofs l i t) :
    ∃ t', runBlock isa (ofs ++ blockOps body) t = some t' ∧ XInv p m O0 l X fB ckF t₀ t' (i + 1) ∧
      t'.gpr .ebx = t.gpr .ebx := by
  have hn := L.n32
  have hd := L.dw
  obtain ⟨u₁, run₁, o₁, x1₁, g₁, m₁, rd₁, wr₁⟩ := hofs
  obtain E₁ : Env p u₁ := P.env.keep (by rw [g₁]) (by rw [g₁]) rd₁ wr₁ m₁
  obtain hBi := dblk L E₁ (i := i) (by omega_arith)
  obtain a16 : w64 (p.D + BitVec.ofNat 32 (16 * i)) = w64 p.D + BitVec.ofNat 64 (16 * i) := w64_add (by omega_arith)
  obtain a0 : w64 (p.D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 (16 * i) := by
    rw [add_ofNat_assoc32, Nat.add_zero, a16]
  obtain si₁ : u₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₁, P.esi]
  obtain rB : InRegions (u₁.rd ++ u₁.wr) (w64 p.D + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [← a16]; exact in_left (hBi.wr _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  -- the load
  obtain run₂ : runBlock isa [.movdquLoad .xmm3 (at_ .esi 0)] u₁ =
      some (u₁.setXmm .xmm3 (u₁.mem.readW (w64 p.D + BitVec.ofNat 64 (16 * i)) 128)) := by
    srun [si₁, a0, rB]
  -- the body
  obtain ⟨u₃, run₃, b₃, c₃, x0₃, g₃, m₃, rd₃, wr₃⟩ :=
    hB (u₁.setXmm .xmm3 (u₁.mem.readW (w64 p.D + BitVec.ofNat 64 (16 * i)) 128))
  obtain si₃ : u₃.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃, gpr_setXmm, si₁]
  obtain di₃ : u₃.gpr .edi = BitVec.ofNat 32 (i + 1) := by rw [g₃, gpr_setXmm, g₁, P.edi]
  obtain wB : InRegions u₃.wr (w64 p.D + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [wr₃, wr_setXmm, ← a16]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  -- the store and the next block
  obtain ⟨u₄, run₄, m₄, si₄, di₄, g₄, x₄, rd₄, wr₄⟩ : ∃ u₄, runBlock isa
      [.movdquStore (at_ .esi 0) .xmm3, .alu .add .esi (imm 16), .alu .add .edi (imm 1)] u₃ = some u₄ ∧
      u₄.mem = u₃.mem.writeW (w64 p.D + BitVec.ofNat 64 (16 * i)) (u₃.xmm .xmm3) ∧
      u₄.gpr .esi = p.D + BitVec.ofNat 32 (16 * (i + 1)) ∧ u₄.gpr .edi = BitVec.ofNat 32 (i + 1 + 1) ∧
      (∀ r, r ≠ .esi → r ≠ .edi → u₄.gpr r = u₃.gpr r) ∧ u₄.xmm = u₃.xmm ∧ u₄.rd = u₃.rd ∧ u₄.wr = u₃.wr := by
    refine ⟨_, by srun [si₃, a0, wB], by smems [si₃, a0], ?_, ?_, fun r h₁ h₂ => by sregs [h₁, h₂], by smems [],
      by smems [], by smems []⟩
    · sregs [si₃]; rw [add_ofNat_assoc32, show 16 * i + 16 = 16 * (i + 1) by omega_arith]
    · sregs [di₃]; rw [← BitVec.ofNat_add]
  refine ⟨u₄, runBlock_app_of run₁ (runBlock_app_of (runBlock_app_of run₂ run₃) run₄), ?_, ?_⟩
  rotate_left
  · rw [g₄ _ (by decide) (by decide), g₃, gpr_setXmm, g₁]
  obtain hBX : blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) = X i := by rw [P.blk i hi]; simp
  obtain e3 : rv (u₃.xmm .xmm3) = fB (X i) (offAt O0 l (i + 1)) := by
    rw [b₃, xmm_setXmm_self, xmm_setXmm_of_ne (r := .xmm3) (r' := .xmm0) _ _ (by decide), ← blockAtMem_eq, o₁, P.ofs,
      m₁, hBX]; rfl
  obtain fB4 : Frame [⟨w64 p.D + BitVec.ofNat 64 (16 * i), 16⟩] t.mem u₄.mem := by
    rw [m₄, m₃, mem_setXmm, m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain kW : ∀ {d : Nat}, d + 16 ≤ 2560 →
      blockAtMem u₄.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame fB4 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dataBlk_w L (by omega_arith) h).symm
  refine ⟨?_, ?_, ?_, ?_, si₄, di₄, ?_, ?_, fun k hk => ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_⟩
  · exact E₁.mut L (by rw [g₄ _ (by decide) (by decide), g₃, gpr_setXmm, E₁.ebp])
      (by rw [g₄ _ (by decide) (by decide), g₃, gpr_setXmm, E₁.esp]) (by rw [rd₄, rd₃, rd_setXmm])
      (by rw [wr₄, wr₃, wr_setXmm]) (frame_toMut (by rw [m₁]; exact fB4) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩)
  · exact P.frame.trans (fB4.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 p.D, 16 * m⟩, by simp, Offset.sub_base _ (by omega_arith)⟩)
  · rw [rd₄, rd₃, rd_setXmm, rd₁, P.rd]
  · rw [wr₄, wr₃, wr_setXmm, wr₁, P.wr]
  · rw [x₄, x0₃, xmm_setXmm_of_ne (r := .xmm3) (r' := .xmm0) _ _ (by decide), o₁, P.ofs]; rfl
  · rw [x₄, c₃, xmm_setXmm_of_ne (r := .xmm3) (r' := .xmm1) _ _ (by decide), xmm_setXmm_self,
      xmm_setXmm_of_ne (r := .xmm3) (r' := .xmm0) _ _ (by decide), x1₁, P.ck, ← blockAtMem_eq, m₁, hBX, o₁, P.ofs,
      hckF i hi]; rfl
  · by_cases hki : k = i
    · subst hki
      rw [m₄, blockAtMem_writeW, e3]; simp
    · rw [Proof.Ocb.blockAtMem_frame fB4 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega_arith]
      · simp [hk', show ¬ k < i + 1 by omega_arith]
  · rw [kW (by decide), P.l0]
  · exact P.tbl.frame fB4 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dataBlk_w L (by omega_arith) (by decide)).symm
  · rw [g₄ r h₅ h₆, g₃, gpr_setXmm, g₁, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]

/-! ## The blocks, one at a time -/

/-- One iteration of `single`: block `i + 1`, with `m − i` left. -/
theorem singleStep_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i : Nat} (hi : i < m) (P : XInv p m O0 l X fB ckF t₀ t i)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - i)) :
    WP isa (.seq lAddr (.block (ofsDx ++ blockOps body ++ ([.alu .sub .ebx (imm 1)] : List Instr)))) t fun t' =>
      XInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.gpr .ebx = BitVec.ofNat 32 (m - (i + 1)) ∧
      t'.zf = some (decide (m - (i + 1) = 0)) := by
  have hn := L.n32
  refine WP.seq (WP.mono (lAddr_ok L P.env (by omega_arith) (by omega_arith) (by omega_arith) P.edi P.l0 P.tbl)
    fun t₁ P₁ => ?_)
  obtain Q := P.lAddr L hm P₁
  obtain ⟨t₂, run₂, Q₂, bx₂⟩ := blockStep_ok L hB hckF hm hi Q
    (ofsDx_ok L Q.env (by have := P₁.le; omega_arith) P₁.edx P₁.val)
  obtain bx₂' : t₂.gpr .ebx = BitVec.ofNat 32 (m - i) := by
    rw [bx₂, P₁.gpr _ (by decide) (by decide) (by decide), hbx]
  obtain ⟨t₃, run₃, bx₃, zf₃, g₃, m₃, x₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.alu .sub .ebx (imm 1)] t₂ = some t₃ ∧
      t₃.gpr .ebx = BitVec.ofNat 32 (m - (i + 1)) ∧ t₃.zf = some (decide (m - (i + 1) = 0)) ∧
      (∀ r, r ≠ .ebx → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.xmm = t₂.xmm ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by grun [], ?_, ?_, fun r h => by gregs [h], by gmems [], by smems [], by gmems [], by gmems []⟩
    · gregs [bx₂']; rw [sub1_32 (by omega_arith) (by omega_arith), show m - i - 1 = m - (i + 1) by omega_arith]
    · gmems [bx₂']
      rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  exact WP.of_runBlock ⟨t₃, runBlock_app_of run₂ run₃, Q₂.of_eq g₃ m₃ x₃ rd₃ wr₃, bx₃, zf₃⟩

/-- `single`: the blocks from `i₀ + 1` on. -/
theorem single_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i₀ : Nat} (hi₀ : i₀ < m)
    (P : XInv p m O0 l X fB ckF t₀ t i₀) (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - i₀)) :
    WP isa (single body) t fun t' => XInv p m O0 l X fB ckF t₀ t' m ∧ t'.gpr .ebx = BitVec.ofNat 32 (m - m) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ XInv p m O0 l X fB ckF t₀ u i ∧
      u.gpr .ebx = BitVec.ofNat 32 (m - i)) ?_ (m - i₀) _ ⟨i₀, rfl, hi₀, P, hbx⟩
  rintro k u ⟨i, rfl, hi, P, hbx⟩
  refine WP.mono (singleStep_ok L hB hckF hm hi P hbx) fun u' ⟨P', bx', hz⟩ => ?_
  by_cases he : m - (i + 1) = 0
  · left
    obtain rfl : i + 1 = m := by omega_arith
    exact ⟨(eval_ne hz).trans (by simp [he]), P', bx'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P', bx'⟩

/-! ## Four blocks at a time -/

theorem eval_ae {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .ae s = some !b := by
  show s.cf.map _ = _; rw [h]; rfl

theorem ntz_4k1 (k : Nat) : ntz (4 * k + 1) = 0 := Proof.Ocb.ntz_odd (by omega_arith)

theorem ntz_4k3 (k : Nat) : ntz (4 * k + 3) = 0 := Proof.Ocb.ntz_odd (by omega_arith)

theorem ntz_4k2 (k : Nat) : ntz (4 * k + 2) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega_arith) (by omega_arith), show (4 * k + 2) / 2 = 2 * k + 1 by omega_arith,
    Proof.Ocb.ntz_odd (by omega_arith)]

/-- `L_j` from the table, for a block whose `ntz` is `j`. -/
theorem ofsAt_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {i j n : Nat} (hj : j < 6)
    (hjn : j < n) (hT : TblN p l n t.mem) (hn : ntz (i + 1) = j) : OfsOk (ofsAt j) l i t := by
  have h288 : tblO = 288 := rfl
  have r : InRegions (t.rd ++ t.wr) (w64 p.W + BitVec.ofNat 64 (tblO + 16 * j)) 16 := E.perm.wR (by omega_arith)
  have a0 : w64 (p.W + BitVec.ofNat 32 (tblO + 16 * j)) = w64 p.W + BitVec.ofNat 64 (tblO + 16 * j) :=
    L.aW (by omega_arith)
  refine ⟨_, by srun [ofsAt, E.ebp, a0, r], ?_, by smems [], by smems [], by smems [], by smems [], by smems []⟩
  smems [E.ebp, a0, eval_pxor, rv_xor]
  rw [← blockAtMem_eq, hT j hjn hj, hn]

/-- The first three blocks of four, `4k + 1` to `4k + 3`. -/
theorem quadHead_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {k : Nat} (hk : 4 * k + 4 ≤ m)
    (P : XInv p m O0 l X fB ckF t₀ t (4 * k)) :
    ∃ t', runBlock isa (stepAt 0 body ++ stepAt 1 body ++ stepAt 0 body) t = some t' ∧
      XInv p m O0 l X fB ckF t₀ t' (4 * k + 1 + 1 + 1) ∧ t'.gpr .ebx = t.gpr .ebx := by
  -- four blocks: the table has `L_0` and `L_1`
  obtain h0 : 0 < tblLen m := lt_tblLen (by decide) (by omega_arith)
  obtain h1 : 1 < tblLen m := lt_tblLen (by decide) (by omega_arith)
  obtain ⟨t₁, run₁, P₁, b₁⟩ := blockStep_ok L hB hckF hm (by omega_arith) P
    (ofsAt_ok L P.env (j := 0) (by decide) h0 P.tbl (ntz_4k1 k))
  obtain ⟨t₂, run₂, P₂, b₂⟩ := blockStep_ok L hB hckF hm (by omega_arith) P₁
    (ofsAt_ok L P₁.env (j := 1) (by decide) h1 P₁.tbl
      (by rw [show 4 * k + 1 + 1 = 4 * k + 2 by omega_arith, ntz_4k2]))
  obtain ⟨t₃, run₃, P₃, b₃⟩ := blockStep_ok L hB hckF hm (by omega_arith) P₂
    (ofsAt_ok L P₂.env (j := 0) (by decide) h0 P₂.tbl
      (by rw [show 4 * k + 1 + 1 + 1 = 4 * k + 3 by omega_arith, ntz_4k3]))
  exact ⟨t₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, P₃, by rw [b₃, b₂, b₁]⟩

/-- The fourth block, `4k + 4`, and the count of those left. -/
theorem quadTail_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {k : Nat} (hk : 4 * k + 4 ≤ m)
    (P : XInv p m O0 l X fB ckF t₀ t (4 * k + 1 + 1 + 1)) (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 4 * k)) :
    WP isa (.seq lAddr (.block (ofsDx ++ blockOps body ++
        ([.alu .sub .ebx (imm 4), .alu .cmp .ebx (imm 4)] : List Instr)))) t fun t' =>
      XInv p m O0 l X fB ckF t₀ t' (4 * (k + 1)) ∧ t'.gpr .ebx = BitVec.ofNat 32 (m - 4 * (k + 1)) ∧
      t'.cf = some (decide (m - 4 * (k + 1) < 4)) := by
  have hn := L.n32
  refine WP.seq (WP.mono (lAddr_ok L P.env (by omega_arith) (by omega_arith) (by omega_arith) P.edi P.l0 P.tbl)
    fun t₁ P₁ => ?_)
  obtain Q := P.lAddr L hm P₁
  obtain ⟨t₂, run₂, Q₂, b₂⟩ := blockStep_ok L hB hckF hm (by omega_arith) Q
    (ofsDx_ok L Q.env (by have := P₁.le; omega_arith) P₁.edx P₁.val)
  obtain bx₂ : t₂.gpr .ebx = BitVec.ofNat 32 (m - 4 * k) := by
    rw [b₂, P₁.gpr _ (by decide) (by decide) (by decide), hbx]
  obtain e : BitVec.ofNat 32 (m - 4 * k) - BitVec.ofNat 32 4 = BitVec.ofNat 32 (m - 4 * (k + 1)) := by
    rw [Proof.AesGcm.X86.ofNat_sub32 (by omega_arith) (by omega_arith)]; exact congrArg _ (by omega_arith)
  obtain ⟨t₃, run₃, bx₃, cf₃, g₃, m₃, x₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      [.alu .sub .ebx (imm 4), .alu .cmp .ebx (imm 4)] t₂ = some t₃ ∧
      t₃.gpr .ebx = BitVec.ofNat 32 (m - 4 * (k + 1)) ∧ t₃.cf = some (decide (m - 4 * (k + 1) < 4)) ∧
      (∀ r, r ≠ .ebx → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.xmm = t₂.xmm ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by grun [], by gregs [bx₂, e], ?_, fun r h => by gregs [h], by gmems [], by smems [], by gmems [],
      by gmems []⟩
    gmems [bx₂, e, toNat_ofNat32 (show m - 4 * (k + 1) < 2 ^ 32 by omega_arith),
      toNat_ofNat32 (show 4 < 2 ^ 32 by decide)]
  refine WP.of_runBlock ⟨t₃, runBlock_app_of run₂ run₃, ?_, bx₃, cf₃⟩
  rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega_arith]
  exact Q₂.of_eq g₃ m₃ x₃ rd₃ wr₃

/-- `quad`: four blocks at a time from block `4 k₀ + 1`, while four are left. -/
theorem quad_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {k₀ : Nat} (hk₀ : 4 * k₀ + 4 ≤ m)
    (P : XInv p m O0 l X fB ckF t₀ t (4 * k₀)) (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 4 * k₀)) :
    WP isa (quad body) t fun t' => XInv p m O0 l X fB ckF t₀ t' (4 * (m / 4)) ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - 4 * (m / 4)) := by
  refine WP.loop (M := isa) (c := .ae)
    (fun (n : Nat) (u : State) => ∃ k, n = m - 4 * k ∧ 4 * k + 4 ≤ m ∧ XInv p m O0 l X fB ckF t₀ u (4 * k) ∧
      u.gpr .ebx = BitVec.ofNat 32 (m - 4 * k)) ?_ (m - 4 * k₀) _ ⟨k₀, rfl, hk₀, P, hbx⟩
  rintro n u ⟨k, rfl, hk, P, hbx⟩
  obtain ⟨u₃, run₃, P₃, b₃⟩ := quadHead_ok L hB hckF hm hk P
  refine WP.seq (WP.of_runBlock ⟨u₃, run₃, ?_⟩)
  refine WP.mono (quadTail_ok L hB hckF hm hk P₃ (by rw [b₃, hbx])) fun u' ⟨P', bx', cf'⟩ => ?_
  by_cases he : m - 4 * (k + 1) < 4
  · left
    have e : m / 4 = k + 1 := by omega_arith
    rw [e]
    exact ⟨(eval_ae cf').trans (by simp [he]), P', bx'⟩
  · right
    exact ⟨(eval_ae cf').trans (by simp [he]), m - 4 * (k + 1), by omega_arith, k + 1, rfl, by omega_arith, P', bx'⟩

/-! ## The pass -/

/-- The offset and the checksum loaded, and CF set if fewer than four blocks
are left. -/
theorem passLoad_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {ckF : Nat → Block} {t₀ t : State} {i : Nat} (hm : 16 * m ≤ p.n) (P : PassInv p m O0 l X fB ckF t₀ t i) :
    ∃ t', runBlock isa [.movdquLoad .xmm0 (at_ .ebp ofsO), .movdquLoad .xmm1 (at_ .ebp ckO),
        .alu .cmp .ebx (imm 4)] t = some t' ∧
      XInv p m O0 l X fB ckF t₀ t' i ∧ t'.gpr .ebx = BitVec.ofNat 32 (m - i) ∧
      t'.cf = some (decide (m - i < 4)) := by
  have hn := L.n32
  obtain ⟨t₁, run₁, x0, x1, g, mm, rd, wr⟩ := unspill_ok L P.env
  obtain bx₁ : t₁.gpr .ebx = BitVec.ofNat 32 (m - i) := by rw [g, P.ebx]
  obtain ⟨t₂, run₂, cf₂, g₂, m₂, x₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.alu .cmp .ebx (imm 4)] t₁ = some t₂ ∧
      t₂.cf = some (decide (m - i < 4)) ∧ t₂.gpr = t₁.gpr ∧ t₂.mem = t₁.mem ∧ t₂.xmm = t₁.xmm ∧ t₂.rd = t₁.rd ∧
      t₂.wr = t₁.wr := by
    refine ⟨_, by grun [], ?_, by gmems [], by gmems [], by smems [], by gmems [], by gmems []⟩
    gmems [bx₁, toNat_ofNat32 (show m - i < 2 ^ 32 by omega_arith), toNat_ofNat32 (show 4 < 2 ^ 32 by decide)]
  exact ⟨t₂, runBlock_app_of run₁ run₂, ⟨P.env.keep (by rw [g₂, g]) (by rw [g₂, g]) (by rw [rd₂, rd])
    (by rw [wr₂, wr]) (by rw [m₂, mm]), by rw [m₂, mm]; exact P.frame, by rw [rd₂, rd, P.rd],
    by rw [wr₂, wr, P.wr], by rw [g₂, g, P.esi], by rw [g₂, g, P.edi], by rw [x₂, x0, ← blockAtMem_eq, P.ofs],
    by rw [x₂, x1, ← blockAtMem_eq, P.ck], by rw [m₂, mm]; exact P.blk, by rw [m₂, mm]; exact P.l0,
    by rw [m₂, mm]; exact P.tbl, fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g₂, g, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]⟩,
    by rw [g₂, bx₁], cf₂⟩

/-- The blocks four at a time, if there are four. -/
theorem quads_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} (P : XInv p m O0 l X fB ckF t₀ t 0)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 0)) (hcf : t.cf = some (decide (m - 0 < 4))) :
    WP isa (.ite .b (.block []) (quad body)) t fun t' => XInv p m O0 l X fB ckF t₀ t' (4 * (m / 4)) ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - 4 * (m / 4)) := by
  refine WP.ite (decide (m - 0 < 4)) (eval_b hcf) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h : m - 0 < 4 := of_decide_eq_true hb
    rw [show m / 4 = 0 by omega_arith]
    exact ⟨P, hbx⟩
  · have h : ¬ m - 0 < 4 := of_decide_eq_false hb
    exact quad_ok L hB hckF hm (k₀ := 0) (by omega_arith) P hbx

/-- ZF set if no block is left. -/
theorem passTest_ok {p : Prm} {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {ckF : Nat → Block} {t₀ t : State} {i b : Nat} (hb : b < 2 ^ 32) (P : XInv p m O0 l X fB ckF t₀ t i)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 b) :
    ∃ t', runBlock isa [.alu .test .ebx (.reg .ebx)] t = some t' ∧ XInv p m O0 l X fB ckF t₀ t' i ∧
      t'.gpr .ebx = BitVec.ofNat 32 b ∧ t'.zf = some (decide (b = 0)) := by
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, x₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.alu .test .ebx (.reg .ebx)] t = some t₁ ∧
      t₁.zf = some (decide (b = 0)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.xmm = t.xmm ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, by gmems [], by gmems [], by smems [], by gmems [], by gmems []⟩
    gmems [hbx, BitVec.and_self, beq_zero32 hb]
  exact ⟨t₁, run₁, P.of_eq (fun r _ => by rw [g₁]) m₁ x₁ rd₁ wr₁, by rw [g₁, hbx], zf₁⟩

/-- The last blocks one at a time, if there are any. -/
theorem tail_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} (P : XInv p m O0 l X fB ckF t₀ t (4 * (m / 4)))
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - 4 * (m / 4))) (hzf : t.zf = some (decide (m - 4 * (m / 4) = 0))) :
    WP isa (.ite .e (.block []) (single body)) t fun t' => XInv p m O0 l X fB ckF t₀ t' m ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - m) := by
  refine WP.ite (decide (m - 4 * (m / 4) = 0)) (eval_e hzf) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have e : 4 * (m / 4) = m := by have := of_decide_eq_true hb; omega_arith
    rw [e] at P hbx
    exact ⟨P, hbx⟩
  · exact single_ok L hB hckF hm (by have := of_decide_eq_false hb; omega_arith) P hbx

/-- The offset and the checksum stored. -/
theorem passStore_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {ckF : Nat → Block} {t₀ t : State} {i : Nat} (hm : 16 * m ≤ p.n)
    (P : XInv p m O0 l X fB ckF t₀ t i) (hbx : t.gpr .ebx = BitVec.ofNat 32 (m - i)) :
    ∃ t', runBlock isa [.movdquStore (at_ .ebp ofsO) .xmm0, .movdquStore (at_ .ebp ckO) .xmm1] t = some t' ∧
      PassInv p m O0 l X fB ckF t₀ t' i := by
  obtain ⟨t', run, mm, g, x, rd, wr⟩ := spill_ok L P.env
  have f : Frame (spillR p) t.mem t'.mem := by rw [mm]; exact spill_frame p _ _ _
  have kW : ∀ {d : Nat}, d + 16 ≤ ofsO ∨ ckO + 16 ≤ d → d + 16 ≤ 2560 →
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by simp only [ofsO, ckO] at h ⊢; omega_arith) h' (by decide)
  refine ⟨t', run, P.env.mut L (by rw [g, P.env.ebp]) (by rw [g, P.env.esp]) rd wr (frame_toMut f (inMut_spillR p)),
    P.frame.trans (f.mono fun r hr => ?_), by rw [rd, P.rd], by rw [wr, P.wr], by rw [g, P.esi], by rw [g, P.edi],
    by rw [g, hbx], ?_, ?_, fun k hk => ?_, by rw [kW (.inr (by decide)) (by decide), P.l0], ?_,
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · rw [blockAtMem_eq, mm, spill_ofs, P.ofs]
  · rw [blockAtMem_eq, mm, spill_ck, P.ck]
  · rw [Proof.Ocb.blockAtMem_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact dataBlk_w L (by omega_arith) (by decide)), P.blk k hk]
  · exact P.tbl.frame f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact tblR_w (.inl (by decide)) (by decide)

theorem pass_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} (P : PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv p m O0 l X fB ckF t₀ t' m) := by
  have hn := L.n32
  obtain ⟨t₁, run₁, Q₁, bx₁, cf₁⟩ := passLoad_ok L hm P
  unfold pass
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (quads_ok L hB hckF hm Q₁ bx₁ cf₁) fun t₂ ⟨Q₂, bx₂⟩ => ?_)
  obtain ⟨t₃, run₃, Q₃, bx₃, zf₃⟩ := passTest_ok (by omega_arith) Q₂ bx₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.seq (WP.mono (tail_ok L hB hckF hm Q₃ bx₃ zf₃) fun t₄ ⟨Q₄, bx₄⟩ => ?_)
  obtain ⟨t₅, run₅, P₅⟩ := passStore_ok L hm Q₄ bx₄
  exact WP.of_runBlock ⟨t₅, run₅, P₅⟩

end VG.Proof.AesOcb.X86

end

end

/-! ### `AesOcb.X86.Whole`, which only this module used -/

section

/-!
# AES-OCB on x86: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`wholeIn_ok`), after the
table of `L_j` (`whole_ok`): block `k` becomes
`Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz ctxCiph ctxInv)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left toNat_w64 add_ofNat_assoc32)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, `i`, the
table, the working space of the functions called, the stack and the data. -/
abbrev wholeR (p : Prm) (k : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    tblR p, wC p.W, stk p, ⟨w64 p.D, 16 * k⟩]

/-- The `m` blocks of the data, for a call. -/
theorem DReg.d {p : Prm} (L : Lay p) {s : State} (E : Env p s) {m : Nat} (hm : 16 * m ≤ p.n) : DReg p s p.D m := by
  have hd := L.dw
  obtain sub : Region.Sub ⟨w64 p.D, 16 * m⟩ ⟨w64 p.D, p.n⟩ := Region.sub_prefix hm
  refine ⟨by omega_using [hm, hd], (L.k_d.sub_left (Region.sub_prefix (by decide))).sub_right sub,
    (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide)), L.bd.sub_right sub, covers_prefix E.perm.d hm,
    fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, by simp, sub⟩

/-- `DECIPHER` with the key context, after a frame within `mutR`. -/
theorem ctxInv_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') :
    ctxInv m' (w64 p.K) p.R = ctxInv m (w64 p.K) p.R := by
  unfold ctxInv
  have hb := L.rounds_le
  rw [Proof.AesGcm.X86.bytesAt_frame h (fun r hr => (k_mut L r hr).sub_left (Region.sub_prefix (by omega_using [hb])))
    (by omega_using [hb])]

/-- `passStart`: the data, its `m` whole blocks, `i = 1`. -/
theorem passStart_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {m : Nat}
    (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧ t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * 0) ∧
      t'.gpr .ebx = BitVec.ofNat 32 (m - 0) ∧ t'.gpr .edi = BitVec.ofNat 32 (0 + 1) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  have hD := E.slots.data
  simp only [slotv_eq] at hD hnb
  exact ⟨_, by grun [passStart, E.ebp, L.aW, E.perm.wR, hD, hnb], by gregs [hD]; exact (BitVec.add_zero _).symm,
    by gregs [hnb, Nat.sub_zero], by gregs [], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
    by gmems []⟩

/-- What `whole` leaves. -/
structure WholePost (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

/-- The passes around the call, with the table. -/
theorem wholeIn_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n)
    {O0 l : Block} (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) (hT : Tbl p l m t.mem)
    (hckF1 : ∀ i < m, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i < m, ckF2 (i + 1) = fC2 (ckF2 i)
      (G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (wholeIn fn pre post) t (WholePost p m O0 l
      (fun k => G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hn := L.n32
  -- the first pass
  obtain ⟨s₁, run₁, si₁, bx₁, di₁, g₁, m₁, rd₁, wr₁⟩ := passStart_ok L E hnb
  obtain E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide) (by decide)])
    (by rw [g₁ _ (by decide) (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain P₀ : PassInv p m O0 l (fun k => blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₁, edi := di₁, ebx := bx₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      tbl := by rw [m₁]; exact hT
      gpr := fun _ _ _ _ _ _ _ => rfl }
  unfold wholeIn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i hi => by rw [hckF1 i hi, m₁]) hmn P₀) fun s₂ P₂ => ?_)
  obtain fP₂ : Frame (mutR p) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inl (by decide))
    · exact ⟨_, by simp, Region.sub_prefix hmn⟩
  -- the call
  have hD₂ := P₂.env.slots.data
  obtain hnb₂' : slotv s₂.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [← m₁] at hnb
    rw [← hnb]
    exact P₂.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub (by decide))).symm) (by decide)
  simp only [slotv_eq] at hD₂ hnb₂'
  obtain hargs : ∃ s₁, runBlock isa [.mov .edx (slot dataO), .mov .ebx (slot nbO)] s₂ = some s₁ ∧
      s₁.gpr .edx = p.D ∧ s₁.gpr .ebx = BitVec.ofNat 32 m ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = s₂.gpr r) ∧ s₁.mem = s₂.mem ∧
      s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr :=
    ⟨_, by grun [P₂.env.ebp, L.aW, P₂.env.perm.wR, hD₂, hnb₂'], by gregs [hD₂], by gregs [hnb₂'],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  refine WP.seq (WP.mono (callBlocks_ok ok nosp stack L P₂.env hargs (DReg.d L P₂.env hmn)) fun s₃ P₃ => ?_)
  have E₃ := P₃.env
  -- what the call keeps
  obtain kC : ∀ {d k : Nat}, d + k ≤ scrO → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ →
      ∀ r ∈ [⟨w64 p.D, 16 * m⟩, ⟨w64 p.W + BitVec.ofNat 64 scrO, 2048⟩, stk p],
        (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h hD r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hD
    · exact Lay.w_w (.inl h) (by simp only [scrO] at h; omega_using [h]) (by decide)
    · exact (L.bw' (by simp only [scrO] at h; omega_using [h])).symm
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨w64 p.D, 16 * m⟩ :=
    fun h => ((L.d_w.sub_left (Region.sub_prefix hmn)).sub_right (Lay.wSub h)).symm
  -- the blocks and slots of `W` the first pass and the call keep
  obtain kP : ∀ {d : Nat}, (d + 16 ≤ ofsO ∨ (48 ≤ d ∧ d + 16 ≤ lO) ∨ (112 ≤ d ∧ d + 16 ≤ kO) ∨ 224 ≤ d) →
      d + 16 ≤ scrO → blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) :=
    fun h₁ h₂ => by
      rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC h₂ (dW (by simp only [scrO] at h₂; omega_using [h₂]))),
        Proof.Ocb.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega_using [h₁]) (by simp only [scrO] at h₂; omega_using [h₂]) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega_using [h₁]) (by simp only [scrO] at h₂; omega_using [h₂]) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO] at h₁ ⊢; omega_using [h₁]) (by simp only [scrO] at h₂; omega_using [h₂]) (by decide)
        · exact Lay.w_w (by simp only [ofsO, lO, kO, ckO] at h₁ ⊢; omega_using [h₁]) (by simp only [scrO] at h₂; omega_using [h₂])
            (by decide)
        · exact dW (by simp only [scrO] at h₂; omega_using [h₂]))]
  obtain o0₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0 := by rw [kP (by decide) (by decide), m₁, ho0]
  obtain ck₃ : blockAtMem s₃.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [Proof.Ocb.blockAtMem_frame P₃.frame (kC (by decide) (dW (by decide))), P₂.ck, hckF2₀]
  obtain nb₃ : slotv s₃.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← hnb₂']
    exact P₃.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _)
      (kC (by decide) (dW (by decide))) (by decide)
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := copy16_ok L E₃ (s := o0O) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  obtain f₄a : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] s₃.mem s₄a.mem := by
    rw [m₄a]; exact copyMem16_frame _ _ _ _ _
  obtain E₄a : Env p s₄a := E₃.mut L (by rw [g₄a _ (by decide), E₃.ebp]) (by rw [g₄a _ (by decide), E₃.esp]) rd₄a wr₄a
    (frame_toMut f₄a fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain nb₄a : slotv s₄a.mem p.W nbO = BitVec.ofNat 32 m := by
    rw [slotv_eq, ← nb₃, slotv_eq]
    exact f₄a.readW (r := ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  obtain ⟨s₄, run₄, si₄, bx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := passStart_ok L E₄a nb₄a
  obtain E₄ : Env p s₄ := E₄a.keep (by rw [g₄ _ (by decide) (by decide) (by decide)])
    (by rw [g₄ _ (by decide) (by decide) (by decide)]) rd₄ wr₄ m₄
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact Proof.Ocb.blockAtMem_frame f₄a fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  obtain hG₂ : G s₂.mem = G t.mem := by rw [hG fP₂, m₁]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    obtain hBk := dblk L E₄ (i := k) (by omega_using [hmn, hk])
    rw [← w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega_using [hmn, hk, this]), kB₄ hBk.w,
      w64_add (show p.D.toNat + 16 * k < 2 ^ 32 by have := L.dw; omega_using [hmn, hk, this]), hcall P₃ k hk, hG₂, P₂.blk k hk]
    simp only [hk, ↓reduceIte, m₁]
  obtain P₀' : PassInv p m O0 l (fun k => blockAtMem s₄.mem (w64 p.D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, esi := si₄, edi := di₄, ebx := bx₄
      ofs := by rw [m₄, m₄a, copyMem16_block, o0₃]; rfl
      ck := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, Proof.Ocb.blockAtMem_frame f₄a (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)),
          kP (by decide) (by decide), m₁, hl0]
      tbl := by
        rw [m₄]
        exact ((P₂.tbl.frame P₃.frame (kC (by decide) (dW (by decide)))).frame f₄a
          fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact tblR_w (.inl (by decide)) (by decide))
      gpr := fun _ _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, runBlock_app_of run₄a run₄, ?_⟩)
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2 i hi, X₄ i hi]) hmn P₀') fun s₅ P₅ => ?_
  obtain subP : ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩],
      ∃ r' ∈ wholeR p m, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, by simp, Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, rd₄a, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, wr₄a, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subP).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨wC p.W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨stk p, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (f₄a.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subP)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

/-- `whole`: the table, then the passes around the call. -/
theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n)
    {O0 l : Block} (hnb : slotv t.mem p.W nbO = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < m, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i < m, ckF2 (i + 1) = fC2 (ckF2 i)
      (G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (whole fn pre post) t (WholePost p m O0 l
      (fun k => G t.mem (blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hn := L.n32
  unfold whole
  refine WP.seq (WP.mono (ltable_ok L E (m := m) (by omega_using [hmn, hn]) hnb hl0) fun t₁ ⟨T₁, K₁⟩ => ?_)
  obtain f₁ := K₁.frame
  obtain E₁ : Env p t₁ := K₁.env L E
  -- what the table keeps
  obtain kW : ∀ {d : Nat}, d + 16 ≤ tblO ∨ tblO + 96 ≤ d → d + 16 ≤ 2560 →
      blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (tblR_w h h').symm
  obtain kD : ∀ i < m, blockAtMem t₁.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) =
      blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) := fun i hi =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dataBlk_w L (by omega_using [hmn, hi]) (by decide)
  obtain hG₁ : G t₁.mem = G t.mem := hG (frame_toMut f₁ (inMut_tblR p))
  obtain nb₁ : slotv t₁.mem p.W nbO = BitVec.ofNat 32 m := by rw [K₁.nb, hnb]
  refine WP.mono (wholeIn_ok ok nosp stack hcall hG hB1 hB2 L E₁ hmn nb₁
    (by rw [kW (.inl (by decide)) (by decide), hofs]) (by rw [kW (.inl (by decide)) (by decide), ho0])
    (by rw [kW (.inl (by decide)) (by decide), hck]) (by rw [kW (.inl (by decide)) (by decide), hl0]) T₁
    (fun i hi => by rw [kD i hi]; exact hckF1 i hi) hckF2₀
    (fun i hi => by rw [hG₁, kD i hi]; exact hckF2 i hi)) fun t' P => ?_
  refine ⟨P.env, (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans P.frame,
    by rw [P.rd, K₁.rd], by rw [P.wr, K₁.wr], fun k hk => ?_, P.ofs, P.ck⟩
  rw [P.blk k hk]
  simp only [hG₁, kD k hk]

end VG.Proof.AesOcb.X86

end

end


/-!
# AES-OCB on x86: the data (`body`)

Untrusted: everything here is checked by Lean. `body` keeps the number of
whole blocks `m = len / 16` in `W` and runs `whole` on them if there are any
(`wholeIte_ok`), then `rest` on the `len mod 16` bytes after them if there
are any (`restIte_ok`): for `seal` (`bodySeal_ok`) and `open`
(`bodyOpen_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}` and `Pad`,
`pad(·)`, the variables at `[216, 384)`, the working space of the functions
called, the stack and the data. -/
abbrev bodyR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩,
    wV p.W, wC p.W, stk p, ⟨w64 p.D, p.n⟩]

theorem bodyR_mut {p : Prm} {m m' : Mem} (h : Frame (bodyR p) m m') : Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact inMut_stk p
  · exact inMut_d p

/-- A part of `W` within `bodyR`. -/
theorem inBodyR (p : Prm) {d k : Nat}
    (h : 16 ≤ d ∧ d + k ≤ 48 ∨ 96 ≤ d ∧ d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 160 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨
      384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ bodyR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h | h
  · exact ⟨_, by simp, Offset.sub _ (e := 16) (k := 32) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 32) (by omega_arith) (by omega_arith)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 144) (k := 16) (by omega_arith) (by omega_arith)⟩
  · exact ⟨wV p.W, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩

/-- The number of whole blocks, kept in `W`. -/
theorem bodyHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s₁, runBlock isa [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)] s = some s₁ ∧
      s₁.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 (p.n / 16)) ∧
      s₁.zf = some (decide (p.n / 16 = 0)) ∧
      (∀ r, r ≠ .ebx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hn := L.n32
  have hl := E.slots.len
  simp only [slotv_eq] at hl
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hl], by gmems [hl, shr4_32 hn], ?_,
    fun r h => by gregs [h], by gmems [], by gmems []⟩
  gmems [hl, shr4_32 hn, BitVec.and_self, beq_zero32 (show p.n / 16 < 2 ^ 32 by omega_arith)]

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck
  tail : 0 < p.n % 16 → bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
    bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)

theorem wholeR_body {p : Prm} {k : Nat} (hk : 16 * k ≤ p.n) {m m' : Mem} (h : Frame (wholeR p k) m m') :
    Frame (bodyR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  · exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {s : State} (E : Env p s) {O0 l : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < p.n / 16, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i < p.n / 16, ckF2 (i + 1) = fC2 (ckF2 i)
      (G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)]) (.ite .e (.block []) (whole fn pre post))) s
      (WholeIte p (p.n / 16) O0 l
        (fun k => G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  obtain ⟨s₁, run₁, m₁, zf₁, g₁, rd₁, wr₁⟩ := bodyHead_ok L E
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fB₁ : Frame (bodyR p) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain E₁ : Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (bodyR_mut fB₁)
  obtain kB : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩ →
      blockAtMem s₁.mem Q = blockAtMem s.mem Q := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  obtain kW : ∀ {d : Nat}, d + 16 ≤ nbO → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => kB (Lay.w_w (.inl h) (by simp only [nbO] at h; omega_arith)
        (by decide))
  obtain kD : ∀ k, 16 * (k + 1) ≤ p.n → blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) := fun k hk =>
    kB ((L.d_w.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub (by decide)))
  obtain tail₁ : 0 < p.n % 16 → bytesAt s₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
      bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := fun hr => by
    have hd := L.dw
    obtain sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega_arith)]; exact Offset.sub_base _ (by omega_arith)
    exact Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))) (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, fB₁, rd₁, wr₁, fun k hk => absurd hk (by omega_arith), by rw [kW (by decide), hofs, hm]; rfl,
      by rw [kW (by decide), hck, hm, hckF2₀, hm], fun hr => tail₁ hr⟩
  · have hm : p.n / 16 ≠ 0 := of_decide_eq_false h0
    obtain hG₁ : G s₁.mem = G s.mem := hG (bodyR_mut fB₁)
    refine WP.mono (whole_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp stack hcall hG hB1 hB2 L E₁
      (m := p.n / 16) (by omega_arith)
      (by rw [slotv_eq, m₁, Mem.readW_writeW_self32]) (by rw [kW (by decide), hofs]) (by rw [kW (by decide), ho0])
      (by rw [kW (by decide), hck]) (by rw [kW (by decide), hl0])
      (fun i hi => by rw [hckF1 i hi, kD i (by omega_arith)]) hckF2₀
      (fun i hi => by rw [hckF2 i hi, hG₁, kD i (by omega_arith)])) fun t P => ?_
    refine ⟨P.env, fB₁.trans (wholeR_body (Nat.mul_div_le p.n 16) P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      fun k hk => ?_, P.ofs, P.ck, fun hr => ?_⟩
    · rw [P.blk k hk, hG₁, kD k (by omega_arith)]
    · rw [← tail₁ hr]
      have hd := L.dw
      obtain a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
        w64_add (by omega_arith)
      obtain sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
        rw [a16]; exact Offset.sub_base _ (by omega_arith)
      exact Proof.AesGcm.X86.bytesAt_frame P.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.bd.sub_right sub).symm
        · rw [a16]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) (by omega_arith)

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁, runBlock isa [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
        .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)] t = some t₁ ∧
      t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t₁.zf = some (decide (p.n % 16 = 0)) ∧
      t₁.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 restO) (BitVec.ofNat 32 (p.n % 16)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hn := L.n32
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl
  obtain hsub : BitVec.ofNat 32 p.n - BitVec.ofNat 32 (p.n % 16) = BitVec.ofNat 32 (16 * (p.n / 16)) := by
    rw [sub32' (Nat.mod_le _ _) hn, show p.n - p.n % 16 = 16 * (p.n / 16) by omega_arith]
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hD, hl], by gregs [hD, hl, and15_32 hn, hsub], ?_,
    by gmems [hl, and15_32 hn], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hl, and15_32 hn, BitVec.and_self, beq_zero32 (show p.n % 16 < 2 ^ 32 by omega_arith)]

/-- The tail of the data. -/
theorem rbuf_tail {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hr : 0 < p.n % 16) :
    RBuf p s (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) := by
  have hd := L.dw
  obtain a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
    w64_add (by omega_arith)
  obtain sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨by rw [toNat_add32 (by omega_arith)]; omega_arith, L.d_w.sub_left sub, L.bd.sub_right sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega_arith) (by omega_arith)
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub⟩

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (p : Prm) (P : BitVec 32) (r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (bodyR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (w64 P) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (w64 P) r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
        (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))))
    else bytesAt t.mem (w64 P) r
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (w64 P) r)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)
  pre : bytesAt t'.mem (w64 p.D) (16 * (p.n / 16)) = bytesAt t.mem (w64 p.D) (16 * (p.n / 16))

theorem restR_body {p : Prm} {P : BitVec 32} {r : Nat}
    (hPD : Region.Sub ⟨w64 P, r⟩ ⟨w64 p.D, p.n⟩) {m m' : Mem} (h : Frame (restR p P r) m m') :
    Frame (bodyR p) m m' := h.sub fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inBodyR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, hPD⟩

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax),
        .alu .and .ecx (imm 15), .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (rest (callees v) enc))) t
      (TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) t) := by
  obtain ⟨t₁, run₁, si₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok L E
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fB₁ : Frame (bodyR p) t.mem t₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (bodyR_mut fB₁)
  obtain kB : ∀ {d : Nat}, d + 16 ≤ restO → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [restO] at h; omega_arith)
        (by decide)
  obtain hK : ∀ {m : Mem}, Frame (mutR p) t.mem m → ctxLstar m (w64 p.K) = ctxLstar t.mem (w64 p.K) ∧
      ctxCiph m (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R := fun h => ⟨lstar_mut L h, ctxCiph_mut L h⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true h0; omega_arith
    obtain b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
      rw [show p.n % 16 = 0 by omega_arith]; rfl
    obtain dpre : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ : Region)],
        (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))
    refine ⟨E₁, fB₁, rd₁, wr₁, ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame f₁ dpre (by have := L.dw; omega_arith)⟩ <;>
      simp only [hr, ↓reduceIte, b0]
    · exact kB (by decide)
    · exact kB (by decide)
  · have hr : 0 < p.n % 16 := by have := of_decide_eq_false h0; omega_arith
    obtain hP := rbuf_tail L E₁ hr
    obtain cnt₁ : slotv t₁.mem p.W restO = BitVec.ofNat 32 (p.n % 16) := by rw [slotv_eq, m₁, Mem.readW_writeW_self32]
    refine WP.mono (rest_ok v enc L E₁ hr (Nat.mod_lt _ (by decide)) si₁ cnt₁ hP) fun t' P => ?_
    have hd := L.dw
    obtain sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega_arith)]; exact Offset.sub_base _ (by omega_arith)
    obtain ⟨lT, cT⟩ := hK (bodyR_mut fB₁)
    obtain pT : bytesAt t₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
        bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
    obtain dpre : ∀ q ∈ (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)), (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := by
      obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint
          ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ := fun h =>
        (L.d_w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub h)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact (L.bd.sub_right (Region.sub_prefix (by omega_arith))).symm
      · rw [w64_add (by omega_arith)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)
    obtain fpre : Frame (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)) t.mem t'.mem :=
      (f₁.mono (by simp)).trans (P.frame.mono fun q hq => List.mem_cons_of_mem _ hq)
    refine ⟨P.env, fB₁.trans (restR_body sub P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame fpre dpre (by omega_arith)⟩ <;> simp only [hr, ↓reduceIte]
    · rw [P.ofs, kB (by decide), lT]
    · rw [P.out, kB (by decide), lT, cT, pT]
    · rw [P.ck, kB (by decide)]
      cases enc
      · rfl
      · simp only [↓reduceIte, pT]

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (w64 p.D) p.n = out
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

/-- The facts both `body` proofs use. -/
theorem body_facts {p : Prm} (L : Lay p) (m : Mem) :
    (∀ i < p.n / 16, blockAtMem m (w64 p.D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt m (w64 p.D) p.n) i) ∧
    (0 < p.n % 16 → (bytesAt m (w64 p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt m (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)) := by
  have hd := L.dw
  refine ⟨fun i hi => (Proof.Ocb.blockAt_bytesAt m _ (by omega_arith)).symm, fun hr => ?_⟩
  rw [Proof.Ocb.bytesAt_drop m _ (Nat.mul_div_le p.n 16), show p.n - 16 * (p.n / 16) = p.n % 16 by omega_arith,
    w64_add (by omega_arith)]

/-- The data after `body`, from its whole blocks and its rest. -/
theorem body_out {enc : Bool} {p : Prm} (L : Lay p) {t t' : State} (P : TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
    (p.n % 16) t t') {X : List Byte} (hX : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) = X) :
    bytesAt t'.mem (w64 p.D) p.n = X ++ bytesAt t'.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
  have hd := L.dw
  obtain e := Proof.Ocb.bytesAt_append t'.mem (w64 p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega_arith] at e
  rw [e, P.pre, hX]
  by_cases hr : 0 < p.n % 16
  · rw [w64_add (by omega_arith)]
  · rw [show p.n % 16 = 0 by omega_arith]; rfl

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {s : State} (E : Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (callees v) true) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := body_facts L s.mem
  simp only [body, ↓reduceIte]
  refine seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxCiph m (w64 p.K) p.R)
    (ckF1 := ckOf fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => ctxCiph_mut L h) sealPre_ok xorOfs_ok
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR p) s.mem t.mem := bodyR_mut Pw.frame
  refine WP.mono (restIte_ok v true L Pw.env) fun t' Pt => ?_
  obtain cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := ctxCiph_mut L fW
  obtain lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := lstar_mut L fW
  obtain blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, BitVec.xor_comm]
  obtain ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_eq hl]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega_arith]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, hrest hr]
    · simp only [hr, ↓reduceIte]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {s : State} (E : Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (callees v) false) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)))))
      else Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := body_facts L s.mem
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxInv m (w64 p.K) p.R) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => ctxInv s.mem (w64 p.K) p.R
      (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1))
    v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => ctxInv_mut L h) xorOfs_ok openPost_ok
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR p) s.mem t.mem := bodyR_mut Pw.frame
  refine WP.mono (restIte_ok v false L Pw.env) fun t' Pt => ?_
  obtain cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := ctxCiph_mut L fW
  obtain lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := lstar_mut L fW
  obtain blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, Proof.Ocb.decBlock,
      BitVec.xor_comm]
  obtain ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega_arith]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, hrest hr]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86
