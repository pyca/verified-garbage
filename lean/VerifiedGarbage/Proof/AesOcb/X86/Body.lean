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
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16W_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
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

/-- A block of `B` that the code may read and write, apart from `W`. -/
structure BBlk (p : Prm) (t : State) (B : BitVec 32) : Prop where
  fit : B.toNat + 16 ≤ 2 ^ 32
  w : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  wr : Covers [⟨w64 B, 16⟩] t.wr
  inm : InMut p [⟨w64 B, 16⟩]

theorem BBlk.of_eq {p : Prm} {t t' : State} {B : BitVec 32} (h : BBlk p t B) (hwr : t'.wr = t.wr) : BBlk p t' B :=
  ⟨h.fit, h.w, by rw [hwr]; exact h.wr, h.inm⟩

/-- A word of `W` after a word of a block `B` apart from it written. -/
theorem readW_BW {p : Prm} (L : Lay p) {B : Addr}
    (hd : (⟨B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (m : Mem) (v : BitVec 32) {a b : Nat} (ha : a + 4 ≤ 2560)
    (hb : b + 4 ≤ 16) :
    (m.writeW (B + BitVec.ofNat 64 b) v).readW (w64 p.W + BitVec.ofNat 64 a) 32 =
      m.readW (w64 p.W + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (hd.symm.sep (Offset.contains_base _ ha (by have := L.ww; omega_arith))
    (Offset.contains_base _ hb (by omega_arith))) (by decide)

/-- What a body does to the block at `B` (in `esi`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (p : Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : BitVec 32), Env p t → t.gpr .esi = B → BBlk p t B →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem (w64 B) = fB (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (w64 B)) (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨w64 B, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {p : Prm} (L : Lay p) : BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B E hsi hB
  obtain aB : ∀ {k : Nat}, k < 16 → w64 (B + BitVec.ofNat 32 k) = w64 B + BitVec.ofNat 64 k := fun hk =>
    w64_add (by have := hB.fit; omega_arith)
  obtain rB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions (t.rd ++ t.wr) (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_left (in_off hB.wr hk (by decide))
  obtain wB : ∀ {k : Nat}, k + 4 ≤ 16 → InRegions t.wr (w64 B + BitVec.ofNat 64 k) 4 := fun hk =>
    in_off hB.wr hk (by decide)
  obtain ⟨t', run, m', g', rd', wr'⟩ : ∃ t', runBlock isa xorOfs t = some t' ∧
      t'.mem = xor2Mem t.mem (w64 B) (w64 p.W + BitVec.ofNat 64 ofsO) (w64 B) ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    refine ⟨_, by grun [xorOfs, List.flatMap_cons, List.flatMap_nil, hsi, aB, rB, wB, E.ebp, L.aW, E.perm.wR,
      (readW_BW L hB.w)], ?_, fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [(readW_BW L hB.w)]
    simp only [xor2Mem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd,
      show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]
  obtain fB : Frame [⟨w64 B, 16⟩] t.mem t'.mem := by rw [m']; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨t', run, by rw [m', xor2Mem_block], ?_, fB.mono (by simp), g', rd', wr'⟩
  exact Proof.Ocb.blockAtMem_frame fB fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hB.w.sub_right (Lay.wSub (by decide))).symm

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {B : BitVec 32} (hsi : t.gpr .esi = B)
    (hB : BBlk p t B) :
    ∃ t', runBlock isa addCk t = some t' ∧
      t'.mem = xorMem16 t.mem (w64 B) 0 (w64 p.W) ckO ∧
      (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  xor16R_ok L E (b := .esi) (by decide) hsi hB.fit hB.w (Proof.AesGcm.X86.covers_left hB.wr) (s := 0) (d := ckO) (by decide) (by decide)

theorem blockAtMem_ck {p : Prm} {B : BitVec 32} (hBW : (⟨w64 B, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' (w64 B) = blockAtMem m (w64 B) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {p : Prm} {m m' : Mem} (h : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (w64 p.W + BitVec.ofNat 64 ofsO) = blockAtMem m (w64 p.W + BitVec.ofNat 64 ofsO) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

theorem addCk_val (m : Mem) (B : BitVec 32) (W : BitVec 32) :
    blockAtMem (xorMem16 m (w64 B) 0 (w64 W) ckO) (w64 W + BitVec.ofNat 64 ckO) =
      blockAtMem m (w64 W + BitVec.ofNat 64 ckO) ^^^ blockAtMem m (w64 B) := by
  rw [xorMem16_block, show w64 B + BitVec.ofNat 64 0 = w64 B from BitVec.add_zero _]

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {p : Prm} (L : Lay p) :
    BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, m₁, g₁, rd₁, wr₁⟩ := addCk_ok L E hsi hB
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by rw [m₁]; exact xorMem16_frame _ _ _ _ _
  obtain E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, rd₂, wr₂⟩ := xorOfs_ok L t₁ B E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [b₂, blockAtMem_ck hB.w f₁, blockAtMem_ofs_ck f₁]
  · rw [c₂, m₁, addCk_val]
  · exact (f₁.mono (by simp)).trans f₂
  · rw [g₂ r h, g₁ r h]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {p : Prm} (L : Lay p) :
    BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B E hsi hB
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, rd₁, wr₁⟩ := xorOfs_ok L t B E hsi hB
  obtain E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hB.inm _ (List.mem_singleton_self _)
      · exact inMut_w p (.inl (by decide)))
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := addCk_ok L E₁ (by rw [g₁ _ (by decide), hsi]) (hB.of_eq wr₁)
  obtain f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩] t₁.mem t₂.mem := by rw [m₂]; exact xorMem16_frame _ _ _ _ _
  refine ⟨t₂, runBlock_app_of run₁ run₂, ?_, ?_, ?_, fun r h => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [blockAtMem_ck hB.w f₂, b₁]
  · rw [m₂, addCk_val, c₁, b₁]
  · exact f₁.trans (f₂.mono (by simp))
  · rw [g₂ r h, g₁ r h]

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

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨w64 p.D, 16 * m⟩] t₀.mem t.mem
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
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → t.gpr r = t₀.gpr r

theorem pass_step {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.zf = some (decide (m - (i + 1) = 0)) := by
  have hn := L.n32
  have hd := L.dw
  obtain a16 : ∀ k, 16 * (k + 1) ≤ p.n → w64 (p.D + BitVec.ofNat 32 (16 * k)) = w64 p.D + BitVec.ofNat 64 (16 * k) :=
    fun k hk => w64_add (by omega_arith)
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (lNtz_ok L P.env (by omega_arith) (by omega_arith) P.edi P.l0) fun t₁ P₁ => ?_))
  obtain E₁ := P₁.env L P.env
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E₁ (s := lO) (d := ofsO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  obtain E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide)))
  obtain g₂' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₂ r h₁, P₁.gpr r h₁ h₂ h₃]
  obtain fW₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
      ⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans (by
      rw [m₂]
      exact (xorMem16_frame _ _ _ _ _).mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp)
  obtain kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => Proof.Ocb.blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  obtain ofs₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [m₂, xorMem16_block, Proof.Ocb.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ofs, P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.ck]
  obtain hBi := dblk L E₂ (i := i) (by omega_arith)
  obtain Bi₂ : blockAtMem t₂.mem (w64 (p.D + BitVec.ofNat 32 (16 * i))) = X i := by
    rw [kW₂ hBi.w, a16 i (by omega_arith), P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, rd₃, wr₃⟩ := hB t₂ _ E₂
    (by rw [g₂' _ (by decide) (by decide) (by decide), P.esi]) hBi
  obtain g₃' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₃.gpr r = t.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₃ r h₁, g₂' r h₁ h₂ h₃]
  obtain si₃ : t₃.gpr .esi = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.esi]
  obtain di₃ : t₃.gpr .edi = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide) (by decide) (by decide), P.edi]
  obtain bx₃ : t₃.gpr .ebx = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide) (by decide) (by decide), P.ebx]
  obtain ⟨t₄, run₄, si₄, di₄, bx₄, zf₄, g₄, m₄, rd₄, wr₄⟩ : ∃ t₄, runBlock isa nextBlock t₃ = some t₄ ∧
      t₄.gpr .esi = p.D + BitVec.ofNat 32 (16 * (i + 1)) ∧ t₄.gpr .edi = BitVec.ofNat 32 (i + 1 + 1) ∧
      t₄.gpr .ebx = BitVec.ofNat 32 (m - (i + 1)) ∧ t₄.zf = some (decide (m - (i + 1) = 0)) ∧
      (∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .edi → t₄.gpr r = t₃.gpr r) ∧ t₄.mem = t₃.mem ∧ t₄.rd = t₃.rd ∧
      t₄.wr = t₃.wr := by
    refine ⟨_, by grun [nextBlock], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
      by gmems []⟩
    · gregs [si₃]; rw [add_ofNat_assoc32, show 16 * i + 16 = 16 * (i + 1) by omega_arith]
    · gregs [di₃]; rw [← BitVec.ofNat_add]
    · gregs [bx₃]; rw [sub1_32 (by omega_arith) (by omega_arith), show m - i - 1 = m - (i + 1) by omega_arith]
    · gmems [bx₃]
      rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  refine WP.of_runBlock ⟨t₄, runBlock_app_of run₃ run₄, ?_⟩
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 (p.D + BitVec.ofNat 32 (16 * i)), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [Proof.Ocb.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  obtain kW₃ : ∀ {d : Nat}, (d + 16 ≤ ckO ∨ ckO + 16 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 d) := fun h h' =>
    Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub h')).symm
      · exact Lay.w_w h h' (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, si₄, di₄, bx₄, ?_, ?_, fun k hk => ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_⟩, zf₄⟩
  · exact E₂.mut L (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.ebp])
      (by rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide), E₂.esp]) (by rw [rd₄, rd₃])
      (by rw [wr₄, wr₃]) (frame_toMut (by rw [m₄]; exact fr₃) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hBi.inm _ (List.mem_singleton_self _)
        · exact inMut_w p (.inl (by decide)))
  · rw [m₄]
    exact P.frame.trans ((fW₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp).trans
      (fr₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨w64 p.D, 16 * m⟩, by simp, by rw [a16 i (by omega_arith)]; exact Offset.sub_base _ (by omega_arith)⟩
        · exact ⟨_, by simp, fun _ h => h⟩))
  · rw [rd₄, rd₃, rd₂, P₁.rd, P.rd]
  · rw [wr₄, wr₃, wr₂, P₁.wr, P.wr]
  · rw [m₄, kW₃ (.inl (by decide)) (by decide), ofs₂]
  · rw [m₄, ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · rw [m₄]
    by_cases hki : k = i
    · subst hki
      rw [← a16 k (by omega_arith), blk₃, Bi₂, ofs₂]; simp
    · have hBk := dblk L E₂ (i := k) (by omega_arith)
      rw [← a16 k (by omega_arith), kB₃ (by
        rw [a16 k (by omega_arith), a16 i (by omega_arith)]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) hBk.w,
        a16 k (by omega_arith), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega_arith]
      · simp [hk', show ¬ k < i + 1 by omega_arith]
  · rw [m₄, kW₃ (.inr (by decide)) (by decide), Proof.Ocb.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), P.l0]
  · rw [g₄ r h₂ h₅ h₆, g₃' r h₁ h₃ h₄, P.gpr r h₁ h₂ h₃ h₄ h₅ h₆]

theorem pass_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t : State} (P : PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv p m O0 l X fB ckF t₀ u i) ?_ (m - 0) _
    ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hm hi P) fun u' ⟨P', hz⟩ => ?_
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

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
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
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
working space of the functions called, the stack and the data. -/
abbrev wholeR (p : Prm) (k : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 ofsO, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 lO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 kO, 4⟩,
    wC p.W, stk p, ⟨w64 p.D, 16 * k⟩]

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

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m)
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
      gpr := fun _ _ _ _ _ _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i hi => by rw [hckF1 i hi, m₁]) hmn hm0 P₀) fun s₂ P₂ => ?_)
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
      gpr := fun _ _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, runBlock_app_of run₄a run₄, ?_⟩)
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2 i hi, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
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
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
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
      (m := p.n / 16) (by omega_arith) (by omega_arith)
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
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
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
    v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => ctxCiph_mut L h) (sealPre_ok L) (xorOfs_ok L)
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
    v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => ctxInv_mut L h) (xorOfs_ok L) (openPost_ok L)
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
