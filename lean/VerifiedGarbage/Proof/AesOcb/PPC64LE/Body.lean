module

public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.LNtz
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK

/-! ### `AesOcb.PPC64LE.RestTag`, which this module and modules that import it used -/

section

/-!
# AES-OCB on PPC64LE: the rest of the data (`rest`) and the tag (`tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`
(`restHead_ok`), XORs the last bytes with `Pad` (`xorPad_ok`) and adds the
padded plaintext to the checksum (`padCk_ok`), in the order of `seal` or
`open` (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
As on AArch64 (`Proof/AesOcb/AArch64/XorPad.lean`, `RestTag.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Ocb (length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (xorLoop_ok in_left in_off covers_off covers_left)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_addi → cwp_addi

/-- The callee-saved registers are unchanged. -/
abbrev Saved (t t' : State) : Prop := ∀ r ∈ preserved, t'.gpr r = t.gpr r

theorem saved_of {t t' : State} {rs : List Reg} (h : ∀ r, r ∉ rs → t'.gpr r = t.gpr r)
    (hd : ∀ r ∈ rs, r ∉ preserved := by decide) : Saved t t' :=
  fun r hr => h r fun h' => hd r h' hr

theorem Saved.trans {t₁ t₂ t₃ : State} (h₁ : Saved t₁ t₂) (h₂ : Saved t₂ t₃) : Saved t₁ t₃ :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

/-- The registers `xorPad` and `padCk` write. -/
abbrev xpRegs : List Reg := [.r0, .r3, .r4, .r5, .r6]

/-- `xorPad`: the `r` bytes at `P` (in `r24`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (h24 : s.gpr .r24 = P) (h25 : s.gpr .r25 = BitVec.ofNat 64 r)
    (hP : DBuf K W s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hA : WP isa (.block [.addi .r3 .r31 tmpO, Impl.AesGcm.PPC64LE.mov .r4 .r24,
      Impl.AesGcm.PPC64LE.mov .r5 .r25]) s fun s₃ =>
      s₃.gpr .r3 = W + BitVec.ofNat 64 112 ∧ s₃.gpr .r4 = P ∧ s₃.gpr .r5 = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r) ∧ Proof.AesGcm.PPC64LE.Keeps s s₃ :=
    cwp_addi (by decide) (by decide) fun s₁ u₁ => cwp_or fun s₂ u₂ => cwp_or fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h31]; rfl,
        by rw [u₃.other _ (by decide), u₂.gpr, BitVec.or_self, u₁.other _ (by decide), h24],
        by rw [u₃.gpr, BitVec.or_self, u₂.other _ (by decide), u₁.other _ (by decide), h25],
        fun q a b c => by rw [u₃.other _ c, u₂.other _ b, u₁.other _ a],
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr]⟩⟩
  unfold xorPad
  refine WP.seq (WP.mono hA fun s₁ ⟨r3₁, r4₁, r5₁, g₁, k₁⟩ => ?_)
  obtain pre : Proof.AesGcm.PPC64LE.LoopPre s₁ (W + BitVec.ofNat 64 112) P r :=
    ⟨r3₁, r4₁, r5₁, hr, by omega_arith, by rw [k₁.rd, k₁.wr]; exact covers_left (covers_off hw (by omega_arith) (by decide)),
      by rw [k₁.wr]; exact hP.wr, (hP.w.sub_right (Lay.wSub (W := W) (d := 112) (n := r) (by omega_arith))).symm⟩
  refine WP.mono (xorLoop_ok s₁ pre) fun t ⟨mt, ot⟩ => ?_
  obtain ⟨rdt, wrt, spt, lrt⟩ := ot.keeps
  refine ⟨by rw [mt, k₁.mem]; rfl, fun q hq => ?_, by rw [spt, k₁.sp], by rw [lrt, k₁.lr], by rw [rdt, k₁.rd],
    by rw [wrt, k₁.wr]⟩
  simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [ot.other q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2, g₁ q hq.2.1 hq.2.2.1 hq.2.2.2.1]

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `r24`. -/
theorem padCk_ok {K W : Addr} (L : Lay K W) {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {S : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (h24 : s.gpr .r24 = S) (h25 : s.gpr .r25 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
        blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk xorW
  refine WP.seq (WP.mono (padTo_ok h31 hw hr hr' (by decide) h24 h25 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ P₁ => ?_)
  obtain h31₁ : t₁.gpr .r31 = W := by rw [P₁.gpr _ (by decide), h31]
  obtain ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  refine WP.mono (xorB_ok (s := t₁) (pd := ckO) (qd := t2O) (cd := ckO) (by decide) (by decide) (by decide)
    h31₁ h31₁ h31₁ (by decide) (by decide) (by decide) (in_left (ww (by decide))) (in_left (ww (by decide)))
    (in_left (ww (by decide))) (in_left (ww (by decide))) (ww (by decide)) (ww (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide)) (Offset.sep _ (by decide) (by decide) (by decide)))
    fun t₂ B₂ => ⟨(P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_, fun q hq => ?_,
      by rw [B₂.sp, P₁.sp], by rw [B₂.lr, P₁.lr], by rw [B₂.rd, P₁.rd], by rw [B₂.wr, P₁.wr]⟩
  · rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]
  · simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [B₂.gpr q (by simp [hq.2.1, hq.2.2.1]), P₁.gpr q (by simp [padRegs, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
      hq.2.2.2.2])]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29)
  tmp : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem (V .r29) R (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29))
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) :
    WP isa (.seq (.block (xorB .r31 .r29 .r31 ofsO 240 ofsO ++ copy16 ofsO tmpO)) (encOne tmpO)) t
      (RestHead V sp R t) := by
  refine WP.seq (WP.block_append (WP.mono (xorB_ok (s := t) (pd := ofsO) (qd := 240) (cd := ofsO) (by decide)
    (by decide) (by decide) E.r31 E.r29 E.r31 (by decide) (by decide) (by decide) (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    ((L.k_w' (a := 248) (n := 8) (d := 16) (k := 8) (by decide) (by decide)).sep (Region.contains_self _ _)
      (Region.contains_self _ _))) fun t₁ B₁ => ?_))
  obtain E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  refine WP.mono (copy16_ok (s := t₁) (a := ofsO) (d := tmpO) (by decide) (by decide) E₁.r31
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide)))
    fun t₂ B₂ => ?_
  obtain E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  obtain fr₂ : Frame [⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain ofs₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29) := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  obtain cK : ctxCiph t₂.mem (V .r29) R = ctxCiph t.mem (V .r29) R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega_arith)]
  refine WP.mono (encOne_ok L hR h28 E₂ (d := tmpO) (by decide)) fun t₃ P₃ => ?_
  refine ⟨P₃.env E₂, ?_, ?_, ?_, ?_, by rw [P₃.rd, B₂.rd, B₁.rd], by rw [P₃.wr, B₂.wr, B₁.wr]⟩
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
    show ctxCiph t₂.mem (V .r29) R _ = _
    rw [cK]; rfl
  · exact (saved_of B₁.gpr).trans ((saved_of B₂.gpr).trans P₃.saved)

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
structure RestPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29)
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem (V .r29) R
      (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29))))
  ck : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (h24 : t.gpr .r24 = P) (h25 : t.gpr .r25 = BitVec.ofNat 64 r)
    (hP : DBuf (V .r29) (V .r31) t P r) :
    WP isa (rest enc) t (RestPost enc V sp R P r t) := by
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (restHead_ok L E hR h28) fun t₃ H => ?_))
  obtain h24₃ : t₃.gpr .r24 = P := by rw [H.saved _ (by decide), h24]
  obtain h25₃ : t₃.gpr .r25 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide), h25]
  obtain hP₃ : DBuf (V .r29) (V .r31) t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  obtain dH : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩], (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact dW (by decide)
  obtain dT : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  obtain dTmp : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  obtain dOfs : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := Proof.Cmac.bytesAt_frame H.frame dH (by omega_arith)
  obtain hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  obtain hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega_arith
  obtain fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  obtain xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (V .r31 + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P
          (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (V .r31 + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes (ctxCiph t.mem (V .r29) R
          (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .r29)))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega_arith), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega_arith), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  obtain dCk : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩], (⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain ck₃ : blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 ckO) = blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  obtain pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)],
      (⟨V .r31 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok E₃.r31 E₃.perm.w hr hr' h24₃ h25₃ hP₃)
      fun t₄ ⟨m₄, g₄, sp₄, lr₄, rd₄, wr₄⟩ => ?_)
    obtain E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    obtain fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄.r31 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h24₃])
      (by rw [g₄ _ (by decide), h25₃]) (by rw [rd₄, wr₄]; exact hS₃) hP.w)
      fun t₅ ⟨fr₅, ck₅, g₅, sp₅, lr₅, rd₅, wr₅⟩ => ?_
    obtain p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := Proof.Cmac.bytesAt_frame fr₅ dT (by omega_arith)
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((saved_of g₄).trans (saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L E₃.r31 E₃.perm.w hr hr' h24₃ h25₃ hS₃ hP.w)
      fun t₄ ⟨fr₄, ck₄, g₄, sp₄, lr₄, rd₄, wr₄⟩ => ?_)
    obtain E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    obtain p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := Proof.Cmac.bytesAt_frame fr₄ dT (by omega_arith)
    refine WP.mono (xorPad_ok E₄.r31 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h24₃])
      (by rw [g₄ _ (by decide), h25₃]) (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, sp₅, lr₅, rd₅, wr₅⟩ => ?_
    obtain fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((saved_of g₄).trans (saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (V : Reg → BitVec 64) (sp : Addr) (R d : Nat) (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 d, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩] t.mem t'.mem
  val : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 d) =
    ctxCiph t.mem (V .r29) R (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 sumO)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {d : Nat}
    (hd : d = tagO ∨ d = t2O) :
    WP isa (tag d) t (TagPost V sp R d t) := by
  have hd' : d = 0 ∨ d = 256 := hd
  obtain hd8 : d % 4 = 0 ∧ d + 8 < 2 ^ 15 := by omega_arith
  obtain hd16 : d + 16 ≤ 2560 := by omega_arith
  unfold tag xorW
  rw [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := t) (a := ckO) (d := tmpO) (by decide) (by decide) E.r31
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide)))
    fun t₁ B₁ => ?_))
  obtain E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  refine WP.block_append (WP.mono (xorB_ok (s := t₁) (pd := tmpO) (qd := ofsO) (cd := tmpO) (by decide)
    (by decide) (by decide) E₁.r31 E₁.r31 E₁.r31 (by decide) (by decide) (by decide) (E₁.perm.wR (by decide))
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide))
    (E₁.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_)
  obtain E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  refine WP.mono (xorB_ok (s := t₂) (pd := tmpO) (qd := ldO) (cd := tmpO) (by decide)
    (by decide) (by decide) E₂.r31 E₂.r31 E₂.r31 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide))
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide))
    (E₂.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₃ B₃ => ?_
  obtain E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  obtain tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨V .r31 + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  obtain fr₃ : Frame [⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  obtain tmp₃ : blockAtMem t₃.mem (V .r31 + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  obtain cK : ctxCiph t₃.mem (V .r29) R = ctxCiph t.mem (V .r29) R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega_arith)]
  refine WP.seq (WP.mono (encOne_ok L hR h28 E₃ (d := tmpO) (by decide)) fun t₄ P₄ => ?_)
  obtain E₄ := P₄.env E₃
  obtain tmp₄ : blockAtMem t₄.mem (V .r31 + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem (V .r29) R (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ldO)) := by
    rw [P₄.enc0, tmp₃, ← cK]; rfl
  refine WP.block_append (WP.mono (copy16_ok (s := t₄) (a := tmpO) (d := d) (by decide) hd8 E₄.r31
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega_arith)) (E₄.perm.wW (by omega_arith)))
    fun t₅ B₅ => ?_)
  obtain E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  refine WP.mono (xorB_ok (s := t₅) (pd := d) (qd := sumO) (cd := d) hd8 (by decide) hd8 E₅.r31 E₅.r31 E₅.r31
    (by decide) (by decide) (by decide) (E₅.perm.wR (by omega_arith)) (E₅.perm.wR (by omega_arith)) (E₅.perm.wR (by decide))
    (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega_arith)) (E₅.perm.wW (by omega_arith))
    (Offset.sep _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (Offset.sep _ (by simp only [sumO]; omega_arith) (by decide) (by omega_arith))) fun t₆ B₆ => ?_
  obtain dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨V .r31 + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega_arith)
  obtain dCall : ∀ q ∈ [(⟨V .r31 + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩],
      (⟨V .r31 + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
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
  · rw [B₆.val, B₅.val, tmp₄, blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega_arith) (by decide)),
      blockAtMem_frame P₄.frame dCall, blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.PPC64LE

end

end

/-! ### `AesOcb.PPC64LE.Whole`, which this module and modules that import it used -/

section

/-! ### `AesOcb.PPC64LE.Pass`, which this module and modules that import it used -/

section

/-!
# AES-OCB on PPC64LE: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. A pass over the `m` whole
blocks of the data computes each block's offset (`lNtz_ok`, `xorB_ok`),
replaces the block with `fB` of it and the offset, and the checksum with
`fC` of them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`);
`pass_ok` gives the blocks and the checksum after all `m`. As on AArch64
(`Proof/AesOcb/AArch64/Pass.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_addi → cwp_addi, wp_subi → cwp_subi

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.r3, .r4]

/-- What a body does to the block at `B` (in `r24`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) :
    Prop :=
  ∀ (t : State) (B : Addr), t.gpr .r24 = B → t.gpr .r31 = W →
    InRegions (t.rd ++ t.wr) B 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr B 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    Covers [⟨W, 2560⟩] t.wr → (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    WP isa (.block body) t fun t' =>
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.lr = t.lr ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem add0 (B : Addr) : B + BitVec.ofNat 64 0 = B := BitVec.add_zero _

/-- `xorOfs`: the block at `B` XORed with the offset. -/
theorem xorOfs_ok' {W B : Addr} {t : State} (h24 : t.gpr .r24 = B) (h31 : t.gpr .r31 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wB₀ : InRegions t.wr B 8) (wB₈ : InRegions t.wr (B + BitVec.ofNat 64 8) 8) (hw : Covers [⟨W, 2560⟩] t.wr)
    (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block xorOfs) t (BlkStep B 0 (blockAtMem t.mem B ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO))
      bodyRegs t) := by
  obtain e := add0 B
  obtain hb := xorB_ok (s := t) (P := B) (Q := W) (C := B) (pd := 0) (qd := ofsO) (cd := 0) (pb := .r24)
    (qb := .r31) (cb := .r24) (by decide) (by decide) (by decide) h24 h31 h24 (by decide) (by decide) (by decide)
    (by rw [e]; exact rB₀) rB₈ (in_left (in_off hw (by decide) (by decide)))
    (in_left (in_off hw (by decide) (by decide))) (by rw [e]; exact wB₀) wB₈
    (Offset.sep B (d := 8) (n := 8) (e := 0) (k := 8) (.inr (by decide)) (by decide) (by decide))
    (by
      rw [e]
      exact Region.Disjoint.sep (hBW.sub_right (Lay.wSub (W := W) (d := ofsO + 8) (n := 8) (by decide))).symm
        (Region.contains_self _ _) (contains_pre _ (by decide)))
  rw [e] at hb
  exact hb

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (h24 : t.gpr .r24 = B) (h31 : t.gpr .r31 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (hw : Covers [⟨W, 2560⟩] t.wr) (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.block addCk) t
      (BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) bodyRegs t) := by
  obtain e := add0 B
  obtain hb := xorB_ok (s := t) (P := W) (Q := B) (C := W) (pd := ckO) (qd := 0) (cd := ckO) (pb := .r31)
    (qb := .r24) (cb := .r31) (by decide) (by decide) (by decide) h31 h24 h31 (by decide) (by decide) (by decide)
    (in_left (in_off hw (by decide) (by decide))) (in_left (in_off hw (by decide) (by decide)))
    (by rw [e]; exact rB₀) rB₈ (in_off hw (by decide) (by decide)) (in_off hw (by decide) (by decide))
    (Offset.sep W (.inr (by decide)) (by decide) (by decide))
    (Region.Disjoint.sep (hBW.sub_right (Lay.wSub (W := W) (d := ckO) (n := 8) (by decide)))
      (Offset.contains_base B (d := 8) (n := 8) (k := 16) (by decide) (by decide)) (Region.contains_self _ _))
  rw [e] at hb
  exact hb

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega_arith) (by omega_arith)

theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.mono (xorOfs_ok' h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW) fun t' Bk => ?_
  have f := Bk.frame
  have v := Bk.val
  rw [add0] at f v
  exact ⟨v, blockAtMem_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := ckO) (n := 16) (by decide))).symm),
    f.mono (by simp), Bk.gpr, Bk.sp, Bk.lr, Bk.rd, Bk.wr⟩

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.block_append (WP.mono (addCk_ok h24 h31 rB₀ rB₈ hw hBW) fun t₁ B₁ => ?_)
  refine WP.mono (xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), h24]) (by rw [B₁.gpr _ (by decide), h31])
    (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈) (by rw [B₁.wr]; exact wB₀)
    (by rw [B₁.wr]; exact wB₈) (by rw [B₁.wr]; exact hw) hBW) fun t₂ ⟨b₂, c₂, f₂, g₂, sp₂, lr₂, rd₂, wr₂⟩ => ?_
  refine ⟨?_, ?_, (B₁.frame.mono (by simp)).trans f₂, fun r hr => by rw [g₂ r hr, B₁.gpr r hr],
    by rw [sp₂, B₁.sp], by rw [lr₂, B₁.lr], by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, blockAtMem_ck hBW B₁.frame, blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW
  refine WP.block_append (WP.mono (xorOfs_ok t B h24 h31 rB₀ rB₈ wB₀ wB₈ hw hBW)
    fun t₁ ⟨b₁, c₁, f₁, g₁, sp₁, lr₁, rd₁, wr₁⟩ => ?_)
  refine WP.mono (addCk_ok (t := t₁) (by rw [g₁ _ (by decide), h24]) (by rw [g₁ _ (by decide), h31])
    (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈) (by rw [wr₁]; exact hw) hBW) fun t₂ B₂ => ?_
  refine ⟨?_, ?_, f₁.trans (B₂.frame.mono (by simp)), fun r hr => by rw [B₂.gpr r hr, g₁ r hr],
    by rw [B₂.sp, sp₁], by rw [B₂.lr, lr₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env V sp t
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 lO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r24 : t.gpr .r24 = D + BitVec.ofNat 64 (16 * i)
  r26 : t.gpr .r26 = BitVec.ofNat 64 (i + 1)
  r25 : t.gpr .r25 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .r29) (V .r31)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : List Instr} (hB : BodyOk (V .r31) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .r29) (V .r31) t₀ D (16 * m)) (hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv V sp D m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv V sp D m O0 l X fB ckF t₀ t' (i + 1) := by
  obtain hDt : DBuf (V .r29) (V .r31) t D (16 * m) := hD.of_eq P.rd P.wr
  obtain hBi := hDt.slice (a := 16 * i) (k := 16) (by omega_arith)
  have E := P.env
  have hw := E.perm.w
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.r31 hw (by omega_arith) (by omega_arith) P.r26 P.l0) fun t₁ P₁ => ?_))
  obtain h31₁ : t₁.gpr .r31 = V .r31 := by rw [P₁.gpr _ (by decide), E.r31]
  obtain hw₁ : Covers [⟨V .r31, 2560⟩] t₁.wr := by rw [P₁.wr]; exact hw
  refine WP.mono (xorB_ok (s := t₁) (pd := ofsO) (qd := lO) (cd := ofsO) (by decide) (by decide) (by decide)
    h31₁ h31₁ h31₁ (by decide) (by decide) (by decide) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_left (in_off hw₁ (by decide) (by decide)))
    (in_left (in_off hw₁ (by decide) (by decide))) (in_off hw₁ (by decide) (by decide))
    (in_off hw₁ (by decide) (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])),
      P₁.gpr r hr]
  obtain rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  obtain wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  obtain sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  obtain lr₂ : t₂.lr = t.lr := by rw [B₂.lr, P₁.lr]
  obtain h31₂ : t₂.gpr .r31 = V .r31 := by rw [g₂ _ (by decide), E.r31]
  obtain h24₂ : t₂.gpr .r24 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.r24]
  obtain fW₂ : Frame [⟨V .r31 + BitVec.ofNat 64 lO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  obtain kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ →
      blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  obtain ofs₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  obtain Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  refine WP.block_append (WP.mono (hB t₂ _ h24₂ h31₂
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _, contains_pre _ (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _, contains_pre _ (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hw) hBi.w) fun t₃ ⟨blk₃, ck₃, fr₃, g₃, sp₃, lr₃, rd₃, wr₃⟩ => ?_)
  obtain g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h])), g₂ r hr]
  obtain r25₃ : t₃.gpr .r25 = BitVec.ofNat 64 (m - i) := by rw [g₃' _ (by decide), P.r25]
  obtain r26₃ : t₃.gpr .r26 = BitVec.ofNat 64 (i + 1) := by rw [g₃' _ (by decide), P.r26]
  obtain r24₃ : t₃.gpr .r24 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃' _ (by decide), P.r24]
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine cwp_addi (by decide) (by decide) fun t₄ u₄ => cwp_addi (by decide) (by decide) fun t₅ u₅ =>
    cwp_subi (by decide) (by decide) fun t₆ u₆ => WP.block_nil ?_
  obtain hmem : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hwr := hD.wrap
  refine
    { env := E.keep (fun r hr => by
          obtain ⟨h0, h24, h25, h26⟩ := (show ∀ r ∈ Proof.AesGcm.PPC64LE.frozen,
            r ∉ ntzRegs ∧ r ≠ .r24 ∧ r ≠ .r25 ∧ r ≠ .r26 by decide) r hr
          rw [u₆.other _ h25, u₅.other _ h26, u₄.other _ h24, g₃' r h0])
        (by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, sp₂]) (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂])
        (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂])
      frame := by
        rw [hmem]
        exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega_arith)⟩
          · exact ⟨⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
      rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂, P.rd]
      wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂, P.wr]
      r24 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, r24₃, Offset.add_add,
          show 16 * i + 16 = 16 * (i + 1) by omega_arith]
      r26 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), r26₃, ← BitVec.ofNat_add]
      r25 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r25₃, Offset.ofNat_sub_ofNat (by omega_arith),
          Nat.sub_sub]
      ofs := by
        rw [hmem, blockAtMem_frame fr₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hBi.w.sub_right (Lay.wSub (W := V .r31) (d := 16) (n := 16) (by decide))).symm
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
      ck := by rw [hmem, ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
      blk := fun k hk => ?_
      l0 := by
        rw [hmem, blockAtMem_frame fr₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hBi.w.sub_right (Lay.wSub (W := V .r31) (d := 80) (n := 16) (by decide))).symm
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
      gpr := fun r hr => by
        simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₆.other _ hr.2.2.2.2.2.2.2.1, u₅.other _ hr.2.2.2.2.2.2.2.2, u₄.other _ hr.2.2.2.2.2.2.1,
          g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
          P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
            hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])] }
  rw [hmem]
  by_cases hki : k = i
  · subst hki
    rw [blk₃, Bi₂, ofs₂]; simp
  · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega_arith)
    rw [kB₃ (Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) hBk.w, P.blk k hk]
    by_cases hk' : k < i
    · simp [hk', show k < i + 1 by omega_arith]
    · simp [hk', show ¬ k < i + 1 by omega_arith]

theorem pass_ok {V : Reg → BitVec 64} {sp D : Addr} (L : Lay (V .r29) (V .r31)) {m : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block}
    {body : List Instr} (hB : BodyOk (V .r31) body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf (V .r29) (V .r31) t₀ D (16 * m)) {j : Nat} (hj : j < m) (hm : m < 2 ^ 60) {t : State}
    (P : PassInv V sp D m O0 l X fB ckF t₀ t j) :
    WP isa (pass body) t (fun t' => PassInv V sp D m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv V sp D m O0 l X fB ckF t₀ u i) ?_
    (m - j) _ ⟨j, rfl, hj, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hD hm hi P) fun u' P' => ?_
  obtain ev := eval_nonzero P'.r25 (by omega_arith)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega_arith) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.PPC64LE

end

end

/-!
# AES-OCB on PPC64LE: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs a
pass with `pre` over the `m` whole blocks of the data, calls `f` on all of
them (`callBlocks_ok`), copies `Offset_0` back and runs a pass with `post`
(`whole_ok`): each block becomes `G (X ⊕ Offset_i) ⊕ Offset_i`, and the
checksum is the second pass's. As on AArch64
(`Proof/AesOcb/AArch64/Whole.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (in_left in_off shr4 Keeps)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_lsr → cwp_lsr, wp_li → cwp_li

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W s D n) (hk : k ≤ n) :
    DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega_using [hk])
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data, `len` (in `r23`) bytes at `r27`. -/
theorem dataArgs_ok {D : Addr} {t : State} (h27 : t.gpr .r27 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h23 : t.gpr .r23 = BitVec.ofNat 64 len) :
    ArgsOk [Impl.AesGcm.PPC64LE.mov .r5 .r27, .lsr .d .r6 .r23 4] t D (len / 16) := by
  refine ⟨(t.write .r5 (t.gpr .r27 ||| t.gpr .r27)).write .r6 ((t.write .r5 (t.gpr .r27 ||| t.gpr .r27)).gpr .r23 >>> 4),
    ?_, by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, BitVec.or_self, h27],
    by rw [gpr_write_self, gpr_write_of_ne _ _ (by decide), h23, shr4 hl],
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [Impl.AesGcm.PPC64LE.mov, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_d (show 4 < 64 by decide), Option.bind_some]

/-- The start of a pass: `r24 ← D`, `r25 ← m`, `r26 ← 1`. -/
theorem passStart_ok {D : Addr} {t : State} (h27 : t.gpr .r27 = D) {len : Nat} (hl : len < 2 ^ 64)
    (h23 : t.gpr .r23 = BitVec.ofNat 64 len) :
    WP isa (.block passStart) t fun t' =>
      t'.gpr .r24 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .r25 = BitVec.ofNat 64 (len / 16 - 0) ∧
      t'.gpr .r26 = BitVec.ofNat 64 (0 + 1) ∧ (∀ r, r ∉ [.r24, .r25, .r26] → t'.gpr r = t.gpr r) ∧ Keeps t t' := by
  refine cwp_or fun t₁ u₁ => cwp_lsr (by decide) fun t₂ u₂ => cwp_li (by decide) fun t₃ u₃ => WP.block_nil
    ⟨?_, ?_, ?_, fun r hr => ?_, ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr]⟩⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, h27]; simp
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h23, shr4 hl]; rfl
  · rw [u₃.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-- What `whole` leaves. -/
structure WholePost (V : Reg → BitVec 64) (sp D : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame (wholeR (V .r31) D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {len : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 len) (hD : DBuf (V .r29) (V .r31) t (V .r27) len) (hm0 : 0 < len / 16)
    {O0 l : Block}
    (hofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (len / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (.call name c) pre post) t (WholePost V sp (V .r27) (len / 16) O0 l
      (fun k => G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 (len / 16)) t) := by
  have hl := hD.lt
  generalize hmd : len / 16 = m at *
  obtain hmn : 16 * m ≤ len := by omega_using [hmd]
  obtain hm : m < 2 ^ 60 := by omega_using [hl, hmd]
  obtain hDm := hD.take' hmn
  -- the first pass
  unfold whole
  refine WP.seq (WP.mono (passStart_ok E.r27 hl (E.r23.trans h23)) fun s₁ ⟨r24₁, r25₁, r26₁, g₁, k₁⟩ => ?_)
  rw [hmd] at r25₁
  obtain E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  obtain hD₁ : DBuf (V .r29) (V .r31) s₁ (V .r27) (16 * m) := hDm.of_eq k₁.rd k₁.wr
  obtain P₀ : PassInv V sp (V .r27) m O0 l (fun k => blockAtMem s₁.mem (V .r27 + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, r24 := r24₁, r26 := r26₁, r25 := r25₁
      ofs := by rw [k₁.mem, hofs]; rfl
      ck := by rw [k₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, k₁.mem]) hD₁ hm0 hm P₀) fun s₂ P₂ => ?_)
  have hw := hD.wrap
  obtain hD₂ : DBuf (V .r29) (V .r31) s₂ (V .r27) (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.assoc (WP.seq (WP.mono (callBlocks_ok (f := f) L ok nf hR h28 P₂.env
    (fun s₃ g₃ k₃ => by
      have := dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.r27]) hl
        (by rw [g₃ _ (by decide) (by decide) (by decide), P₂.env.r23, h23])
      rwa [hmd] at this) (dstD hD₂)) fun s₃ P₃ => ?_))
  obtain E₃ := P₃.env P₂.env
  obtain kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r27, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  obtain kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem s₁.mem (V .r31 + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega_using [hd]))).symm) (L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega_using [hd]))).symm)]
  obtain o0₃ : blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), k₁.mem, ho0]
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) (by decide) (by decide)
    E₃.r31 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide)))
    fun s₄a B₄ => WP.mono (passStart_ok (t := s₄a) (D := V .r27) (len := len) (by rw [B₄.gpr _ (by decide), E₃.r27]) hl
      (by rw [B₄.gpr _ (by decide), E₃.r23, h23])) fun s₄ ⟨r24₄, r25₄, r26₄, g₄, k₄⟩ => ?_))
  obtain E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  rw [hmd] at r25₄
  obtain E₄ := E₄a.others g₄ k₄.sp k₄.rd k₄.wr
  obtain hD₄ : DBuf (V .r29) (V .r31) s₄ (V .r27) (16 * m) :=
    hD₂.of_eq (by rw [k₄.rd, B₄.rd, P₃.rd]) (by rw [k₄.wr, B₄.wr, P₃.wr])
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨V .r31, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [k₄.mem]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  obtain hK : bytesAt s₂.mem (V .r29) (16 * (R + 1)) = bytesAt t.mem (V .r29) (16 * (R + 1)) := by
    obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]), k₁.mem]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (V .r27 + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem (V .r29) (16 * (R + 1)))
        (blockAtMem t.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega_using [hk])).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, k₁.mem]
  obtain ck₃ : blockAtMem s₃.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  obtain P₀' : PassInv V sp (V .r27) m O0 l (fun k => blockAtMem s₄.mem (V .r27 + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, r24 := r24₄, r26 := r26₄, r25 := r25₄
      ofs := by rw [k₄.mem, B₄.val, o0₃]; rfl
      ck := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [k₄.mem, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 hm P₀') fun s₅ P₅ => ?_
  obtain subW : ∀ r ∈ [(⟨V .r31 + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .r27, 16 * m⟩], ∃ r' ∈ wholeR (V .r31) (V .r27) (16 * m),
        Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨V .r27, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, k₄.rd, B₄.rd, P₃.rd, P₂.rd, k₁.rd],
    by rw [P₅.wr, k₄.wr, B₄.wr, P₃.wr, P₂.wr, k₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← k₁.mem]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨V .r27, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [k₄.mem] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
          (by decide)⟩).trans (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.PPC64LE

end

end

/-!
# AES-OCB on PPC64LE: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs the whole blocks,
if any (`wholeIte_ok`), and the rest, if any (`restIte_ok`): for `seal`
`OCB-ENCRYPT`'s ciphertext, offset and checksum (`bodySeal_ok`), for `open`
`OCB-DECRYPT`'s (`bodyOpen_ok`). As on AArch64
(`Proof/AesOcb/AArch64/Body.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (eval_zero and15 shr4 ofNat_sub64 Keeps)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_lsr → cwp_lsr, wp_li → cwp_li, wp_and → cwp_and,
  wp_sub → cwp_sub, wp_add → cwp_add

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 l : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem (V .r29) (16 * (R + 1)))
        (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole (.call name c) pre post))) s
      (WholePost V sp (V .r27) (n / 16) O0 l
        (fun k => G (bytesAt s.mem (V .r29) (16 * (R + 1)))
          (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  refine WP.seq (cwp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have r3₁ : s₁.gpr .r3 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, E.r23, h23, shr4 hn]
  have E₁ : Env V sp s₁ := E.others (rs := [.r3]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr
  refine WP.ite _ (eval_zero r3₁ (by omega_arith)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [u₁.mem]; exact Frame.refl _ _, u₁.rd, u₁.wr, fun k hk => absurd hk (by omega_arith),
      by rw [u₁.mem, hofs, hm]; rfl, by rw [u₁.mem, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    have hD₁ := hD.of_eq u₁.rd u₁.wr
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR h28 h23 hD₁ (by omega_arith)
      (by rw [u₁.mem, hofs]) (by rw [u₁.mem, ho0]) (by rw [u₁.mem, hck]) (by rw [u₁.mem, hl0])
      (fun i => by rw [u₁.mem, hckF1]) hckF2₀ (fun i => by rw [u₁.mem, hckF2])) fun t P => ?_
    refine ⟨P.env, by have f := P.frame; rwa [u₁.mem] at f, by rw [P.rd, u₁.rd], by rw [P.wr, u₁.wr],
      fun k hk => by rw [P.blk k hk, u₁.mem], P.ofs, by rw [P.ck]⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {V : Reg → BitVec 64} {sp : Addr} {t : State} (E : Env V sp t) {n : Nat} (hn : n < 2 ^ 64)
    (h23 : V .r23 = BitVec.ofNat 64 n) :
    WP isa (.block [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r24 .r23 .r25, .add .r24 .r24 .r27]) t fun t₁ =>
      t₁.gpr .r24 = V .r27 + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r25 = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ∉ [.r0, .r24, .r25] → t₁.gpr r = t.gpr r) ∧ Keeps t t₁ := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega_arith]
  refine cwp_li (by decide) fun t₁ u₁ => cwp_and fun t₂ u₂ => cwp_sub fun t₃ u₃ => cwp_add fun t₄ u₄ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.lr, u₃.lr, u₂.lr, u₁.lr]⟩⟩
  · have r25₂ : t₂.gpr .r25 = BitVec.ofNat 64 (n % 16) := by
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), E.r23, h23, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have r24₃ : t₃.gpr .r24 = BitVec.ofNat 64 (16 * (n / 16)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r23, h23, r25₂, hsub]
    rw [u₄.gpr, r24₃, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r27,
      BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), E.r23, h23, and15,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.2.1, u₂.other _ hr.2.2, u₁.other _ hr.1]

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .r29)
    else blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (V .r29) R
        (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .r29))))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ckO) =
    if 0 < r then
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) t (V .r27) n) :
    WP isa (.seq (.block [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r24 .r23 .r25, .add .r24 .r24 .r27])
        (.ite (.zero .d .r25) (.block []) (rest enc))) t
      (TailPost enc V sp R (V .r27 + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  refine WP.seq (WP.mono (bodyTail_ok E hn h23) fun t₁ ⟨r24₁, r25₁, g₁, k₁⟩ => ?_)
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.ite _ (eval_zero r25₁ (by omega_arith)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega_arith
    refine ⟨E₁, by rw [k₁.mem]; exact Frame.refl _ _, k₁.rd, k₁.wr, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, k₁.mem]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega_arith
    have hP : DBuf (V .r29) (V .r31) t₁ (V .r27 + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)).of_eq k₁.rd k₁.wr
    refine WP.mono (rest_ok enc L E₁ hR h28 hr (Nat.mod_lt _ (by decide)) r24₁ r25₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← k₁.mem]; exact P.frame, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, k₁.mem]
    · rw [P.out, k₁.mem]
    · rw [P.ck, k₁.mem]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (V : Reg → BitVec 64) (sp D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (bodyR (V .r31) D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ck

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

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Offset.sub W (by decide)
      (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (body true) s (BodyPost V sp (V .r27) n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)
       else offAt O0 (ctxLstar s.mem (V .r29)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16) ^^^ pad ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .r29) (V .r31) s (V .r27) (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .r29) (V .r31) s ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  have dDP : (⟨(V .r27), 16 * (n / 16)⟩ : Region).Disjoint ⟨(V .r27) + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint (V .r27) (Nat.le_refl _) (by omega_arith)
  have hl : ∀ i < n / 16, blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem (V .r27) n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem (V .r27) (by omega_arith)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29))
    (ckF1 := ckOf fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames hcall_enc sealPre_ok xorOfs_ok L E hR h28 h23 hD
    hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .r31) (V .r27) (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok true L Pw.env hR h28 h23 (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .r29) R = ctxCiph s.mem (V .r29) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .r29) = ctxLstar s.mem (V .r29) :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_arith)
  have rest : (bytesAt s.mem (V .r27) n).drop (16 * (n / 16)) = bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem (V .r27) hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  have ckT : blockAtMem t.mem ((V .r31) + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem (V .r27) (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem (V .r27) (16 * (n / 16)) (n % 16)
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
theorem bodyOpen_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (body false) s (BodyPost V sp (V .r27) n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29))))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)
       else offAt O0 (ctxLstar s.mem (V .r29)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .r29) (V .r31) s (V .r27) (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .r29) (V .r31) s ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  have dDP : (⟨(V .r27), 16 * (n / 16)⟩ : Region).Disjoint ⟨(V .r27) + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint (V .r27) (Nat.le_refl _) (by omega_arith)
  have hl : ∀ i < n / 16, blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem (V .r27) n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem (V .r27) (by omega_arith)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .r29) (16 * (R + 1)))
      (blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .r29)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .r29)) (i + 1))
    Proof.Aes.PPC64LE.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok openPost_ok L E hR h28 h23 hD
    hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .r31) (V .r27) (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok false L Pw.env hR h28 h23 (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .r29) R = ctxCiph s.mem (V .r29) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .r29) = ctxLstar s.mem (V .r29) :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_arith)
  have rest : (bytesAt s.mem (V .r27) n).drop (16 * (n / 16)) = bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem (V .r27) hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  have ckT : blockAtMem t.mem ((V .r31) + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem (V .r27) (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem (V .r27) (16 * (n / 16)) (n % 16)
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

end VG.Proof.AesOcb.PPC64LE
