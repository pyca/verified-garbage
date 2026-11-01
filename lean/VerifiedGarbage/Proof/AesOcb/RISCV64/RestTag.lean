module

import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Spec.Ocb

/-!
# AES-OCB on RISC-V: the rest of the data (`rest`) and the tag (`tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`
(`restHead_ok`), XORs the last bytes with `Pad` (`xorPad_ok`) and adds the
padded plaintext to the checksum (`padCk_ok`), in the order of `seal` or
`open` (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
As on PPC64LE (`Proof/AesOcb/PPC64LE/RestTag.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Ocb (length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (xorLoop_ok LoopPre in_left in_off covers_off covers_left)

/-- The callee-saved registers are unchanged. -/
abbrev Saved (t t' : State) : Prop := ∀ r ∈ preserved, t'.gpr r = t.gpr r

theorem saved_of {t t' : State} {rs : List Reg} (h : ∀ r, r ∉ rs → t'.gpr r = t.gpr r)
    (hd : ∀ r ∈ rs, r ∉ preserved := by decide) : Saved t t' :=
  fun r hr => h r fun h' => hd r h' hr

theorem Saved.trans {t₁ t₂ t₃ : State} (h₁ : Saved t₁ t₂) (h₂ : Saved t₂ t₃) : Saved t₁ t₃ :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

/-- Not in a list, so not one of its elements. -/
theorem ne_of_not_mem {q x : Reg} {rs : List Reg} (h : q ∉ rs) (hx : x ∈ rs := by decide) : q ≠ x :=
  fun e => h (e ▸ hx)

/-- Not in a list, so not in a sublist of it. -/
theorem not_mem_of_sub {q : Reg} {rs rs' : List Reg} (h : q ∉ rs) (hs : ∀ x ∈ rs', x ∈ rs := by decide) :
    q ∉ rs' :=
  fun h' => h (hs _ h')

/-- The registers `xorPad` and `padCk` write. -/
abbrev xpRegs : List Reg := [.t0, .t1, .t2, .a0, .a1, .a2, .a3]

/-- `xorPad`: the `r` bytes at `P` (in `s4`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W : Addr} {s : State} (hs0 : s.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (hs4 : s.gpr .s4 = P) (hs5 : s.gpr .s5 = BitVec.ofNat 64 r)
    (hP : DBuf K W s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hA : WP isa (.block [.addi .a0 .s0 (tmpO : Int), Impl.AesGcm.RISCV64.mov .a1 .s4,
      Impl.AesGcm.RISCV64.mov .a2 .s5]) s fun s₃ =>
      s₃.gpr .a0 = W + BitVec.ofNat 64 112 ∧ s₃.gpr .a1 = P ∧ s₃.gpr .a2 = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₃.gpr r = s.gpr r) ∧ Proof.AesGcm.RISCV64.Keeps s s₃ :=
    wp_addi (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs0]; rfl,
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hs4],
        by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hs5],
        fun q a b c => by rw [u₃.other _ c, u₂.other _ b, u₁.other _ a],
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp]⟩⟩
  unfold xorPad
  refine WP.seq (WP.mono hA fun s₁ ⟨a0₁, a1₁, a2₁, g₁, k₁⟩ => ?_)
  have pre : LoopPre s₁ (W + BitVec.ofNat 64 112) P r :=
    ⟨a0₁, a1₁, a2₁, hr, by omega, by rw [k₁.rd, k₁.wr]; exact covers_left (covers_off hw (by omega) (by decide)),
      by rw [k₁.wr]; exact hP.wr, (hP.w.sub_right (Lay.wSub (W := W) (d := 112) (n := r) (by omega))).symm⟩
  refine WP.mono (xorLoop_ok s₁ pre) fun t ⟨mt, ot⟩ => ?_
  obtain ⟨rdt, wrt, spt⟩ := ot.keeps
  refine ⟨by rw [mt, k₁.mem]; rfl, fun q hq => ?_, by rw [spt, k₁.sp], by rw [rdt, k₁.rd], by rw [wrt, k₁.wr]⟩
  rw [ot.other q (ne_of_not_mem hq) (ne_of_not_mem hq) (ne_of_not_mem hq) (ne_of_not_mem hq) (ne_of_not_mem hq),
    g₁ q (ne_of_not_mem hq) (ne_of_not_mem hq) (ne_of_not_mem hq)]

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `s4`. -/
theorem padCk_ok {K W : Addr} (L : Lay K W) {s : State} (hs0 : s.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {S : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (hs4 : s.gpr .s4 = S) (hs5 : s.gpr .s5 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
        blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk xorW
  refine WP.seq (WP.mono (padTo_ok hs0 L.wal hw hr hr' (by decide) hs4 hs5 hS
    (hSW.sub_right (Lay.wSub (by decide)))) fun t₁ P₁ => ?_)
  have hs0₁ : t₁.gpr .s0 = W := by rw [P₁.gpr _ (by decide), hs0]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  refine WP.mono (xorB_ok (s := t₁) (pd := ckO) (qd := t2O) (cd := ckO) L.wal L.wal L.wal (by decide) (by decide)
    (by decide) hs0₁ hs0₁ hs0₁ (by decide) (by decide) (by decide) (in_left (ww (by decide)))
    (in_left (ww (by decide))) (in_left (ww (by decide))) (in_left (ww (by decide))) (ww (by decide))
    (ww (by decide)) (Offset.sep _ (by decide) (by decide) (by decide)) (Offset.sep _ (by decide) (by decide)
    (by decide)))
    fun t₂ B₂ => ⟨(P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_, fun q hq => ?_,
      by rw [B₂.sp, P₁.sp], by rw [B₂.rd, P₁.rd], by rw [B₂.wr, P₁.wr]⟩
  · rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]
  · rw [B₂.gpr q (not_mem_of_sub hq), P₁.gpr q (not_mem_of_sub hq (fun x hx => by
      simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env V sp t'
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2)
  tmp : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem (V .s2) R (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2))
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) :
    WP isa (.seq (.block (xorB .s0 .s2 .s0 ofsO 240 ofsO ++ copy16 ofsO tmpO)) (encOne tmpO)) t
      (RestHead V sp R t) := by
  refine WP.seq (WP.block_append (WP.mono (xorB_ok (s := t) (pd := ofsO) (qd := 240) (cd := ofsO) L.wal L.kal L.wal (by decide)
    (by decide) (by decide) E.s0 E.s2 E.s0 (by decide) (by decide) (by decide) (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    ((L.k_w' (a := 248) (n := 8) (d := 16) (k := 8) (by decide) (by decide)).sep (Region.contains_self _ _)
      (Region.contains_self _ _))) fun t₁ B₁ => ?_))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  refine WP.mono (copy16_ok (s := t₁) (a := ofsO) (d := tmpO) L.wal (by decide) (by decide) E₁.s0
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide)))
    fun t₂ B₂ => ?_
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  have fr₂ : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have ofs₂ : blockAtMem t₂.mem (V .s0 + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2) := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₂.mem (V .s2) R = ctxCiph t.mem (V .s2) R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega_arith)]
  refine WP.mono (encOne_ok L hR hs3 E₂ (d := tmpO) (by decide)) fun t₃ P₃ => ?_
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
    show ctxCiph t₂.mem (V .s2) R _ = _
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
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2)
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem (V .s2) R
      (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2))))
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (hs4 : t.gpr .s4 = P) (hs5 : t.gpr .s5 = BitVec.ofNat 64 r)
    (hP : DBuf (V .s2) (V .s0) t P r) :
    WP isa (rest enc) t (RestPost enc V sp R P r t) := by
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (restHead_ok L E hR hs3) fun t₃ H => ?_))
  have hs4₃ : t₃.gpr .s4 = P := by rw [H.saved _ (by decide), hs4]
  have hs5₃ : t₃.gpr .s5 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide), hs5]
  have hP₃ : DBuf (V .s2) (V .s0) t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩], (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact dW (by decide)
  have dT : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩],
      (⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := Proof.Cmac.bytesAt_frame H.frame dH (by omega_arith)
  have hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega_arith
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (V .s0 + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P
          (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (V .s0 + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes (ctxCiph t.mem (V .s2) R
          (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem (V .s2)))) := by
    intro u hu ht
    rw [hu, xor_bytesAt_block _ _ _ hl (by omega_arith), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega_arith), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩], (⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have ck₃ : blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 ckO) = blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)],
      (⟨V .s0 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (xorPad_ok E₃.s0 E₃.perm.w hr hr' hs4₃ hs5₃ hP₃)
      fun t₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (padCk_ok L E₄.s0 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), hs4₃])
      (by rw [g₄ _ (by decide), hs5₃]) (by rw [rd₄, wr₄]; exact hS₃) hP.w)
      fun t₅ ⟨fr₅, ck₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := Proof.Cmac.bytesAt_frame fr₅ dT (by omega_arith)
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((saved_of g₄).trans (saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (padCk_ok L E₃.s0 E₃.perm.w hr hr' hs4₃ hs5₃ hS₃ hP.w)
      fun t₄ ⟨fr₄, ck₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := Proof.Cmac.bytesAt_frame fr₄ dT (by omega_arith)
    refine WP.mono (xorPad_ok E₄.s0 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), hs4₃])
      (by rw [g₄ _ (by decide), hs5₃]) (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
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
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 d, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩] t.mem t'.mem
  val : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 d) =
    ctxCiph t.mem (V .s2) R (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ldO)) ^^^
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 sumO)
  saved : Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State} (E : Env V sp t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {d : Nat}
    (hd : d = tagO ∨ d = t2O) :
    WP isa (tag d) t (TagPost V sp R d t) := by
  have hd' : d = 0 ∨ d = 256 := hd
  have hd8 : d % 8 = 0 ∧ d + 8 < 2048 := by omega_arith
  have hd16 : d + 16 ≤ 2560 := by omega_arith
  unfold tag xorW
  rw [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy16_ok (s := t) (a := ckO) (d := tmpO) L.wal (by decide) (by decide) E.s0
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide)))
    fun t₁ B₁ => ?_))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  refine WP.block_append (WP.mono (xorB_ok (s := t₁) (pd := tmpO) (qd := ofsO) (cd := tmpO) L.wal L.wal L.wal (by decide)
    (by decide) (by decide) E₁.s0 E₁.s0 E₁.s0 (by decide) (by decide) (by decide) (E₁.perm.wR (by decide))
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide))
    (E₁.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₂ B₂ => ?_)
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  refine WP.mono (xorB_ok (s := t₂) (pd := tmpO) (qd := ldO) (cd := tmpO) L.wal L.wal L.wal (by decide)
    (by decide) (by decide) E₂.s0 E₂.s0 E₂.s0 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide))
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide))
    (E₂.perm.wW (by decide)) (Offset.sep _ (by decide) (by decide) (by decide))
    (Offset.sep _ (by decide) (by decide) (by decide))) fun t₃ B₃ => ?_
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨V .s0 + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  have fr₃ : Frame [⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  have tmp₃ : blockAtMem t₃.mem (V .s0 + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₃.mem (V .s2) R = ctxCiph t.mem (V .s2) R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega_arith)]
  refine WP.seq (WP.mono (encOne_ok L hR hs3 E₃ (d := tmpO) (by decide)) fun t₄ P₄ => ?_)
  have E₄ := P₄.env E₃
  have tmp₄ : blockAtMem t₄.mem (V .s0 + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem (V .s2) R (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^
        blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ldO)) := by
    rw [P₄.enc0, tmp₃, ← cK]; rfl
  refine WP.block_append (WP.mono (copy16_ok (s := t₄) (a := tmpO) (d := d) L.wal (by decide) hd8 E₄.s0
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega_arith)) (E₄.perm.wW (by omega_arith)))
    fun t₅ B₅ => ?_)
  have E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  refine WP.mono (xorB_ok (s := t₅) (pd := d) (qd := sumO) (cd := d) L.wal L.wal L.wal hd8 (by decide) hd8 E₅.s0 E₅.s0 E₅.s0
    (by decide) (by decide) (by decide) (E₅.perm.wR (by omega_arith)) (E₅.perm.wR (by omega_arith)) (E₅.perm.wR (by decide))
    (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega_arith)) (E₅.perm.wW (by omega_arith))
    (Offset.sep _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (Offset.sep _ (by simp only [sumO]; omega_arith) (by decide) (by omega_arith))) fun t₆ B₆ => ?_
  have dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨V .s0 + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega_arith)
  have dCall : ∀ q ∈ [(⟨V .s0 + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩],
      (⟨V .s0 + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
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

end VG.Proof.AesOcb.RISCV64
