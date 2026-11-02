module

import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTLabel
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTPriv
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBase
public import VerifiedGarbage.Proof.RsaOaep.Scan

/-!
# RSAES-OAEP decryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Verified.lean`): constant time
(`code_constantTime`, from `code_ct`); a state meeting the precondition,
which does not depend on the hash functions (`dec_sat`); `dec_verified`; and
decryption for two linked hash functions (`dec_link_verified`, with
encryption's `Link`), which the registration files bind.
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTMain.lean`). Two runs from entry states with
the anchor's public data leak alike: the code between the calls by the
taint analysis (`Dc/CTBlocks`), the private operation by its constant time
(`priv_ct`), the hash functions' calls by their contracts (`hashLabel_ct`,
MGF1's `mgfXor_ctS`), and the branch on the public `k` (`two_ite`); what
each run satisfies between them follows from correctness. The scan's index,
the shift's count and the private operation's result differ between the
runs, but only as data.
-/
namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep.RISCV64 (Base Saves off offs MgfA MFit HashCT two_seq mgfXor_ok mgfXor_ctS sub_k
  seedArgs_taint dbArgs_taint chkK_taint restore_taint)
open VG.Proof.RsaOaep (scan_idx)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .a4).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]; exact h

/-- `DX` with the check passed. -/
def DK (D : Nat) (a t : State) : Prop := DX a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DX a t ∧ t.gpr .s6 = off (stackArg a 13) src ∧ t.gpr .s7 = BitVec.ofNat 64 srcLen ∧
    t.gpr .s8 = off (stackArg a 13) dst ∧ t.gpr .s9 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {src srcLen dst dstLen : Nat} {a t : State} (h : MgfD src srcLen dst dstLen a t) :
    MgfA SX VX PreX PubX src srcLen dst dstLen a t := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h6, h7, h8, h9⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  exact ⟨_, pX, pubX_bx P hm p, bX, h6, h7, h8, h9⟩

section
variable {G : Hash} (hG : HashOK G) (cG : HashCT hG) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

include cG hF hGh hGl hGv in
/-- `mgfXor`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXor G) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfA SX VX PreX PubX x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXor_ctS okX hG cG hF x.2 hGh hGl hGv).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hF hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD src srcLen dst dstLen a t) : WP isa (mgfXor G) t (DX a) := by
  obtain ⟨⟨s, m, P, p, hm, b⟩, h6, h7, h8, h9⟩ := h
  exact WP.mono (mgfXor_ok (fits P (s' := withMem s m) rfl rfl) hG hF hGh hGl hGv hf b
    (h6.trans (off13 p _)) h7 (h8.trans (off13 p _)) h9) fun _ h' => ⟨s, m, P, p, hm, h'.1⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .a4).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .a4 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {H : Hash} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.pins
  refine wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
    fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE, Nat.zero_add]
  · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, r1, sub_k (by omega)]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {H : Hash} (hD64 : H.D ≤ 64) {a t : State} (h : DK H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.pins
  refine wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
    fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE]
  · rw [o₄.get .s7, o₃.get .s7, e₂]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE, Nat.zero_add]
  · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, r1, sub_k (by omega)]

/-- `DX` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {D : Nat} {c : Prog isa} {a t : State} (h : DK D a t)
    (hw : ∀ s m, PreD s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK D a) :=
  let ⟨⟨s, m, P, p, hm, b⟩, hk⟩ := h
  WP.mono (hw s m P p (hk_s p hk) hm b) fun _ b' => ⟨⟨s, m, P, p, hm, b'⟩, hk⟩

/-- After the scan: the index, below `k`. -/
def DI (D : Nat) (a t : State) : Prop := DK D a t ∧ ∃ idx, idx < kA a ∧ t.gpr .s6 = BitVec.ofNat 64 idx

theorem dk_pins {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → DK D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

include hH cH fH cG fG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK H.D)) (decMain H G) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK H.D) ((hashLabel_ct hH cH fH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t h => WP.mono (hashLabel_dx hH fH h.1) fun _ h' => ⟨h', h.2⟩) ?_
  refine two_seq (Ψ := DK H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0]))
    (fun a t h => dk_wp h fun s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1]))
    (fun a t ⟨⟨s, m, P, p, hm, b⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    refine WP.mono (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ => ⟨⟨⟨s, m, P, p, hm, b'⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .s5)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by rw [ea]; omega, i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0]))
    (fun a t ⟨⟨⟨s, m, P, p, hm, b⟩, hk⟩, idx, hi, h6⟩ => WP.mono (clearBuf_ok P b) fun t' ⟨b', g', _⟩ =>
      ⟨⟨⟨s, m, P, p, hm, b'⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  refine two_seq (Ψ := DI H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, p, hm, b⟩, hk⟩, idx, hi, h6⟩ => WP.mono (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ => ⟨⟨⟨s, m, P, p, hm, b'⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, p, hm, b⟩, hk⟩, idx, hi, h6⟩ => ?_) ?_
  · have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    exact WP.mono (shift_ok P b h6 (by rw [← ea]; exact hi)) fun _ h' => ⟨⟨s, m, P, p, hm, h'.1⟩, hk⟩
  refine two_seq (Ψ := DK H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .s3 = a.gpr .a2)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1, .s2])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r3⟩ := h.1.pins
    obtain ⟨⟨s, m, P, p, hm, b⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g'.get .s3).trans r3⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

/-- After the private operation, from an entry state with `a`'s public data. -/
def AP (a v : State) : Prop := ∃ s, PreD s ∧ PubD a s ∧ AfterPriv s v

/-- After the check of `k`. -/
def AC (D : Nat) (a v : State) : Prop :=
  ∃ s, PreD s ∧ PubD a s ∧ AfterPriv s v ∧ (v.gpr .a0 != 0) = decide (kk s < 2 * D + 2)

theorem AP.dx {a v : State} (h : AP a v) : DX a v := let ⟨_, P, p, A⟩ := h; DX.of_after P p A

theorem AC.dx {D : Nat} {a v : State} (h : AC D a v) : DX a v := let ⟨_, P, p, A, _⟩ := h; DX.of_after P p A

theorem AC.r0 {D : Nat} {a v : State} (h : AC D a v) : (v.gpr .a0 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨s, _, p, _, r⟩ := h
  rw [r]; show decide ((s.gpr .a4).toNat < _) = _; rw [p.g .a4 (by decide)]

include hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv in
theorem code_ct : RelCT isa (Two fun a s => PreD s ∧ PubD a s) (decrypt H G) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := AEnt)
    (dentry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.sp, h₂.2.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P) fun t E => ⟨s, P, p, E⟩) ?_
  refine two_seq (Ψ := AP) priv_ct (fun a t h => priv_dx h) ?_
  refine two_seq (Ψ := AC H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.dx) []))
    (fun a v ⟨s, P, p, A⟩ => WP.mono (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ => ⟨s, P, p, A', r⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, PreD s ∧ PubD a s ∧ Saves s u) ?_
    fun a v ⟨s, P, p, A, r⟩ => WP.mono (ite_done hH hG fH fG hHh hHl hHv hGh hGl hGv P A r)
      fun _ d => ⟨s, P, p, d.1⟩)
    (restore_taint fun a u₁ u₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r0, h₂.r0])
    (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.s1, .s2, .s3])) ?_
  refine (decMain_ct hH cH fH hG cG fG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
  rw [eval_nonzero, h₁.r0] at c₁
  have hk : HK H.D a := by simp at c₁; omega
  exact ⟨a, ⟨h₁.dx, hk⟩, ⟨h₂.dx, hk⟩⟩

end

end VG.Proof.RsaOaep.RISCV64.Dec


namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (HashCT Link)

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include cH fH cG fG hHh hHl hHv hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre
      (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pub (decrypt H G) :=
  RelCT.constantTime ((code_ct hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preD_of h₁, pubD_refl s₁⟩, preD_of h₂, pubD_of hp⟩) fun _ _ h => h)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` against its shared contract, given a
state meeting it. -/
theorem dec_verified (hsat : ∃ s, (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre s) :
    Verified RISCV64.target (decrypt H G) (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes) :=
  ⟨code_correct hH hG fH fG hHh hHl hHv hGh hGl hGv,
    code_constantTime hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, an empty label, a working space of 2080
words, and the stack arguments at `sp`. -/
def decSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10000 then 1
    else bif Nat.beq a.toNat 0x10009 then 0x43 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x44 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x45 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x46 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x47 else bif Nat.beq a.toNat 0x10059 then 0x41
    else bif Nat.beq a.toNat 0x10060 then 64 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat (H G : Spec.Mgf1.Hash) : ∃ s, (Spec.RsaOaep.decryptContract H G abi stackBytes).pre s := by
  refine ⟨decSatState, ?_⟩
  -- The precondition does not depend on the hash functions: with them and the
  -- stack literal, `sig_sat_check` decides it in the kernel.
  change (Spec.RsaOaep.decryptContract Spec.Mgf1.md5 Spec.Mgf1.md5 abi 3472).pre decSatState
  sig_sat_check [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen,
    List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` for the linked hash functions. -/
theorem dec_link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified RISCV64.target (decrypt H G) (Spec.RsaOaep.decryptContract lh.G lg.G abi stackBytes) :=
  dec_verified lh.ok lh.ct lh.fits lg.ok lg.ct lg.fits lh.hash lh.len lh.valid lg.hash lg.len lg.valid
    (dec_sat lh.G lg.G)

end VG.Proof.RsaOaep.RISCV64.Dec
