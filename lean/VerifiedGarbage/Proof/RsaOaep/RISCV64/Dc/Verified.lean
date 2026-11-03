module

import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgfT
public import VerifiedGarbage.Proof.HashTable.RISCV64
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTLabel
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTPriv
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBase
public import VerifiedGarbage.Proof.RsaOaep.Scan

/-!
# RSAES-OAEP decryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTMain.lean`, `Dc/Verified.lean`): constant time
(`code_constantTime`, from `code_ct`, for MGF1's table that of the first
run, which the public data makes the second's); a state meeting the
precondition, which does not depend on the label's hash function, with
MGF1's table that of any `w` of `vs`, at `0x300000` (`dec_sat`); and
`dec_verified`.
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: constant time

Two runs from entry states with the anchor's public data leak alike: the
code between the calls by the taint analysis (`Dc/CTBlocks`), the private
operation by its constant time (`priv_ct`), the hash functions' calls by
their contracts (`hashLabel_ct`, MGF1's `mgfXorT_ctS`, with the table at
the same address and its functions at the same addresses: `DXT`), and the
branch on the public `k` (`two_ite`); what each run satisfies between them
follows from correctness. The scan's index, the shift's count and the
private operation's result differ between the runs, but only as data.
-/

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep.RISCV64 (Base Saves SC off offs MgfAT MFit HashCT TabS TabA two_seq mgfXorT_ok mgfXorT_ctS
  sub_k seedArgs_taint dbArgs_taint chkK_taint restore_taint)
open VG.Proof.RsaOaep (scan_idx)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf Coh)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .a4).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]; exact h

/-- `G`'s functions at the anchor's addresses. -/
def SymG (G : Hash) (a s : State) : Prop :=
  s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧ s.syms G.finN = a.syms G.finN

/-- `DX`, with MGF1's table, `G`'s, on entry, its functions at the anchor's
addresses, and the entry's addresses of statics. -/
def DXT (G : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s m, PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15) ∧ PubD a s ∧ SymG G a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t ∧ t.syms = s.syms

theorem DXT.dx {G : Hash} {f : Fns} {a t : State} (h : DXT G f a t) : DX a t :=
  let ⟨s, m, P, _, p, _, hm, b, _⟩ := h; ⟨s, m, P, p, hm, b⟩

theorem DXT.only {G : Hash} {f : Fns} {a t t' : State} {rs : List Reg} (h : DXT G f a t) (o : Only rs t t')
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ Proof.RsaOaep.RISCV64.fixed := by decide) : DXT G f a t' :=
  let ⟨s, m, P, T, p, y, hm, b, sy⟩ := h
  ⟨s, m, P, T, p, y, hm, b.only (fits P (s' := withMem s m) rfl rfl) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 15 SX x (stackArg x 15)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : Proof.RsaOaep.RISCV64.OkS SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 15 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- `DXT` with the check passed. -/
def DK (G : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G f a t ∧ t.gpr .s6 = off (stackArg a 13) src ∧ t.gpr .s7 = BitVec.ofNat 64 srcLen ∧
    t.gpr .s8 = off (stackArg a 13) dst ∧ t.gpr .s9 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h6, h7, h8, h9⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a15.trans (p.args 15 (by decide)), y⟩, bX, sy, h6, h7, h8, h9⟩
  rw [a15]
  exact tabS_to P T hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G : Hash} (hG : HashOK G) (cG : HashCT hG) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hF hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 15) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG hF x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hF hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G f src srcLen dst dstLen a t) : WP isa (mgfXorT f 15) t (DXT G f a) := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h6, h7, h8, h9⟩ := h
  exact WP.mono (mgfXorT_ok (fits P (s' := withMem s m) rfl rfl) hG hF (tabS_wm P T hm) hGh hGl hGv hf b sy
    (h6.trans (off13 p _)) h7 (h8.trans (off13 p _)) h9) fun _ h' => ⟨s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .a4).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .a4 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1) (h := by omega)
    fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE, Nat.zero_add]
  · rw [o₄.get .s7, o₃.get .s7, e₂, o₁.get .s1, r1, sub_k (by omega)]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .a4).toNat := rfl
  obtain ⟨-, r0, r1, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega)
    fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₃ o₃ e₃ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, r0, hE]
  · rw [o₄.get .s7, o₃.get .s7, e₂]
  · rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, r0, hE, Nat.zero_add]
  · rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, r1, sub_k (by omega)]

/-- `DXT` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G f D a t)
    (hw : ∀ s m, PreD s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G f D a) :=
  let ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below `k`. -/
def DI (G : Hash) (f : Fns) (D : Nat) (a t : State) : Prop :=
  DK G f D a t ∧ ∃ idx, idx < kA a ∧ t.gpr .s6 = BitVec.ofNat 64 idx

theorem dk_pins {G : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH fH cG fG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G f H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₁).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G f H.D) ((mgf_anyD hG cG fG hGh hGl hGv q₂).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
    (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG fG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G f H.D) ((hashLabel_ct hH cH fH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.dx, h₂.1.dx⟩)
    fun _ _ h => h) (fun a t h => dk_wp h fun s m P _ _ hm b => WP.mono (hashLabel_ok P hH fH hm b)
      fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0]))
    (fun a t h => dk_wp h fun s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1]))
    (fun a t ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .s5)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by rw [ea]; omega, i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  refine two_seq (Ψ := DI G f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g'.get .s6).trans h6⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.s0, .s1]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h6⟩ => ?_) ?_
  · have ea : kA a = kk s := by show (a.gpr .a4).toNat = (s.gpr .a4).toNat; rw [p.g .a4 (by decide)]
    exact WP.mono_syms (shift_ok P b h6 (by rw [← ea]; exact hi)) fun _ h' y' =>
      ⟨⟨s, m, P, T, p, y, hm, h'.1, y'.trans sy⟩, hk⟩
  refine two_seq (Ψ := DK G f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .s3 = a.gpr .a2)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.s0, .s1, .s2])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r3⟩ := h.1.dx.pins
    obtain ⟨⟨s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
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

/-- After the entry, from an entry state with MGF1's table, `G`'s, and `a`'s
public data. -/
def AEntT (G : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s, PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15) ∧ PubD a s ∧ SymG G a s ∧ Entered s t ∧ t.syms = s.syms

/-- After the private operation, from such an entry state. -/
def AP (G : Hash) (f : Fns) (a v : State) : Prop :=
  ∃ s, PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15) ∧ PubD a s ∧ SymG G a s ∧ AfterPriv s v ∧ v.syms = s.syms

/-- After the check of `k`. -/
def AC (G : Hash) (f : Fns) (D : Nat) (a v : State) : Prop :=
  ∃ s, PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15) ∧ PubD a s ∧ SymG G a s ∧ AfterPriv s v ∧ v.syms = s.syms ∧
    (v.gpr .a0 != 0) = decide (kk s < 2 * D + 2)

theorem AP.dx {G : Hash} {f : Fns} {a v : State} (h : AP G f a v) : DX a v :=
  let ⟨_, P, _, p, _, A, _⟩ := h; DX.of_after P p A

theorem AC.dxt {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) : DXT G f a v :=
  let ⟨s, P, T, p, y, A, sy, _⟩ := h; ⟨s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) : DX a v := h.dxt.dx

theorem AC.r0 {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) :
    (v.gpr .a0 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .a4).toNat < _) = _; rw [p.g .a4 (by decide)]

include hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv in
theorem code_ct {f : Fns} :
    RelCT isa (Two fun a s => (PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15)) ∧ (PubD a s ∧ SymG G a s))
      (decrypt H f) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := AEntT G f)
    (dentry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.1.sp, h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y⟩) ?_
  refine two_seq (Ψ := AP G f) (priv_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _⟩, ⟨s₂, P₂, _, p₂, _, E₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, E₁⟩, ⟨s₂, P₂, p₂, E₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy⟩ => WP.mono_syms (priv_ok P E) fun v A y => ⟨s, P, T, p, g, A, y.trans sy⟩) ?_
  refine two_seq (Ψ := AC G f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.dx) []))
    (fun a v ⟨s, P, T, p, g, A, sy⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
      ⟨s, P, T, p, g, A', y.trans sy, r⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, PreD s ∧ PubD a s ∧ Saves s u) ?_
    fun a v ⟨s, P, T, p, _, A, sy, r⟩ => WP.mono (ite_done hH hG fH fG hHh hHl hHv hGh hGl hGv P T A sy r)
      fun _ d => ⟨s, P, p, d.1⟩)
    (restore_taint fun a u₁ u₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r0, h₂.r0])
    (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.s1, .s2, .s3])) ?_
  refine (decMain_ct hH cH fH hG cG fG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
  rw [eval_nonzero, h₁.r0] at c₁
  have hk : HK H.D a := by simp at c₁; omega
  exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩

end

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) {Hs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
include cH fH hHh hHl hHv

theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (decSpec Hs (tables vs)).pre (decSpec Hs (tables vs)).pub (decrypt H (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T, hT, hh⟩, -⟩ := spec_tabD h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiff⟩ := pubD_of hp
  have hn := Proof.HashTable.RISCV64.mem_names hw
  exact code_ct hH cH fH w.l.ok w.l.ct w.l.fits hHh hHl hHv w.l.hash w.l.len w.l.valid _ _ _ _ _ _
    ⟨s₁, ⟨⟨preD_of h₁, tabS_entryD hc h₁ hw hh⟩, pubD_refl s₁, rfl, rfl, rfl⟩,
      ⟨preD_of h₂, tabS_entryD hc h₂ hw ((hiff _ hT).mp hh)⟩, p, (hsy _ hn.1).symm, (hsy _ hn.2.1).symm,
      (hsy _ hn.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_<H>_mgf1_decrypt` against its contract, for the tables of
`vs`, given a state meeting it. -/
theorem dec_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (decSpec Hs (tables vs)).pre s) :
    Verified RISCV64.target (decrypt H (fnsOf vs)) (decSpec Hs (tables vs)) :=
  ⟨code_correct hH fH hHh hHl hHv hc, code_constantTime hH cH fH hHh hHl hHv hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the table: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp`, and MGF1's
table's address `0x300000`. -/
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
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x1007A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 40⟩, ⟨0x10000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 16) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 16) (e : stackArg decSatState j = v) :
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) j = v :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_dsat j hj)).trans e

theorem dsat_args :
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 0 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 1 = 0x4300 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 2 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 3 = 0x4400 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 4 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 5 = 0x4500 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 6 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 7 = 0x4600 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 8 = 1 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 9 = 0x4700 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 10 = 0 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 11 = 0x4100 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 12 = 64 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 13 = 0x20000 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 14 = 2080 ∧
    stackArg (Proof.HashTable.RISCV64.withTable decSatState vs w) 15 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with MGF1's table that of `w`, at
`0x300000`. -/
theorem dec_sat (H : Spec.Mgf1.Hash) (hw : w ∈ vs) (hl : (Proof.HashTable.RISCV64.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec H (tables vs)).pre s := by
  refine ⟨Proof.HashTable.RISCV64.withTable decSatState vs w, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := dsat_args (vs := vs) (w := w)
  have e : stackArgAddr (Proof.HashTable.RISCV64.withTable decSatState vs w) 0 = 0x10000 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3472 : stackBytes = 3471 + 1 := rfl
  unfold decSpec
  rw [e3472]
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, e]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨Proof.HashTable.RISCV64.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.RISCV64.withTable_held _ _ _⟩
    | exact Proof.HashTable.symsOf_distinct hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.RISCV64.Dec
