module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTLabel
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTPriv
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Written
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSAES-OAEP decryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`Dc/CTBlocks`), the private operation by its constant time
(`priv_ct`), the hash functions' calls by their contracts (`hashLabel_ct`,
MGF1's `mgfXorT_ctS`, with the table at the same address and its functions
at the same addresses: `DXT`), and the branch on the public `k` (`two_ite`); what
each run satisfies between them follows from correctness. The scan's index,
the shift's count and the private operation's result differ between the
runs, but only as data.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep (scan_idx)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .r7).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .r7).toNat; rw [p.g .r7 (by decide)]; exact h

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
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : DXT G f a t' :=
  let ⟨s, m, P, T, p, y, hm, b, sy⟩ := h; ⟨s, m, P, T, p, y, hm, b.only (fitsM P) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 15 SX x (stackArg x 15)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : OkS SX (PreXT G f) (PubXT G) := ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 15 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- `DXT` with the check passed. -/
def DK (G : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G f a t ∧ t.gpr .r24 = off (stackArg a 13) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (stackArg a 13) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a15.trans (p.args 15 (by decide)), y⟩, bX, sy, h24, h25, h26, h27⟩
  rw [a15]
  exact tabS_to P T hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G : Hash} (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 15) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G f src srcLen dst dstLen a t) : WP isa (mgfXorT f 15) t (DXT G f a) := by
  obtain ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  exact WP.mono (mgfXorT_ok (fitsM P) hG (tabS_wm P T hm) hGh hGl hGv hf b sy (h24.trans (off13 p _)) h25
    (h26.trans (off13 p _)) h27) fun _ h' => ⟨s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .r7).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .r7 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_li (by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inr (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE, Nat.zero_add]
  · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, r15, sub_r15 (by omega)]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_li (by omega) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_subi (h := by omega) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega, by omega, .inl (by omega), by omega⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE]
  · rw [o₄.get .r25, o₃.get .r25, e₂]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE, Nat.zero_add]
  · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, r15, sub_r15 (by omega)]

/-- `DX` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G f D a t)
    (hw : ∀ s m, PreD s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G f D a) :=
  let ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below the buffer's size. -/
def DI (G : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DK G f D a t ∧ ∃ idx < 1023, t.gpr .r25 = BitVec.ofNat 64 idx

theorem dk_pins {G : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH cG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G f H.D) ((mgf_anyD hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G f H.D) ((mgf_anyD hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G f H.D) ((hashLabel_ct hH cH).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.dx, h₂.1.dx⟩)
    fun _ _ h => h) (fun a t h => dk_wp h fun s m P _ _ _ b => WP.mono (hashLabel_ok P hH b) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14]))
    (fun a t h => dk_wp h fun s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15]))
    (fun a t ⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .r24)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by unfold kk at *; omega, i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  refine two_seq (Ψ := DI G f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨⟨⟨s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨h, idx, hi, h25⟩ => dk_wp h fun s m P _ _ _ b => WP.mono (shift_ok P b h25 hi) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .r17 = a.gpr .r5)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15, .r16])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r17, -, -⟩ := h.1.dx.pins
    obtain ⟨⟨s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g' .r17 (by simp)).trans r17⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
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
    (v.gpr .r3 != 0) = decide (kk s < 2 * D + 2)

theorem AP.dx {G : Hash} {f : Fns} {a v : State} (h : AP G f a v) : DX a v :=
  let ⟨_, P, _, p, _, A, _⟩ := h; DX.of_after P p A

theorem AC.dxt {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) : DXT G f a v :=
  let ⟨s, P, T, p, y, A, sy, _⟩ := h; ⟨s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) : DX a v := h.dxt.dx

theorem AC.r3 {G : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G f D a v) :
    (v.gpr .r3 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .r7).toNat < _) = _; rw [p.g .r7 (by decide)]

include hH cH hG cG hHh hHl hHv hGh hGl hGv in
theorem code_ct {f : Fns} :
    RelCT isa (Two fun a s => (PreD s ∧ TabS G f 15 (SD s) s (stackArg s 15)) ∧ (PubD a s ∧ SymG G a s))
      (decrypt H f) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.sp.trans h₂.2.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := AEntT G f)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.sp,
      h₂.2.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y⟩) ?_
  refine two_seq (Ψ := AP G f) (priv_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _⟩, ⟨s₂, P₂, _, p₂, _, E₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, E₁⟩, ⟨s₂, P₂, p₂, E₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy⟩ => WP.mono_syms (priv_ok P E) fun v A y => ⟨s, P, T, p, g, A, y.trans sy⟩) ?_
  refine two_seq (Ψ := AC G f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.dx) []))
    (fun a v ⟨s, P, T, p, g, A, sy⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
      ⟨s, P, T, p, g, A', y.trans sy, r⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, PreD s ∧ PubD a s ∧ Saves s u) ?_
    fun a v ⟨s, P, T, p, _, A, sy, r⟩ => WP.mono (ite_done hH hG hHh hHl hHv hGh hGl hGv P T A sy r)
      fun _ d => ⟨s, P, p, d.1⟩)
    (restore_taint fun a u₁ u₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r3, h₂.r3])
    (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.r15, .r16, .r17])) ?_
  refine (decMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
  rw [eval_nonzero, h₁.r3] at c₁
  have hk : HK H.D a := by simp at c₁; omega
  exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩

end

end VG.Proof.RsaOaep.PPC64LE.Dec
