module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTHash
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Post
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix

/-!
# RSASSA-PSS verification on PPC64LE: constant time after the public operation

Untrusted: everything here is checked by Lean. Two runs from states with
`BL` for the same anchor, whose salt length fits if one is given (`Fit`),
leak alike (`post_ct`): the blocks and call-free loops by the taint analysis
(`CTBlocks`), MGF1 through its table by `mgfXorT_ct`, the hashing of `M'`
through the hash function's table by `hashFixed_ct` and `ctHash_ct`, and the branches on the salt-length mode by `two_ite`, which
`r20` holds for both; between them each run keeps `BL` by correctness.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa mgfXorT)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (compressK)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off view fx Agree Ok B two_seq HashCT hfits offs MFit MgfAT mgfXorT_ct
  mgfXorT_ok)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep Two Pins two_post two_ite eval_zero)

/-- The salt length given fits in `DB`. -/
abbrev Fit (D : Nat) (a : State) : Prop := anyL a = 0 → (stackArg a 0).toNat + 1 ≤ (dbLen D a).toNat

/-- MGF1's arguments for unmasking `DB`, from the anchor. -/
abbrev qM (D : Nat) (a : State) : Nat × Nat × Nat × Nat :=
  ((lo a).toNat + (dbLen D a).toNat, D, (lo a).toNat, (dbLen D a).toNat)

section
variable {D : Nat} {Z : Tabs}

theorem acc0_wp {a t : State} (h : BL D Z a t) : WP isa (.block acc0) t (BL D Z a) := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.of_syms (WP.mono (acc0_ok (agree_lay P g) b) fun t' ⟨b', _⟩ y => ⟨s, P, g, b', y.trans sy⟩)

theorem qM_fit {a t : State} (h : BL D Z a t) :
    MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 := by
  have := h.dn
  show MFit ((lo a).toNat + (dbLen D a).toNat) D (lo a).toNat (dbLen D a).toNat
  exact ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩

/-- MGF1's arguments, from the anchor. -/
abbrev MgfL (D : Nat) (Z : Tabs) (a t : State) : Prop :=
  MgfAT Sp (vP D) (PreL D Z) (PubL D Z) (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 a t

theorem dbArgs_wp {H : Hash} (hD : H.D = D) {a t : State} (h : BL D Z a t) :
    WP isa (.block (dbArgs H)) t (MgfL D Z a) := by
  obtain ⟨s, P, g, b, sy⟩ := h
  have hS : Sp s = Sp a := g.1.S
  exact WP.of_syms (WP.mono (dbArgs_ok (agree_lay P g) hD b) fun t' ⟨b', _, x24, x25, x26, x27⟩ y =>
    ⟨s, P, g, b', y.trans sy, by rw [x24, hS], x25, by rw [x26, hS], x27⟩)

section
variable (hG : HashOK Z.G) (cG : HashCT hG) {Gm : Spec.Mgf1.Hash} (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x)
  (hGml : Gm.len = Z.G.D) (hGmv : Proof.Mgf1.Valid Gm)

include cG hGmh hGml hGmv in
theorem mgf_two : RelCT isa (Two fun a t => MgfL D Z a t ∧
      MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2) (mgfXorT Z.g gArg) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT Sp (vP D) (PreL D Z) (PubL D Z) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (lOk D Z) hG cG x.2 hGmh hGml hGmv (tabG D Z)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qM D a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include hGmh hGml hGmv in
theorem mgf_wp {a t : State} (h : MgfL D Z a t) : WP isa (mgfXorT Z.g gArg) t (BL D Z a) := by
  obtain ⟨s, P, g, b, sy, h24, h25, h26, h27⟩ := h
  have hS : Sp s = Sp a := g.1.S
  exact WP.mono (mgfXorT_ok P.1.F hG ((tabG D Z).tab P) hGmh hGml hGmv (qM_fit ⟨s, P, g, b, sy⟩) b sy
    (by rw [h24, hS]) h25 (by rw [h26, hS]) h27) fun t' ⟨⟨b', _⟩, y'⟩ => ⟨s, P, g, b', y'⟩

end

theorem clearTop_wp {a t : State} (h : BL D Z a t) : WP isa (.block clearTop) t (BL D Z a) := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.of_syms (WP.mono (clearTop_ok (agree_lay P g) b) fun t' ⟨b', _⟩ y => ⟨s, P, g, b', y.trans sy⟩)

/-- Some position in `DB` in `r8`. -/
abbrev Pos8 (D : Nat) (a t : State) : Prop := ∃ pos < (dbLen D a).toNat, t.gpr .r8 = BitVec.ofNat 64 pos

theorem scan_wp {a t : State} (h : BL D Z a t) : WP isa scan t fun t' => BL D Z a t' ∧ Pos8 D a t' := by
  obtain ⟨s, P, g, b, sy⟩ := h
  have L := agree_lay P g
  have hd1 := L.d1
  exact WP.of_syms (WP.mono (scan_ok L b (w := fun j => view t.mem (Sp s) ((lo a).toNat + j)) fun _ _ => rfl)
    fun t' ⟨b', _, _, x8, _⟩ y => ⟨⟨s, P, g, b', y.trans sy⟩, _, by split <;> omega_arith, x8⟩)

/-- Some position in `DB` in `r8`, and the length of the salt after it in `r25`. -/
abbrev Pos25 (D : Nat) (a t : State) : Prop :=
  ∃ pos < (dbLen D a).toNat, t.gpr .r8 = BitVec.ofNat 64 pos ∧
    t.gpr .r25 = BitVec.ofNat 64 ((dbLen D a).toNat - pos - 1)

theorem posCheck_wp {a t : State} (h : BL D Z a t) (hp : Pos8 D a t) :
    WP isa (.block posCheck) t fun t' => BL D Z a t' ∧ Pos25 D a t' := by
  obtain ⟨s, P, g, b, sy⟩ := h
  obtain ⟨pos, hp, x8⟩ := hp
  exact WP.of_syms (WP.mono (posCheck_ok (agree_lay P g) b rfl x8 hp rfl) fun t' ⟨b', o', _, x25⟩ y =>
    ⟨⟨s, P, g, b', y.trans sy⟩, pos, hp, by rw [o'.get .r8, x8], x25⟩)

theorem lenCheck_wp {a t : State} (h : BL D Z a t) (hp : Pos25 D a t) :
    WP isa lenCheck t fun t' => BL D Z a t' ∧ Pos25 D a t' := by
  obtain ⟨s, P, g, b, sy⟩ := h
  obtain ⟨pos, hp, x8, x25⟩ := hp
  exact WP.of_syms (WP.mono (lenCheck_ok (agree_lay P g) b rfl x25) fun t' ⟨b', o', _⟩ y =>
    ⟨⟨s, P, g, b', y.trans sy⟩, pos, hp, by rw [o'.get .r8, x8], by rw [o'.get .r25, x25]⟩)

theorem prefix_wp {H : Hash} (hD : H.D = D) {n : Nat} (hn : 8 ≤ n) (hn' : n ≤ 2048) {a t : State} (h : BL D Z a t) :
    WP isa (mPrefix H n) t fun t' => BL D Z a t' ∧ ∀ r ∈ kpR, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.mono_syms (prefix_ok (agree_lay P g) hD hn hn' b) fun t' ⟨b', g', _⟩ y =>
    ⟨⟨s, P, g, b', y.trans sy⟩, g'⟩

theorem r10_agree {a s : State} (g : PubL D Z a s) : stackArg s 0 = stackArg a 0 := g.1.v .r19 (by decide)

theorem salt_wp {H : Hash} (hD : H.D = D) {a t : State} (h : BL D Z a t)
    (hsl : (stackArg a 0).toNat + 1 ≤ (dbLen D a).toNat) : WP isa (copySalt H) t (BL D Z a) := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.of_syms (WP.mono (salt_ok (agree_lay P g) hD b (by rw [r10_agree g]; exact hsl)) fun t' ⟨b', _⟩ y =>
    ⟨s, P, g, b', y.trans sy⟩)

theorem hashFixed_wp (hH : HashOK Z.H) (hD : Z.H.D = D) {a t : State} (h : BL D Z a t)
    (hsl : (stackArg a 0).toNat + 8 + D ≤ 2048) : WP isa (hashFixed Z.H Z.f hArg) t (BL D Z a) := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.mono (hashFixed_ok P.1.F hH ((tabH D Z).tab P) hD b sy (by rw [r10_agree g]; exact hsl))
    fun t' ⟨⟨b', _⟩, y'⟩ => ⟨s, P, g, b', y'⟩

theorem copyDb_wp {H : Hash} (hD : H.D = D) {a t : State} (h : BL D Z a t) :
    WP isa (copyDb H) t fun t' => BL D Z a t' ∧ ∀ r ∈ kpR, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, g, b, sy⟩ := h
  exact WP.mono_syms (copyDb_ok (agree_lay P g) hD b) fun t' ⟨b', g', _⟩ y => ⟨⟨s, P, g, b', y.trans sy⟩, g'⟩

theorem shift_wp {H : Hash} (hD : H.D = D) {a t : State} (h : BL D Z a t) (hp : Pos8 D a t) :
    WP isa (shift H) t fun t' => BL D Z a t' ∧ t'.gpr .r25 = t.gpr .r25 := by
  obtain ⟨s, P, g, b, sy⟩ := h
  obtain ⟨pos, hp, x8⟩ := hp
  exact WP.mono_syms (shift_ok (agree_lay P g) hD b x8 hp) fun t' ⟨b', k', _⟩ y =>
    ⟨⟨s, P, g, b', y.trans sy⟩, k'.gpr .r25 (by decide)⟩

theorem Pos25.keep {a t t' : State} (h : Pos25 D a t) (g : ∀ r ∈ kpR, t'.gpr r = t.gpr r) : Pos25 D a t' := by
  obtain ⟨pos, hp, x8, x25⟩ := h
  exact ⟨pos, hp, by rw [g .r8 (by decide), x8], by rw [g .r25 (by decide), x25]⟩

variable (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) (hG : HashOK Z.G) (cG : HashCT hG)
  {Gm : Spec.Mgf1.Hash} (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = Z.G.D)
  (hGmv : Proof.Mgf1.Valid Gm) {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md Z.cc Z.dc) (ct : CtTaint P)
  (hcc : ConstantTime isa (compressK md).pre (compressK md).pub Z.cc)
  (hdc : ConstantTime isa (digestK md).pre (digestK md).pub Z.dc)

include hH cH hD hG cG hGmh hGml hGmv ok ct hcc hdc in
/-- The code after the public operation, in both runs. -/
theorem post_ct : RelCT isa (Two fun a t => BL D Z a t ∧ Fit D a)
    (.seq (.block acc0) (.seq (.block (dbArgs Z.H)) (.seq (mgfXorT Z.g gArg) (.seq (.block clearTop) (.seq scan
      (.seq (.block posCheck) (.seq lenCheck (finish Z.H P Z.f)))))))) fun _ _ => True := by
  let P0 := fun (a t : State) => BL D Z a t ∧ Fit D a
  refine two_seq (Ψ := P0) (acc0_taint (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r15, .r17]))
    (fun a t h => WP.mono (acc0_wp h.1) fun t' b => ⟨b, h.2⟩) ?_
  refine two_seq (Ψ := fun a t => (MgfL D Z a t ∧ MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2) ∧
      Fit D a)
    (dbArgs_taint Z.H (bl_pins (an := id) (fun _ _ h => h.1) []))
    (fun a t h => WP.mono (dbArgs_wp hD h.1) fun t' m => ⟨⟨m, qM_fit h.1⟩, h.2⟩) ?_
  refine two_seq (Ψ := P0) ((mgf_two hG cG hGmh hGml hGmv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
      fun _ _ h => h)
    (fun a t h => WP.mono (mgf_wp hG hGmh hGml hGmv h.1.1) fun t' b => ⟨b, h.2⟩) ?_
  refine two_seq (Ψ := P0) (clearTop_taint (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r17]))
    (fun a t h => WP.mono (clearTop_wp h.1) fun t' b => ⟨b, h.2⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos8 D a t)
    (scan_taint (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r17, .r21]))
    (fun a t h => WP.mono (scan_wp h.1) fun t' ⟨b, p⟩ => ⟨⟨b, h.2⟩, p⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos25 D a t)
    (posCheck_taint (bl_pins (an := id) (fun _ _ h => h.1.1) [.r14, .r15]))
    (fun a t h => WP.mono (posCheck_wp h.1.1 h.2) fun t' ⟨b, p⟩ => ⟨⟨b, h.1.2⟩, p⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos25 D a t)
    (lenCheck_taint (bl_pins (an := id) (fun _ _ h => h.1.1) [.r20]))
    (fun a t h => WP.mono (lenCheck_wp h.1.1 h.2) fun t' ⟨b, p⟩ => ⟨⟨b, h.1.2⟩, p⟩) ?_
  -- The salt's hash, by the salt-length mode.
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.1.v (r := .r20), h₂.1.1.v (r := .r20)])
    ?_ ?_
  · have ha : ∀ {a t : State}, (P0 a t ∧ Pos25 D a t) ∧ isa.eval (.zero .d .r20) t = some true → anyL a = 0 :=
      fun ⟨h, e⟩ => by rw [eval_zero, h.1.1.v (r := .r20)] at e; exact beq_iff_eq.mp (Option.some.inj e)
    let F0 := fun (a t : State) => BL D Z a t ∧ (stackArg a 0).toNat + 1 ≤ (dbLen D a).toNat
    refine two_seq (Ψ := F0) (mPrefix_taint Z.H 8 (bl_pins (an := id) (fun _ _ h => h.1.1.1) [.r14, .r16]))
      (fun a t h => WP.mono (prefix_wp hD (by decide) (by decide) h.1.1.1) fun t' ⟨b, _⟩ =>
        ⟨b, h.1.1.2 (ha h)⟩) ?_
    refine two_seq (Ψ := F0) (copySalt_taint Z.H (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r17, .r19, .r21]))
      (fun a t h => WP.mono (salt_wp hD h.1 h.2) fun t' b => ⟨b, h.2⟩) ?_
    have hb : ∀ {a t : State}, F0 a t → (stackArg a 0).toNat + 8 + D ≤ 2048 := fun h => by
      have := h.1.dn; have := h.2; omega_arith
    refine two_seq (Ψ := BL D Z) ((hashFixed_ct hH cH hD).mono (fun _ _ ⟨a, h₁, h₂⟩ =>
        ⟨a, ⟨h₁.1, hb h₁⟩, ⟨h₂.1, hb h₂⟩⟩) fun _ _ h => h)
      (fun a t h => hashFixed_wp hH hD h.1 (hb h)) ?_
    exact cmpH_taint Z.H oDig (bl_pins (an := id) (fun _ _ h => h) [.r14, .r17, .r21])
  · let A0 := fun (a t : State) => BL D Z a t ∧ Pos25 D a t
    refine two_seq (Ψ := A0) (mPrefix_taint Z.H 2048 (bl_pins (an := id) (fun _ _ h => h.1.1.1) [.r14, .r16]))
      (fun a t h => WP.mono (prefix_wp hD (by decide) (by decide) h.1.1.1) fun t' ⟨b, g⟩ =>
        ⟨b, h.1.2.keep g⟩) ?_
    refine two_seq (Ψ := A0) (copyDb_taint Z.H (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r17, .r21]))
      (fun a t h => WP.mono (copyDb_wp hD h.1) fun t' ⟨b, g⟩ => ⟨b, h.2.keep g⟩) ?_
    let A1 := fun (a t : State) => BL D Z a t ∧ ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl
    refine two_seq (Ψ := A1) (shift_taint Z.H (bl_pins (an := id) (fun _ _ h => h.1) [.r14, .r21]))
      (fun a t h => ?_) ?_
    · obtain ⟨pos, hp, x8, x25⟩ := h.2
      exact WP.mono (shift_wp hD h.1 ⟨pos, hp, x8⟩) fun t' ⟨b, g⟩ =>
        ⟨b, (dbLen D a).toNat - pos - 1, by omega_arith, by rw [g, x25]⟩
    refine two_seq (Ψ := BL D Z) (ctHash_ct hH cH hD ok ct hcc hdc)
      (fun a t h => ctHash_wp hH hD ok h.1 h.2) ?_
    exact cmpH_taint Z.H oDig (bl_pins (an := id) (fun _ _ h => h) [.r14, .r17, .r21])

end

end VG.Proof.RsaPss.PPC64LE
