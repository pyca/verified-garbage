module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTPost
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTPub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry

/-!
# RSASSA-PSS verification on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data (`PubK`) leak alike (`code_ct`): the checks'
blocks by the taint analysis and their branches by `two_ite`, on values both
runs compute from the public data (the modulus' first byte, its length and
the salt-length mode and length); the call of
`vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`); and the
rest by `post_ct`, from the states `BL` after the call.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off fx kR Agree Ok B pins_of two_seq HashCT words_entry bytes_entry
  allocated_sp allocated_gpr restore_taint Saves fb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc eval_zero eval_nonzero pdCallCT)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {D : Nat}

/-- An entry state with the anchor's public data, and `Base` from it. -/
theorem pk_pins {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → ∃ s, PreP D s ∧ PubK (an x) s ∧ Base Sp (vP D) s t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of (pssOk D) h rs hrs

theorem call_ct : RelCT isa (Two fun a t => ∃ s, PreP D s ∧ PubK a s ∧ AtCall D s t)
    Impl.RsaPkcs1Sig.PPC64LE.pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁, pdOk_of P₂ c₂,
    ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.base.sp, c₂.base.sp, fb, fb, p₁.1.sp, p₂.1.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, p₁.1.pSp, p₂.1.pSp]
    · rw [c₁.g4, c₂.g4, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.1.args 3 (by decide) (by decide), p₂.1.args 3 (by decide) (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.1.args 4 (by decide) (by decide), p₂.1.args 4 (by decide) (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g8, c₂.g8, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g9, c₂.g9, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g10, c₂.g10, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.1.pSp, p₂.1.pSp]
  · rw [c₁.a1, c₂.a1, p₁.1.args 2 (by decide) (by decide), p₂.1.args 2 (by decide) (by decide)]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_entry c₁.base.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.base.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.1.w, p₂.1.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8,
      bytes_entry c₁.base.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega_arith),
      bytes_entry c₂.base.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega_arith), p₁.1.e, p₂.1.e]

end

/-- The checks passed, for an entry state. -/
structure Ck (D : Nat) (s : State) : Prop where
  h0 : s.mem (s.gpr .r3) ≠ 0
  em : D + 2 ≤ kk s - loN s
  fit : anyL s = 0 → (s.gpr .r10).toNat + 1 ≤ kk s - loN s - D - 1

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)

include hH hGl in
/-- After the call, from an entry state that passed the checks. -/
theorem bl_after {a s t : State} (P : PreP Gs.len s) (p : PubK a s) (c : AfterCall Gs.len s t) (C : Ck Gs.len s) :
    BL Gs.len a t ∧ Fit Gs.len a := by
  have L := lay_reE P hH hGl c.mem C.h0 C.em
  have g := p.1.agree (D := Gs.len) p.2
  have g' : Agree Sp (vP Gs.len) a (reE s t.mem) :=
    ⟨(reE_sp _ _).trans p.1.sp, (reE_Sp P c.mem).trans p.1.pSp, fun r hr => by rw [reE_vP P c.mem]; exact g.v r hr⟩
  refine ⟨⟨reE s t.mem, L.canon, g', c.base⟩, fun ha => ?_⟩
  have hk2 : kk s ≤ 1024 := P.k2
  have e21 : dbLen Gs.len s = dbLen Gs.len a := g.v .r21 (by decide)
  have hdb : (dbLen Gs.len (reE s t.mem)).toNat = kk s - loN s - Gs.len - 1 := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have e : dbLen Gs.len (reE s t.mem) = dbLen Gs.len s := by
    unfold dbLen; rw [lo_reE P c.mem]; rfl
  rw [← e21, ← e, hdb, ← p.1.g .r10 (by decide)]
  exact C.fit (by rw [p.1.pAny]; exact ha)

include hH cH hGh hGl hGv in
theorem main_ct : RelCT isa (Two fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Before Gs.len s t ∧ Ck Gs.len s)
    (verifyMain H) fun _ _ => True := by
  refine two_seq (Ψ := fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ AtCall Gs.len s t ∧ Ck Gs.len s)
    (pubArgs_taint (pk_pins (fun _ _ ⟨s, P, p, B, _⟩ => ⟨s, P, p, B.base⟩) []))
    (fun a t ⟨s, P, p, B, C⟩ => WP.mono (pubArgs_ok P B) fun t' c => ⟨s, P, p, c, C⟩) ?_
  refine two_seq (Ψ := fun a t => BL Gs.len a t ∧ Fit Gs.len a)
    (call_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, c₁, _⟩, ⟨s₂, P₂, p₂, c₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, p, c, C⟩ => WP.mono (call_ok P c) fun t' c' => bl_after hH hGl P p c' C) ?_
  exact post_ct hH cH hGl.symm hGh hGl hGv

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (a t : State) : Prop := ∃ s, PreP D s ∧ PubK a s ∧ Entered D s t

include hH cH hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En Gs.len)) (checks H) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Gs.len a t) → Pins Φ [] := fun h =>
    pk_pins (an := id) (fun a t hp => let ⟨s, P, p, E⟩ := h a t hp; ⟨s, P, p, E.base⟩) []
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁⟩ ⟨s₂, _, p₂, E₂⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, p₁.1.pN0 p₁.2, p₂.1.pN0 p₂.2])
    (fail_taint (pin fun _ _ h => h.1)) ?_
  let E1 := fun (a t : State) => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Entered Gs.len s t ∧ s.mem (s.gpr .r3) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2))
    (chkEm_taint H (pin fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, E⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono (chkEm_ok P hGl hD64 E h0) fun t' ⟨E', r3⟩ =>
      ⟨⟨s, P, p, E', h0⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩)) ?_
  let E2 := fun (a t : State) => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Entered Gs.len s t ∧ s.mem (s.gpr .r3) ≠ 0 ∧
    Gs.len + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Gs.len + 2 := by simpa using hc
    exact ⟨s, P, p, E, h0, by rw [p.1.pKk, p.1.pLoN p.2]; omega_arith⟩
  -- The salt length expected.
  let E3 := fun (a t : State) => E2 a t ∧ t.gpr .r4 = if anyL a = 0 then a.gpr .r10 else 0
  refine two_seq (Ψ := E3) (expLen_taint (pk_pins (an := id) (fun a t hp =>
      let ⟨s, P, p, E, _⟩ := e2 hp; ⟨s, P, p, E.base⟩) [.r20]))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, h0, hem⟩ := e2 h
    exact WP.mono (expLen_ok E.base.pany E.base.psl) fun t' ⟨o, e⟩ =>
      ⟨⟨s, P, p, E.only P o, h0, hem⟩, by rw [e, p.1.pAny, p.1.g .r10 (by decide)]⟩
  refine two_seq (Ψ := fun a t => E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .r10 else 0).toNat))
    (chkSalt_taint H (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1; ⟨s, P, p, E⟩))
    (fun a t ⟨⟨s, P, p, E, h0, hem⟩, h4⟩ => WP.mono (chkSalt_ok P hGl hD64 E h0 hem
      (by rw [h4, p.1.pAny, p.1.g .r10 (by decide)])) fun t' ⟨E', r3⟩ =>
        ⟨⟨s, P, p, E', h0, hem⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2, p.1.pAny, p.1.g .r10 (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩)) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .r10 else 0).toNat)) ∧
      isa.eval (.nonzero .d .r3) t = some false →
      ∃ s, PreP Gs.len s ∧ PubK a s ∧ Before Gs.len s t ∧ Ck Gs.len s := fun {a t} ⟨⟨⟨s, P, p, E, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .r10 else 0).toNat := by simpa using hc
    refine ⟨s, P, p, E.before, h0, hem, fun ha => ?_⟩
    rw [← p.1.pAny, ifp ha, ← p.1.g .r10 (by decide), ← p.1.pKk, ← p.1.pLoN p.2] at hn
    omega_arith
  exact (main_ct hH cH hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

include hH cH hGh hGl hGv in
/-- Two runs of `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` from entry states
with the same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreP Gs.len s ∧ PubK a s) (verifyPrecomputed H) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.sp.trans h₂.2.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := En Gs.len)
    (entry_taint H fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.sp,
      h₂.2.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂, allocated_gpr, allocated_gpr, h₁.2.1.g .r3 (by decide),
          h₂.2.1.g .r3 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P hGl.symm hD64) fun t E => ⟨s, P, p, E⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Saves s t)
    (checks_ct hH cH hGh hGl hGv) fun a t ⟨s, P, p, E⟩ =>
      WP.mono (checks_done P hH hGh hGl hGv E) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.PPC64LE
