module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: hashing `M'`, twice

Untrusted: everything here is checked by Lean. After the public operation,
two runs are compared through the anchor `a` with `BL`: `Base` from entry
states whose encoding parameters are those of their registers (`PreL`) and
that agree with the anchor on what `Base` fixes. `hashFixed_ct`: the hash of
`M'` for a given salt length, its blocks by the taint analysis and its calls
by `init_two`, `upd_ct` and `fin_ct`, with arguments from the anchor;
`hashAny_ct`: for any salt length, the loop over the lengths (`round_two`),
whose counters both runs agree on.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off fx hiRegs Agree Ok B B.agree B.only pins_of st_wp
  init_two init_wp two_seq UpdArgs FinArgs upd_ct fin_ct HashCT upd_ok fin_ok sdis sc_cov cR_dis hfits offs
  st_taint)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-- An entry state whose encoding parameters are those of its registers. -/
abbrev PreL (D : Nat) (s : State) : Prop := Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8)

theorem Lay.canon {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) : PreL D s := by
  have h1 : (lo s).toNat = lN := by rw [L.hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.l1; omega_arith)]
  have h2 : (dbLen D s).toNat = dN := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hk; have := L.k2; omega_arith)]
  have h3 : (cm s).setWidth 8 = c := by rw [L.hc, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  show Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8)
  rw [h1, h2, h3]; exact L

theorem lOk (D : Nat) : Ok Sp (vP D) (PreL D) (Agree Sp (vP D)) := ⟨fun P => P.F, id⟩

/-- `Base` from such an entry state agreeing with the anchor. -/
abbrev BL (D : Nat) : State → State → Prop := B Sp (vP D) (PreL D) (Agree Sp (vP D))

section
variable {D : Nat}

theorem BL.r14 {a t : State} (h : BL D a t) : t.gpr .r14 = Sp a := ((h.agree (lOk D)).2.1)
theorem BL.v {a t : State} (h : BL D a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.agree (lOk D)).2.2 r hr
theorem BL.only' {a t t' : State} {rs : List Reg} (h : BL D a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : BL D a t' := h.only (lOk D) o hrs

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs := pins_of (lOk D) h rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D s) (g : Agree Sp (vP D) a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm a).setWidth 8) := by
  have e17 : lo s = lo a := g.v .r17 (by decide)
  have e18 : cm s = cm a := g.v .r18 (by decide)
  have e21 : dbLen D s = dbLen D a := g.v .r21 (by decide)
  rw [← e17, ← e18, ← e21]; exact P

theorem BL.lay {a t : State} (h : BL D a t) :
    ∃ s, Lay D s (lo a).toNat (dbLen D a).toNat ((cm a).setWidth 8) ∧ Base Sp (vP D) s t :=
  let ⟨s, P, g, b⟩ := h; ⟨s, agree_lay P g, b⟩

theorem BL.dn {a t : State} (h : BL D a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, L, -⟩ := h.lay
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega_arith, L.D0, L.D64⟩

end

section
variable {D : Nat} {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hD : H.D = D)

include hH cH in
/-- `update` from states agreeing on its arguments, in both runs. -/
theorem upd_two {α : Type} {Φ : α → State → Prop} {an : α → State} {o : α → Nat} {len : α → Nat}
    (h : ∀ x t, Φ x t → BL D (an x) t ∧ oW + 1024 ≤ o x ∧ o x + len x ≤ oRsa ∧
      t.gpr .r3 = off (Sp (an x)) oSt ∧ t.gpr .r5 = off (Sp (an x)) (o x) ∧ (t.gpr .r6).toNat = len x ∧
      t.gpr .r7 = off (Sp (an x)) oW)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .r4 = t₂.gpr .r4) :
    RelCT isa (Two Φ) H.callUpd fun _ _ => True :=
  upd_twoG (lOk D) hH cH h hr

include cH in
/-- `finalize` from states agreeing on its arguments, in both runs. -/
theorem fin_two {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → BL D (an x) t ∧ t.gpr .r3 = off (Sp (an x)) oSt ∧ t.gpr .r5 = off (Sp (an x)) oDig ∧
      t.gpr .r6 = off (Sp (an x)) oW)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .r4 = t₂.gpr .r4) :
    RelCT isa (Two Φ) H.callFin fun _ _ => True :=
  fin_twoG (lOk D) hH cH h hr

include hH in
/-- `init` keeps `BL` and the callee-saved registers. -/
theorem init_wp' {a t : State} (h : BL D a t) (h3 : t.gpr .r3 = off (Sp a) oSt) :
    WP isa H.callInit t fun t' => BL D a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (VG.Proof.RsaOaep.PPC64LE.init_ok P.F hH b (by rw [h3, g.S])) fun t' ⟨b', g', _⟩ =>
    ⟨⟨s, P, g, b'⟩, g'⟩

include hH in
/-- `update` keeps `BL` and the callee-saved registers. -/
theorem upd_wp {a t : State} (h : BL D a t) {o len : Nat} (ho : oW + 1024 ≤ o) (hl : o + len ≤ oRsa)
    (h3 : t.gpr .r3 = off (Sp a) oSt) (h5 : t.gpr .r5 = off (Sp a) o) (h6 : (t.gpr .r6).toNat = len)
    (h7 : t.gpr .r7 = off (Sp a) oW) :
    WP isa H.callUpd t fun t' => BL D a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r :=
  upd_wpG (lOk D) hH h ho hl h3 h5 h6 h7

include hH in
/-- `finalize` keeps `BL` and the callee-saved registers. -/
theorem fin_wp {a t : State} (h : BL D a t) (h3 : t.gpr .r3 = off (Sp a) oSt) (h5 : t.gpr .r5 = off (Sp a) oDig)
    (h6 : t.gpr .r6 = off (Sp a) oW) :
    WP isa H.callFin t fun t' => BL D a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, g, A⟩ := fin_argsG (lOk D) h h3 h5 h6
  exact WP.mono (fin_ok A.P hH A.b A.h3 A.h5 A.h6) fun t' ⟨b', g', _⟩ => ⟨⟨s, P, g, b'⟩, g'⟩

include hH cH hD in
/-- `H' = Hash(M')` for a given salt length, in both runs. -/
theorem hashFixed_ct :
    RelCT isa (Two fun a t => BL D a t ∧ (a.gpr .r10).toNat + 8 + D ≤ 2048) (hashFixed H) fun _ _ => True :=
  hashFixedG_ct (lOk D) hH cH hD (fun a => (a.gpr .r10).toNat) fun a => by
    show a.gpr .r10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- In the loop over the lengths, for the length `L`: `BL`, the counters and
some salt length in `r25`. -/
def LoopR (D : Nat) (ac : State × Nat) (u : State) : Prop :=
  BL D ac.1 u ∧ (∃ sl, u.gpr .r25 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .r26 = BitVec.ofNat 64 ac.2 ∧
    u.gpr .r27 = BitVec.ofNat 64 ((dbLen D ac.1).toNat - ac.2) ∧ ac.2 < (dbLen D ac.1).toNat

theorem LoopR.keep {ac : State × Nat} {u u' : State} (h : LoopR D ac u) (hb : BL D ac.1 u')
    (hg : ∀ r ∈ [Reg.r25, .r26, .r27], u'.gpr r = u.gpr r) : LoopR D ac u' := by
  obtain ⟨-, ⟨sl, x25, hs⟩, x26, x27, hL⟩ := h
  exact ⟨hb, ⟨sl, by rw [hg .r25 (by decide), x25], hs⟩, by rw [hg .r26 (by decide), x26],
    by rw [hg .r27 (by decide), x27], hL⟩

theorem pres_three {u u' : State} (h : ∀ r ∈ preserved, u'.gpr r = u.gpr r) :
    ∀ r ∈ [Reg.r25, .r26, .r27], u'.gpr r = u.gpr r := fun r hr => h r (by revert r; decide)

include hH in
theorem copyN_wp {ac : State × Nat} {u : State} (h : LoopR D ac u) {a b : Nat}
    (hab : a = oSt ∧ b = oBk ∨ a = oBk ∧ b = oSt) :
    WP isa (copyN a b H.S) u (LoopR D ac) := by
  have F := hfits hH
  obtain ⟨_, hSt, _, _, _, hR⟩ := offs
  have hB : oBk = 4608 := rfl
  have hS1 : 0 < H.S := by have := hH.dims.N; simp only [Hash.S]; omega_arith
  obtain ⟨s, P, g, b'⟩ := h.1
  have L := agree_lay P g
  have k : ∀ {u' : State}, Base Sp (vP D) s u' → Keep [.r4, .r5, .r6, .r7] u u' → LoopR D ac u' := fun b'' k =>
    h.keep ⟨s, P, g, b''⟩ fun r hr => k.gpr r (by revert r; decide)
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact WP.mono (copyN_ok L b' (a := oSt) (b := oBk) (n := H.S) hS1 (by omega_arith) (by omega_arith) (by omega_arith)
      (.inl (by omega_arith)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => k b'' k'
  · exact WP.mono (copyN_ok L b' (a := oBk) (b := oSt) (n := H.S) hS1 (by omega_arith) (by omega_arith) (by omega_arith)
      (.inr (by omega_arith)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => k b'' k'

/-- The loop's invariant, with the lengths left. -/
abbrev LoopN (D n : Nat) (ac : State × Nat) (u : State) : Prop := LoopR D ac u ∧ n = (dbLen D ac.1).toNat - ac.2

include hH cH hD in
/-- A round of the loop over the lengths, in both runs; both agree on whether
another follows. -/
theorem round_two (n : Nat) :
    RelCT isa (Two (LoopN D n)) (lenRound H) fun u₁ u₂ =>
      isa.eval (.nonzero .d .r27) u₁ = isa.eval (.nonzero .d .r27) u₂ ∧
      (isa.eval (.nonzero .d .r27) u₁ = some false → True) ∧
      (isa.eval (.nonzero .d .r27) u₁ = some true → ∃ m < n, Two (LoopN D m) u₁ u₂) := by
  subst hD
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2560 := rfl
  have pin0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR H.D ac u) → Pins Φ [] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) []
  have pin14 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR H.D ac u) → Pins Φ [.r14] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) [.r14]
  -- The state to `oBk`.
  refine two_seq (Ψ := LoopN H.D n) (copyN_taint oSt oBk H.S (pin14 fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp hH h (.inl ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `finalize` after `8 + hLen + L` bytes.
  let A4 := fun (ac : State × Nat) (u : State) => LoopN H.D n ac u ∧
    u.gpr .r4 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := A4) (lr1_taint H (pin0 fun _ _ h => h.1)) (fun ac u h => wp_addi (h := by omega_arith)
    fun u' o e => wp_nil ⟨⟨h.1.keep (h.1.1.only' o) fun r hr => o.gpr r (by revert r; decide), h.2⟩,
      by rw [e, h.1.2.2.1]⟩) ?_
  let A3 := fun (ac : State × Nat) (u : State) => A4 ac u ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧
    u.gpr .r5 = off (Sp ac.1) oDig ∧ u.gpr .r6 = off (Sp ac.1) oW
  have w3 : ∀ ac u, A4 ac u →
      WP isa (.block [.addi .r3 .r14 oSt, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) u (A3 ac) := fun ac u h =>
    WP.mono (finRegs_wpG (lOk _) h.1.1.1) fun u' ⟨b', o', x3, x5, x6⟩ =>
      ⟨⟨⟨h.1.1.keep b' (fun r hr => o'.gpr r (by revert r; decide)), h.1.2⟩, by rw [o'.get .r4, h.2]⟩, x3, x5, x6⟩
  refine two_seq (Ψ := LoopN H.D n) (two_seq (Ψ := A3) (finRegs_taint (pin0 fun _ _ h => h.1.1)) w3
      (fin_two hH cH (an := Prod.fst) (fun ac u h => ⟨h.1.1.1.1, h.2.1, h.2.2.1, h.2.2.2⟩)
        (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.1.2, h₂.1.2])))
    (fun ac u h => WP.seq (WP.mono (w3 ac u h) fun u' h' => WP.mono (fin_wp hH h'.1.1.1.1 h'.2.1 h'.2.2.1 h'.2.2.2)
      fun u'' ⟨b'', g''⟩ => ⟨h'.1.1.1.keep b'' (pres_three g''), h'.1.1.2⟩)) ?_
  -- The selection.
  refine two_seq (Ψ := LoopN H.D n) (select_taint H (pin14 fun _ _ h => h.1)) (fun ac u ⟨h, hn⟩ => ?_) ?_
  · obtain ⟨s, P, g, b⟩ := h.1
    obtain ⟨sl, x25, hs⟩ := h.2.1
    have hb := h.1.dn
    exact WP.mono (select_ok (agree_lay P g) rfl b h.2.2.1 x25 (by have := h.2.2.2.2; omega_arith) hs)
      fun u' ⟨b', k', _⟩ => ⟨h.keep ⟨s, P, g, b'⟩ fun r hr => k'.gpr r (by revert r; decide), hn⟩
  -- The state back.
  refine two_seq (Ψ := LoopN H.D n) (copyN_taint oBk oSt H.S (pin14 fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp hH h (.inr ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `update` with the next byte.
  let A6 := fun (ac : State × Nat) (u : State) => LoopN H.D n ac u ∧
    u.gpr .r4 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + H.D) ∧
    u.gpr .r5 = off (Sp ac.1) (oY + 8 + H.D + ac.2) ∧ u.gpr .r6 = BitVec.ofNat 64 1
  refine two_seq (Ψ := A6) (lr2_taint H (pin0 fun _ _ h => h.1)) (fun ac u h => ?_) ?_
  · refine wp_addi (h := by omega_arith) fun u₁ o₁ e₁ => wp_addi (h := by omega_arith) fun u₂ o₂ e₂ => wp_add fun u₃ o₃ e₃ =>
      wp_li (by decide) fun u₄ o₄ e₄ => wp_nil ?_
    have k₄ : Only [.r4, .r5, .r6] u u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    refine ⟨⟨h.1.keep (h.1.1.only' k₄) fun r hr => k₄.gpr r (by revert r; decide), h.2⟩, ?_, ?_, e₄⟩
    · rw [o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.1.2.2.1]
    · rw [o₄.get .r5, e₃, e₂, o₂.get .r26, o₁.get .r26, o₁.get .r14, h.1.1.r14, h.1.2.2.1]; exact off_off _ _ _
  let A7 := fun (ac : State × Nat) (u : State) => A6 ac u ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧
    u.gpr .r7 = off (Sp ac.1) oW
  have w7 : ∀ ac u, A6 ac u → WP isa (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW]) u (A7 ac) := fun ac u h =>
    WP.mono (updRegs_wpG (lOk _) h.1.1.1) fun u' ⟨b', o', x3, x7⟩ =>
      ⟨⟨⟨h.1.1.keep b' (fun r hr => o'.gpr r (by revert r; decide)), h.1.2⟩, by rw [o'.get .r4, h.2.1],
        by rw [o'.get .r5, h.2.2.1], by rw [o'.get .r6, h.2.2.2]⟩, x3, x7⟩
  have h6 : ∀ {ac : State × Nat} {u : State}, A7 ac u → (u.gpr .r6).toNat = 1 := fun h => by rw [h.1.2.2.2]; rfl
  have hb7 : ∀ {ac : State × Nat} {u : State}, A7 ac u → oY + 8 + H.D + ac.2 + 1 ≤ oRsa := fun h => by
    have := h.1.1.1.2.2.2.2; have := h.1.1.1.1.dn; omega_arith
  refine two_seq (Ψ := LoopN H.D n) (two_seq (Ψ := A7) (updRegs_taint (pin0 fun _ _ h => h.1.1)) w7
      (upd_two hH cH (an := Prod.fst) (o := fun ac => oY + 8 + H.D + ac.2) (len := fun _ => 1)
        (fun ac u h => ⟨h.1.1.1.1, by omega_arith, hb7 h, h.2.1, h.1.2.2.1, h6 h, h.2.2⟩)
        (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.1.2.1, h₂.1.2.1])))
    (fun ac u h => WP.seq (WP.mono (w7 ac u h) fun u' h' => WP.mono (upd_wp hH h'.1.1.1.1
      (o := oY + 8 + H.D + ac.2) (len := 1) (by omega_arith) (hb7 h') h'.2.1 h'.1.2.2.1 (h6 h') h'.2.2)
      fun u'' ⟨b'', g''⟩ => ⟨h'.1.1.1.keep b'' (pres_three g''), h'.1.1.2⟩)) ?_
  -- The counters.
  let Po := fun (ac : State × Nat) (u : State) => BL H.D ac.1 u ∧
    (∃ sl, u.gpr .r25 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .r26 = BitVec.ofNat 64 (ac.2 + 1) ∧
    u.gpr .r27 = BitVec.ofNat 64 ((dbLen H.D ac.1).toNat - ac.2 - 1) ∧ ac.2 < (dbLen H.D ac.1).toNat ∧
    n = (dbLen H.D ac.1).toNat - ac.2
  have w8 : ∀ ac u, LoopN H.D n ac u → WP isa (.block [.addi .r26 .r26 1, .subi .r27 .r27 1]) u (Po ac) := by
    intro ac u h
    refine wp_addi (h := by decide) fun u₁ o₁ e₁ => wp_subi fun u₂ o₂ e₂ =>
      wp_nil ⟨(h.1.1.only' o₁).only' o₂, ?_, ?_, ?_, h.1.2.2.2.2, h.2⟩
    · obtain ⟨sl, x25, hs⟩ := h.1.2.1
      exact ⟨sl, by rw [o₂.get .r25, o₁.get .r25, x25], hs⟩
    · rw [o₂.get .r26, e₁, h.1.2.2.1, BitVec.ofNat_add]
    · rw [e₂, o₁.get .r27, h.1.2.2.2.1, Offset.ofNat_sub_ofNat (by have := h.1.2.2.2.2; omega_arith)]
  have hfin := two_post (Φ := LoopN H.D n) (Ψ := Po) (lr3_taint (pin0 fun _ _ h => h.1)) w8
  refine hfin.mono (fun _ _ h => h) fun u₁ u₂ ⟨ac, h₁, h₂⟩ => ?_
  refine ⟨by rw [eval_nonzero, eval_nonzero, h₁.2.2.2.1, h₂.2.2.2.1], fun _ => trivial, fun ht => ?_⟩
  rw [eval_nonzero, h₁.2.2.2.1] at ht
  have hb := h₁.1.dn
  have hne : (dbLen H.D ac.1).toNat - ac.2 - 1 ≠ 0 := fun h0 => by rw [h0] at ht; simp at ht
  have hlt : ac.2 + 1 < (dbLen H.D ac.1).toNat := by omega_arith
  refine ⟨(dbLen H.D ac.1).toNat - (ac.2 + 1), by have := h₁.2.2.2.2.2; omega_arith, (ac.1, ac.2 + 1),
    ⟨⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩,
    ⟨⟨h₂.1, h₂.2.1, h₂.2.2.1, by rw [h₂.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩⟩

/-- Some salt length in `r25`. -/
abbrev S25 (t : State) : Prop := ∃ sl, t.gpr .r25 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63

theorem S25.keep {t t' : State} (h : S25 t) (e : t'.gpr .r25 = t.gpr .r25) : S25 t' :=
  let ⟨sl, x, hs⟩ := h; ⟨sl, by rw [e, x], hs⟩

include hH cH hD in
/-- `H'` for every length, in both runs. -/
theorem hashAny_ct : RelCT isa (Two fun a t => BL D a t ∧ S25 t) (hashAny H) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2560 := rfl
  subst hD
  let Φ₀ := fun (a t : State) => BL H.D a t ∧ S25 t
  -- `init`.
  have w1 : ∀ a t, Φ₀ a t → WP isa (.block [.addi .r3 .r14 oSt]) t fun t' => Φ₀ a t' ∧ t'.gpr .r3 = off (Sp a) oSt :=
    fun a t h => wp_addi fun t' o e => wp_nil ⟨⟨h.1.only' o, h.2.keep (o.get .r25)⟩, by rw [e, h.1.r14]⟩
  refine two_seq (Ψ := Φ₀) (two_seq (st_taint (bl_pins (fun _ _ h => h.1) [])) w1
      (init_two (lOk H.D) hH cH fun _ _ h => ⟨h.1.1, h.2⟩))
    (fun a t h => WP.seq (WP.mono (w1 a t h) fun t' h' => WP.mono (init_wp' hH h'.1.1 h'.2) fun t'' ⟨b, g⟩ =>
      ⟨b, h'.1.2.keep (g .r25 (by decide))⟩)) ?_
  -- `update` with `0⁸ ‖ mHash`.
  let U := fun (a t : State) => Φ₀ a t ∧ t.gpr .r4 = 0#64 ∧ t.gpr .r5 = off (Sp a) oY ∧
    t.gpr .r6 = BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := U) (anyUpd_taint H (bl_pins (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · refine wp_li (by decide) fun t₁ o₁ e₁ => wp_addi (h := by decide) fun t₂ o₂ e₂ =>
      wp_li (by omega_arith) fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    exact ⟨⟨h.1.only' k₃, h.2.keep (k₃.get .r25)⟩, by rw [o₃.get .r4, o₂.get .r4, e₁],
      by rw [o₃.get .r5, e₂, o₁.get .r14, h.1.r14], e₃⟩
  let U' := fun (a t : State) => U a t ∧ t.gpr .r3 = off (Sp a) oSt ∧ t.gpr .r7 = off (Sp a) oW
  have wU : ∀ a t, U a t → WP isa (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW]) t (U' a) := fun a t h =>
    WP.mono (updRegs_wpG (lOk _) h.1.1) fun t' ⟨b', o', x3, x7⟩ => ⟨⟨⟨b', h.1.2.keep (o'.get .r25)⟩,
      by rw [o'.get .r4, h.2.1], by rw [o'.get .r5, h.2.2.1], by rw [o'.get .r6, h.2.2.2]⟩, x3, x7⟩
  have h6 : ∀ {a t : State}, U' a t → (t.gpr .r6).toNat = 8 + H.D := fun h => by
    rw [h.1.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  refine two_seq (Ψ := Φ₀) (two_seq (Ψ := U') (updRegs_taint (bl_pins (fun _ _ h => h.1.1) [])) wU
      (upd_two hH cH (an := id) (o := fun _ => oY) (len := fun _ => 8 + H.D)
        (fun a t h => ⟨h.1.1.1, by decide, by omega_arith, h.2.1, h.1.2.2.1, h6 h, h.2.2⟩)
        (fun a t₁ t₂ h₁ h₂ => by rw [h₁.1.2.1, h₂.1.2.1])))
    (fun a t h => WP.seq (WP.mono (wU a t h) fun t' h' => WP.mono (upd_wp hH h'.1.1.1 (o := oY) (len := 8 + H.D)
      (by decide) (by omega_arith) h'.2.1 h'.1.2.2.1 (h6 h') h'.2.2) fun _ ⟨b'', g''⟩ =>
        ⟨b'', h'.1.1.2.keep (g'' .r25 (by decide))⟩)) ?_
  -- The counters, and the loop.
  refine two_seq (Ψ := fun a u => LoopR H.D (a, 0) u) (loopInit_taint (bl_pins (fun _ _ h => h.1) []))
    (fun a t h => ?_) ?_
  · refine wp_li (by decide) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_nil ?_
    have k₂ : Only [.r26, .r27] t t₂ := (o₁.trans o₂).mono
    have hb := h.1.dn
    exact ⟨h.1.only' k₂, h.2.keep (k₂.get .r25), by rw [o₂.get .r26, e₁],
      by rw [e₂, o₁.get .r21, h.1.v (r := .r21), Nat.sub_zero]; exact (ofNat_toNat _).symm,
      show 0 < (dbLen H.D a).toNat by omega_arith⟩
  exact (RelCT.exists_ (P := fun n => Two (LoopN H.D n)) fun n => RelCT.loop _ (round_two hH cH rfl) n).mono
    (fun u₁ u₂ ⟨a, h₁, h₂⟩ => ⟨_, (a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h

end

end VG.Proof.RsaPss.PPC64LE
