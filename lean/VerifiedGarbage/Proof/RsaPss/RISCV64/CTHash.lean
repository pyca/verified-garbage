module

-- separate module: it builds in parallel with the correctness proofs after the scan (`Finish` to `Post`),
-- which `CTPost` also needs.

import VerifiedGarbage.Proof.RsaPss.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPss.RISCV64.Select
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid

/-!
# RSASSA-PSS on RISC-V: hashing `M'`, twice

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/CTFixed.lean`, `CTHash.lean`). For any function
whose shared code compares runs through an anchor `a` (`Ok S vf Pre Pub`,
`B`) and keeps a salt length `sl a` in `s6`: the arguments of the hash calls
from the anchor's (`upd_argsG`, `fin_argsG`), the calls in both runs
(`upd_twoG`, `fin_twoG`), and `hashFixedG_ct`, the hash of `M'` for a given
salt length, its blocks by the taint analysis and its calls by `init_two`,
`upd_ct` and `fin_ct`. After the public operation of verification, two runs
are compared through the anchor with `BL`: `Base` from entry states whose
encoding parameters are those of their registers (`PreL`) and that agree
with the anchor on what `Base` fixes. `hashAny_ct`: for any salt length,
the loop over the lengths (`round_two`), whose counters both runs agree on.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oSt oDig oRsa)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off fx fixed Agree Ok B B.agree B.only pins_of
  init_two two_seq UpdArgs FinArgs upd_ct fin_ct HashCT init_ok upd_ok fin_ok sdis sc_cov cR_dis hfits offs
  st_taint)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-! ## Any function's hash calls -/

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : Ok S vf Pre Pub) {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208)

include X hH in
theorem upd_argsG {a t : State} (h : B S vf Pre Pub a t) {o len : Nat} (ho : oY ≤ o) (hl : o + len ≤ oRsa)
    (h0 : t.gpr .a0 = off (S a) oSt) (h2 : t.gpr .a2 = off (S a) o) (h3 : (t.gpr .a3).toNat = len) :
    ∃ s, Pre s ∧ Pub a s ∧ UpdArgs S vf H s t (off (S s) o) len := by
  have F := hfits hH
  obtain ⟨_, hSt, _, _, hR⟩ := offs
  have hY : oY = 2048 := rfl
  obtain ⟨s, P, p, b⟩ := h
  have hS : S s = S a := (X.agree p).S
  exact ⟨s, P, p, X.fits P, b, by rw [h0, hS], by rw [h2, hS], h3,
    Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) hl), sdis (.inr (by omega)) hl (by omega),
    cR_dis (X.fits P) hl⟩

include X in
theorem fin_argsG {a t : State} (h : B S vf Pre Pub a t) (h0 : t.gpr .a0 = off (S a) oSt)
    (h2 : t.gpr .a2 = off (S a) oDig) : ∃ s, Pre s ∧ Pub a s ∧ FinArgs S vf s t := by
  obtain ⟨s, P, p, b⟩ := h
  have hS : S s = S a := (X.agree p).S
  exact ⟨s, P, p, X.fits P, b, by rw [h0, hS], by rw [h2, hS]⟩

include X hH cH hF in
/-- `update` from states agreeing on its arguments, in both runs. -/
theorem upd_twoG {α : Type} {Φ : α → State → Prop} {an : α → State} {o : α → Nat} {len : α → Nat}
    (h : ∀ x t, Φ x t → B S vf Pre Pub (an x) t ∧ oY ≤ o x ∧ o x + len x ≤ oRsa ∧
      t.gpr .a0 = off (S (an x)) oSt ∧ t.gpr .a2 = off (S (an x)) (o x) ∧ (t.gpr .a3).toNat = len x)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .a1 = t₂.gpr .a1) :
    RelCT isa (Two Φ) H.callUpd fun _ _ => True :=
  upd_ct (S := S) (vf := vf) cH hF fun t₁ t₂ ⟨x, h₁, h₂⟩ => by
    obtain ⟨b₁, ho, hl, x0, x2, x3⟩ := h x t₁ h₁
    obtain ⟨b₂, -, -, y0, y2, y3⟩ := h x t₂ h₂
    obtain ⟨s₁, -, -, A₁⟩ := upd_argsG X hH b₁ ho hl x0 x2 x3
    obtain ⟨s₂, -, -, A₂⟩ := upd_argsG X hH b₂ ho hl y0 y2 y3
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr' => ?_, (b₁.agree X).1.trans (b₂.agree X).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · rw [x0, y0]
    · exact hr x t₁ t₂ h₁ h₂
    · rw [x2, y2]
    · exact BitVec.eq_of_toNat_eq (x3.trans y3.symm)

include X cH hF in
/-- `finalize` from states agreeing on its arguments, in both runs. -/
theorem fin_twoG {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → B S vf Pre Pub (an x) t ∧ t.gpr .a0 = off (S (an x)) oSt ∧
      t.gpr .a2 = off (S (an x)) oDig)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .a1 = t₂.gpr .a1) :
    RelCT isa (Two Φ) H.callFin fun _ _ => True :=
  fin_ct (S := S) (vf := vf) cH hF fun t₁ t₂ ⟨x, h₁, h₂⟩ => by
    obtain ⟨b₁, x0, x2⟩ := h x t₁ h₁
    obtain ⟨b₂, y0, y2⟩ := h x t₂ h₂
    obtain ⟨s₁, -, -, A₁⟩ := fin_argsG X b₁ x0 x2
    obtain ⟨s₂, -, -, A₂⟩ := fin_argsG X b₂ y0 y2
    refine ⟨s₁, s₂, A₁, A₂, fun r hr' => ?_, (b₁.agree X).1.trans (b₂.agree X).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · rw [x0, y0]
    · exact hr x t₁ t₂ h₁ h₂
    · rw [x2, y2]

include X hH hF in
/-- `init` keeps `B` and the callee-saved registers. -/
theorem init_wpG {a t : State} (h : B S vf Pre Pub a t) (h0 : t.gpr .a0 = off (S a) oSt) :
    WP isa H.callInit t fun t' => B S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, p, b⟩ := h
  exact WP.mono (init_ok (X.fits P) hH hF b (by rw [h0, (X.agree p).S])) fun t' ⟨b', g', _⟩ => ⟨⟨s, P, p, b'⟩, g'⟩

include X hH hF in
/-- `update` keeps `B` and the callee-saved registers. -/
theorem upd_wpG {a t : State} (h : B S vf Pre Pub a t) {o len : Nat} (ho : oY ≤ o) (hl : o + len ≤ oRsa)
    (h0 : t.gpr .a0 = off (S a) oSt) (h2 : t.gpr .a2 = off (S a) o) (h3 : (t.gpr .a3).toNat = len) :
    WP isa H.callUpd t fun t' => B S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, p, A⟩ := upd_argsG X hH h ho hl h0 h2 h3
  exact WP.mono (upd_ok A.P hH hF A.b A.h0 A.h2 A.h3 A.hdc A.hd₁ A.hd₃) fun t' ⟨b', g', _⟩ =>
    ⟨⟨s, P, p, b'⟩, g'⟩

include X hH hF in
/-- `finalize` keeps `B` and the callee-saved registers. -/
theorem fin_wpG {a t : State} (h : B S vf Pre Pub a t) (h0 : t.gpr .a0 = off (S a) oSt)
    (h2 : t.gpr .a2 = off (S a) oDig) :
    WP isa H.callFin t fun t' => B S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, p, A⟩ := fin_argsG X h h0 h2
  exact WP.mono (fin_ok A.P hH hF A.b A.h0 A.h2) fun t' ⟨b', g', _⟩ => ⟨⟨s, P, p, b'⟩, g'⟩

include X in
/-- `a0 := S + oSt`. -/
theorem st_wpG {a t : State} (h : B S vf Pre Pub a t) :
    WP isa (.block [.addi .a0 .s0 oSt]) t fun t' => B S vf Pre Pub a t' ∧ Only [.a0] t t' ∧
      t'.gpr .a0 = off (S a) oSt :=
  wp_addi (imm := oSt) fun t' o e => wp_nil ⟨h.only X o, o, by rw [e, (h.agree X).2.1]⟩

include X in
/-- `a0 := S + oSt`, `a2 := S + oDig`. -/
theorem finRegs_wpG {a t : State} (h : B S vf Pre Pub a t) :
    WP isa (.block [.addi .a0 .s0 oSt, .addi .a2 .s0 oDig]) t fun t' =>
      B S vf Pre Pub a t' ∧ Only [.a0, .a2] t t' ∧ t'.gpr .a0 = off (S a) oSt ∧ t'.gpr .a2 = off (S a) oDig :=
  wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := oDig) (h := by decide) fun t₂ o₂ e₂ =>
    wp_nil ⟨(h.only X o₁).only X o₂, (o₁.trans o₂).mono, by rw [o₂.get .a0, e₁, (h.agree X).2.1],
      by rw [e₂, o₁.get .s0, (h.agree X).2.1]⟩

include X hH cH hF in
/-- `H' = Hash(M')` for the salt length `sl a` in `s6`, in both runs. -/
theorem hashFixedG_ct {D : Nat} (hD : H.D = D) (sl : State → BitVec 64) :
    RelCT isa (Two fun a t => B S vf Pre Pub a t ∧ t.gpr .s6 = sl a ∧ (sl a).toNat + 8 + D ≤ 2048)
      (hashFixed H) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2048 := rfl
  subst hD
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → B S vf Pre Pub a t) → Pins Φ [] := fun h =>
    pins_of X (an := id) h []
  let K := fun (a t : State) => B S vf Pre Pub a t ∧ t.gpr .s6 = sl a ∧ (sl a).toNat + 8 + H.D ≤ 2048
  have wst : ∀ a t, K a t → WP isa (.block [.addi .a0 .s0 oSt]) t fun t' => K a t' ∧ t'.gpr .a0 = off (S a) oSt :=
    fun a t h => WP.mono (st_wpG X h.1) fun t' ⟨b', o', e'⟩ => ⟨⟨b', by rw [o'.get .s6, h.2.1], h.2.2⟩, e'⟩
  -- `init`.
  refine two_seq (Ψ := K) (two_seq (Ψ := fun a t => K a t ∧ t.gpr .a0 = off (S a) oSt)
      (st_taint (pin fun _ _ h => h.1)) wst (init_two X hH cH fun _ _ h => ⟨h.1.1, h.2⟩))
    (fun a t h => WP.seq (WP.mono (wst a t h) fun t₁ h₁ =>
      WP.mono (init_wpG X hH hF h₁.1.1 h₁.2) fun t₂ ⟨b₂, g₂⟩ => ⟨b₂, by rw [g₂ .s6 (by decide), h₁.1.2.1], h.2.2⟩))
    ?_
  -- `update` with `8 + hLen + salt_len` bytes of `M'`.
  let U := fun (a t : State) => K a t ∧ t.gpr .a1 = 0#64 ∧ t.gpr .a2 = off (S a) oY ∧
    t.gpr .a3 = BitVec.ofNat 64 ((sl a).toNat + 8 + H.D)
  refine two_seq (Ψ := U) (fixUpd_taint H (pin fun _ _ h => h.1)) (fun a t h => ?_) ?_
  · simp only [List.cons_append, List.nil_append]
    refine wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => ?_
    refine wp_yBase (by rw [o₁.get .s0, (h.1.agree X).2.1]) fun t₂ o₂ e₂ =>
      wp_addi (imm := 8 + H.D) (h := by omega) fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.a1, .a2, .a3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨⟨h.1.only X k₃, by rw [k₃.get .s6, h.2.1], h.2.2⟩, by rw [o₃.get .a1, o₂.get .a1, e₁],
      by rw [o₃.get .a2, e₂], ?_⟩
    rw [e₃, o₂.get .s6, o₁.get .s6, h.2.1]
    have := h.2.2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h3 : ∀ {a t : State}, U a t → (t.gpr .a3).toNat = (sl a).toNat + 8 + H.D := fun {a t} h => by
    rw [h.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.1.2.2; omega)]
  let U' := fun (a t : State) => U a t ∧ t.gpr .a0 = off (S a) oSt
  have wU : ∀ a t, U a t → WP isa (.block [.addi .a0 .s0 oSt]) t (U' a) := fun a t h =>
    WP.mono (st_wpG X h.1.1) fun t' ⟨b', o', e'⟩ => ⟨⟨⟨b', by rw [o'.get .s6, h.1.2.1], h.1.2.2⟩,
      by rw [o'.get .a1, h.2.1], by rw [o'.get .a2, h.2.2.1], by rw [o'.get .a3, h.2.2.2]⟩, e'⟩
  refine two_seq (Ψ := K) (two_seq (Ψ := U') (st_taint (pin fun _ _ h => h.1.1)) wU
      (upd_twoG X hH cH hF (an := id) (o := fun _ => oY) (len := fun a => (sl a).toNat + 8 + H.D)
        (fun a t h => ⟨h.1.1.1, Nat.le_refl _, by have := h.1.1.2.2; omega, h.2, h.1.2.2.1, h3 h.1⟩)
        (fun a t₁ t₂ h₁ h₂ => by rw [h₁.1.2.1, h₂.1.2.1])))
    (fun a t h => WP.seq (WP.mono (wU a t h) fun t' h' => WP.mono (upd_wpG X hH hF h'.1.1.1 (o := oY)
      (Nat.le_refl _) (by have := h'.1.1.2.2; omega) h'.2 h'.1.2.2.1 (h3 h'.1)) fun _ ⟨b'', g''⟩ =>
        ⟨b'', by rw [g'' .s6 (by decide), h'.1.1.2.1], h.1.2.2⟩)) ?_
  -- `finalize` after `8 + hLen + salt_len` bytes.
  let V := fun (a t : State) => K a t ∧ t.gpr .a1 = sl a + BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := V) (fixFin_taint H (pin fun _ _ h => h.1)) (fun a t h =>
    wp_addi (imm := 8 + H.D) (h := by omega) fun t' o e =>
      wp_nil ⟨⟨h.1.only X o, by rw [o.get .s6, h.2.1], h.2.2⟩, by rw [e, h.2.1]⟩) ?_
  exact two_seq (Ψ := fun a t => V a t ∧ t.gpr .a0 = off (S a) oSt ∧ t.gpr .a2 = off (S a) oDig)
    (finRegs_taint (pin fun _ _ h => h.1.1)) (fun a t h => WP.mono (finRegs_wpG X h.1.1)
      fun t' ⟨b', o', x0, x2⟩ => ⟨⟨⟨b', by rw [o'.get .s6, h.1.2.1], h.1.2.2⟩, by rw [o'.get .a1, h.2]⟩, x0, x2⟩)
    (fin_twoG X hH cH hF (an := id) (fun a t h => ⟨h.1.1.1, h.2.1, h.2.2⟩)
      (fun a t₁ t₂ h₁ h₂ => by rw [h₁.1.2, h₂.1.2]))

end

/-! ## Verification's runs -/

/-- An entry state whose encoding parameters are those of its registers. -/
abbrev PreL (D : Nat) (s : State) : Prop := Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8)

theorem Lay.canon {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) : PreL D s := by
  have h1 : (lo s).toNat = lN := by rw [L.hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.l1; omega)]
  have h2 : (dbLen D s).toNat = dN := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hk; have := L.k2; omega)]
  have h3 : (cm s).setWidth 8 = c := by rw [L.hc, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  show Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8)
  rw [h1, h2, h3]; exact L

/-- An entry state agrees with the anchor on what `Base` fixes, and on `c`,
`salt_len` and the salt-length mode, which `s5`–`s7` hold (`Xs`). -/
structure AgreeP (D : Nat) (a s : State) : Prop where
  ag : Agree Sp (vP D) a s
  cm : cm s = cm a
  sl : stackArg s 0 = stackArg a 0
  any : anyL s = anyL a

theorem lOk (D : Nat) : Ok Sp (vP D) (PreL D) (AgreeP D) := ⟨fun P => P.F, fun p => p.ag⟩

/-- `Base` from such an entry state agreeing with the anchor. -/
abbrev BL (D : Nat) : State → State → Prop := B Sp (vP D) (PreL D) (AgreeP D)

/-- `Xs`, from the anchor. -/
structure Xa (a t : State) : Prop where
  s5 : t.gpr .s5 = cm a
  s6 : t.gpr .s6 = stackArg a 0
  s7 : t.gpr .s7 = anyL a

theorem Xa.xs {D : Nat} {a s t : State} (g : AgreeP D a s) (x : Xa a t) : Xs s t :=
  ⟨x.s5.trans g.cm.symm, x.s6.trans g.sl.symm, x.s7.trans g.any.symm⟩

theorem Xs.xa {D : Nat} {a s t : State} (g : AgreeP D a s) (x : Xs s t) : Xa a t :=
  ⟨x.s5.trans g.cm, x.s6.trans g.sl, x.s7.trans g.any⟩

theorem Xa.of {a t u : State} (h : Xa a t) (g : ∀ r ∈ [Reg.s5, .s6, .s7], u.gpr r = t.gpr r) : Xa a u :=
  ⟨(g _ (by decide)).trans h.s5, (g _ (by decide)).trans h.s6, (g _ (by decide)).trans h.s7⟩

section
variable {D : Nat}

theorem BL.s0 {a t : State} (h : BL D a t) : t.gpr .s0 = Sp a := ((h.agree (lOk D)).2.1)
theorem BL.v {a t : State} (h : BL D a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.agree (lOk D)).2.2 r hr
theorem BL.only' {a t t' : State} {rs : List Reg} (h : BL D a t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : BL D a t' := h.only (lOk D) o hrs

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs := pins_of (lOk D) h rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D s) (g : AgreeP D a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm s).setWidth 8) := by
  have e3 : lo s = lo a := g.ag.v .s3 (by decide)
  have e4 : dbLen D s = dbLen D a := g.ag.v .s4 (by decide)
  rw [← e3, ← e4]; exact P

theorem BL.dn {a t : State} (h : BL D a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, P, g, -⟩ := h
  have L := agree_lay P g
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega, L.D0, L.D64⟩

end

section
variable {D : Nat} {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) (hD : H.D = D)

include hH cH hF hD in
/-- `H' = Hash(M')` for a given salt length, in both runs. -/
theorem hashFixed_ct :
    RelCT isa (Two fun a t => BL D a t ∧ t.gpr .s6 = stackArg a 0 ∧ (stackArg a 0).toNat + 8 + D ≤ 2048)
      (hashFixed H) fun _ _ => True :=
  hashFixedG_ct (lOk D) hH cH hF hD (fun a => stackArg a 0)

/-- In the loop over the lengths, for the length `L`: `BL`, the counters and
some salt length in `s11`. -/
def LoopR (D : Nat) (ac : State × Nat) (u : State) : Prop :=
  BL D ac.1 u ∧ (∃ sl, u.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .s8 = BitVec.ofNat 64 ac.2 ∧
    u.gpr .s9 = BitVec.ofNat 64 ((dbLen D ac.1).toNat - ac.2) ∧ ac.2 < (dbLen D ac.1).toNat

theorem LoopR.keep {ac : State × Nat} {u u' : State} (h : LoopR D ac u) (hb : BL D ac.1 u')
    (hg : ∀ r ∈ [Reg.s11, .s8, .s9], u'.gpr r = u.gpr r) : LoopR D ac u' := by
  obtain ⟨-, ⟨sl, x11, hs⟩, x8, x9, hL⟩ := h
  exact ⟨hb, ⟨sl, by rw [hg .s11 (by decide), x11], hs⟩, by rw [hg .s8 (by decide), x8],
    by rw [hg .s9 (by decide), x9], hL⟩

theorem pres_three {u u' : State} (h : ∀ r ∈ preserved, u'.gpr r = u.gpr r) :
    ∀ r ∈ [Reg.s11, .s8, .s9], u'.gpr r = u.gpr r := fun r hr => h r (by revert r; decide)

include hH in
theorem copyN_wp {ac : State × Nat} {u : State} (h : LoopR D ac u) {a b : Nat}
    (hab : a = oSt ∧ b = oBk ∨ a = oBk ∧ b = oSt) :
    WP isa (copyN a b H.S) u (LoopR D ac) := by
  have F := hfits hH
  obtain ⟨_, hSt, _, _, hR⟩ := offs
  have hB : oBk = 1376 := rfl
  have hN := hH.hN
  have hS1 : 0 < H.S := by simp only [Hash.S]; omega
  obtain ⟨s, P, g, b'⟩ := h.1
  have L := agree_lay P g
  have k : ∀ {u' : State}, Base Sp (vP D) s u' → Kept [.a4, .a1, .a5, .t0] u u' → LoopR D ac u' := fun b'' k =>
    h.keep ⟨s, P, g, b''⟩ fun r hr => k.gpr r (by revert r; decide)
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact WP.mono (copyN_ok L b' (a := oSt) (b := oBk) (n := H.S) hS1 (by omega) (by omega) (by omega)
      (.inl (by omega)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => k b'' k'
  · exact WP.mono (copyN_ok L b' (a := oBk) (b := oSt) (n := H.S) hS1 (by omega) (by omega) (by omega)
      (.inr (by omega)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => k b'' k'

/-- The loop's invariant, with the lengths left. -/
abbrev LoopN (D n : Nat) (ac : State × Nat) (u : State) : Prop := LoopR D ac u ∧ n = (dbLen D ac.1).toNat - ac.2

include hH cH hF hD in
/-- A round of the loop over the lengths, in both runs; both agree on whether
another follows. -/
theorem round_two (n : Nat) :
    RelCT isa (Two (LoopN D n)) (lenRound H) fun u₁ u₂ =>
      isa.eval (.nonzero .s9) u₁ = isa.eval (.nonzero .s9) u₂ ∧
      (isa.eval (.nonzero .s9) u₁ = some false → True) ∧
      (isa.eval (.nonzero .s9) u₁ = some true → ∃ m < n, Two (LoopN D m) u₁ u₂) := by
  subst hD
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2048 := rfl
  have pin0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR H.D ac u) → Pins Φ [] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) []
  have pinS : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR H.D ac u) → Pins Φ [.s0] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) [.s0]
  -- The state to `oBk`.
  refine two_seq (Ψ := LoopN H.D n) (copyN_taint oSt oBk H.S (pinS fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp hH h (.inl ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `finalize` after `8 + hLen + L` bytes.
  let A4 := fun (ac : State × Nat) (u : State) => LoopN H.D n ac u ∧
    u.gpr .a1 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := A4) (lr1_taint H (pin0 fun _ _ h => h.1)) (fun ac u h =>
    wp_addi (imm := 8 + H.D) (h := by omega) fun u' o e =>
      wp_nil ⟨⟨h.1.keep (h.1.1.only' o) fun r hr => o.gpr r (by revert r; decide), h.2⟩,
        by rw [e, h.1.2.2.1]⟩) ?_
  let A3 := fun (ac : State × Nat) (u : State) => A4 ac u ∧ u.gpr .a0 = off (Sp ac.1) oSt ∧
    u.gpr .a2 = off (Sp ac.1) oDig
  have w3 : ∀ ac u, A4 ac u → WP isa (.block [.addi .a0 .s0 oSt, .addi .a2 .s0 oDig]) u (A3 ac) :=
    fun ac u h => WP.mono (finRegs_wpG (lOk _) h.1.1.1) fun u' ⟨b', o', x0, x2⟩ =>
      ⟨⟨⟨h.1.1.keep b' (fun r hr => o'.gpr r (by revert r; decide)), h.1.2⟩, by rw [o'.get .a1, h.2]⟩, x0, x2⟩
  refine two_seq (Ψ := LoopN H.D n) (two_seq (Ψ := A3) (finRegs_taint (pin0 fun _ _ h => h.1.1)) w3
      (fin_twoG (lOk _) hH cH hF (an := Prod.fst) (fun ac u h => ⟨h.1.1.1.1, h.2.1, h.2.2⟩)
        (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.1.2, h₂.1.2])))
    (fun ac u h => WP.seq (WP.mono (w3 ac u h) fun u' h' =>
      WP.mono (fin_wpG (lOk _) hH hF h'.1.1.1.1 h'.2.1 h'.2.2)
      fun u'' ⟨b'', g''⟩ => ⟨h'.1.1.1.keep b'' (pres_three g''), h'.1.1.2⟩)) ?_
  -- The selection.
  refine two_seq (Ψ := LoopN H.D n) (select_taint H (pinS fun _ _ h => h.1)) (fun ac u ⟨h, hn⟩ => ?_) ?_
  · have hb := h.1.dn
    obtain ⟨s, P, g, b⟩ := h.1
    obtain ⟨sl, x11, hs⟩ := h.2.1
    exact WP.mono (select_ok (agree_lay P g) rfl b h.2.2.1 x11 (by have := h.2.2.2.2; omega) hs)
      fun u' ⟨b', k', _⟩ => ⟨h.keep ⟨s, P, g, b'⟩ fun r hr => k'.gpr r (by revert r; decide), hn⟩
  -- The state back.
  refine two_seq (Ψ := LoopN H.D n) (copyN_taint oBk oSt H.S (pinS fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp hH h (.inr ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `update` with the next byte.
  let A6 := fun (ac : State × Nat) (u : State) => LoopN H.D n ac u ∧
    u.gpr .a1 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + H.D) ∧
    u.gpr .a2 = off (Sp ac.1) (oY + 8 + H.D + ac.2) ∧ u.gpr .a3 = BitVec.ofNat 64 1
  refine two_seq (Ψ := A6) (lr2_taint H (pin0 fun _ _ h => h.1)) (fun ac u h => ?_) ?_
  · simp only [List.cons_append, List.nil_append]
    refine wp_addi (imm := 8 + H.D) (h := by omega) fun u₁ o₁ e₁ => ?_
    refine wp_yBase (by rw [o₁.get .s0, h.1.1.s0]) fun u₂ o₂ e₂ =>
      wp_addi (imm := 8 + H.D) (h := by omega) fun u₃ o₃ e₃ => wp_add fun u₄ o₄ e₄ =>
      wp_li (imm := 1) (by decide) fun u₅ o₅ e₅ => wp_nil ?_
    have k₅ : Only [.a1, .a2, .a3] u u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    refine ⟨⟨h.1.keep (h.1.1.only' k₅) fun r hr => k₅.gpr r (by revert r; decide), h.2⟩, ?_, ?_, e₅⟩
    · rw [o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁, h.1.2.2.1]
    · rw [o₅.get .a2, e₄, e₃, e₂, o₃.get .s8, o₂.get .s8, o₁.get .s8, h.1.2.2.1]
      show off (off (off (Sp ac.1) oY) (8 + H.D)) ac.2 = _
      rw [off_off, off_off, Nat.add_assoc oY 8 H.D, Nat.add_assoc oY (8 + H.D)]
  let A7 := fun (ac : State × Nat) (u : State) => A6 ac u ∧ u.gpr .a0 = off (Sp ac.1) oSt
  have w7 : ∀ ac u, A6 ac u → WP isa (.block [.addi .a0 .s0 oSt]) u (A7 ac) := fun ac u h =>
    WP.mono (st_wpG (lOk _) h.1.1.1) fun u' ⟨b', o', x0⟩ =>
      ⟨⟨⟨h.1.1.keep b' (fun r hr => o'.gpr r (by revert r; decide)), h.1.2⟩, by rw [o'.get .a1, h.2.1],
        by rw [o'.get .a2, h.2.2.1], by rw [o'.get .a3, h.2.2.2]⟩, x0⟩
  have h3 : ∀ {ac : State × Nat} {u : State}, A7 ac u → (u.gpr .a3).toNat = 1 := fun h => by
    rw [h.1.2.2.2]; rfl
  have hb7 : ∀ {ac : State × Nat} {u : State}, A7 ac u → oY + 8 + H.D + ac.2 + 1 ≤ oRsa := fun h => by
    have := h.1.1.1.2.2.2.2; have := h.1.1.1.1.dn; omega
  refine two_seq (Ψ := LoopN H.D n) (two_seq (Ψ := A7) (st_taint (pin0 fun _ _ h => h.1.1)) w7
      (upd_twoG (lOk _) hH cH hF (an := Prod.fst) (o := fun ac => oY + 8 + H.D + ac.2) (len := fun _ => 1)
        (fun ac u h => ⟨h.1.1.1.1, by omega, hb7 h, h.2, h.1.2.2.1, h3 h⟩)
        (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.1.2.1, h₂.1.2.1])))
    (fun ac u h => WP.seq (WP.mono (w7 ac u h) fun u' h' => WP.mono (upd_wpG (lOk _) hH hF h'.1.1.1.1
      (o := oY + 8 + H.D + ac.2) (len := 1) (by omega) (hb7 h') h'.2 h'.1.2.2.1 (h3 h'))
      fun u'' ⟨b'', g''⟩ => ⟨h'.1.1.1.keep b'' (pres_three g''), h'.1.1.2⟩)) ?_
  -- The counters.
  let Po := fun (ac : State × Nat) (u : State) => BL H.D ac.1 u ∧
    (∃ sl, u.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .s8 = BitVec.ofNat 64 (ac.2 + 1) ∧
    u.gpr .s9 = BitVec.ofNat 64 ((dbLen H.D ac.1).toNat - ac.2 - 1) ∧ ac.2 < (dbLen H.D ac.1).toNat ∧
    n = (dbLen H.D ac.1).toNat - ac.2
  have w8 : ∀ ac u, LoopN H.D n ac u → WP isa (.block [.addi .s8 .s8 1, .addi .s9 .s9 (-1)]) u (Po ac) := by
    intro ac u h
    refine wp_addi (imm := 1) fun u₁ o₁ e₁ => wp_subi (imm := 1) fun u₂ o₂ e₂ =>
      wp_nil ⟨(h.1.1.only' o₁).only' o₂, ?_, ?_, ?_, h.1.2.2.2.2, h.2⟩
    · obtain ⟨sl, x11, hs⟩ := h.1.2.1
      exact ⟨sl, by rw [o₂.get .s11, o₁.get .s11, x11], hs⟩
    · rw [o₂.get .s8, e₁, h.1.2.2.1, BitVec.ofNat_add]
    · rw [e₂, o₁.get .s9, h.1.2.2.2.1, Offset.ofNat_sub_ofNat (by have := h.1.2.2.2.2; omega)]
  have hfin := two_post (Φ := LoopN H.D n) (Ψ := Po) (lr3_taint (pin0 fun _ _ h => h.1)) w8
  refine hfin.mono (fun _ _ h => h) fun u₁ u₂ ⟨ac, h₁, h₂⟩ => ?_
  refine ⟨by rw [eval_nonzero, eval_nonzero, h₁.2.2.2.1, h₂.2.2.2.1], fun _ => trivial, fun ht => ?_⟩
  rw [eval_nonzero, h₁.2.2.2.1] at ht
  have hb := h₁.1.dn
  have hne : (dbLen H.D ac.1).toNat - ac.2 - 1 ≠ 0 := fun h0 => by rw [h0] at ht; simp at ht
  have hlt : ac.2 + 1 < (dbLen H.D ac.1).toNat := by omega
  refine ⟨(dbLen H.D ac.1).toNat - (ac.2 + 1), by have := h₁.2.2.2.2.2; omega, (ac.1, ac.2 + 1),
    ⟨⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩,
    ⟨⟨h₂.1, h₂.2.1, h₂.2.2.1, by rw [h₂.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩⟩

/-- Some salt length in `s11`. -/
abbrev S11 (t : State) : Prop := ∃ sl, t.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63

theorem S11.keep {t t' : State} (h : S11 t) (e : t'.gpr .s11 = t.gpr .s11) : S11 t' :=
  let ⟨sl, x, hs⟩ := h; ⟨sl, by rw [e, x], hs⟩

include hH cH hF hD in
/-- `H'` for every length, in both runs. -/
theorem hashAny_ct : RelCT isa (Two fun a t => BL D a t ∧ S11 t) (hashAny H) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2048 := rfl
  subst hD
  let Φ₀ := fun (a t : State) => BL H.D a t ∧ S11 t
  -- `init`.
  have w1 : ∀ a t, Φ₀ a t → WP isa (.block [.addi .a0 .s0 oSt]) t fun t' => Φ₀ a t' ∧
      t'.gpr .a0 = off (Sp a) oSt :=
    fun a t h => WP.mono (st_wpG (lOk _) h.1) fun t' ⟨b', o', e'⟩ => ⟨⟨b', h.2.keep (o'.get .s11)⟩, e'⟩
  refine two_seq (Ψ := Φ₀) (two_seq (st_taint (bl_pins (fun _ _ h => h.1) [])) w1
      (init_two (lOk H.D) hH cH fun _ _ h => ⟨h.1.1, h.2⟩))
    (fun a t h => WP.seq (WP.mono (w1 a t h) fun t' h' => WP.mono (init_wpG (lOk _) hH hF h'.1.1 h'.2)
      fun t'' ⟨b, g⟩ => ⟨b, h'.1.2.keep (g .s11 (by decide))⟩)) ?_
  -- `update` with `0⁸ ‖ mHash`.
  let U := fun (a t : State) => Φ₀ a t ∧ t.gpr .a1 = 0#64 ∧ t.gpr .a2 = off (Sp a) oY ∧
    t.gpr .a3 = BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := U) (anyUpd_taint H (bl_pins (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · simp only [List.cons_append, List.nil_append]
    refine wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => ?_
    refine wp_yBase (by rw [o₁.get .s0, h.1.s0]) fun t₂ o₂ e₂ =>
      wp_li (imm := 8 + H.D) (by omega) fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.a1, .a2, .a3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    exact ⟨⟨h.1.only' k₃, h.2.keep (k₃.get .s11)⟩, by rw [o₃.get .a1, o₂.get .a1, e₁],
      by rw [o₃.get .a2, e₂], e₃⟩
  let U' := fun (a t : State) => U a t ∧ t.gpr .a0 = off (Sp a) oSt
  have wU : ∀ a t, U a t → WP isa (.block [.addi .a0 .s0 oSt]) t (U' a) := fun a t h =>
    WP.mono (st_wpG (lOk _) h.1.1) fun t' ⟨b', o', x0⟩ => ⟨⟨⟨b', h.1.2.keep (o'.get .s11)⟩,
      by rw [o'.get .a1, h.2.1], by rw [o'.get .a2, h.2.2.1], by rw [o'.get .a3, h.2.2.2]⟩, x0⟩
  have h3 : ∀ {a t : State}, U' a t → (t.gpr .a3).toNat = 8 + H.D := fun h => by
    rw [h.1.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine two_seq (Ψ := Φ₀) (two_seq (Ψ := U') (st_taint (bl_pins (fun _ _ h => h.1.1) [])) wU
      (upd_twoG (lOk _) hH cH hF (an := id) (o := fun _ => oY) (len := fun _ => 8 + H.D)
        (fun a t h => ⟨h.1.1.1, Nat.le_refl _, by omega, h.2, h.1.2.2.1, h3 h⟩)
        (fun a t₁ t₂ h₁ h₂ => by rw [h₁.1.2.1, h₂.1.2.1])))
    (fun a t h => WP.seq (WP.mono (wU a t h) fun t' h' => WP.mono (upd_wpG (lOk _) hH hF h'.1.1.1
      (o := oY) (len := 8 + H.D) (Nat.le_refl _) (by omega) h'.2 h'.1.2.2.1 (h3 h')) fun _ ⟨b'', g''⟩ =>
        ⟨b'', h'.1.1.2.keep (g'' .s11 (by decide))⟩)) ?_
  -- The counters, and the loop.
  refine two_seq (Ψ := fun a u => LoopR H.D (a, 0) u) (loopInit_taint (bl_pins (fun _ _ h => h.1) []))
    (fun a t h => ?_) ?_
  · refine wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_nil ?_
    have k₂ : Only [.s8, .s9] t t₂ := (o₁.trans o₂).mono
    have hb := h.1.dn
    exact ⟨h.1.only' k₂, h.2.keep (k₂.get .s11), by rw [o₂.get .s8, e₁],
      by rw [e₂, o₁.get .s4, h.1.v (r := .s4), Nat.sub_zero]; exact (ofNat_toNat _).symm,
      show 0 < (dbLen H.D a).toNat by omega⟩
  exact (RelCT.exists_ (P := fun n => Two (LoopN H.D n)) fun n => RelCT.loop _ (round_two hH cH hF rfl) n).mono
    (fun u₁ u₂ ⟨a, h₁, h₂⟩ => ⟨_, (a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h
end

end VG.Proof.RsaPss.RISCV64
