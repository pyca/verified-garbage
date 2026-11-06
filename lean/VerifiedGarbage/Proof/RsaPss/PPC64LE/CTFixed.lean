module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSASSA-PSS on PPC64LE: hashing `M'` for a given salt length, twice

Untrusted: everything here is checked by Lean. For any function whose shared
code compares runs through an anchor `a` (`Ok S vf Pre Pub`, `B`), and whose
`Base` keeps the salt length in `r19` (`vf a .r19`): the arguments of the
hash calls from the anchor's (`upd_argsG`, `fin_argsG`), the calls in both
runs (`upd_twoG`, `fin_twoG`), and `hashFixedG_ct`: the hash of `M'` for a
given salt length, its blocks by the taint analysis and its calls by
`init_two`, `upd_ct` and `fin_ct`. Verification (`CTHash`) and signing use it.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Impl.RsaPss.PPC64LE (MdFns)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off fx hiRegs Ok B BT BT.b B.agree B.only pins_of st_wp init_two init_wp two_seq
  UpdArgs FinArgs init_ct upd_ct fin_ct HashCT upd_ok sc_cov sdis cR_dis hfits offs st_taint)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins wp_li wp_addi wp_nil)

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : Ok S vf Pre Pub) {H : Hash} (hH : HashOK H) (cH : HashCT hH)

include X hH in
theorem upd_argsS {a s t : State} (P : Pre s) (p : Pub a s) (b : Base S vf s t) {o len : Nat} (ho : oW + 1024 ≤ o)
    (hl : o + len ≤ oRsa) (h3 : t.gpr .r3 = off (S a) oSt) (h5 : t.gpr .r5 = off (S a) o)
    (h6 : (t.gpr .r6).toNat = len) (h7 : t.gpr .r7 = off (S a) oW) : UpdArgs S vf H s t (off (S s) o) len := by
  have F := hfits hH
  obtain ⟨_, _, _, _, hW, hR⟩ := offs
  have hS : S s = S a := (X.agree p).S
  exact ⟨X.fits P, b, by rw [h3, hS], by rw [h5, hS], h6, by rw [h7, hS],
    Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) hl), sdis (.inr (by omega)) hl (by omega),
    sdis (.inr (by omega)) hl (by omega), cR_dis (X.fits P) hl⟩

include X hH in
theorem upd_argsG {a t : State} (h : B S vf Pre Pub a t) {o len : Nat} (ho : oW + 1024 ≤ o) (hl : o + len ≤ oRsa)
    (h3 : t.gpr .r3 = off (S a) oSt) (h5 : t.gpr .r5 = off (S a) o) (h6 : (t.gpr .r6).toNat = len)
    (h7 : t.gpr .r7 = off (S a) oW) : ∃ s, Pre s ∧ Pub a s ∧ UpdArgs S vf H s t (off (S s) o) len :=
  let ⟨s, P, p, b⟩ := h; ⟨s, P, p, upd_argsS X hH P p b ho hl h3 h5 h6 h7⟩

include X in
theorem fin_argsG {a t : State} (h : B S vf Pre Pub a t) (h3 : t.gpr .r3 = off (S a) oSt)
    (h5 : t.gpr .r5 = off (S a) oDig) (h6 : t.gpr .r6 = off (S a) oW) :
    ∃ s, Pre s ∧ Pub a s ∧ FinArgs S vf s t := by
  obtain ⟨s, P, p, b⟩ := h
  have hS : S s = S a := (X.agree p).S
  exact ⟨s, P, p, X.fits P, b, by rw [h3, hS], by rw [h5, hS], by rw [h6, hS]⟩

include X hH cH in
/-- `update` from states agreeing on its arguments, in both runs. -/
theorem upd_twoG {α : Type} {Φ : α → State → Prop} {an : α → State} {o : α → Nat} {len : α → Nat}
    (h : ∀ x t, Φ x t → B S vf Pre Pub (an x) t ∧ oW + 1024 ≤ o x ∧ o x + len x ≤ oRsa ∧
      t.gpr .r3 = off (S (an x)) oSt ∧ t.gpr .r5 = off (S (an x)) (o x) ∧ (t.gpr .r6).toNat = len x ∧
      t.gpr .r7 = off (S (an x)) oW)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .r4 = t₂.gpr .r4) :
    RelCT isa (Two Φ) H.callUpd fun _ _ => True :=
  upd_ct (S := S) (vf := vf) cH fun t₁ t₂ ⟨x, h₁, h₂⟩ => by
    obtain ⟨b₁, ho, hl, x3, x5, x6, x7⟩ := h x t₁ h₁
    obtain ⟨b₂, -, -, y3, y5, y6, y7⟩ := h x t₂ h₂
    obtain ⟨s₁, -, -, A₁⟩ := upd_argsG X hH b₁ ho hl x3 x5 x6 x7
    obtain ⟨s₂, -, -, A₂⟩ := upd_argsG X hH b₂ ho hl y3 y5 y6 y7
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr' => ?_, (b₁.agree X).1.trans (b₂.agree X).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · rw [x3, y3]
    · exact hr x t₁ t₂ h₁ h₂
    · rw [x5, y5]
    · exact BitVec.eq_of_toNat_eq (x6.trans y6.symm)
    · rw [x7, y7]

include X cH in
/-- `finalize` from states agreeing on its arguments, in both runs. -/
theorem fin_twoG {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → B S vf Pre Pub (an x) t ∧ t.gpr .r3 = off (S (an x)) oSt ∧
      t.gpr .r5 = off (S (an x)) oDig ∧ t.gpr .r6 = off (S (an x)) oW)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .r4 = t₂.gpr .r4) :
    RelCT isa (Two Φ) H.callFin fun _ _ => True :=
  fin_ct (S := S) (vf := vf) cH fun t₁ t₂ ⟨x, h₁, h₂⟩ => by
    obtain ⟨b₁, x3, x5, x6⟩ := h x t₁ h₁
    obtain ⟨b₂, y3, y5, y6⟩ := h x t₂ h₂
    obtain ⟨s₁, -, -, A₁⟩ := fin_argsG X b₁ x3 x5 x6
    obtain ⟨s₂, -, -, A₂⟩ := fin_argsG X b₂ y3 y5 y6
    refine ⟨s₁, s₂, A₁, A₂, fun r hr' => ?_, (b₁.agree X).1.trans (b₂.agree X).1.symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · rw [x3, y3]
    · exact hr x t₁ t₂ h₁ h₂
    · rw [x5, y5]
    · rw [x6, y6]

include X hH in
include X in
include X in
section
variable {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} (A : MdTabA H cn cc dn dc f j S Pre Pub)

include X A hH cH in
/-- `H' = Hash(M')` for the salt length `sl a` in `r19`, through the hash
function's table, in both runs. -/
theorem hashFixedG_ct {D : Nat} (hD : H.D = D) (sl : State → Nat)
    (h19 : ∀ a, vf a .r19 = BitVec.ofNat 64 (sl a)) :
    RelCT isa (Two fun a t => BT S vf Pre Pub a t ∧ sl a + 8 + D ≤ 2048) (hashFixed H f j) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2560 := rfl
  subst hD
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → BT S vf Pre Pub a t) → Pins Φ [] := fun h =>
    pins_of X (an := id) (fun a t hx => (h a t hx).b) []
  have bto : ∀ {a t t' : State} {rs : List Reg}, BT S vf Pre Pub a t → Only rs t t' → t'.syms = t.syms →
      (∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs) → BT S vf Pre Pub a t' := fun h o y hrs =>
    let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only (X.fits P) o hrs, y.trans sy⟩
  have r14 : ∀ {a t : State}, BT S vf Pre Pub a t → t.gpr .r14 = S a := fun h => (h.b.agree X).2.1
  have r19 : ∀ {a t : State}, BT S vf Pre Pub a t → t.gpr .r19 = BitVec.ofNat 64 (sl a) := fun h => by
    rw [(h.b.agree X).2.2 .r19 (by decide), h19]
  let M := fun (a t : State) => BT S vf Pre Pub a t ∧ sl a + 8 + H.D ≤ 2048
  -- `init`.
  have wst : ∀ a t, M a t → WP isa (.block [.addi .r3 .r14 oSt]) t fun t' => M a t' ∧ t'.gpr .r3 = off (S a) oSt :=
    fun a t h => WP.of_syms (wp_addi fun t' o e => wp_nil fun y => ⟨⟨bto h.1 o y (by decide), h.2⟩,
      by rw [e, r14 h.1]⟩)
  refine two_seq (Ψ := M) (two_seq (Ψ := fun a t => M a t ∧ t.gpr .r3 = off (S a) oSt)
      (st_taint (pin fun _ _ h => h.1)) wst
      (tcall_twoM X.s A (an := id) (fun a t h => h.1.1) (k := 0) (by decide)
        (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
        (init_ct (S := S) (vf := vf) cH fun u₁ u₂ hp => ?_)))
    (fun a t h => WP.seq (WP.mono (wst a t h) fun t₁ ⟨⟨⟨s, P, p, b, sy⟩, hb⟩, h3⟩ =>
      WP.mono (initM_ok (X.fits P) (A.tab P) hH b sy (by rw [h3, (X.agree p).S])) fun t₂ ⟨⟨b₂, _⟩, sy₂⟩ =>
        ⟨⟨s, P, p, b₂, sy₂⟩, hb⟩)) ?_
  · obtain ⟨a, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := bto h₁.1.1 o₁ y₁ (by decide)
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := bto h₂.1.1 o₂ y₂ (by decide)
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2, (X.agree p₁).S], X.fits P₂, b₂,
      by rw [o₂.get .r3, h₂.2, (X.agree p₂).S], by rw [o₁.get .r3, o₂.get .r3, h₁.2, h₂.2],
      (Base.spA X.s p₁ b₁).trans (Base.spA X.s p₂ b₂).symm⟩
  -- `update` with `8 + hLen + salt_len` bytes of `M'`.
  let U := fun (a t : State) => BT S vf Pre Pub a t ∧ sl a + 8 + H.D ≤ 2048 ∧ t.gpr .r4 = 0#64 ∧
    t.gpr .r5 = off (S a) oY ∧ t.gpr .r6 = BitVec.ofNat 64 (sl a + 8 + H.D)
  refine two_seq (Ψ := U) (fixUpd_taint H (pin fun _ _ h => h.1)) (fun a t ⟨h, hb⟩ => ?_) ?_
  · refine WP.of_syms (wp_li (by decide) fun t₁ o₁ e₁ => wp_addi (h := by decide) fun t₂ o₂ e₂ =>
      wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨bto h k₃ y (by decide), hb, by rw [o₃.get .r4, o₂.get .r4, e₁],
      by rw [o₃.get .r5, e₂, o₁.get .r14, r14 h], ?_⟩
    rw [e₃, o₂.get .r19, o₁.get .r19, r19 h, BitVec.ofNat_add_ofNat]; congr 1; omega
  have h6 : ∀ {a t : State}, U a t → (t.gpr .r6).toNat = sl a + 8 + H.D := fun {a t} h => by
    rw [h.2.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.1; omega)]
  let U' := fun (a t : State) => U a t ∧ t.gpr .r3 = off (S a) oSt ∧ t.gpr .r7 = off (S a) oW
  have hU' : ∀ a t, U a t → WP isa (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW]) t (U' a) := fun a t h =>
    WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_nil fun y => by
      have k : Only [.r3, .r7] t t₂ := (o₁.trans o₂).mono
      exact ⟨⟨bto h.1 k y (by decide), h.2.1, by rw [k.get .r4, h.2.2.1], by rw [k.get .r5, h.2.2.2.1],
        by rw [k.get .r6, h.2.2.2.2]⟩, by rw [o₂.get .r3, e₁, r14 h.1], by rw [e₂, o₁.get .r14, r14 h.1]⟩)
  refine two_seq (Ψ := M) (two_seq (Ψ := U') (updRegs_taint (pin fun _ _ h => h.1)) hU'
      (tcall_twoM X.s A (an := id) (fun a t h => h.1.1) (k := 1) (by decide)
        (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
        (upd_twoG X hH cH (an := id) (o := fun _ => oY) (len := fun a => sl a + 8 + H.D)
          (fun a u ⟨t, h, o, _⟩ => ⟨h.1.1.b.only X o, by decide, by have := h.1.2.1; omega,
            by rw [o.get .r3, h.2.1]; rfl, by rw [o.get .r5, h.1.2.2.2.1]; rfl, by rw [o.get .r6, h6 h.1],
            by rw [o.get .r7, h.2.2]; rfl⟩)
          (fun a u₁ u₂ ⟨t₁, h₁, o₁, _⟩ ⟨t₂, h₂, o₂, _⟩ => by
            rw [o₁.get .r4, o₂.get .r4, h₁.1.2.2.1, h₂.1.2.2.1]))))
    (fun a t h => WP.seq (WP.mono (hU' a t h) fun t' h' => by
      have h6' := h6 h'.1
      have hb' := h'.1.2.1
      obtain ⟨⟨⟨s, P, p, b, sy⟩, hb, -, h5, -⟩, h3, h7⟩ := h'
      have A' := upd_argsS X hH P p b (o := oY) (by decide) (by omega) h3 h5 h6' h7
      exact WP.mono (updM_ok A'.P (A.tab P) hH A'.b sy A'.h3 A'.h5 A'.h6 A'.h7 A'.hdc A'.hd₁ A'.hd₂ A'.hd₃)
        fun t'' ⟨⟨b', _⟩, y'⟩ => ⟨⟨s, P, p, b', y'⟩, hb⟩)) ?_
  -- `finalize` after `8 + hLen + salt_len` bytes.
  let V := fun (a t : State) => BT S vf Pre Pub a t ∧ t.gpr .r4 = vf a .r19 + BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := V) (fixFin_taint H (pin fun _ _ h => h.1)) (fun a t h => WP.of_syms (wp_addi (h := by omega)
      fun t' o e => wp_nil fun y => ⟨bto h.1 o y (by decide), by rw [e, (h.1.b.agree X).2.2 .r19 (by decide)]⟩)) ?_
  let V' := fun (a t : State) => V a t ∧ t.gpr .r3 = off (S a) oSt ∧ t.gpr .r5 = off (S a) oDig ∧
    t.gpr .r6 = off (S a) oW
  have hV' : ∀ a t, V a t → WP isa (.block [.addi .r3 .r14 oSt, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) t (V' a) :=
    fun a t h => WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ =>
      wp_nil fun y => by
        have k : Only [.r3, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
        exact ⟨⟨bto h.1 k y (by decide), by rw [k.get .r4, h.2]⟩, by rw [o₃.get .r3, o₂.get .r3, e₁, r14 h.1],
          by rw [o₃.get .r5, e₂, o₁.get .r14, r14 h.1], by rw [e₃, o₂.get .r14, o₁.get .r14, r14 h.1]⟩)
  exact two_seq (Ψ := V') (finRegs_taint (pin fun _ _ h => h.1)) hV'
    (tcall_twoM X.s A (an := id) (fun a t h => h.1.1) (k := 2) (by decide)
      (fun P p => ⟨(A.tab P).ok.fz, by rw [show 8 * 2 = 16 from rfl]; exact (A.tab P).mem.2.2, A.af p⟩)
      (fin_twoG X hH cH (an := id) (fun a u ⟨t, h, o, _⟩ => ⟨h.1.1.b.only X o, by rw [o.get .r3, h.2.1]; rfl,
          by rw [o.get .r5, h.2.2.1]; rfl, by rw [o.get .r6, h.2.2.2]; rfl⟩)
        (fun a u₁ u₂ ⟨t₁, h₁, o₁, _⟩ ⟨t₂, h₂, o₂, _⟩ => by rw [o₁.get .r4, o₂.get .r4, h₁.1.2, h₂.1.2])))

end

end

end VG.Proof.RsaPss.PPC64LE
