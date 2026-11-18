module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTPub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Post
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-! ### `RsaPss.PPC64LE.CTMain`, which the modules that import this one used -/

section

/-! ### `RsaPss.PPC64LE.CTPost`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.CTHash`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.CTFixed`, which this module and modules that import it used -/

section

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
    Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) hl), sdis (.inr (by omega_arith)) hl (by omega_arith),
    sdis (.inr (by omega_using [ho, F])) hl (by omega_using [ho, hl, F]), cR_dis (X.fits P) hl⟩

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
      wp_addi (h := by omega_using [hD64]) fun t₃ o₃ e₃ => wp_nil fun y => ?_)
    have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    refine ⟨bto h k₃ y (by decide), hb, by rw [o₃.get .r4, o₂.get .r4, e₁],
      by rw [o₃.get .r5, e₂, o₁.get .r14, r14 h], ?_⟩
    rw [e₃, o₂.get .r19, o₁.get .r19, r19 h, BitVec.ofNat_add_ofNat]; congr 1; omega_using []
  have h6 : ∀ {a t : State}, U a t → (t.gpr .r6).toNat = sl a + 8 + H.D := fun {a t} h => by
    rw [h.2.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.1; omega_using [this])]
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
          (fun a u ⟨t, h, o, _⟩ => ⟨h.1.1.b.only X o, by decide, by have := h.1.2.1; omega_using [hR, hY, this],
            by rw [o.get .r3, h.2.1]; rfl, by rw [o.get .r5, h.1.2.2.2.1]; rfl, by rw [o.get .r6, h6 h.1],
            by rw [o.get .r7, h.2.2]; rfl⟩)
          (fun a u₁ u₂ ⟨t₁, h₁, o₁, _⟩ ⟨t₂, h₂, o₂, _⟩ => by
            rw [o₁.get .r4, o₂.get .r4, h₁.1.2.2.1, h₂.1.2.2.1]))))
    (fun a t h => WP.seq (WP.mono (hU' a t h) fun t' h' => by
      have h6' := h6 h'.1
      have hb' := h'.1.2.1
      obtain ⟨⟨⟨s, P, p, b, sy⟩, hb, -, h5, -⟩, h3, h7⟩ := h'
      have A' := upd_argsS X hH P p b (o := oY) (by decide) (by omega_using [hR, hY, hb']) h3 h5 h6' h7
      exact WP.mono (updM_ok A'.P (A.tab P) hH A'.b sy A'.h3 A'.h5 A'.h6 A'.h7 A'.hdc A'.hd₁ A'.hd₂ A'.hd₃)
        fun t'' ⟨⟨b', _⟩, y'⟩ => ⟨⟨s, P, p, b', y'⟩, hb⟩)) ?_
  -- `finalize` after `8 + hLen + salt_len` bytes.
  let V := fun (a t : State) => BT S vf Pre Pub a t ∧ t.gpr .r4 = vf a .r19 + BitVec.ofNat 64 (8 + H.D)
  refine two_seq (Ψ := V) (fixFin_taint H (pin fun _ _ h => h.1)) (fun a t h => WP.of_syms (wp_addi (h := by omega_using [hD64])
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

end

end

/-!
# RSASSA-PSS verification on PPC64LE: hashing `M'` for a given salt length, twice

Untrusted: everything here is checked by Lean. After the public operation,
two runs are compared through the anchor `a` with `BL`: `Base` from entry
states whose encoding parameters are those of their registers and that hold
the tables of the hash functions (`PreL`: the hash function's of `MdHash`
and MGF1's of `MdHash`, as `Tabs` names them), that agree with the anchor on
what `Base` fixes and on the tables and the addresses of their functions
(`PubL`), with the entry's addresses of statics. `hashFixed_ct`: the hash of
`M'` for a given salt length, its blocks by the taint analysis and its calls
through the table by `tcall_twoM`, `init_ct`, `upd_ct` and `fin_ct`, with
arguments from the anchor.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off fx hiRegs Agree Ok B BT BT.b B.agree B.only pins_of st_wp
  two_seq UpdArgs FinArgs init_ct upd_ct fin_ct HashCT sdis sc_cov cR_dis hfits offs st_taint TabS TabA)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-- The tables on entry. -/
def TabsOn (Z : Tabs) (s : State) : Prop :=
  TabS Z.G Z.g gArg Sp s (stackArg s 7) ∧ MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp s (stackArg s 6)

/-- The tables at the anchor's addresses, with its addresses of their functions. -/
def TabsAg (Z : Tabs) (a s : State) : Prop :=
  stackArg s 7 = stackArg a 7 ∧ s.syms Z.G.initN = a.syms Z.G.initN ∧ s.syms Z.G.updN = a.syms Z.G.updN ∧
    s.syms Z.G.finN = a.syms Z.G.finN ∧ stackArg s 6 = stackArg a 6 ∧ s.syms Z.H.initN = a.syms Z.H.initN ∧
    s.syms Z.H.updN = a.syms Z.H.updN ∧ s.syms Z.H.finN = a.syms Z.H.finN ∧ s.syms Z.cn = a.syms Z.cn ∧
    s.syms Z.dn = a.syms Z.dn

/-- An entry state whose encoding parameters are those of its registers, with
the tables. -/
abbrev PreL (D : Nat) (Z : Tabs) (s : State) : Prop :=
  Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) ∧ TabsOn Z s

/-- What it agrees on with the anchor. -/
abbrev PubL (D : Nat) (Z : Tabs) (a s : State) : Prop := Agree Sp (vP D) a s ∧ TabsAg Z a s

theorem Lay.canon {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) :
    Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) := by
  have h1 : (lo s).toNat = lN := by rw [L.hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.l1; omega_arith)]
  have h2 : (dbLen D s).toNat = dN := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hk; have := L.k2; omega_arith)]
  have h3 : (cm s).setWidth 8 = c := by rw [L.hc, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [h1, h2, h3]; exact L

theorem lOk (D : Nat) (Z : Tabs) : Ok Sp (vP D) (PreL D Z) (PubL D Z) := ⟨fun P => P.1.F, fun p => p.1⟩

theorem tabG (D : Nat) (Z : Tabs) : TabA Z.G Z.g gArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2.1⟩

theorem tabH (D : Nat) (Z : Tabs) : MdTabA Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.2, fun p => p.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.2⟩

/-- `Base` from such an entry state agreeing with the anchor, with its
addresses of statics. -/
abbrev BL (D : Nat) (Z : Tabs) : State → State → Prop := BT Sp (vP D) (PreL D Z) (PubL D Z)

section
variable {D : Nat} {Z : Tabs}

theorem BL.r14 {a t : State} (h : BL D Z a t) : t.gpr .r14 = Sp a := ((h.b.agree (lOk D Z)).2.1)
theorem BL.v {a t : State} (h : BL D Z a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.b.agree (lOk D Z)).2.2 r hr
theorem BL.only' {a t t' : State} {rs : List Reg} (h : BL D Z a t) (o : Only rs t t') (y : t'.syms = t.syms)
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : BL D Z a t' :=
  let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only P.1.F o hrs, y.trans sy⟩

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D Z (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of (lOk D Z) (fun x t hx => (h x t hx).b) rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D Z s) (g : PubL D Z a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm a).setWidth 8) := by
  have e17 : lo s = lo a := g.1.v .r17 (by decide)
  have e18 : cm s = cm a := g.1.v .r18 (by decide)
  have e21 : dbLen D s = dbLen D a := g.1.v .r21 (by decide)
  rw [← e17, ← e18, ← e21]; exact P.1

theorem BL.dn {a t : State} (h : BL D Z a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, P, g, -, -⟩ := h
  have L := agree_lay P g
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega_arith, L.D0, L.D64⟩

end

/-! ## `hashFixed`, through the table -/

theorem hashFixed_ct {D : Nat} {Z : Tabs} (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) :
    RelCT isa (Two fun a t => BL D Z a t ∧ (stackArg a 0).toNat + 8 + D ≤ 2048) (hashFixed Z.H Z.f hArg)
      fun _ _ => True :=
  hashFixedG_ct (lOk D Z) hH cH (tabH D Z) hD (fun a => (stackArg a 0).toNat) fun a => by
    show stackArg a 0 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## `ctHash`, in two runs -/

section CtHash

open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (CalleeOk compressK ofNat_shr ofNat_shl)
open VG.Impl.RsaOaep.PPC64LE (tcall)
open VG.Proof.RsaOaep.PPC64LE (view fb)
open VG.Impl.MdStream.PPC64LE (Params lg)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (wp_lsr wp_lsl wp_add)

variable {D : Nat} {Z : Tabs} {P : Params} {md : Md P.B P.N P.L}

/-- The number of blocks `ctHash` compresses, from the anchor's `dbLen`. -/
def nbmOf (D : Nat) (P : Params) (a : State) : Nat := ((dbLen D a).toNat + (8 + D - 1 + P.L)) / P.B + 1

/-- After `ctLens`: `nbm` in `r28` and `ℓ` in `r29`, of some salt length
below `dbLen`. -/
def K1 (D : Nat) (Z : Tabs) (P : Params) (a t : State) : Prop :=
  BL D Z a t ∧ t.gpr .r28 = BitVec.ofNat 64 (nbmOf D P a) ∧
    ∃ sl < (dbLen D a).toNat, t.gpr .r29 = BitVec.ofNat 64 (8 + D + sl)

/-- After `lenField`: `nbm` in `r28` and some last block below it in `r27`. -/
def K2 (D : Nat) (Z : Tabs) (P : Params) (a t : State) : Prop :=
  BL D Z a t ∧ t.gpr .r28 = BitVec.ofNat 64 (nbmOf D P a) ∧ ∃ fb < nbmOf D P a, t.gpr .r27 = BitVec.ofNat 64 fb

/-- In the compression loop, before block `ac.2`. -/
def LI (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  BL D Z ac.1 u ∧ u.gpr .r28 = BitVec.ofNat 64 (nbmOf D P ac.1 - ac.2) ∧ u.gpr .r26 = BitVec.ofNat 64 ac.2 ∧
    ac.2 < nbmOf D P ac.1 ∧ ∃ fb < nbmOf D P ac.1, u.gpr .r27 = BitVec.ofNat 64 fb

theorem nbm_le (ok : CtOK P md Z.cc Z.dc) {a t : State} (h : BL D Z a t) :
    nbmOf D P a * P.B ≤ 2048 ∧ 0 < nbmOf D P a := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.dn
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have := Nat.div_mul_le_self ((dbLen D a).toNat + (8 + D - 1 + P.L)) P.B
  refine ⟨?_, Nat.succ_pos _⟩
  unfold nbmOf
  rw [Nat.add_mul, Nat.one_mul]; rcases hBd with e | e <;> rw [e] at this ⊢ <;> omega_using [hd2, hLd]

theorem ne0_ofNat {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have e : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [show (BitVec.ofNat 64 k != 0) = true from bne_iff_ne.mpr e]; simp [h]

theorem pins_r28 {α : Type} {Φ : α → State → Prop} {an : α → State} {v : α → BitVec 64}
    (hb : ∀ x t, Φ x t → BL D Z (an x) t) (h28 : ∀ x t, Φ x t → t.gpr .r28 = v x) : Pins Φ [.r14, .r28] :=
  fun x t₁ t₂ h₁ h₂ => ⟨((bl_pins hb []) x t₁ t₂ h₁ h₂).1, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hb x t₁ h₁).r14, (hb x t₂ h₂).r14]
    · rw [h28 x t₁ h₁, h28 x t₂ h₂]⟩

section
variable (ok : CtOK P md Z.cc Z.dc)
include ok

theorem ctLens_wp (hD : Z.H.D = D) {a t : State} (h : BL D Z a t)
    (hs : ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa (.block (ctLens Z.H P)) t (K1 D Z P a) := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.dn
  obtain ⟨s, Pr, p, b, sy⟩ := h
  have L := agree_lay Pr p
  obtain ⟨sl, hsl, h25⟩ := hs
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hLd := ok.dims.L
  subst hD
  refine WP.of_syms (wp_addi (h := by omega_using [hd2]) fun t₁ o₁ e₁ => wp_addi (h := by omega_using [hLd, hd2]) fun t₂ o₂ e₂ =>
    wp_lsr (h := by omega_using [hlg7]) fun t₃ o₃ e₃ => wp_addi (h := by decide) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_)
  have k₄ : Only [.r29, .r28] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨s, Pr, p, b.only L.F k₄, y₄.trans sy⟩, ?_, sl, hsl, ?_⟩
  · rw [e₄, e₃, e₂, o₁.get .r21, b.pdb, L.hdb, BitVec.ofNat_add_ofNat, ofNat_shr (by omega_using [hLd, hd2]), hlg,
      BitVec.ofNat_add_ofNat]; rfl
  · rw [o₄.get .r29, o₃.get .r29, o₂.get .r29, e₁, h25, BitVec.ofNat_add_ofNat]; congr 1; omega_using []

omit ok in
theorem hInit_K1 (hH : HashOK Z.H) {a t : State} (h : K1 D Z P a t) : WP isa (hInit Z.f hArg) t (K1 D Z P a) := by
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have X := lOk D Z
  refine WP.seq (WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  exact WP.mono (initM_ok (X.fits Pr) ((tabH D Z).tab Pr) hH (b.only (X.fits Pr) o₁) (y₁.trans sy)
    (by rw [e₁, b.r14])) fun t₂ ⟨⟨b₂, g₂, _⟩, y₂⟩ =>
      ⟨⟨s, Pr, p, b₂, y₂⟩, by rw [g₂ _ (by decide), o₁.get .r28, h28], sl, hsl,
        by rw [g₂ _ (by decide), o₁.get .r29, h29]⟩

theorem pad80_K1 {a t : State} (h : K1 D Z P a t) : WP isa (pad80 P) t (K1 D Z P a) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.1.dn
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have L := agree_lay Pr p
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  exact WP.of_syms (WP.mono (pad80_ok L hlg hlg7 b h28 h29 hnb (Nat.mul_pos hn0 ok.dims.pos) (by omega_using [hd2, hsl]))
    fun t' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], sl, hsl, by rw [k'.get .r29, h29]⟩)

theorem lenField_K2 {a t : State} (h : K1 D Z P a t) : WP isa (.block (lenField P)) t (K2 D Z P a) := by
  obtain ⟨hd1, hd2, hD0, hD64⟩ := h.1.dn
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, sl, hsl, h29⟩ := h
  have L := agree_lay Pr p
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  have hNd := ok.dims.N
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have hO : oLen = 4608 := rfl
  refine WP.of_syms (WP.mono (lenField_ok L ok.shape ok.lenLr (by rcases hBd with e | e <;> omega_using [hNd, hO, e]) hLd.2 hlg7
    b h29 (by omega_using [hd2, hsl])) fun t' ⟨b', k', g27, _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28],
      (8 + D + sl + P.L) / 2 ^ lg P, ?_, g27⟩)
  rw [hlg]; unfold nbmOf
  exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega_using [hsl]))

theorem lenLoop_K2 {a t : State} (h : K2 D Z P a t) : WP isa (lenLoop P) t (K2 D Z P a) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, fb, hfb, h27⟩ := h
  have L := agree_lay Pr p
  have hBd := ok.dims.B
  have hLd := ok.dims.L
  have hn32 : nbmOf D P a ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega_using [hnb]
  exact WP.of_syms (WP.mono (lenLoop_ok L hBd (by rcases hBd with e | e <;> omega_using [hLd, e]) hLd.1 b h28 h27 hn0 hnb
    (by omega_using [hfb, hn32]) (len := (List.range P.L).map fun k => view t.mem (Sp s) (oLen + k)) fun k hk => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
        Option.getD_some])
    fun t' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], fb, hfb, by rw [k'.get .r27, h27]⟩)

/-- The arguments of the compression of block `ac.2`. -/
def CA (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  LI D Z P ac u ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧ u.gpr .r4 = off (Sp ac.1) (oY + P.B * ac.2) ∧
    u.gpr .r5 = BitVec.ofNat 64 1 ∧ u.gpr .r6 = off (Sp ac.1) oW

omit ok in
theorem compArgs_CA {ac : State × Nat} {u : State} (h : LI D Z P ac u) (hlg : 2 ^ lg P = P.B) (hlg7 : lg P ≤ 7)
    (hb : P.B * ac.2 + P.B ≤ 2048) : WP isa (.block (compArgs P)) u (CA D Z P ac) := by
  have h14 := h.1.r14
  refine WP.of_syms (wp_addi (h := by decide) fun u₁ p₁ f₁ => wp_lsl (h := by omega_using [hlg7]) fun u₂ p₂ f₂ =>
    wp_add fun u₃ p₃ f₃ => wp_addi (h := by decide) fun u₄ p₄ f₄ => wp_li (by decide) fun u₅ p₅ f₅ =>
    wp_addi (h := by decide) fun u₆ p₆ f₆ => wp_nil fun y₆ => ?_)
  have k₆ : Only [.r3, .r4, .r5, .r6] u u₆ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans p₆))))).mono
  obtain ⟨hb', h28, h26, hi, fb, hfb, h27⟩ := h
  refine ⟨⟨hb'.only' k₆ y₆, by rw [k₆.get .r28, h28], by rw [k₆.get .r26, h26], hi, fb, hfb,
    by rw [k₆.get .r27, h27]⟩, by rw [p₆.get .r3, p₅.get .r3, p₄.get .r3, p₃.get .r3, p₂.get .r3, f₁, h14],
    ?_, by rw [p₆.get .r5, f₅], by rw [f₆, p₅.get .r14, p₄.get .r14, p₃.get .r14, p₂.get .r14, p₁.get .r14, h14]⟩
  rw [p₆.get .r4, p₅.get .r4, f₄, f₃, f₂, p₁.get .r26, h26, p₂.get .r14, p₁.get .r14, h14,
    ofNat_shl (by rw [hlg]; omega_using [hb]), hlg]
  show _ = Sp ac.1 + _
  rw [BitVec.add_comm (BitVec.ofNat 64 _) (Sp ac.1), BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []

theorem comp_LI {ac : State × Nat} {u : State} (h : CA D Z P ac u) (hb : P.B * ac.2 + P.B ≤ 2048) :
    WP isa (tcall hArg 3 Z.f.comp) u (LI D Z P ac) := by
  obtain ⟨⟨⟨s, Pr, p, b, sy⟩, h28, h26, hi, fb, hfb, h27⟩, h3, h4, h5, h6⟩ := h
  have X := lOk D Z
  have hS : Sp s = Sp ac.1 := (X.agree p).S
  exact WP.mono (compM_ok (X.fits Pr) ((tabH D Z).tab Pr) ok.callee ok.dims.N.2 ok.dims.so.2 b sy (b := P.B * ac.2)
    (by rw [h3, hS]) (by rw [h4, hS]) h5 (by rw [h6, hS]) hb) fun u' ⟨⟨b', g', _⟩, y'⟩ =>
      ⟨⟨s, Pr, p, b', y'⟩, by rw [g' _ (by decide), h28], by rw [g' _ (by decide), h26], hi, fb, hfb,
        by rw [g' _ (by decide), h27]⟩

theorem sel_LI {ac : State × Nat} {u : State} (h : LI D Z P ac u) : WP isa (selHash P) u (LI D Z P ac) := by
  obtain ⟨hnb, hn0⟩ := nbm_le ok h.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, h26, hi, fb, hfb, h27⟩ := h
  have L := agree_lay Pr p
  have hBd := ok.dims.B
  have hn32 : nbmOf D P ac.1 ≤ 32 := by rcases hBd with e | e <;> rw [e] at hnb <;> omega_using [hnb]
  exact WP.of_syms (WP.mono (selHash_ok L ok.dims.N.1 ok.dims.N.2 b h26 h27 (by omega_using [hi, hn32]) (by omega_using [hfb, hn32]))
    fun u' ⟨b', k', _⟩ y => ⟨⟨s, Pr, p, b', y.trans sy⟩, by rw [k'.get .r28, h28], by rw [k'.get .r26, h26], hi,
      fb, hfb, by rw [k'.get .r27, h27]⟩)

/-- After the step of the compression loop. -/
def LS (D : Nat) (Z : Tabs) (P : Params) (ac : State × Nat) (u : State) : Prop :=
  BL D Z ac.1 u ∧ u.gpr .r28 = BitVec.ofNat 64 (nbmOf D P ac.1 - (ac.2 + 1)) ∧
    u.gpr .r26 = BitVec.ofNat 64 (ac.2 + 1) ∧ ∃ fb < nbmOf D P ac.1, u.gpr .r27 = BitVec.ofNat 64 fb

omit ok in
theorem step_LS {ac : State × Nat} {u : State} (h : LI D Z P ac u) :
    WP isa (.block [.addi .r26 .r26 1, .subi .r28 .r28 1]) u (LS D Z P ac) := by
  obtain ⟨hb, h28, h26, hi, fb, hfb, h27⟩ := h
  refine WP.of_syms (wp_addi fun u₁ p₁ f₁ => wp_subi fun u₂ p₂ f₂ => wp_nil fun y₂ => ?_)
  have k₂ : Only [.r26, .r28] u u₂ := (p₁.trans p₂).mono
  refine ⟨hb.only' k₂ y₂, ?_, by rw [p₂.get .r26, f₁, h26, BitVec.ofNat_add_ofNat], fb, hfb,
    by rw [k₂.get .r27, h27]⟩
  rw [f₂, p₁.get .r28, h28, show nbmOf D P ac.1 - ac.2 = (nbmOf D P ac.1 - (ac.2 + 1)) + 1 by omega_using [hi],
    ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel]

omit ok in
theorem ca_args {ac : State × Nat} {t u : State} (h : CA D Z P ac t) (o : Only [.r12] t u) (y : u.syms = t.syms)
    (hb : P.B * ac.2 + P.B ≤ 2048) (hN : P.N ≤ 64) (hso : P.so ≤ 1024) :
    ∃ s, CompArgs Sp (vP D) P s u (P.B * ac.2) ∧ u.gpr .r3 = off (Sp ac.1) oSt ∧
      u.gpr .r4 = off (Sp ac.1) (oY + P.B * ac.2) ∧ u.gpr .r5 = BitVec.ofNat 64 1 ∧ u.gpr .r6 = off (Sp ac.1) oW ∧
      u.sp = fb ac.1 := by
  obtain ⟨⟨hm, -⟩, x3, x4, x5, x6⟩ := h
  obtain ⟨s, Pr, p, b, -⟩ := hm.only' o y
  have X := lOk D Z
  have hS : Sp s = Sp ac.1 := (X.agree p).S
  refine ⟨s, ⟨X.fits Pr, b, by rw [o.get .r3, x3, hS], by rw [o.get .r4, x4, hS], by rw [o.get .r5, x5],
    by rw [o.get .r6, x6, hS], hb, hN, hso⟩, by rw [o.get .r3, x3], by rw [o.get .r4, x4], by rw [o.get .r5, x5],
    by rw [o.get .r6, x6], Base.spA X.s p b⟩

end

theorem hInit_two {α : Type} {Φ : α → State → Prop} {an : α → State} (hH : HashOK Z.H) (cH : HashCT hH)
    (hb : ∀ x t, Φ x t → BL D Z (an x) t) : RelCT isa (Two Φ) (hInit Z.f hArg) fun _ _ => True := by
  have X := lOk D Z
  have A := tabH D Z
  refine RelCT.seq (two_post (Ψ := fun x t => BL D Z (an x) t ∧ t.gpr .r3 = off (Sp (an x)) oSt)
      (st_taint (bl_pins hb [])) fun x t h => WP.of_syms (wp_addi fun t' o e => wp_nil fun y =>
        ⟨(hb x t h).only' o y, by rw [e, (hb x t h).r14]⟩))
    (tcall_twoM X.s A (an := an) (fun x t h => h.1) (k := 0) (by decide)
      (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
      (init_ct (S := Sp) (vf := vP D) cH fun u₁ u₂ hp => ?_))
  obtain ⟨x, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
  obtain ⟨s₁, P₁, p₁, b₁, -⟩ := h₁.1.only' o₁ y₁
  obtain ⟨s₂, P₂, p₂, b₂, -⟩ := h₂.1.only' o₂ y₂
  exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2, (X.agree p₁).S], X.fits P₂, b₂,
    by rw [o₂.get .r3, h₂.2, (X.agree p₂).S], by rw [o₁.get .r3, o₂.get .r3, h₁.2, h₂.2],
    (Base.spA X.s p₁ b₁).trans (Base.spA X.s p₂ b₂).symm⟩

/-- `ctHash` keeps `BL`. -/
theorem ctHash_wp (hH : HashOK Z.H) (hD : Z.H.D = D) (ok : CtOK P md Z.cc Z.dc) {a t : State} (h : BL D Z a t)
    (hs : ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa (ctHash Z.H P Z.f hArg) t (BL D Z a) := by
  refine WP.seq (WP.mono (ctLens_wp ok hD h hs) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (hInit_K1 hH h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (pad80_K1 ok h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (lenField_K2 ok h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (lenLoop_K2 ok h₄) fun t₅ h₅ => ?_)
  obtain ⟨hnb, hn0⟩ := nbm_le ok h₅.1
  obtain ⟨⟨s, Pr, p, b, sy⟩, h28, fb, hfb, h27⟩ := h₅
  have L := agree_lay Pr p
  have X := lOk D Z
  refine WP.seq (WP.mono (compLoop_ok L ((tabH D Z).tab Pr) ok b sy h28 h27 hn0 hnb hfb) fun t₆ I => ?_)
  refine WP.seq (WP.of_syms (wp_addi (h := by decide) fun t₇ o₇ e₇ => wp_addi (h := by decide)
    fun t₈ o₈ e₈ => wp_nil fun y₈ => ?_))
  have k : Only [.r3, .r4] t₆ t₈ := (o₇.trans o₈).mono
  exact WP.mono (digM_ok (X.fits Pr) ((tabH D Z).tab Pr) ok.dig ok.digNF ok.dims.N.2 (I.base.only (X.fits Pr) k)
    (y₈.trans I.sy) (by rw [o₈.get .r3, e₇, I.base.r14]) (by rw [e₈, o₇.get .r14, I.base.r14]))
    fun t' ⟨⟨b', _⟩, y'⟩ => ⟨s, Pr, p, b', y'⟩

/-- `ctHash` from some salt length below `dbLen` in `r25`, in both runs. -/
theorem ctHash_ct (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) (ok : CtOK P md Z.cc Z.dc)
    (ct : CtTaint P) (hcc : ConstantTime isa (compressK md).pre (compressK md).pub Z.cc)
    (hdc : ConstantTime isa (digestK md).pre (digestK md).pub Z.dc) :
    RelCT isa (Two fun a t => BL D Z a t ∧ ∃ sl < (dbLen D a).toNat, t.gpr .r25 = BitVec.ofNat 64 sl)
      (ctHash Z.H P Z.f hArg) fun _ _ => True := by
  have X := lOk D Z
  have A := tabH D Z
  obtain ⟨hlg1, hlg7, hlg⟩ := ok.dims.log
  refine two_seq (Ψ := K1 D Z P) (ctLens_taint Z.H ct (bl_pins (an := id) (fun _ _ h => h.1) []))
    (fun a t h => ctLens_wp ok hD h.1 h.2) ?_
  refine two_seq (Ψ := K1 D Z P) (hInit_two hH cH (an := id) fun _ _ h => h.1) (fun a t h => hInit_K1 hH h) ?_
  refine two_seq (Ψ := K1 D Z P) (pad80_taint ct (pins_r28 (an := id) (fun _ _ h => h.1) fun _ _ h => h.2.1))
    (fun a t h => pad80_K1 ok h) ?_
  refine two_seq (Ψ := K2 D Z P) (lenField_taint ct (bl_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t h => lenField_K2 ok h) ?_
  refine two_seq (Ψ := K2 D Z P) (lenLoop_taint ct (pins_r28 (an := id) (fun _ _ h => h.1) fun _ _ h => h.2.1))
    (fun a t h => lenLoop_K2 ok h) ?_
  refine RelCT.seq (R := Two fun a t => BL D Z a t) ?_ ?_
  · -- The compression loop.
    let Ln := fun (n : Nat) (ac : State × Nat) (u : State) => LI D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2
    have hbB : ∀ {ac u}, LI D Z P ac u → P.B * ac.2 + P.B ≤ 2048 := fun {ac u} h => by
      obtain ⟨hnb, -⟩ := nbm_le ok h.1
      have hi := h.2.2.2.1
      calc P.B * ac.2 + P.B = P.B * (ac.2 + 1) := (Nat.mul_succ _ _).symm
        _ ≤ P.B * nbmOf D P ac.1 := Nat.mul_le_mul_left _ hi
        _ = nbmOf D P ac.1 * P.B := Nat.mul_comm _ _
        _ ≤ 2048 := hnb
    have step : ∀ n, RelCT isa (Two (Ln n)) (.seq (.block (compArgs P)) (.seq (tcall hArg 3 Z.f.comp)
        (.seq (selHash P) (.block [.addi .r26 .r26 1, .subi .r28 .r28 1])))) fun s₁ s₂ =>
        isa.eval (.nonzero .d .r28) s₁ = isa.eval (.nonzero .d .r28) s₂ ∧
        (isa.eval (.nonzero .d .r28) s₁ = some false → Two (fun a t => BL D Z a t) s₁ s₂) ∧
        (isa.eval (.nonzero .d .r28) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
      refine two_seq (Ψ := fun ac u => CA D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2)
        (compArgs_taint ct (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) []))
        (fun ac u h => (compArgs_CA h.1 hlg hlg7 (hbB h.1)).mono fun u' h' => ⟨h', h.2⟩) ?_
      refine two_seq (Ψ := Ln n) (tcall_twoM X.s A (an := Prod.fst) (fun ac t h => h.1.1.1) (k := 3) (by decide)
          (fun P p => ⟨(A.tab P).ok.c, by rw [show 8 * 3 = 24 from rfl]; exact (A.tab P).mc, A.ac p⟩)
          (comp_ct (S := Sp) (vf := vP D) ok.callee hcc fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_))
        (fun ac u h => (comp_LI ok h.1 (hbB h.1.1)).mono fun u' h' => ⟨h', h.2⟩) ?_
      · obtain ⟨s₁, C₁, x3, x4, x5, x6, xs⟩ := ca_args h₁.1 o₁ y₁ (hbB h₁.1.1) ok.dims.N.2 ok.dims.so.2
        obtain ⟨s₂, C₂, z3, z4, z5, z6, zs⟩ := ca_args h₂.1 o₂ y₂ (hbB h₂.1.1) ok.dims.N.2 ok.dims.so.2
        refine ⟨s₁, s₂, _, _, C₁, C₂, fun r hr => ?_, xs.trans zs.symm⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [x3.trans z3.symm, x4.trans z4.symm, x5.trans z5.symm, x6.trans z6.symm]
      refine two_seq (Ψ := Ln n) (selHash_taint ct (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) [.r14]))
        (fun ac u h => (sel_LI ok h.1).mono fun u' h' => ⟨h', h.2⟩) ?_
      refine (two_post (Ψ := fun ac u => LS D Z P ac u ∧ n = nbmOf D P ac.1 - ac.2 ∧ ac.2 < nbmOf D P ac.1)
        (compStep_taint (bl_pins (an := Prod.fst) (fun _ _ h => h.1.1) []))
        fun ac u h => (step_LS h.1).mono fun u' h' => ⟨h', h.2, h.1.2.2.2.1⟩).mono (fun _ _ h => h)
          fun s₁ s₂ ⟨ac, ⟨h₁, hn, hi⟩, ⟨h₂, _, _⟩⟩ => ?_
      have hnb' : nbmOf D P ac.1 - (ac.2 + 1) < 2 ^ 64 := by
        have := (nbm_le ok h₁.1).1
        have : nbmOf D P ac.1 ≤ nbmOf D P ac.1 * P.B := Nat.le_mul_of_pos_right _ ok.dims.pos
        omega_arith
      rw [eval_nonzero, eval_nonzero, h₁.2.1, h₂.2.1, ne0_ofNat hnb']
      refine ⟨rfl, fun _ => ⟨ac.1, h₁.1, h₂.1⟩, fun e => ?_⟩
      have hlt : ac.2 + 1 < nbmOf D P ac.1 := by simp only [Option.some.injEq, decide_eq_true_eq] at e; omega_using [e]
      exact ⟨nbmOf D P ac.1 - (ac.2 + 1), by omega_using [hn, hi], (ac.1, ac.2 + 1),
        ⟨⟨h₁.1, h₁.2.1, h₁.2.2.1, hlt, h₁.2.2.2⟩, rfl⟩, ⟨⟨h₂.1, h₂.2.1, h₂.2.2.1, hlt, h₂.2.2.2⟩, rfl⟩⟩
    refine RelCT.seq (two_post (Ψ := fun a t => LI D Z P (a, 0) t)
        (compInit_taint (bl_pins (an := id) (fun _ _ h => h.1) [])) fun a t h => ?_)
      ((RelCT.exists_ fun n => RelCT.loop (fun n => Two (Ln n)) step n).mono
        (fun _ _ ⟨a, h₁, h₂⟩ => ⟨nbmOf D P a - 0, (a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
    obtain ⟨-, hn0⟩ := nbm_le ok h.1
    obtain ⟨hm, h28, fb, hfb, h27⟩ := h
    exact WP.of_syms (wp_li (by decide) fun t' o e => wp_nil fun y =>
      ⟨hm.only' o y, by rw [o.get .r28, h28, Nat.sub_zero], e, hn0, fb, hfb, by rw [o.get .r27, h27]⟩)
  · -- The digest.
    have hN := ok.dims.N
    refine two_seq (Ψ := fun a t => BL D Z a t ∧ t.gpr .r3 = off (Sp a) oSel ∧ t.gpr .r4 = off (Sp a) oDig)
      (digArgs_taint (bl_pins (an := id) (fun _ _ h => h) [])) (fun a t h => WP.of_syms (wp_addi (h := by decide)
        fun t₁ o₁ e₁ => wp_addi (h := by decide) fun t₂ o₂ e₂ => wp_nil fun y => ?_)) ?_
    · have k : Only [.r3, .r4] t t₂ := (o₁.trans o₂).mono
      exact ⟨h.only' k y, by rw [o₂.get .r3, e₁, h.r14], by rw [e₂, o₁.get .r14, h.r14]⟩
    refine tcall_twoM X.s A (an := id) (fun a t h => h.1) (k := 4) (by decide)
      (fun P p => ⟨(A.tab P).ok.d, by rw [show 8 * 4 = 32 from rfl]; exact (A.tab P).md, A.ad p⟩)
      (dig_ct (S := Sp) (vf := vP D) (P := P) ok.dig hdc fun u₁ u₂ ⟨a, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := h₁.1.only' o₁ y₁
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := h₂.1.only' o₂ y₂
    have S₁ : Sp s₁ = Sp a := (X.agree p₁).S
    have S₂ : Sp s₂ = Sp a := (X.agree p₂).S
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2.1, S₁], by rw [o₁.get .r4, h₁.2.2, S₁], hN.2⟩,
      ⟨X.fits P₂, b₂, by rw [o₂.get .r3, h₂.2.1, S₂], by rw [o₂.get .r4, h₂.2.2, S₂], hN.2⟩, fun r hr => ?_,
      (Base.spA X.s p₁ b₁).trans (Base.spA X.s p₂ b₂).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o₁.get .r3, o₂.get .r3, h₁.2.1, h₂.2.1]
    · rw [o₁.get .r4, o₂.get .r4, h₁.2.2, h₂.2.2]

end CtHash

end VG.Proof.RsaPss.PPC64LE

end

end

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

end

end

/-!
# RSASSA-PSS verification on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data and tables (`PreT`, `PubT`), whose hash
function's table holds the same index, leak alike (`code_ct`): the load of
the index and the choice by it (`byIdx_ct`), the checks'
blocks by the taint analysis and their branches by `two_ite`, on values both
runs compute from the public data (the modulus' first byte, its length and
the salt-length mode and length); the call of
`vg_rsa_public_precomputed_checked` by its contract (`pdCallCT`); and the
rest by `post_ct`, from the states `BL` after the call.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore oRsa arg tword)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (compressK)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits off fx kR Agree Ok B pins_of two_seq HashCT words_entry bytes_entry
  allocated_sp allocated_gpr restore_taint Saves fb SC TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc eval_zero eval_nonzero pdCallCT)
open VG.Proof.Mgf1 (ifp ifn)

/-- An entry state, with the tables. -/
abbrev PreT (Z : Tabs) (D : Nat) (s : State) : Prop := PreP D s ∧ TabsOn Z s

/-- The anchor's public data and tables. -/
abbrev PubT (Z : Tabs) (a s : State) : Prop := PubK a s ∧ TabsAg Z a s

section
variable {D : Nat} {Z : Tabs}

theorem tOk : Ok Sp (vP D) (PreT Z D) (PubT Z) := ⟨fun P => P.1.fits, fun p => p.1.1.agree p.1.2⟩

/-- An entry state with the anchor's public data, and `Base` from it. -/
theorem pk_pins {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → ∃ s, PreT Z D s ∧ PubT Z (an x) s ∧ Base Sp (vP D) s t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of tOk h rs hrs

theorem call_ct : RelCT isa (Two fun a t => ∃ s, PreT Z D s ∧ PubT Z a s ∧ AtCall D s t)
    Impl.RsaPkcs1Sig.PPC64LE.pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩ => ⟨pdOk_of P₁.1 c₁, pdOk_of P₂.1 c₂,
    ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.base.sp, c₂.base.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, p₁.1.1.pSp, p₂.1.1.pSp]
    · rw [c₁.g4, c₂.g4, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.1.1.args 4 (by decide) (by decide), p₂.1.1.args 4 (by decide) (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.1.1.args 5 (by decide) (by decide), p₂.1.1.args 5 (by decide) (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g8, c₂.g8, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g9, c₂.g9, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
    · rw [c₁.g10, c₂.g10, p₁.1.1.g _ (by decide), p₂.1.1.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.1.1.pSp, p₂.1.1.pSp]
  · rw [c₁.a1, c₂.a1, p₁.1.1.args 3 (by decide) (by decide), p₂.1.1.args 3 (by decide) (by decide)]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_entry c₁.base.mem P₁.1.kp ((P₁.1.sp).sub_left (sc_sub P₁.1)) P₁.1.wp,
      words_entry c₂.base.mem P₂.1.kp ((P₂.1.sp).sub_left (sc_sub P₂.1)) P₂.1.wp, p₁.1.1.w, p₂.1.1.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8,
      bytes_entry c₁.base.mem P₁.1.ke ((P₁.1.es.symm).sub_left (sc_sub P₁.1)) (by have := P₁.1.we; omega_arith),
      bytes_entry c₂.base.mem P₂.1.ke ((P₂.1.es.symm).sub_left (sc_sub P₂.1)) (by have := P₂.1.we; omega_arith),
      p₁.1.1.e, p₂.1.1.e]

end

/-- The checks passed, for an entry state. -/
structure Ck (D : Nat) (s : State) : Prop where
  h0 : s.mem (s.gpr .r3) ≠ 0
  em : D + 2 ≤ kk s - loN s
  fit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - D - 1

section
variable {Z : Tabs} {Gs Gm : Spec.Mgf1.Hash} (hH : HashOK Z.H) (cH : HashCT hH)
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = Z.H.D) (hHv : Proof.Mgf1.Valid Gs)
  (hG : HashOK Z.G) (cG : HashCT hG) (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = Z.G.D)
  (hGmv : Proof.Mgf1.Valid Gm) {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md Z.cc Z.dc)
  (ct : CtTaint P') (hcc : ConstantTime isa (compressK md).pre (compressK md).pub Z.cc)
  (hdc : ConstantTime isa (digestK md).pre (digestK md).pub Z.dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : Z.H.N = P'.N) (hB : Z.H.B = P'.B)

include hH hGl in
/-- After the call, from an entry state that passed the checks. -/
theorem bl_after {a s t : State} (P : PreT Z Gs.len s) (p : PubT Z a s) (c : AfterCall Gs.len s t)
    (sy : t.syms = s.syms) (C : Ck Gs.len s) : BL Gs.len Z a t ∧ Fit Gs.len a := by
  have L := lay_reE P.1 hH hGl c.mem C.h0 C.em
  have g := p.1.1.agree (D := Gs.len) p.1.2
  have hS := reE_Sp P.1 c.mem
  have hSC : SC Sp (reE s t.mem) = SC Sp s := by simp only [SC, hS]
  have hA : ∀ j < 8, ∀ r ∈ [kR s, scR s], Region.Disjoint ⟨stackArgAddr s j, 8⟩ r := fun j hj r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.ka.sub_right (in_aR_sub hj)).symm
    · exact (P.1.sa.sub_right (in_aR_sub hj)).symm
  have Tg' : TabS Z.G Z.g gArg Sp (reE s t.mem) (stackArg s 7) := P.2.1.transfer rfl rfl rfl hSC c.mem (hA 7 (by decide)) fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.ktg.sub_right (tab_sub (n := 11) (by omega_using [hk]))).symm
    · exact (P.1.stg.sub_right (tab_sub (n := 11) (by omega_using [hk]))).symm
  have T' : MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp (reE s t.mem) (stackArg s 6) := P.2.2.transfer rfl rfl rfl hSC c.mem (hA 6 (by decide)) fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.1.kth.sub_right (tab_sub (n := 11) hk)).symm
    · exact (P.1.sth.sub_right (tab_sub (n := 11) hk)).symm
  have e6 := reE_args P.1 c.mem 6 (by decide)
  have e7 := reE_args P.1 c.mem 7 (by decide)
  have g' : Agree Sp (vP Gs.len) a (reE s t.mem) :=
    ⟨(reE_sp _ _).trans p.1.1.sp, hS.trans p.1.1.pSp, fun r hr => by rw [reE_vP P.1 c.mem]; exact g.v r hr⟩
  have q := p.2
  refine ⟨⟨reE s t.mem, ⟨L.canon, by rw [TabsOn, e6, e7]; exact ⟨Tg', T'⟩⟩,
    ⟨g', by rw [e7]; exact q.1, q.2.1, q.2.2.1, q.2.2.2.1, by rw [e6]; exact q.2.2.2.2.1, q.2.2.2.2.2⟩, c.base, sy⟩,
    fun ha => ?_⟩
  have hk2 : kk s ≤ 1024 := P.1.k2
  have e21 : dbLen Gs.len s = dbLen Gs.len a := g.v .r21 (by decide)
  have hdb : (dbLen Gs.len (reE s t.mem)).toNat = kk s - loN s - Gs.len - 1 := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have e : dbLen Gs.len (reE s t.mem) = dbLen Gs.len s := by
    unfold dbLen; rw [lo_reE P.1 c.mem]; rfl
  rw [← e21, ← e, hdb, ← p.1.1.args 0 (by decide) (by decide)]
  exact C.fit (by rw [p.1.1.pAny]; exact ha)

include hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc in
theorem main_ct : RelCT isa (Two fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Before Gs.len s t ∧
      t.syms = s.syms ∧ Ck Gs.len s) (verifyMain Z.H P' Z.f Z.g) fun _ _ => True := by
  refine two_seq (Ψ := fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ AtCall Gs.len s t ∧ t.syms = s.syms ∧
      Ck Gs.len s)
    (pubArgs_taint (pk_pins (fun _ _ ⟨s, P, p, B, _⟩ => ⟨s, P, p, B.base⟩) []))
    (fun a t ⟨s, P, p, B, sy, C⟩ => WP.mono_syms (pubArgs_ok P.1 B) fun t' c y => ⟨s, P, p, c, y.trans sy, C⟩) ?_
  refine two_seq (Ψ := fun a t => BL Gs.len Z a t ∧ Fit Gs.len a)
    (call_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, c₁, _⟩, ⟨s₂, P₂, p₂, c₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, p, c, sy, C⟩ => WP.mono_syms (call_ok P.1 c) fun t' c' y =>
      bl_after hH hGl P p c' (y.trans sy) C) ?_
  exact post_ct hH cH hGl.symm hG cG hGmh hGml hGmv ok ct hcc hdc

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (Z : Tabs) (D : Nat) (a t : State) : Prop :=
  ∃ s, PreT Z D s ∧ PubT Z a s ∧ Entered D s t ∧ t.syms = s.syms

include hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc in
theorem checks_ct : RelCT isa (Two (En Z Gs.len)) (checks Z.H P' Z.f Z.g) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Z Gs.len a t) → Pins Φ [] := fun h =>
    pk_pins (an := id) (fun a t hp => let ⟨s, P, p, E, _⟩ := h a t hp; ⟨s, P, p, E.base⟩) []
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, p₁.1.1.pN0 p₁.1.2, p₂.1.1.pN0 p₂.1.2])
    (fail_taint (pin fun _ _ h => h.1)) ?_
  let E1 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered Gs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r3) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2))
    (chkEm_taint Z.H (pin fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, E, sy⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hGl hD64 E h0) fun t' ⟨E', r3⟩ y =>
      ⟨⟨s, P, p, E', y.trans sy, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩)) ?_
  let E2 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered Gs.len s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r3) ≠ 0 ∧ Gs.len + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Gs.len + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, sy, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Gs.len + 2 := by simpa using hc
    exact ⟨s, P, p, E, sy, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega_arith⟩
  -- The salt length expected.
  let E3 := fun (a t : State) => E2 a t ∧ t.gpr .r4 = if anyL a = 0 then stackArg a 0 else 0
  refine two_seq (Ψ := E3) (expLen_taint (pk_pins (an := id) (fun a t hp =>
      let ⟨s, P, p, E, _⟩ := e2 hp; ⟨s, P, p, E.base⟩) [.r20]))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, sy, h0, hem⟩ := e2 h
    exact WP.mono_syms (expLen_ok E.base.pany E.base.psl) fun t' ⟨o, e⟩ y =>
      ⟨⟨s, P, p, E.only P.1 o, y.trans sy, h0, hem⟩, by
        rw [e, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)]⟩
  refine two_seq (Ψ := fun a t => E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat))
    (chkSalt_taint Z.H (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1; ⟨s, P, p, E, sy⟩))
    (fun a t ⟨⟨s, P, p, E, sy, h0, hem⟩, h4⟩ => WP.mono_syms (chkSalt_ok P.1 hGl hD64 E h0 hem
      (by rw [h4, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)])) fun t' ⟨E', r3⟩ y =>
        ⟨⟨s, P, p, E', y.trans sy, h0, hem⟩, by
          rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2, p.1.1.pAny, p.1.1.args 0 (by decide) (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩)) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧ (t.gpr .r3 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat)) ∧
      isa.eval (.nonzero .d .r3) t = some false →
      ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Before Gs.len s t ∧ t.syms = s.syms ∧ Ck Gs.len s :=
    fun {a t} ⟨⟨⟨s, P, p, E, sy, h0, hem⟩, c⟩, hc⟩ => by
      rw [eval_nonzero, c] at hc
      have hn : ¬ kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then stackArg a 0 else 0).toNat := by simpa using hc
      refine ⟨s, P, p, E.before, sy, h0, hem, fun ha => ?_⟩
      rw [← p.1.1.pAny, ifp ha, ← p.1.1.args 0 (by decide) (by decide), ← p.1.1.pKk, ← p.1.1.pLoN p.1.2] at hn
      omega_arith
  exact (main_ct hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

/-- After the frame's push and the choice by the index, from an entry state. -/
abbrev Ix (Z : Tabs) (D i : Nat) (a u : State) : Prop :=
  ∃ s, (PreT Z D s ∧ PubT Z a s) ∧ Only [.r11, .r12] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i

include hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB in
/-- The frame's body, for the hash function's sizes. -/
theorem body_ct {i : Nat} : RelCT isa (Two (Ix Z Gs.len i)) (body Z.H P' Z.f Z.g) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine two_seq (Ψ := En Z Gs.len)
    (entry_taint Z.H fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => ⟨by rw [o₁.sp, o₂.sp, allocated_sp,
      allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, o₁.get .r3, o₂.get .r3, allocated_gpr, allocated_gpr, h₁.2.1.1.g .r3 (by decide),
          h₂.2.1.1.g .r3 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, o, sy, _⟩ => WP.mono_syms (entry_ok P.1 hGl.symm hD64 o) fun t E y =>
      ⟨s, P, p, E, y.trans sy⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Saves s t)
    (checks_ct hH cH hGl hG cG hGmh hGml hGmv ok ct hcc hdc) fun a t ⟨s, P, p, E, sy⟩ =>
      WP.mono (checks_done P.1 hH hGh hGl hHv hG P.2.1 hGmh hGml hGmv P.2.2 ok hl hN hB E sy) fun t' d =>
        ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

include hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB in
/-- Two runs of `vg_rsa_pss_verify_precomputed` from entry states with the
same public data and tables, whose hash function's table holds the index
`i` of `H`'s sizes, leak alike. -/
theorem code_ct {i : Nat} (hi : i ∈ idxs) (hD : (shapeOf i).1.D = Z.H.D) (hP : (shapeOf i).2 = P') :
    RelCT isa (Two fun a s => (PreT Z Gs.len s ∧ PubT Z a s) ∧
      s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
      (verifyPrecomputed Z.f Z.g) fun _ _ => True := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.1.2.1.1.sp.trans h₂.1.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  let A0 := fun (a s : State) => (PreT Z Gs.len s ∧ PubT Z a s) ∧
    s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i
  let A1 := fun (a u : State) => ∃ s, A0 a s ∧ Only [.r11] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = stackArg s 6
  let A2 := fun (a u : State) => ∃ s, A0 a s ∧ Only [.r11] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i
  have spA : ∀ {a s₁ s₂ : State}, A0 a s₁ → A0 a s₂ → (allocated frameBytes s₁).sp = (allocated frameBytes s₂).sp :=
    fun h₁ h₂ => by rw [allocated_sp, allocated_sp, h₁.1.2.1.1.sp, h₂.1.2.1.1.sp]
  show RelCT isa _ (.seq (.block ([.addSp .r11 0, .load .d .r11 .r11 (arg hArg)] ++ [.load .d .r11 .r11 (8 * 5)]))
    _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := A1)
      (twA11_taint hArg fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; exact spA h₁ h₂, fun _ h => nomatch h⟩)
      fun a u ⟨s, h, e⟩ => ?_)
    (two_post (Ψ := A2) (twB11_taint (8 * 5) fun a u₁ u₂ ⟨s₁, h₁, o₁, _, e₁⟩ ⟨s₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact spA h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂, h₁.1.2.1.1.args 6 (by decide) (by decide),
          h₂.1.2.1.1.args 6 (by decide) (by decide)]⟩) fun a u ⟨s, h, o, y, e⟩ => ?_))) ?_
  · subst e
    exact WP.of_syms ((argA_ok (j := hArg) (by decide) ⟨aR s, by rw [h.1.1.1.hrd]; simp, in_aR (by decide)⟩
      (h.1.1.1.ka.sub_right (in_aR_sub (by decide))).symm).mono fun u' ⟨o', e'⟩ y => ⟨s, h, o', y, e'⟩)
  · have P := h.1.1.1
    exact WP.of_syms ((wordA_ok o e (by decide) ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide)
      (by decide)⟩ (P.kth.sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm).mono fun u' ⟨o', e'⟩ y' =>
        ⟨s, h, o', y'.trans y, by rw [e']; exact h.2⟩)
  refine byIdx_ct (D := i) (by omega_using [hi8]) (Φ := Ix Z Gs.len i)
    (fun _ _ ⟨_, _, _, _, e⟩ => e) (fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => by
      rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp])
    (fun a u u' ⟨s, h, o, y, e⟩ o' y' => ⟨s, h, (o.trans o').mono, y'.trans y, by rw [o'.get .r11]; exact e⟩)
    ?_ hi idxs_certs |>.mono (fun _ _ ⟨a, ⟨s₁, h₁, o₁, y₁, e₁⟩, ⟨s₂, h₂, o₂, y₂, e₂⟩⟩ =>
      ⟨a, ⟨s₁, h₁.1, o₁.mono, y₁, e₁⟩, ⟨s₂, h₂.1, o₂.mono, y₂, e₂⟩⟩) fun _ _ h => h
  · rw [body_D hD, hP]
    exact body_ct hH cH hGh hGl hHv hG cG hGmh hGml hGmv ok ct hcc hdc hl hN hB

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS signing on PPC64LE: the public data

Untrusted: everything here is checked by Lean. The shared contract's public
data (`PubS`, `pubS_of`): the stack pointer, the pointers and lengths (all
the arguments), the modulus and `e`. An entry state with the anchor's public
data has its modulus' first byte (`PubS.byte`), so its `lo`, and agrees with
it on what `Base` fixes (`signOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE (Agree Ok B fx)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The shared contract's public data, by name. -/
structure PubS (pc : Bool) (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 16, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r5) (a.gpr .r6).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  pre : pc = true → stackArg s 16 = stackArg a 16 ∧ stackArg s 17 = stackArg a 17 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 16) (Spec.Rsa.precomputedWords (a.gpr .r6).toNat)

/-- The contract's public data: `PubS`, the tables' functions at the same
addresses, and the same tables held. -/
theorem pubS_of {hs gs : List FnTable} {s₁ s₂ : State} (h : (signSpec hs gs).pub s₁ s₂) :
    PubS false s₁ s₂ ∧
      (∀ f ∈ (hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ hs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  have e : stackBytes false = 3775 + 1 := rfl
  unfold signSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_sixteen, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, htab', hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h
  have hl' := hl
  simp only [List.map_append] at hl'
  obtain ⟨hn, he⟩ := List.append_inj hl' (by simp [bytesAt_length, h6])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm, fun h => nomatch h⟩, hsy,
    fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm]

theorem pubS_refl (s : State) : PubS pc s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

section
variable {a s : State} (p : PubS pc a s)
include p

theorem PubS.pKk : kk s = kk a := by rw [kk, kk, p.g .r6 (by decide)]

theorem PubS.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .r5) = a.mem (a.gpr .r5) := by
  have := congrArg (·.getD 0 0) p.n
  rwa [VG.Proof.RsaPkcs1Sig.bytesAt_getD hk, VG.Proof.RsaPkcs1Sig.bytesAt_getD (by have := p.pKk; unfold kk at this hk; omega_using [hk, this]),
    BitVec.add_zero, BitVec.add_zero] at this

theorem PubS.pLo (hk : 1 ≤ kk s) : loS s = loS a := by simp only [loS, p.byte hk]

theorem PubS.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubS.agree (hk : 1 ≤ kk s) : Agree Ss vS a s := ⟨p.sp, p.args 12 (by decide), fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vS]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.args 11 (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk⟩

end

/-- `PubS`, for a nonempty modulus. -/
def PubK (pc : Bool) (a s : State) : Prop := PubS pc a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs, for an entry state with
`PreS`. -/
theorem signOk (D : Nat) {Pre : State → Prop} {Pub : State → State → Prop} (hP : ∀ {s}, Pre s → PreS pc D s)
    (hQ : ∀ {a s}, Pub a s → PubK pc a s) : Ok Ss vS Pre Pub where
  fits P := fits (hP P)
  agree p := (hQ p).1.agree (hQ p).2

end VG.Proof.RsaPss.PPC64LE.Sg
