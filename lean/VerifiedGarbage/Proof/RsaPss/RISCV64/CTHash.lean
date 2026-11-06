module

-- separate module: it builds in parallel with the correctness proofs after the scan (`Finish` to `Post`),
-- which `CTPost` also needs.

import VerifiedGarbage.Proof.RsaPss.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPss.RISCV64.Select
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.RsaPss.RISCV64.CTTab
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Hash
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
salt length, its blocks by the taint analysis and its calls by `hInit_two`,
`upd_ct` and `fin_ct`. After the public operation of verification, two runs
are compared through the anchor with `BL`: `Base` from entry states whose
encoding parameters are those of their registers (`PreL`) and that agree
with the anchor on what `Base` fixes. `hashAny_ct`: for any salt length,
the loop over the lengths (`round_two`), whose counters both runs agree on.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oSt oDig oRsa tcall Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off fx fixed Agree Ok OkS Ok.s B B.agree B.only B.spS
  B.s0S BT BT.b TabA TabS pins_of two_seq HashCT sdis sc_cov cR_dis hfits offs st_taint)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-! ## Any function's hash calls through its table -/

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {H : Hash} {hH : HashOK H} {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat}
  (A : TabAM M dN f j S Pre Pub) (cH : HashCT hH) (hF : H.F ≤ 208) {α : Type} {an : α → State}

omit A in
include X in
theorem bt_only {a t t' : State} {rs : List Reg} (h : BT S vf Pre Pub a t) (o : Only rs t t')
    (y : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : BT S vf Pre Pub a t' :=
  let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only (X.fits P) o hrs, y.trans sy⟩

omit A in
include X in
theorem bt_pins {Φ : α → State → Prop} (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t) : Pins Φ [] :=
  fun x t₁ t₂ h₁ h₂ => ⟨((h x t₁ h₁).b.spS X).trans ((h x t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩

omit A in
include X in
theorem bt_s0 {a t : State} (h : BT S vf Pre Pub a t) : t.gpr .s0 = S a := h.b.s0S X

include X A cH in
/-- `init` through the table, in both runs. -/
theorem hInit_two {Φ : α → State → Prop} (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t) :
    RelCT isa (Two Φ) (hInit f j) fun _ _ => True :=
  two_seq (Ψ := fun x u => BT S vf Pre Pub (an x) u ∧ u.gpr .a0 = off (S (an x)) oSt) (st_taint (bt_pins X h))
    (fun x t hp => WP.of_syms (wp_addi (imm := oSt) fun t' o e => wp_nil fun sy =>
      ⟨bt_only X (h x t hp) o sy, by rw [e, bt_s0 X (h x t hp)]⟩))
    (initM_two X A cH fun _ _ h => h)

include X A hF in
theorem hInit_wp {a t : State} (h : BT S vf Pre Pub a t) :
    WP isa (hInit f j) t fun t' => BT S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, p, b, sy⟩ := h
  exact WP.mono (hInit_ok (X.fits P) hF (A.tab P) b sy) fun t' ⟨⟨b', g', _⟩, y'⟩ => ⟨⟨s, P, p, b', y'⟩, g'⟩

include X A cH hF in
/-- `update` through the table, in both runs with the same arguments. -/
theorem hUpd_two {Φ : α → State → Prop} {o len : α → Nat}
    (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t ∧ oY ≤ o x ∧ o x + len x ≤ oRsa ∧
      t.gpr .a2 = off (S (an x)) (o x) ∧ (t.gpr .a3).toNat = len x)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .a1 = t₂.gpr .a1) :
    RelCT isa (Two Φ) (hUpd f j) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, hSt, _, _, hR⟩ := offs
  have hY : oY = 2048 := rfl
  let Ψ := fun (x : α) (u : State) => ∃ t, Φ x t ∧ Only [.a0] t u ∧ u.syms = t.syms ∧
    u.gpr .a0 = off (S (an x)) oSt
  refine two_seq (Ψ := Ψ) (st_taint (bt_pins X fun x t hp => (h x t hp).1))
    (fun x t hp => WP.of_syms (wp_addi (imm := oSt) fun t' oo e => wp_nil fun sy =>
      ⟨t, hp, oo, sy, by rw [e, bt_s0 X (h x t hp).1]⟩)) ?_
  refine updM_two (vf := vf) (an := an) X A cH hF (fun x u ⟨t, hp, oo, y, e0⟩ => ?_)
    (fun x u₁ u₂ ⟨t₁, h₁, o₁, _, e₁⟩ ⟨t₂, h₂, o₂, _, e₂⟩ r hq => ?_)
  · obtain ⟨⟨s, P, p, b, sy⟩, ho, hl, h2, h3⟩ := h x t hp
    have hS : S s = S (an x) := X.S p
    have b' := b.only (X.fits P) oo
    exact ⟨s, off (S s) (o x), len x, P, p, ⟨X.fits P, b', by rw [e0, hS], by rw [oo.get .a2, h2, hS],
      by rw [oo.get .a3, h3], Covers.right (by rw [b'.wr]; exact sc_cov (X.fits P) hl),
      sdis (.inr (by omega)) hl (by omega), cR_dis (X.fits P) hl⟩, y.trans sy⟩
  · obtain ⟨-, -, -, x2, x3⟩ := h x t₁ h₁
    obtain ⟨-, -, -, z2, z3⟩ := h x t₂ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [e₁, e₂]
    · rw [o₁.get .a1, o₂.get .a1]; exact hr x t₁ t₂ h₁ h₂
    · rw [o₁.get .a2, o₂.get .a2, x2, z2]
    · rw [o₁.get .a3, o₂.get .a3]; exact BitVec.eq_of_toNat_eq (x3.trans z3.symm)

include X A hF in
theorem hUpd_wp {a t : State} (h : BT S vf Pre Pub a t) {o len : Nat} (ho : oY ≤ o) (hl : o + len ≤ oRsa)
    (h2 : t.gpr .a2 = off (S a) o) (h3 : (t.gpr .a3).toNat = len) :
    WP isa (hUpd f j) t fun t' => BT S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  have F := hfits hH
  obtain ⟨_, hSt, _, _, hR⟩ := offs
  have hY : oY = 2048 := rfl
  obtain ⟨s, P, p, b, sy⟩ := h
  have hS := X.S p
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil fun sy₁ => ?_))
  have b₁ := b.only (X.fits P) o₁
  exact WP.mono (updM_ok (A.tab P) (X.fits P) hF b₁ (sy₁.trans sy) (dat := off (S s) o) (len := len)
    (by rw [e₁, b.s0]) (by rw [o₁.get .a2, h2, hS]) (by rw [o₁.get .a3, h3])
    (Covers.right (by rw [b₁.wr]; exact sc_cov (X.fits P) hl)) (sdis (.inr (by omega)) hl (by omega))
    (cR_dis (X.fits P) hl))
    fun t' ⟨⟨b', g, _, _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr]⟩

include X A cH hF in
/-- `finalize` through the table, in both runs after the same number of bytes. -/
theorem hFin_two {Φ : α → State → Prop} (h : ∀ x t, Φ x t → BT S vf Pre Pub (an x) t)
    (hr : ∀ x t₁ t₂, Φ x t₁ → Φ x t₂ → t₁.gpr .a1 = t₂.gpr .a1) :
    RelCT isa (Two Φ) (hFin f j) fun _ _ => True := by
  let Ψ := fun (x : α) (u : State) => ∃ t, Φ x t ∧ Only [.a0, .a2] t u ∧ u.syms = t.syms ∧
    u.gpr .a0 = off (S (an x)) oSt ∧ u.gpr .a2 = off (S (an x)) oDig
  refine two_seq (Ψ := Ψ) (finRegs_taint (bt_pins X h))
    (fun x t hp => WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := oDig) (h := by decide)
      fun t₂ o₂ e₂ => wp_nil fun sy => ⟨t, hp, (o₁.trans o₂).mono, sy, by rw [o₂.get .a0, e₁, bt_s0 X (h x t hp)],
        by rw [e₂, o₁.get .s0, bt_s0 X (h x t hp)]⟩)) ?_
  refine finM_two (vf := vf) (an := an) X A cH hF (fun x u ⟨t, hp, o, y, e0, e2⟩ => ?_)
    (fun x u₁ u₂ ⟨t₁, h₁, o₁, _, x0, x2⟩ ⟨t₂, h₂, o₂, _, z0, z2⟩ r hq => ?_)
  · obtain ⟨s, P, p, b, sy⟩ := h x t hp
    exact ⟨s, P, p, ⟨X.fits P, b.only (X.fits P) o, by rw [e0, X.S p], by rw [e2, X.S p]⟩, y.trans sy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [x0, z0]
    · rw [o₁.get .a1, o₂.get .a1]; exact hr x t₁ t₂ h₁ h₂
    · rw [x2, z2]

include X A hF in
theorem hFin_wp {a t : State} (h : BT S vf Pre Pub a t) :
    WP isa (hFin f j) t fun t' => BT S vf Pre Pub a t' ∧ ∀ r ∈ preserved, t'.gpr r = t.gpr r := by
  obtain ⟨s, P, p, b, sy⟩ := h
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := oDig) (h := by decide)
    fun t₂ o₂ e₂ => wp_nil fun sy₂ => ?_))
  have k₂ : Only [.a0, .a2] t t₂ := (o₁.trans o₂).mono
  exact WP.mono (finM_ok (A.tab P) (X.fits P) hF (b.only (X.fits P) k₂) (sy₂.trans sy)
    (by rw [o₂.get .a0, e₁, b.s0]) (by rw [e₂, o₁.get .s0, b.s0]))
    fun t' ⟨⟨b', g, _, _⟩, y⟩ => ⟨⟨s, P, p, b', y⟩, fun r hr => by rw [g r hr, pres_of k₂ (by decide) r hr]⟩

include X A cH hF in
/-- `H' = Hash(M')` for the salt length `sl a` in `s6`, in both runs. -/
theorem hashFixedG_ct (hal : ∀ {s}, Pre s → (S s).toNat % 8 = 0) (sl : State → BitVec 64) :
    RelCT isa (Two fun a t => BT S vf Pre Pub a t ∧ t.gpr .s6 = sl a ∧ (sl a).toNat + 8 + H.D ≤ 1880)
      (hashFixed H M.be f j) fun _ _ => True := by
  have F := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := hH.hD64
  have hY : oY = 2048 := rfl
  have hCs : oCs = 1664 := rfl
  obtain ⟨hL, hL8⟩ := M.hL
  have hB : H.B = 2 ^ H.b := rfl
  have hB' : H.B = 64 ∨ H.B = 128 := by rcases hH.hb with e | e <;> simp [hB, e]
  have hB0 : 0 < H.B := by omega
  have hL' : M.L ≤ 16 := by rcases hB' with e | e <;> rw [hL, e] <;> decide
  let K := fun (a t : State) => BT S vf Pre Pub a t ∧ t.gpr .s6 = sl a ∧ (sl a).toNat + 8 + H.D ≤ 1880
  -- `init`.
  refine two_seq (Ψ := K) (hInit_two X A cH (an := id) fun _ _ h => h.1)
    (fun a t h => WP.mono (hInit_wp X A hF h.1) fun t' ⟨b, g⟩ => ⟨b, by rw [g .s6 (by decide), h.2.1], h.2.2⟩) ?_
  -- The padding, and the compression function's arguments.
  let n := fun (a : State) => (8 + H.D + (sl a).toNat + M.L) / H.B + 1
  have hn : ∀ a : State, (sl a).toNat + 8 + H.D ≤ 1880 → oY + H.B * n a ≤ oRsa := fun a h => by
    have := padB_bounds (ℓ := 8 + H.D + (sl a).toNat) (L := M.L) hB0
    unfold padB at this
    show oY + H.B * ((8 + H.D + (sl a).toNat + M.L) / H.B + 1) ≤ oRsa
    rcases hB' with e | e <;> rw [e] at this ⊢ <;> omega
  let C := fun (a t : State) => (BT S vf Pre Pub a t ∧ oY + H.B * n a ≤ oRsa) ∧ t.gpr .a0 = off (S a) oSt ∧
    t.gpr .a1 = off (S a) oY ∧ t.gpr .a2 = BitVec.ofNat 64 (n a) ∧ t.gpr .a3 = off (S a) oCs
  refine two_seq (Ψ := C) (padAll_taint H hH.hb M.be fun a t₁ t₂ h₁ h₂ => ⟨(bt_pins X (an := id)
      (Φ := K) (fun _ _ h => h.1) a t₁ t₂ h₁ h₂).1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [bt_s0 X h₁.1, bt_s0 X h₂.1]
      · rw [h₁.2.1, h₂.2.1]⟩)
    (fun a t h => ?_) ?_
  · obtain ⟨⟨s, P, p, b, sy⟩, h6, hb⟩ := h
    have hS := X.S p
    exact WP.mono_syms (padAll_ok (X.fits P) M (sl := (sl a).toNat) (by rw [h6, ofNat_toNat]) b (by omega))
      fun t' ⟨b', _, _, x0, x1, x2, x3, _⟩ y => ⟨⟨⟨s, P, p, b', y.trans sy⟩, hn a hb⟩, by rw [x0, hS],
        by rw [x1, hS], by rw [x2], by rw [x3, hS]⟩
  -- The compression function.
  have ca : ∀ {a t : State}, C a t → ∃ s, Pre s ∧ Pub a s ∧ CompArgs S vf s t oY (n a) ∧ t.syms = s.syms :=
    fun {a t} ⟨⟨⟨s, P, p, b, sy⟩, _⟩, x0, x1, x2, x3⟩ => by
      have hS := X.S p
      exact ⟨s, P, p, ⟨X.fits P, b, hal P, by rw [x0, hS], by rw [x1, hS], x2, by rw [x3, hS], by omega⟩, sy⟩
  refine two_seq (Ψ := fun a t => BT S vf Pre Pub a t)
    (compM_two X A (an := id) (fun a t h => let ⟨s, P, p, Ca, y⟩ := ca h; ⟨s, oY, n a, P, p, Ca, h.1.2, y⟩)
      (fun a t₁ t₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
          h₁.2.2.2.2.trans h₂.2.2.2.2.symm]))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, Ca, y⟩ := ca h
    exact WP.mono (compM_ok (A.tab P) (X.fits P) Ca.al Ca.b y Ca.h0 Ca.h1 Ca.h2 Ca.h3 Ca.ho h.1.2)
      fun t' ⟨⟨b', _⟩, y'⟩ => ⟨s, P, p, b', y'⟩
  -- The digest.
  refine two_seq (Ψ := fun a t => BT S vf Pre Pub a t ∧ t.gpr .a0 = off (S a) oSt ∧ t.gpr .a1 = off (S a) oDig)
    (digArgs_taint (bt_pins X (an := id) fun _ _ h => h))
    (fun a t h => WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := oDig) (h := by decide)
      fun t₂ o₂ e₂ => wp_nil fun sy => ⟨bt_only X h ((o₁.trans o₂).mono : Only [.a0, .a1] t t₂) sy,
        by rw [o₂.get .a0, e₁, bt_s0 X h], by rw [e₂, o₁.get .s0, bt_s0 X h]⟩)) ?_
  exact digM_two X A (an := id) fun _ _ h => h

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

/-- Verification's tables: `hash`, our stack argument 6, of `MdHash`, naming
`H` (with `M`, and the digest `dg`), and `mgf1`, our stack argument 7, of
`Hash`, naming `G`. -/
structure VT where
  H : Hash
  hH : HashOK H
  M : MdL H hH
  dg : String
  f : MdFns
  G : Hash
  g : Fns

/-- The names of the tables' functions. -/
def VT.names (W : VT) : List String :=
  [W.H.initN, W.H.updN, W.H.finN, W.M.compN, W.dg, W.G.initN, W.G.updN, W.G.finN]

/-- `PreL`, with the tables. -/
def PreV (D : Nat) (W : VT) (s : State) : Prop :=
  PreL D s ∧ TabM W.M W.dg W.f 6 Sp s (stackArg s 6) ∧ TabS W.G W.g 7 Sp s (stackArg s 7)

/-- `AgreeP`, with the tables at the anchor's addresses, and their functions. -/
def PubV (D : Nat) (W : VT) (a s : State) : Prop :=
  AgreeP D a s ∧ stackArg s 6 = stackArg a 6 ∧ stackArg s 7 = stackArg a 7 ∧ ∀ n ∈ W.names, s.syms n = a.syms n

theorem lOk (D : Nat) (W : VT) : Ok Sp (vP D) (PreV D W) (PubV D W) := ⟨fun P => P.1.F, fun p => p.1.ag⟩

theorem vTab (D : Nat) (W : VT) : TabAM W.M W.dg W.f 6 Sp (PreV D W) (PubV D W) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.2 _ (by simp [VT.names]),
    fun p => p.2.2.2 _ (by simp [VT.names]), fun p => p.2.2.2 _ (by simp [VT.names]),
    fun p => p.2.2.2 _ (by simp [VT.names]), fun p => p.2.2.2 _ (by simp [VT.names])⟩

theorem vTabG (D : Nat) (W : VT) : TabA W.G W.g 7 Sp (PreV D W) (PubV D W) :=
  ⟨fun P => P.2.2, fun p => p.2.2.1, fun p => p.2.2.2 _ (by simp [VT.names]),
    fun p => p.2.2.2 _ (by simp [VT.names]), fun p => p.2.2.2 _ (by simp [VT.names])⟩

/-- `Base` from such an entry state agreeing with the anchor. -/
abbrev BL (D : Nat) (W : VT) : State → State → Prop := BT Sp (vP D) (PreV D W) (PubV D W)

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
variable {D : Nat} {W : VT}

theorem BL.s0 {a t : State} (h : BL D W a t) : t.gpr .s0 = Sp a := ((h.b.agree (lOk D W)).2.1)
theorem BL.v {a t : State} (h : BL D W a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.b.agree (lOk D W)).2.2 r hr

/-- What a piece of code does from `Base` from each entry state, from `BL`. -/
theorem BL.lift {a t : State} (h : BL D W a t) {c : Prog isa} {Q : State → Prop}
    (k : ∀ s, PreL D s → AgreeP D a s → Base Sp (vP D) s t → WP isa c t fun t' => Base Sp (vP D) s t' ∧ Q t') :
    WP isa c t fun t' => BL D W a t' ∧ Q t' := by
  obtain ⟨s, P, p, b, y⟩ := h
  exact WP.mono_syms (k s P.1 p.1 b) fun t' ⟨b', q⟩ y' => ⟨⟨s, P, p, b', y'.trans y⟩, q⟩

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D W (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs :=
  pins_of (lOk D W) (fun x t hp => (h x t hp).b) rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D s) (g : AgreeP D a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm s).setWidth 8) := by
  have e3 : lo s = lo a := g.ag.v .s3 (by decide)
  have e4 : dbLen D s = dbLen D a := g.ag.v .s4 (by decide)
  rw [← e3, ← e4]; exact P

theorem BL.dn {a t : State} (h : BL D W a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, P, g, -⟩ := h
  have L := agree_lay P.1 g.1
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega, L.D0, L.D64⟩

end

section
variable {D : Nat} {W : VT} (cH : HashCT W.hH) (hF : W.H.F ≤ 208) (hD : W.H.D = D)

include cH hF hD in
/-- `H' = Hash(M')` for a given salt length, in both runs. -/
theorem hashFixed_ct :
    RelCT isa (Two fun a t => BL D W a t ∧ t.gpr .s6 = stackArg a 0 ∧ (stackArg a 0).toNat + 8 + D ≤ 1880)
      (hashFixed W.H W.M.be W.f 6) fun _ _ => True := by
  subst hD
  exact hashFixedG_ct (lOk W.H.D W).s (vTab W.H.D W) cH hF (fun P => P.1.al) (fun a => stackArg a 0)

/-- In the loop over the lengths, for the length `L`: `BL`, the counters and
some salt length in `s11`. -/
def LoopR (D : Nat) (W : VT) (ac : State × Nat) (u : State) : Prop :=
  BL D W ac.1 u ∧ (∃ sl, u.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .s8 = BitVec.ofNat 64 ac.2 ∧
    u.gpr .s9 = BitVec.ofNat 64 ((dbLen D ac.1).toNat - ac.2) ∧ ac.2 < (dbLen D ac.1).toNat

theorem LoopR.keep {ac : State × Nat} {u u' : State} (h : LoopR D W ac u) (hb : BL D W ac.1 u')
    (hg : ∀ r ∈ [Reg.s11, .s8, .s9], u'.gpr r = u.gpr r) : LoopR D W ac u' := by
  obtain ⟨-, ⟨sl, x11, hs⟩, x8, x9, hL⟩ := h
  exact ⟨hb, ⟨sl, by rw [hg .s11 (by decide), x11], hs⟩, by rw [hg .s8 (by decide), x8],
    by rw [hg .s9 (by decide), x9], hL⟩

theorem pres_three {u u' : State} (h : ∀ r ∈ preserved, u'.gpr r = u.gpr r) :
    ∀ r ∈ [Reg.s11, .s8, .s9], u'.gpr r = u.gpr r := fun r hr => h r (by revert r; decide)

theorem copyN_wp {ac : State × Nat} {u : State} (h : LoopR D W ac u) {a b : Nat}
    (hab : a = oSt ∧ b = oBk ∨ a = oBk ∧ b = oSt) :
    WP isa (copyN a b W.H.S) u (LoopR D W ac) := by
  have F := hfits W.hH
  obtain ⟨_, hSt, _, _, hR⟩ := offs
  have hB : oBk = 1376 := rfl
  have hN := W.hH.hN
  have hS1 : 0 < W.H.S := by simp only [Hash.S]; omega
  refine WP.mono (h.1.lift (Q := fun u' => Kept [.a4, .a1, .a5, .t0] u u') fun s P g b' => ?_)
    fun u' ⟨bl, k⟩ => h.keep bl fun r hr => k.gpr r (by revert r; decide)
  have L := agree_lay P g
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact WP.mono (copyN_ok L b' (a := oSt) (b := oBk) (n := W.H.S) hS1 (by omega) (by omega) (by omega)
      (.inl (by omega)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => ⟨b'', k'⟩
  · exact WP.mono (copyN_ok L b' (a := oBk) (b := oSt) (n := W.H.S) hS1 (by omega) (by omega) (by omega)
      (.inr (by omega)) (by decide) (by decide)) fun u' ⟨b'', k', _⟩ => ⟨b'', k'⟩

/-- The loop's invariant, with the lengths left. -/
abbrev LoopN (D : Nat) (W : VT) (n : Nat) (ac : State × Nat) (u : State) : Prop :=
  LoopR D W ac u ∧ n = (dbLen D ac.1).toNat - ac.2

include cH hF hD in
/-- A round of the loop over the lengths, in both runs; both agree on whether
another follows. -/
theorem round_two (n : Nat) :
    RelCT isa (Two (LoopN D W n)) (lenRound W.H W.f 6) fun u₁ u₂ =>
      isa.eval (.nonzero .s9) u₁ = isa.eval (.nonzero .s9) u₂ ∧
      (isa.eval (.nonzero .s9) u₁ = some false → True) ∧
      (isa.eval (.nonzero .s9) u₁ = some true → ∃ m < n, Two (LoopN D W m) u₁ u₂) := by
  subst hD
  have F := hfits W.hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := W.hH.hD64
  have hY : oY = 2048 := rfl
  have X := (lOk W.H.D W).s
  have A := vTab W.H.D W
  have pin0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR W.H.D W ac u) → Pins Φ [] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) []
  have pinS : ∀ {Φ : State × Nat → State → Prop}, (∀ ac u, Φ ac u → LoopR W.H.D W ac u) → Pins Φ [.s0] :=
    fun h => bl_pins (an := Prod.fst) (fun ac u hp => (h ac u hp).1) [.s0]
  -- The state to `oBk`.
  refine two_seq (Ψ := LoopN W.H.D W n) (copyN_taint oSt oBk W.H.S (pinS fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp h (.inl ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `finalize` after `8 + hLen + L` bytes.
  let A4 := fun (ac : State × Nat) (u : State) => LoopN W.H.D W n ac u ∧
    u.gpr .a1 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + W.H.D)
  refine two_seq (Ψ := A4) (lr1_taint W.H (pin0 fun _ _ h => h.1)) (fun ac u h =>
    WP.mono (h.1.1.lift (Q := fun u' => Only [.a1] u u' ∧ u'.gpr .a1 = u.gpr .s8 + BitVec.ofNat 64 (8 + W.H.D))
      fun s P g b => wp_addi (imm := 8 + W.H.D) (h := by omega) fun u' o e => wp_nil ⟨b.only P.F o, o, e⟩)
      fun u' ⟨bl, o, e⟩ => ⟨⟨h.1.keep bl fun r hr => o.gpr r (by revert r; decide), h.2⟩,
        by rw [e, h.1.2.2.1]⟩) ?_
  refine two_seq (Ψ := LoopN W.H.D W n) (hFin_two X A cH hF (an := Prod.fst) (fun ac u h => h.1.1.1)
      (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.2, h₂.2]))
    (fun ac u h => WP.mono (hFin_wp X A hF h.1.1.1) fun u' ⟨b', g'⟩ => ⟨h.1.1.keep b' (pres_three g'), h.1.2⟩) ?_
  -- The selection.
  refine two_seq (Ψ := LoopN W.H.D W n) (select_taint W.H (pinS fun _ _ h => h.1)) (fun ac u ⟨h, hn⟩ => ?_) ?_
  · have hb := h.1.dn
    obtain ⟨sl, x11, hs⟩ := h.2.1
    exact WP.mono (h.1.lift (Q := fun u' => Kept [.t1, .t2, .t3, .t4, .a1, .a2, .a3] u u') fun s P g b =>
      WP.mono (select_ok (agree_lay P g) rfl b h.2.2.1 x11 (by have := h.2.2.2.2; omega) hs)
        fun u' ⟨b', k', _⟩ => ⟨b', k'⟩)
      fun u' ⟨bl, k'⟩ => ⟨h.keep bl fun r hr => k'.gpr r (by revert r; decide), hn⟩
  -- The state back.
  refine two_seq (Ψ := LoopN W.H.D W n) (copyN_taint oBk oSt W.H.S (pinS fun _ _ h => h.1))
    (fun ac u ⟨h, hn⟩ => WP.mono (copyN_wp h (.inr ⟨rfl, rfl⟩)) fun u' h' => ⟨h', hn⟩) ?_
  -- `update` with the next byte.
  let A6 := fun (ac : State × Nat) (u : State) => LoopN W.H.D W n ac u ∧
    u.gpr .a1 = BitVec.ofNat 64 ac.2 + BitVec.ofNat 64 (8 + W.H.D) ∧
    u.gpr .a2 = off (Sp ac.1) (oY + 8 + W.H.D + ac.2) ∧ u.gpr .a3 = BitVec.ofNat 64 1
  refine two_seq (Ψ := A6) (lr2_taint W.H (pin0 fun _ _ h => h.1)) (fun ac u h => ?_) ?_
  · simp only [List.cons_append, List.nil_append]
    have s0 := h.1.1.s0
    refine WP.mono (h.1.1.lift (Q := fun u' => Only [.a1, .a2, .a3] u u' ∧
        u'.gpr .a1 = u.gpr .s8 + BitVec.ofNat 64 (8 + W.H.D) ∧
        u'.gpr .a2 = off (off (off (Sp ac.1) oY) (8 + W.H.D)) ac.2 ∧ u'.gpr .a3 = BitVec.ofNat 64 1)
      fun s P g b => ?_) fun u' ⟨bl, k₅, x1, x2, x3⟩ => ⟨⟨h.1.keep bl fun r hr => k₅.gpr r (by revert r; decide),
        h.2⟩, by rw [x1, h.1.2.2.1], ?_, x3⟩
    · refine wp_addi (imm := 8 + W.H.D) (h := by omega) fun u₁ o₁ e₁ => ?_
      refine wp_yBase (by rw [o₁.get .s0, s0]) fun u₂ o₂ e₂ =>
        wp_addi (imm := 8 + W.H.D) (h := by omega) fun u₃ o₃ e₃ => wp_add fun u₄ o₄ e₄ =>
        wp_li (imm := 1) (by decide) fun u₅ o₅ e₅ => wp_nil ?_
      have k₅ : Only [.a1, .a2, .a3] u u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
      refine ⟨b.only P.F k₅, k₅, ?_, ?_, e₅⟩
      · rw [o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁]
      · rw [o₅.get .a2, e₄, e₃, e₂, o₃.get .s8, o₂.get .s8, o₁.get .s8, h.1.2.2.1]
    · rw [x2, off_off, off_off, Nat.add_assoc oY 8 W.H.D, Nat.add_assoc oY (8 + W.H.D)]
  have h3 : ∀ {ac : State × Nat} {u : State}, A6 ac u → (u.gpr .a3).toNat = 1 := fun h => by
    rw [h.2.2.2]; rfl
  have hb7 : ∀ {ac : State × Nat} {u : State}, A6 ac u → oY + 8 + W.H.D + ac.2 + 1 ≤ oRsa := fun h => by
    have := h.1.1.2.2.2.2; have := h.1.1.1.dn; omega
  refine two_seq (Ψ := LoopN W.H.D W n)
    (hUpd_two X A cH hF (an := Prod.fst) (o := fun ac => oY + 8 + W.H.D + ac.2) (len := fun _ => 1)
      (fun ac u h => ⟨h.1.1.1, by omega, hb7 h, h.2.2.1, h3 h⟩) (fun ac u₁ u₂ h₁ h₂ => by rw [h₁.2.1, h₂.2.1]))
    (fun ac u h => WP.mono (hUpd_wp X A hF h.1.1.1 (o := oY + 8 + W.H.D + ac.2) (len := 1) (by omega) (hb7 h)
      h.2.2.1 (h3 h)) fun u' ⟨b', g'⟩ => ⟨h.1.1.keep b' (pres_three g'), h.1.2⟩) ?_
  -- The counters.
  let Po := fun (ac : State × Nat) (u : State) => BL W.H.D W ac.1 u ∧
    (∃ sl, u.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63) ∧ u.gpr .s8 = BitVec.ofNat 64 (ac.2 + 1) ∧
    u.gpr .s9 = BitVec.ofNat 64 ((dbLen W.H.D ac.1).toNat - ac.2 - 1) ∧ ac.2 < (dbLen W.H.D ac.1).toNat ∧
    n = (dbLen W.H.D ac.1).toNat - ac.2
  have w8 : ∀ ac u, LoopN W.H.D W n ac u → WP isa (.block [.addi .s8 .s8 1, .addi .s9 .s9 (-1)]) u (Po ac) := by
    intro ac u h
    refine WP.mono (h.1.1.lift (Q := fun u' => Only [.s8, .s9] u u' ∧ u'.gpr .s8 = u.gpr .s8 + 1#64 ∧
        u'.gpr .s9 = u.gpr .s9 - BitVec.ofNat 64 1) fun s P g b => wp_addi (imm := 1) fun u₁ o₁ e₁ =>
      wp_subi (imm := 1) fun u₂ o₂ e₂ => wp_nil ⟨b.only P.F ((o₁.trans o₂).mono : Only [.s8, .s9] u u₂), (o₁.trans o₂).mono,
        by rw [o₂.get .s8, e₁], by rw [e₂, o₁.get .s9]⟩) fun u' ⟨bl, o, x8, x9⟩ => ⟨bl, ?_, ?_, ?_,
        h.1.2.2.2.2, h.2⟩
    · obtain ⟨sl, x11, hs⟩ := h.1.2.1
      exact ⟨sl, by rw [o.get .s11, x11], hs⟩
    · rw [x8, h.1.2.2.1, show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
    · rw [x9, h.1.2.2.2.1, Offset.ofNat_sub_ofNat (by have := h.1.2.2.2.2; omega)]
  have hfin := two_post (Φ := LoopN W.H.D W n) (Ψ := Po) (lr3_taint (pin0 fun _ _ h => h.1)) w8
  refine hfin.mono (fun _ _ h => h) fun u₁ u₂ ⟨ac, h₁, h₂⟩ => ?_
  refine ⟨by rw [eval_nonzero, eval_nonzero, h₁.2.2.2.1, h₂.2.2.2.1], fun _ => trivial, fun ht => ?_⟩
  rw [eval_nonzero, h₁.2.2.2.1] at ht
  have hb := h₁.1.dn
  have hne : (dbLen W.H.D ac.1).toNat - ac.2 - 1 ≠ 0 := fun h0 => by rw [h0] at ht; simp at ht
  have hlt : ac.2 + 1 < (dbLen W.H.D ac.1).toNat := by omega
  refine ⟨(dbLen W.H.D ac.1).toNat - (ac.2 + 1), by have := h₁.2.2.2.2.2; omega, (ac.1, ac.2 + 1),
    ⟨⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩,
    ⟨⟨h₂.1, h₂.2.1, h₂.2.2.1, by rw [h₂.2.2.2.1, Nat.sub_sub], hlt⟩, rfl⟩⟩

/-- Some salt length in `s11`. -/
abbrev S11 (t : State) : Prop := ∃ sl, t.gpr .s11 = BitVec.ofNat 64 sl ∧ sl < 2 ^ 63

theorem S11.keep {t t' : State} (h : S11 t) (e : t'.gpr .s11 = t.gpr .s11) : S11 t' :=
  let ⟨sl, x, hs⟩ := h; ⟨sl, by rw [e, x], hs⟩

include cH hF hD in
/-- `H'` for every length, in both runs. -/
theorem hashAny_ct : RelCT isa (Two fun a t => BL D W a t ∧ S11 t) (hashAny W.H W.f 6) fun _ _ => True := by
  have F := hfits W.hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hD64 := W.hH.hD64
  have hY : oY = 2048 := rfl
  subst hD
  have X := (lOk W.H.D W).s
  have A := vTab W.H.D W
  let Φ₀ := fun (a t : State) => BL W.H.D W a t ∧ S11 t
  -- `init`.
  refine two_seq (Ψ := Φ₀) (hInit_two X A cH (an := id) fun _ _ h => h.1)
    (fun a t h => WP.mono (hInit_wp X A hF h.1) fun t' ⟨b, g⟩ => ⟨b, h.2.keep (g .s11 (by decide))⟩) ?_
  -- `update` with `0⁸ ‖ mHash`.
  let U := fun (a t : State) => Φ₀ a t ∧ t.gpr .a1 = 0#64 ∧ t.gpr .a2 = off (Sp a) oY ∧
    t.gpr .a3 = BitVec.ofNat 64 (8 + W.H.D)
  refine two_seq (Ψ := U) (anyUpd_taint W.H (bl_pins (fun _ _ h => h.1) [])) (fun a t h => ?_) ?_
  · simp only [List.cons_append, List.nil_append]
    have s0 := h.1.s0
    refine WP.mono (h.1.lift (Q := fun t' => Only [.a1, .a2, .a3] t t' ∧ t'.gpr .a1 = 0#64 ∧
        t'.gpr .a2 = off (Sp a) oY ∧ t'.gpr .a3 = BitVec.ofNat 64 (8 + W.H.D)) fun s P g b => ?_)
      fun t' ⟨bl, k₃, x1, x2, x3⟩ => ⟨⟨bl, h.2.keep (k₃.get .s11)⟩, x1, x2, x3⟩
    refine wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => ?_
    refine wp_yBase (by rw [o₁.get .s0, s0]) fun t₂ o₂ e₂ =>
      wp_li (imm := 8 + W.H.D) (by omega) fun t₃ o₃ e₃ => wp_nil ?_
    have k₃ : Only [.a1, .a2, .a3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    exact ⟨b.only P.F k₃, k₃, by rw [o₃.get .a1, o₂.get .a1, e₁], by rw [o₃.get .a2, e₂], e₃⟩
  have h3 : ∀ {a t : State}, U a t → (t.gpr .a3).toNat = 8 + W.H.D := fun h => by
    rw [h.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine two_seq (Ψ := Φ₀) (hUpd_two X A cH hF (an := id) (o := fun _ => oY) (len := fun _ => 8 + W.H.D)
      (fun a t h => ⟨h.1.1, Nat.le_refl _, by omega, h.2.2.1, h3 h⟩) (fun a t₁ t₂ h₁ h₂ => by rw [h₁.2.1, h₂.2.1]))
    (fun a t h => WP.mono (hUpd_wp X A hF h.1.1 (o := oY) (len := 8 + W.H.D) (Nat.le_refl _) (by omega) h.2.2.1
      (h3 h)) fun _ ⟨b'', g''⟩ => ⟨b'', h.1.2.keep (g'' .s11 (by decide))⟩) ?_
  -- The counters, and the loop.
  refine two_seq (Ψ := fun a u => LoopR W.H.D W (a, 0) u) (loopInit_taint (bl_pins (fun _ _ h => h.1) []))
    (fun a t h => ?_) ?_
  · have hb := h.1.dn
    have v4 := h.1.v (r := .s4)
    refine WP.mono (h.1.lift (Q := fun t' => Only [.s8, .s9] t t' ∧ t'.gpr .s8 = BitVec.ofNat 64 0 ∧
        t'.gpr .s9 = t.gpr .s4) fun s P g b => wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ =>
      wp_nil ⟨b.only P.F ((o₁.trans o₂).mono : Only [.s8, .s9] t t₂), (o₁.trans o₂).mono, by rw [o₂.get .s8, e₁],
        by rw [e₂, o₁.get .s4]⟩)
      fun t' ⟨bl, k₂, x8, x9⟩ => ⟨bl, h.2.keep (k₂.get .s11), x8,
        by rw [x9, v4, Nat.sub_zero]; exact (ofNat_toNat _).symm, show 0 < (dbLen W.H.D a).toNat by omega⟩
  exact (RelCT.exists_ (P := fun n => Two (LoopN W.H.D W n)) fun n => RelCT.loop _ (round_two cH hF rfl) n).mono
    (fun u₁ u₂ ⟨a, h₁, h₂⟩ => ⟨_, (a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h
end

end VG.Proof.RsaPss.RISCV64
