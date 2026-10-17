module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the label's hash in constant time

`hashLabel hs o` is constant time in two runs with the same frame, regions,
label's address and length (`LQ`) and selector of the hash function `G`,
whatever the label (`hashLabel_ct`): the blocks between the calls are
checked by the taint analysis, and each call is of `G` in both runs
(`two_callD`), with the same arguments.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs ldSel)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- The label's hash's public data: the frame, the working space, the other
two writable regions, and the label's address and length. -/
structure LQ where
  F : Addr
  S : Addr
  ws : List Region
  lab : Addr
  labLen : Nat

/-- A point of `hashLabel`, for the hash function the selector `kH` names. -/
structure LW (n kH : Nat) (q : LQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ LabAt t q.F q.S W q.lab q.labLen ∧ W 37 = BitVec.ofNat 64 kH

theorem LW.congr {n kH : Nat} {q : LQ} {t t' : State} (h : LW n kH q t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : LW n kH q t' := by
  obtain ⟨V, W, R, A, h37⟩ := h.rep
  exact ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), V, W, hm ▸ R, A.congr hrd hwr rfl rfl, h37⟩

theorem LW.of_mod {n kH : Nat} {q : LQ} {t t₀ : State} (h : LW n kH q t₀) (hm : t.mem = t₀.mem)
    (hrd : t.rd = t₀.rd) (hwr : t.wr = t₀.wr) (g : ∀ r, r ≠ .rax → t.gpr r = t₀.gpr r) : LW n kH q t :=
  h.congr (g .rsp (by decide)) hrd hwr hm

theorem LW.after {n kH : Nat} {q : LQ} {t t' : State} (h : LW n kH q t) (L' : Lay t' q.F q.S) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : LabAt t q.F q.S W q.lab q.labLen) (h37 : W 37 = BitVec.ofNat 64 kH) : LW n kH q t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', V, W, R, A.congr hrd hwr rfl rfl, h37⟩

theorem LW.fr {n kH : Nat} {q : LQ} {t : State} (h : LW n kH q t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ ([] : List Nat), word t.mem q.F (8 * k) = 0 :=
  ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩

/-- The selector, in its slot. -/
theorem LW.sel {n kH : Nat} {q : LQ} {t : State} (h : LW n kH q t) :
    FrV n q.F q.ws t ∧ Lay t q.F q.S ∧ t.mem.readW (off q.F sSelH) 64 = BitVec.ofNat 64 kH := by
  obtain ⟨V, W, R, -, h37⟩ := h.rep
  exact ⟨h.fv, h.L, by rw [R.rd (d := sSelH) 37 rfl (by decide), h37]⟩

/-! ## The points between the calls -/

abbrev Q1 (n kH : Nat) (q : LQ) (t : State) : Prop := LW n kH q t ∧ t.gpr .rdi = off q.S oSt

abbrev Q3 (n kH : Nat) (q : LQ) (t : State) : Prop := LW n kH q t ∧ t.gpr .rdi = off q.S oSt ∧
  t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .rdx = q.lab ∧ t.gpr .rcx = BitVec.ofNat 64 q.labLen ∧
  t.gpr .r8 = off q.S oW

abbrev Q5 (n kH o : Nat) (q : LQ) (t : State) : Prop := LW n kH q t ∧ t.gpr .rdi = off q.S oSt ∧
  t.gpr .rsi = BitVec.ofNat 64 q.labLen ∧ t.gpr .rdx = off q.S o ∧ t.gpr .rcx = off q.S oW

theorem mod_Q1 {n kH : Nat} {q : LQ} {t : State} (h : Mod (Q1 n kH) q t) : Q1 n kH q t :=
  let ⟨_, ⟨p, hdi⟩, hm, hrd, hwr, g⟩ := h
  ⟨p.of_mod hm hrd hwr g, (g _ (by decide)).trans hdi⟩

theorem mod_Q3 {n kH : Nat} {q : LQ} {t : State} (h : Mod (Q3 n kH) q t) : Q3 n kH q t :=
  let ⟨_, ⟨p, hdi, hsi, hdx, hcx, h8⟩, hm, hrd, hwr, g⟩ := h
  ⟨p.of_mod hm hrd hwr g, (g _ (by decide)).trans hdi, (g _ (by decide)).trans hsi, (g _ (by decide)).trans hdx,
    (g _ (by decide)).trans hcx, (g _ (by decide)).trans h8⟩

theorem mod_Q5 {n kH o : Nat} {q : LQ} {t : State} (h : Mod (Q5 n kH o) q t) : Q5 n kH o q t :=
  let ⟨_, ⟨p, hdi, hsi, hdx, hcx⟩, hm, hrd, hwr, g⟩ := h
  ⟨p.of_mod hm hrd hwr g, (g _ (by decide)).trans hdi, (g _ (by decide)).trans hsi, (g _ (by decide)).trans hdx,
    (g _ (by decide)).trans hcx⟩

variable {G : Stream} (hG : StreamOK G) {hs : List (Nat × Stream)} {kH : Nat}

include hG in
/-- The label's hash to `scratch + o`, in two runs with the same `LQ` and
the selector of `G`. -/
theorem hashLabel_ct (hd : Keys hs) (hk : (kH, G) ∈ hs) (n : Nat) (hn : n = 2 ∨ n = 3) {o : Nat}
    (ho : o = oDig ∨ o = oLh) : RelCT isa (Two (LW n kH)) (hashLabel hs o) fun _ _ => True := by
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have ldT : ∃ hc, (taint.check (frT [] [] n) (.block (ldSel sSelH)) hc).isSome = true := by
    rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold hashLabel seqs seqs seqs seqs seqs
  refine RelCT.seq (two_pieceF (Ψ := Q1 n kH) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h =>
      WP.mono (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
        fun t' ⟨hdi, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := LW n kH)
    (two_callD hd hk (f := fun H => .call H.initN H.initC) LQ.F LQ.S LQ.ws (fun q t h => h.1.sel) (by decide) ldT
      (two_map id (fun q t h => mod_Q1 h) (two_init hG LQ.F LQ.S fun q t h => ⟨h.1.L, h.2⟩)))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h37⟩ := h.1.rep
    exact WP.mono (initD_ok hG hs hd hk h.1.L R rfl (by decide) h37 h.2) fun t' ⟨L', rd', wr', _, R', _⟩ =>
      h.1.after L' rd' wr' R' A h37
  refine RelCT.seq (two_pieceF (Ψ := Q3 n kH) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, -⟩ := h.rep
    exact WP.mono (labA_ok h.L R A) fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := LW n kH)
    (two_callD hd hk (f := fun H => .call H.updN H.updC) LQ.F LQ.S LQ.ws (fun q t h => h.1.sel) (by decide) ldT
      (two_map id (fun q t h => mod_Q3 h) (two_updExt hG LQ.F LQ.S LQ.lab LQ.labLen (fun _ => BitVec.ofNat 64 0)
        fun q t h => by
          obtain ⟨V, W, R, A, -⟩ := h.1.rep
          exact ⟨h.1.L, A.len, A.cov, A.dS, A.dK, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h37⟩ := h.1.rep
    exact WP.mono (updExtD_ok hG hs hd hk h.1.L R rfl (by decide) h37 A.len A.cov A.dS A.dK h.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', rd', wr', _, R', _⟩ => h.1.after L' rd' wr' R' A h37
  refine RelCT.seq (two_pieceF (Ψ := Q5 n kH o) [] [] LQ.F LQ.ws
    (fun _ _ => 0) (fun q t h => h.fr) nopin (by decide) (by rcases ho with rfl | rfl <;> rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, -⟩ := h.rep
    exact WP.mono (labF_ok h.L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide))
      fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.1 k.2.2 hm, hdi, hsi, hdx, hcx⟩
  exact two_callD hd hk (f := fun H => .call H.finN H.finC) LQ.F LQ.S LQ.ws (fun q t h => h.1.sel) (by decide) ldT
    (two_map id (fun q t h => mod_Q5 h) (two_fin hG LQ.F LQ.S (fun _ => o) (fun q => BitVec.ofNat 64 q.labLen)
      fun q t h => ⟨h.1.L, Or.inr hoo, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩))

end VG.Proof.RsaOaep.X86_64
