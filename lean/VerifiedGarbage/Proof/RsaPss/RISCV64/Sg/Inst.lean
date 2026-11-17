module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.CTPriv
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.CTBlocks
import VerifiedGarbage.Proof.RsaPss.RISCV64.CTHash
import VerifiedGarbage.Proof.RsaPss.RISCV64.Hash
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Spec
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Inst
import VerifiedGarbage.Proof.RsaPss.RISCV64.ByIdx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-! ### `RsaPss.RISCV64.Sg.Verified`, which only this module used -/

section

/-!
# RSASSA-PSS signing on RISC-V: constant time, and `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/CTMain.lean`, `Sg/Verified.lean`): two runs from
entry states with the anchor's public data leak alike (`code_ct`): the code
between the calls by the taint analysis (`Sg/CTBlocks.lean`), split where it
uses a pointer it loads, with that pointer and the lengths the anchor's; the
checks' branches by `two_ite`, on values both runs compute from the public
data (the modulus' first byte, its length and the salt length); the hash of
`M'` by `hashFixedG_ct`, MGF1 by `mgfXor_ct`, and the private operation by
`priv_ct`. What each run satisfies between them (`M`: `Base`, the saved
arguments and the checks passed, `Ck`) follows from correctness. Then
constant time (`code_constantTime`, with the contract's public data as
`PubS`); a state meeting the precondition for each hash function the other
targets sign with (`sign_sat`); `sign_verified`; and signing for a linked
hash function (`sign_link_verified`, with verification's `Link`), which the
registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa restore mgfXorT argBase)
open VG.Impl.RsaPss.RISCV64 (oY yBase)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Saves off fx B B.sp pins_of two_seq HashCT MgfAT MFit mgfXorT_ct mgfXorT_ok
  fail_taint restore_taint fb offs hfits Ok.s)
open VG.Proof.RsaPss.RISCV64 (hashFixedG_ct hashFixedG_ok VT)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc wp_mov wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The checks passed, in terms of the anchor. -/
structure Ck (D : Nat) (a : State) : Prop where
  h0 : a.mem (a.gpr .a2) ≠ 0
  fit : D + (stackArg a 11).toNat + 2 ≤ kk a - loN a
  k2 : kk a ≤ 1024

/-- `Base` and the saved arguments from an entry state with the anchor's
public data, which passed the checks. -/
abbrev M (pc : Bool) (D : Nat) (W : VT) (a t : State) : Prop := BP pc D W a t ∧ Ck D a

section
variable {pc : Bool} {D : Nat} {W : VT}

/-- The saved arguments of an entry state, as the anchor's. -/
theorem Spilled.anchor {a s : State} (p : PubK pc a s) {m : Mem} (h : Spilled s m) : Spilled a m := by
  have e : Ss s = Ss a := p.1.args 12 (by decide)
  obtain ⟨hn, he, hel, hp, hpl, hc⟩ := h
  rw [e] at hn he hel hp hpl hc
  rw [p.1.byte p.2] at hc
  exact ⟨by rw [hn, p.1.g .a2 (by decide)], by rw [he, p.1.g .a4 (by decide)], by rw [hel, p.1.g .a5 (by decide)],
    by rw [hp, p.1.g .a6 (by decide)], by rw [hpl, p.1.g .a7 (by decide)], hc⟩

theorem Spilled.ofAnchor {a s : State} (p : PubK pc a s) {m : Mem} (h : Spilled a m) : Spilled s m := by
  have e : Ss s = Ss a := p.1.args 12 (by decide)
  obtain ⟨hn, he, hel, hp, hpl, hc⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [e]
  · rw [hn, p.1.g .a2 (by decide)]
  · rw [he, p.1.g .a4 (by decide)]
  · rw [hel, p.1.g .a5 (by decide)]
  · rw [hp, p.1.g .a6 (by decide)]
  · rw [hpl, p.1.g .a7 (by decide)]
  · rw [hc, p.1.byte p.2]

theorem ss_eq {a s : State} (p : PubK pc a s) : Ss s = Ss a := p.1.args 12 (by decide)

theorem ck_s {a s : State} (p : PubK pc a s) (C : Ck D a) :
    s.mem (s.gpr .a2) ≠ 0 ∧ D + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by
  rw [p.1.byte p.2, p.1.pLoN p.2, p.1.pKk, p.1.args 11 (by decide)]; exact ⟨C.h0, C.fit⟩

/-- A step keeping `Base` and the saved arguments, from the entry state of a
run, and `Q`. -/
theorem M.lift {c : Prog isa} {a t : State} (h : M pc D W a t) {Q : State → Prop}
    (k : ∀ s, PreS pc D s → PubK pc a s → Base Ss vS s t → Spilled s t.mem → s.mem (s.gpr .a2) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s →
      WP isa c t fun t' => (Base Ss vS s t' ∧ Spilled s t'.mem) ∧ Q t') :
    WP isa c t fun t' => M pc D W a t' ∧ Q t' :=
  let ⟨⟨s, P, p, b, sp, y⟩, C⟩ := h
  WP.mono_syms (k s P.1 p.1 b sp (ck_s p.1 C).1 (ck_s p.1 C).2) fun _ ⟨⟨b', sp'⟩, q⟩ y' =>
    ⟨⟨⟨s, P, p, b', sp', y'.trans y⟩, C⟩, q⟩

/-- A step keeping `Base` and the saved arguments, from the entry state of a
run. -/
theorem M.step {c : Prog isa} {a t : State} (h : M pc D W a t)
    (k : ∀ s, PreS pc D s → PubK pc a s → Base Ss vS s t → Spilled s t.mem → s.mem (s.gpr .a2) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s → WP isa c t fun t' => Base Ss vS s t' ∧ Spilled s t'.mem) :
    WP isa c t (M pc D W a) :=
  WP.mono (h.lift (Q := fun _ => True) fun s P p b sp h0 hf => WP.mono (k s P p b sp h0 hf) fun _ q => ⟨q, trivial⟩)
    fun _ q => q.1

theorem mpin {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BS pc D W (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs :=
  pins_of (signOkT pc D W) h rs hrs

/-- `a4`, `a1` and `a5` as functions of the anchor. -/
theorem pins3 {α : Type} {Φ : α → State → Prop} {an : α → State} (hb : ∀ x t, Φ x t → BS pc D W (an x) t)
    (v4 v1 v5 : α → BitVec 64) (hv : ∀ x t, Φ x t → t.gpr .a4 = v4 x ∧ t.gpr .a1 = v1 x ∧ t.gpr .a5 = v5 x) :
    Pins Φ [.a4, .a1, .a5] := fun x t₁ t₂ h₁ h₂ => by
  obtain ⟨a₁, b₁, c₁⟩ := hv x t₁ h₁
  obtain ⟨a₂, b₂, c₂⟩ := hv x t₂ h₂
  refine ⟨((hb x t₁ h₁).sp (signOkT pc D W)).trans ((hb x t₂ h₂).sp (signOkT pc D W)).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm]

/-- `copySalt` to `S + d a`, in both runs. -/
theorem copySalt_ct (d : State → Nat) :
    RelCT isa (Two fun a t => M pc D W a t ∧ t.gpr .a1 = off (Ss a) (d a)) copySalt fun _ _ => True := by
  unfold copySalt
  refine two_seq (Ψ := fun a t => M pc D W a t ∧ t.gpr .a4 = stackArg a 10 ∧ t.gpr .a1 = off (Ss a) (d a) ∧
      t.gpr .a5 = stackArg a 11) (saltArgs_taint (mpin (fun _ _ h => h.1.1.bs) []))
    (fun a t h => h.1.lift fun s P p b sp _ _ => ldArg_ok P b (r := .a4) (j := 10) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_nil ?_) ?_
  · have k₃ : Only [.t6, .a4, .a5] t t₃ := (o₂.trans o₃).mono
    exact ⟨⟨b.only (fits P) k₃, by rw [k₃.mem]; exact sp⟩, by rw [o₃.get .a4, e₂, p.1.args 10 (by decide)],
      by rw [k₃.get .a1, h.2], by rw [e₃, o₂.get .s4, Base.ssl b, p.1.args 11 (by decide)]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2.2.2, h₂.2.2.2])
    (copy_taint (pins3 (fun _ _ h => h.1.1.1.bs) _ _ _ fun _ _ h => ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩))
    (skip_taint (mpin (fun _ _ h => h.1.1.1.bs) []))

variable {H : Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
include hD hD0 hD64

/-- `M'`, in both runs. -/
theorem mPrime_ct : RelCT isa (Two (M pc D W)) (mPrime H) fun _ _ => True := by
  have hY : oY = 2048 := rfl
  have hP : oP = 1352 := rfl
  have hR : oRsa = 8192 := rfl
  unfold mPrime
  refine two_seq (Ψ := M pc D W) (zeros8_taint (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.step fun s P p b sp _ _ => WP.mono (zeros_ok P b) fun _ ⟨b', m'⟩ =>
      ⟨b', by rw [m']; exact sp.wb (.inr (by omega_using [hY, hP])) (by rw [List.length_replicate]; omega_using [hY, hR])⟩) ?_
  let Ψ := fun (a t : State) => M pc D W a t ∧ t.gpr .a4 = stackArg a 8 ∧ t.gpr .a1 = off (Ss a) (oY + 8) ∧
    t.gpr .a5 = BitVec.ofNat 64 D
  have hΨ : ∀ a t, M pc D W a t →
      WP isa (.block (([argBase, .load .d .a4 .t6 64] : List Instr) ++ yBase .a1 ++
        ([.addi .a1 .a1 8, .li .a5 H.D] : List Instr))) t (Ψ a) :=
    fun a t h => h.lift fun s P p b sp _ _ => WP.mono (digArgs_ok P hD hD64 b) fun t' ⟨o, e4, e1, e5⟩ =>
      ⟨⟨b.only (fits P) o, by rw [o.mem]; exact sp⟩, by rw [e4, p.1.args 8 (by decide)], by rw [e1, ss_eq p], e5⟩
  refine two_seq (Ψ := M pc D W) (two_seq (Ψ := Ψ) (digArgs_taint H (mpin (fun _ _ h => h.1.bs) [.s0])) hΨ
      (copy_taint (pins3 (fun _ _ h => h.1.1.bs) _ _ _ fun _ _ h => h.2)))
    (fun a t h => WP.seq (WP.mono (hΨ a t h) fun t' ⟨m, e4, e1, e5⟩ =>
      m.step fun s P p b sp _ _ =>
      WP.mono (digCopy_ok P hD0 hD64 b (by rw [e4, p.1.args 8 (by decide)]) (by rw [e1, ss_eq p]) e5)
        fun _ ⟨b', m'⟩ => ⟨b', by
          rw [m']; exact sp.wb (.inr (by omega_using [hY, hP])) (by rw [bytesAt_length]; omega_using [hD64, hY, hR])⟩)) ?_
  refine two_seq (Ψ := fun a t => M pc D W a t ∧ t.gpr .a1 = off (Ss a) (oY + 8 + D))
    (saltDst_taint H (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.lift fun s P p b sp _ _ => WP.mono (saltDst_ok hD hD64 b) fun t' ⟨o, e⟩ =>
      ⟨⟨b.only (fits P) o, by rw [o.mem]; exact sp⟩, by rw [e, ss_eq p]⟩) ?_
  exact copySalt_ct (fun _ => oY + 8 + D)

theorem mPrime_wp {a t : State} (h : M pc D W a t) : WP isa (mPrime H) t (M pc D W a) := by
  have hY : oY = 2048 := rfl
  have hP : oP = 1352 := rfl
  have hR : oRsa = 8192 := rfl
  exact h.step fun s P p b sp _ hf => WP.mono (mPrime_ok P hD hD0 hD64 b (by have := P.k2; unfold kk at hf; omega_using [hf, this]))
    fun _ ⟨b', m'⟩ => ⟨b', by
      have := P.k2; unfold kk at hf
      rw [m']
      exact ((sp.wb (.inr (by omega_using [hY, hP])) (by rw [List.length_replicate]; omega_using [hY, hR])).wb (.inr (by omega_using [hY, hP]))
        (by rw [bytesAt_length]; omega_using [hD64, hY, hR])).wb (.inr (by omega_using [hY, hP])) (by rw [bytesAt_length]; omega_using [hY, hR, hf, this])⟩

omit hD0 in
/-- `0x01` and the salt in `EM`, in both runs. -/
theorem putSalt_ct : RelCT isa (Two (M pc D W)) (putSalt H) fun _ _ => True := by
  unfold putSalt
  let d := fun (a : State) => kk a - (stackArg a 11).toNat - D - 1
  refine two_seq (Ψ := fun a t => M pc D W a t ∧ t.gpr .a1 = off (Ss a) (d a))
    (saltHead_taint H (mpin (fun _ _ h => h.1.bs) [.s0, .s1, .s4]))
    (fun a t h => h.lift fun s P p b sp _ hf => ?_) (copySalt_ct d)
  have := loN_le s
  have k2 : kk s ≤ 1024 := P.k2
  have hP : oP = 1352 := rfl
  exact WP.mono (saltHead_ok P hD hD64 b (by omega_using [hf])) fun t' ⟨b', m', a1⟩ =>
    ⟨⟨b', by rw [m']; exact sp.w8 (by omega_using [k2, hP]) _⟩, by rw [a1, ss_eq p, p.1.pKk, p.1.args 11 (by decide)]⟩

omit hD0 in
theorem putSalt_wp {a t : State} (h : M pc D W a t) : WP isa (putSalt H) t (M pc D W a) :=
  h.step fun s P p b sp _ hf => WP.mono (putSalt_ok P hD hD64 b (by have := loN_le s; omega_using [hf])) fun _ ⟨b', m'⟩ =>
    ⟨b', by
      have k2 : kk s ≤ 1024 := P.k2
      have hP : oP = 1352 := rfl
      have hR : oRsa = 8192 := rfl
      rw [m']
      exact (sp.w8 (by omega_using [k2, hP]) _).wb (.inl (by rw [bytesAt_length]; omega_using [hf, k2, hP])) (by rw [bytesAt_length]; omega_using [hf, k2, hR])⟩

end

/-- MGF1's arguments for `DB`, of the anchor. -/
abbrev qD (D : Nat) (a : State) : Nat × Nat × Nat × Nat := (kk a - D - 1, D, loN a, kk a - loN a - D - 1)

theorem qD_fit {D : Nat} {a : State} (C : Ck D a) : MFit (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 := by
  have := C.fit; have := C.k2; have := loN_le a
  show MFit (kk a - D - 1) D (loN a) (kk a - loN a - D - 1)
  exact ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩

/-- MGF1's arguments, in a run. -/
abbrev MA (pc : Bool) (D : Nat) (W : VT) (a t : State) : Prop :=
  MgfAT Ss vS (PreST pc D W) (PubST pc W) (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 a t

/-- Before MGF1: its arguments, the saved arguments and the checks. -/
def MgfS (pc : Bool) (D : Nat) (W : VT) (a t : State) : Prop :=
  MA pc D W a t ∧ (∃ s, PreS pc D s ∧ PubK pc a s ∧ Spilled s t.mem) ∧ Ck D a

section
variable {pc : Bool} {W : VT} (cH : HashCT W.hH) (hF : W.H.F ≤ 208) {Hs : Spec.Mgf1.Hash} (hHl : Hs.len = W.H.D)
  (hG : HashOK W.G) (cG : HashCT hG) (hFG : W.G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = W.G.D) (hGv : Proof.Mgf1.Valid Gs)

include cG hFG hGh hGl hGv in
/-- `mgfXorT` with the anchor's arguments. -/
theorem mgf_ct : RelCT isa (Two fun a t => MA pc Hs.len W a t ∧ Ck Hs.len a) (mgfXorT W.g 15) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT Ss vS (PreST pc Hs.len W) (PubST pc W) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (signOkT pc Hs.len W) hG cG hFG x.2 hGh hGl hGv (sTabG pc Hs.len W)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qD Hs.len a, qD_fit h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem main_ct : RelCT isa (Two (M pc Hs.len W)) (signMain W.H W.M.be W.f W.g pc) fun _ _ => True := by
  have hD0 : 0 < Hs.len := hHl ▸ W.hH.hD0
  have hD64 : Hs.len ≤ 64 := hHl ▸ W.hH.hD64
  have Fh := hfits W.hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hP : oP = 1352 := rfl
  have hCs : Impl.RsaPss.RISCV64.oCs = 1664 := rfl
  unfold signMain
  refine two_seq (Ψ := M pc Hs.len W) (mPrime_ct hHl.symm hD0 hD64) (fun a t h => mPrime_wp hHl.symm hD0 hD64 h) ?_
  -- `H`.
  refine two_seq (Ψ := M pc Hs.len W)
    (two_seq (Ψ := fun a t => M pc Hs.len W a t ∧ t.gpr .s6 = stackArg a 11)
      (hashArg_taint (mpin (fun _ _ h => h.1.bs) []))
      (fun a t h => h.lift fun s P p b sp _ _ => wp_mov fun t₁ o₁ e₁ => wp_nil
        ⟨⟨b.only (fits P) o₁, by rw [o₁.mem]; exact sp⟩, by rw [e₁, Base.ssl b, p.1.args 11 (by decide)]⟩)
      ((hashFixedG_ct (signOkT pc Hs.len W).s (sTab pc Hs.len W) cH hF (fun P => P.1.als) (fun a => stackArg a 11)).mono
        (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1.1.bt, h₁.2, by have := h₁.1.2.fit; have := h₁.1.2.k2; omega_arith⟩,
          ⟨h₂.1.1.bt, h₂.2, by have := h₂.1.2.fit; have := h₂.1.2.k2; omega_arith⟩⟩) fun _ _ h => h))
    (fun a t ⟨⟨s, P, p, b, sp, y⟩, C⟩ => by
      have hf := (ck_s p.1 C).2
      unfold hashM
      exact WP.seq (WP.of_syms (wp_mov fun t₁ o₁ e₁ => wp_nil fun y₁ => WP.mono
        (hashFixedG_ok (fits P.1) hF P.2.1 P.1.als hHl.symm (sl := (stackArg s 11).toNat)
          (by rw [e₁, Base.ssl b, ofNat_toNat]) (b.only (fits P.1) o₁) (y₁.trans y)
          (by have := P.1.k2; unfold kk at hf; omega_using [hf, this])) fun _ ⟨⟨b', _, s', _⟩, y'⟩ =>
          ⟨⟨s, P, p, b', (show Spilled s t₁.mem by rw [o₁.mem]; exact sp).same s' (by
            have := Fh.1; have hY : oY = 2048 := rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
            omega_using [Fh, hSt, hDg, hP, hCs, hY]), y'⟩, C⟩))) ?_
  -- `EM`.
  refine two_seq (Ψ := M pc Hs.len W) (clearEm_taint (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.step fun s P p b sp _ _ => WP.mono (clearEm_ok P b) fun _ ⟨b', m'⟩ =>
      ⟨b', by
        rw [m']
        exact sp.wb (.inl (by rw [List.length_replicate]; omega_using [hP])) (by rw [List.length_replicate]; omega_using [hR])⟩) ?_
  refine two_seq (Ψ := M pc Hs.len W) (putSalt_ct hHl.symm hD64) (fun a t h => putSalt_wp hHl.symm hD64 h) ?_
  refine two_seq (Ψ := M pc Hs.len W) (putH_taint W.H (mpin (fun _ _ h => h.1.bs) [.s0, .s1]))
    (fun a t h => h.step fun s P p b sp _ hf => WP.mono (putH_ok P hHl.symm hD0 hD64 b (by omega_using [hf]))
      fun _ ⟨b', m'⟩ => ⟨b', by
        have k2 : kk s ≤ 1024 := P.k2
        rw [m']
        exact (sp.wb (.inl (by rw [bytesAt_length]; omega_using [hD64, hP, k2])) (by rw [bytesAt_length]; omega_using [hD64, hR, k2])).w8 (by omega_using [hP, k2]) _⟩) ?_
  -- `maskedDB`.
  refine two_seq (Ψ := MgfS pc Hs.len W) (dbArgs_taint W.H (mpin (fun _ _ h => h.1.bs) []))
    (fun a t ⟨⟨s, P, p, b, sp, y⟩, C⟩ => ?_) ?_
  · have h0 := (ck_s p.1 C).1
    have hf := (ck_s p.1 C).2
    exact WP.mono_syms (dbArgs_ok P.1 hHl.symm hD64 b h0 (by omega_using [hf])) fun t' ⟨b', m', e6, e7, e8, e9⟩ y' =>
      ⟨⟨s, P, p, b', y'.trans y, by rw [e6, ss_eq p.1, p.1.1.pKk], e7, by rw [e8, ss_eq p.1, p.1.1.pLoN p.1.2],
        by rw [e9, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩, ⟨s, P.1, p.1, by rw [m']; exact sp⟩, C⟩
  refine two_seq (Ψ := M pc Hs.len W) ((mgf_ct hG cG hFG hGh hGl hGv).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1, h₁.2.2⟩, ⟨h₂.1, h₂.2.2⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, P, p, b, y, h6, h7, h8, h9⟩, ⟨s', P', p', sp⟩, C⟩ => WP.mono (mgfXorT_ok (fits P.1) hG hFG P.2.2
      hGh hGl hGv (qD_fit C) b y (by rw [h6, ss_eq p.1]) h7 (by rw [h8, ss_eq p.1]) h9) fun t'' ⟨⟨b'', v''⟩, y''⟩ =>
        ⟨⟨s, P, p, b'', ((sp.anchor p').ofAnchor p.1).mix v''
          (by show loN a + (kk a - loN a - Hs.len - 1) ≤ oP; have := C.k2; have := loN_le a; omega_arith), y''⟩, C⟩) ?_
  refine two_seq (Ψ := M pc Hs.len W) (clearTop_taint (mpin (fun _ _ h => h.1.bs) [.s0, .s3]))
    (fun a t h => h.step fun s P p b sp h0 _ => WP.mono (clearTop_ok P b sp h0) fun _ ⟨b', m'⟩ =>
      ⟨b', by have := loN_le s; rw [m']; exact sp.w8 (by omega_using [hP, this]) _⟩) ?_
  -- The private operation.
  exact priv_ct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- After the prologue, from an entry state with the anchor's public data. -/
abbrev Pr (pc : Bool) (D : Nat) (W : VT) (a t : State) : Prop := ∃ s, PreST pc D W s ∧ PubST pc W a s ∧ Pro s t ∧ t.syms = s.syms

/-- After the spills, from an entry state with the anchor's public data. -/
abbrev En (pc : Bool) (D : Nat) (W : VT) (a t : State) : Prop :=
  ∃ s, PreST pc D W s ∧ PubST pc W a s ∧ Entered s t ∧ t.syms = s.syms

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En pc Hs.len W)) (checks W.H W.M.be W.f W.g pc) fun _ _ => True := by
  have hD64 : W.H.D ≤ 64 := W.hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En pc Hs.len W a t) → ∀ rs : List Reg,
      (∀ r ∈ rs, r ∈ Reg.s0 :: fx) → Pins Φ rs := fun h rs hrs =>
    mpin (an := id) (fun a t hp => let ⟨s, P, p, E, _⟩ := h a t hp; ⟨s, P, p, E.base⟩) rs hrs
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.t1, E₂.t1, n0S, n0S, p₁.1.1.byte p₁.1.2, p₂.1.1.byte p₂.1.2])
    (fail_taint (pin (fun _ _ h => h.1) _ (by decide))) ?_
  let E1 := fun (a t : State) => ∃ s, PreST pc Hs.len W s ∧ PubST pc W a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a2) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < W.H.D + 2))
    (chkEm_taint W.H (pin (fun _ _ h => h.1) [] (by decide))) (fun a t ⟨⟨s, P, p, E, y⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hD64 E h0) fun t' ⟨E', r3⟩ y' =>
      ⟨⟨s, P, p, E', y'.trans y, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, y, _⟩ := h.1.1; ⟨s, P, p, E, y⟩) _ (by decide))) ?_
  let E2 := fun (a t : State) => ∃ s, PreST pc Hs.len W s ∧ PubST pc W a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a2) ≠ 0 ∧ W.H.D + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < W.H.D + 2)) ∧
      isa.eval (.nonzero .a0) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, y, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < W.H.D + 2 := by simpa using hc
    exact ⟨s, P, p, E, y, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega_using [this]⟩
  -- The salt's length.
  refine two_seq (Ψ := fun a t => E2 a t ∧
      (t.gpr .a0 != 0) = decide (kk a - loN a - (W.H.D + 2) < (stackArg a 11).toNat))
    (chkSalt_taint W.H (pin (fun _ _ h => let ⟨s, P, p, E, y, _⟩ := e2 h; ⟨s, P, p, E, y⟩) [] (by decide)))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, y, h0, hem⟩ := e2 h
    exact WP.mono_syms (chkSalt_ok P.1 hD64 E h0 hem) fun t' ⟨E', r3⟩ y' =>
      ⟨⟨s, P, p, E', y'.trans y, h0, hem⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2, p.1.1.args 11 (by decide)]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, y, _⟩ := h.1.1; ⟨s, P, p, E, y⟩) _ (by decide))) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧
      (t.gpr .a0 != 0) = decide (kk a - loN a - (W.H.D + 2) < (stackArg a 11).toNat)) ∧
      isa.eval (.nonzero .a0) t = some false → M pc Hs.len W a t :=
    fun {a t} ⟨⟨⟨s, P, p, E, y, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (W.H.D + 2) < (stackArg a 11).toNat := by simpa using hc
    have k2 : kk s ≤ 1024 := P.1.k2
    rw [p.1.1.byte p.1.2, p.1.1.pKk, p.1.1.pLoN p.1.2] at *
    exact ⟨⟨s, P, p, E.base, E.sp, y⟩, ⟨h0, by rw [hHl]; omega_using [hem, hn], k2⟩⟩
  exact (main_ct cH hF hHl hG cG hFG hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

variable {Hh : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = W.hH.SH.H.hash x) (hHv : Proof.Mgf1.Valid Hs)

include cH hF hHl hG cG hFG hGh hGl hGv hHh hHv in
/-- Two runs of the code for the hash function `W.H` from entry states with
the same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreST pc Hs.len W s ∧ PubST pc W a s) (signFor W.H W.M.be W.f W.g pc)
    fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine two_seq (Ψ := Pr pc Hs.len W)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by
      rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.1.1.sp, h₂.2.1.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by
      subst e; exact WP.mono_syms (pro_ok P.1) fun t E y => ⟨s, P, p, E, y.trans rfl⟩) ?_
  refine two_seq (Ψ := En pc Hs.len W)
    (spill_taint fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => ⟨by
      rw [E₁.sv.sp, E₂.sv.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [E₁.s0, E₂.s0, ss_eq p₁.1, ss_eq p₂.1]
        · rw [E₁.args .a2 (by decide), E₂.args .a2 (by decide), p₁.1.1.g .a2 (by decide),
            p₂.1.1.g .a2 (by decide)]⟩)
    (fun a t ⟨s, P, p, E, y⟩ => WP.mono_syms (spill_ok P.1 E) fun t' E' y' => ⟨s, P, p, E', y'.trans y⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreST pc Hs.len W s ∧ PubST pc W a s ∧ Saves s t)
    (checks_ct cH hF hHl hG cG hFG hGh hGl hGv) fun a t ⟨s, P, p, E, y⟩ =>
      WP.mono (checks_done P.1 W.hH hF P.2.1 hHh hHl hHv hG hFG P.2.2 hGh hGl hGv E y) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.RISCV64.Sg

end

end


/-!
# RSASSA-PSS signing on RISC-V with the tables of `vs` and `gs`

Untrusted: everything here is checked by Lean. As verification
(`Proof/RsaPss/RISCV64/Inst.lean`): `sign` loads the index of the hash
function of the table `hash`, our stack argument 14, and runs the code for
its shape; the load changes only `t5`, and the comparisons `t4` (`Sim`), so
the correctness (`code_ok`) and the constant time (`code_ct`) of the code
for a hash function are those of `sign` (`code_correct`,
`code_constantTime`), for the tables of `vs` and `gs`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign
open VG.Impl.RsaPss.RISCV64 (idxLoad byIdx idxs ofIdx beOf MdFns)
open VG.Proof.RsaOaep.RISCV64 (Base Fits kR SC TabS stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_taint wp_ld wp_addSp wp_nil)
open VG.Proof.RsaPss.RISCV64 (Sim Sim.g Sim.addr Sim.arg Sim.kRe Sim.trans VT TabM MdL vtOf vt_names Shape OK
  idx_lt byIdx_ok byIdx_ct idx_certs)
open VG.Proof.MdHashTable.RISCV64 (MVar idx digName tableOf tables fnsOf names Coh held_tableOf hashAt_tableOf
  tabM_of)

/-! ## States but for `t4` and `t5` -/

section
variable {s u : State} (h : Sim s u)
include h

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.kSe {pc : Bool} : VG.Proof.RsaPss.RISCV64.Sg.kS pc u =
    VG.Proof.RsaPss.RISCV64.Sg.kS pc s := by
  simp only [VG.Proof.RsaPss.RISCV64.Sg.kS, h.1.sp]

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.preXS (X : PreXS s) : PreXS u := by
  have e1 := h.g (r := .a0); have e2 := h.g (r := .a1); have e3 := h.g (r := .a2); have e4 := h.g (r := .a3)
  have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have ek := h.kSe (pc := true); have esp := h.1.sp; have em := h.1.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [oR, scR, preR, HypS, e1, e2, e3, e4, e6, e7, ea, ek, esp, em])
  exacts [X.oP, X.sP, X.kP, X.wP, X.pl, X.sp3, X.alP, fun _ => X.hyp rfl]

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.preS {pc : Bool} {D : Nat} (P : PreS pc D s) : PreS pc D u := by
  have e0 := h.g (r := .a0); have e1 := h.g (r := .a1); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e5 := h.g (r := .a5); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have eA := h.addr; have ek := h.kSe (pc := pc)
  have esp := h.1.sp; have erd := h.1.rd; have ewr := h.1.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hp => h.preXS (P.px hp)⟩
  all_goals (try simp only [oR, nR, eR, pR, qR, dpR, dqR, qiR, dgR, sR, scR, tHR, tGR, aR, preR, rdS, e0, e1, e2, e3,
    e4, e5, e6, e7, ea, eA, ek, esp, erd, ewr])
  exacts [P.spal, P.sp1, P.sp2, P.hrd, P.hwr, P.on, P.oe, P.op, P.oq, P.odp, P.odq, P.oqi, P.odg, P.osl, P.os, P.oth,
    P.otg, P.oa, P.ns, P.es, P.ps, P.qs, P.dps, P.dqs, P.qis, P.dgs, P.sls, P.sth, P.stg, P.sa, P.ko, P.kn, P.ke,
    P.kp, P.kq, P.kdp, P.kdq, P.kqi, P.kdg, P.ksl, P.ks, P.kth, P.ktg, P.ka, P.wo, P.wn, P.we, P.wp, P.wq, P.wdp,
    P.wdq, P.wqi, P.wdg, P.wsl, P.wsc, P.wth, P.wtg, P.k1, P.k2, P.ok, P.e1, P.e2, P.p1, P.p2, P.q1, P.q2, P.h3,
    P.h7, P.h5, P.hs, P.als, P.al14, P.al15]

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.postS {Hs Gs : Spec.Mgf1.Hash} {s' : State} (q : Post Hs Gs u s') : Post Hs Gs s s' := by
  have e0 := h.g (r := .a0); have e2 := h.g (r := .a2); have e3 := h.g (r := .a3)
  have e4 := h.g (r := .a4); have e5 := h.g (r := .a5); have e6 := h.g (r := .a6); have e7 := h.g (r := .a7)
  have ea := h.arg; have em := h.1.mem
  have hv : signOut Hs Gs u = signOut Hs Gs s := by
    simp only [signOut, digB, saltB, e2, e3, e4, e5, e6, e7, ea, em]
  obtain ⟨⟨g, sp, ra⟩, r⟩ := q
  refine ⟨⟨fun x hx => (g x hx).trans (h.1.gpr x (by revert x; decide)), sp.trans h.1.sp,
    ra.trans (h.g (r := .ra))⟩, ?_⟩
  rw [← hv, ← e0]
  have ek : kk u = kk s := by simp only [kk, e3]
  rw [← ek]; exact r

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.pubS {pc : Bool} {a : State} (p : PubS pc a s) : PubS pc a u := by
  have e2 := h.g (r := .a2); have e3 := h.g (r := .a3); have e4 := h.g (r := .a4); have e5 := h.g (r := .a5)
  have ea := h.arg; have em := h.1.mem
  exact ⟨h.1.sp.trans p.sp, fun r hr => (h.1.gpr r (by revert r; decide)).trans (p.g r hr),
    fun i hi => (ea i).trans (p.args i hi), by simp only [e2, e3, em]; exact p.n, by simp only [e4, e5, em]; exact p.e,
    fun hp => by rw [ea, ea]; exact p.args2 hp, fun hp => by simp only [ea, e3, em]; exact p.leak hp⟩

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.tabMS {H : Impl.Hmac.Stream.RISCV64.Hash} {hH : Proof.Hmac.Stream.RISCV64.HashOK H} {M : MdL H hH}
    {dN : String} {f : MdFns} {j : Nat} (T : TabM M dN f j Ss s (stackArg s j)) :
    TabM M dN f j Ss u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Ss, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

theorem _root_.VG.Proof.RsaPss.RISCV64.Sim.tabSS {G : Impl.Hmac.Stream.RISCV64.Hash} {g : Impl.RsaOaep.RISCV64.Fns} {j : Nat}
    (T : TabS G g j Ss s (stackArg s j)) : TabS G g j Ss u (stackArg u j) := by
  rw [h.arg]
  exact T.transfer h.1.sp h.1.rd h.2 (by simp only [SC, Ss, h.arg]) (rs := []) (by rw [h.1.mem]; exact Frame.refl _ _)
    (fun _ h => nomatch h) fun _ _ _ h => nomatch h

end

/-! ## The index -/

section
variable {pc : Bool} {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem idxA_wp {t : State} (h : Sim s t) :
    WP isa (.block [.addSp .t5 (8 * 14), .load .d .t5 .t5 0]) t fun u => Sim s u ∧ u.gpr .t5 = stackArg s 14 :=
  WP.of_syms (wp_addSp (imm := 8 * 14) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s 14)
    (by rw [e₁, BitVec.add_zero, h.1.sp]; rfl) (arg_al P (by decide))
    ⟨aR pc s, by rw [o₁.rd, h.1.rd, P.hrd]; cases pc <;> simp, in_aR (by decide)⟩
    (fun u₂ o₂ e₂ => wp_nil fun y => ⟨⟨(h.1.trans (o₁.trans o₂)).mono fun r hr => by revert r; decide,
      y.trans h.2⟩, by rw [e₂, o₁.mem, h.1.mem]; rfl⟩))

theorem idxB_wp {t : State} (h : Sim s t) (h5 : t.gpr .t5 = stackArg s 14) :
    WP isa (.block [.load .d .t5 .t5 40]) t fun u =>
      Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 :=
  WP.of_syms (wp_ld (a := stackArg s 14 + BitVec.ofNat 64 40) (by rw [h5])
    (by
      have e : (stackArg s 14 + BitVec.ofNat 64 40).toNat = (stackArg s 14).toNat + 40 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := P.wth; omega_using [this]
      rw [e]; have := P.al14; omega_using [this])
    ⟨tHR s, by rw [h.1.rd, P.hrd]; cases pc <;> simp,
      Offset.contains_base (stackArg s 14) (by decide) (by decide)⟩
    (fun u o e => wp_nil fun y => ⟨⟨(h.1.trans o).mono fun r hr => by revert r; decide, y.trans h.2⟩,
      by rw [e, h.1.mem]⟩) (by decide))

theorem idxLoad_wp : WP isa (.block (idxLoad 14)) s fun u =>
    Sim s u ∧ u.gpr .t5 = s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 := by
  show WP isa (.block ([.addSp .t5 (8 * 14), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) s _
  rw [WP.block_append_iff]
  exact WP.mono (idxA_wp P ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ => idxB_wp P h e

theorem tabM_entryS {vs : List MVar} (hc : Coh vs)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {v : MVar} (hv : v ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (tableOf v))) :
    TabM v.M (digName v) (fnsOf vs) 14 Ss s (stackArg s 14) := by
  refine tabM_of (by decide) rfl (arg_al P (by decide)) P.al14
    (show (stackArg s 14).toNat + 40 ≤ 2 ^ 64 by have := P.wth; omega_using [this]) (A := aR pc s)
    (by rw [P.hrd]; cases pc <;> simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)) (P.kth.sub_left kR_sub)
    (P.sth.sub_left (sc_sub P)) hc hpw hv hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

theorem tabS_entryS {gs : List MVar} (hc : MdHashTable.RISCV64.Coh gs)
    (hpw : (MdHashTable.RISCV64.names gs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar} (hw : w ∈ gs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (MdHashTable.RISCV64.tableOf w))) :
    TabS w.w.H (MdHashTable.RISCV64.fns3 gs) 15 Ss s (stackArg s 15) := by
  refine MdHashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.al15 P.wtg (A := aR pc s)
    (by rw [P.hrd]; cases pc <;> simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (P.ktg.sub_left kR_sub) (P.stg.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

end

theorem signFor_shape {H H' : Impl.Hmac.Stream.RISCV64.Hash} (hb : H.b = H'.b) (hN : H.N = H'.N) (hD : H.D = H'.D)
    (be : Bool) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) (pc : Bool) : signFor H be f g pc = signFor H' be f g pc := by
  obtain ⟨b, N, D, _, _, _, _, _, _, _⟩ := H
  obtain ⟨b', N', D', _, _, _, _, _, _, _⟩ := H'
  simp only at hb hN hD
  subst hb hN hD
  rfl

theorem shape_codeS {v : MVar} (hv : Shape v) (f : MdFns) (g : Impl.RsaOaep.RISCV64.Fns) (pc : Bool) :
    signFor (ofIdx (idx v)) (beOf (idx v)) f g pc = signFor v.w.H v.M.be f g pc := by
  rw [hv.2.2.2.2, signFor_shape hv.2.1.symm hv.2.2.1.symm hv.2.2.2.1.symm]

/-! ## Correctness -/

section
variable {pc : Bool} {vs : List MVar} {gs : List MVar} (hok : OK vs gs) {Pre : State → Prop}
  (hTab : ∀ {s}, Pre s →
    (∃ T ∈ tables vs, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ MdHashTable.RISCV64.tables gs, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (((tables vs).map (fun T : FnTable => T.fns)).flatten ++
        ((MdHashTable.RISCV64.tables gs).map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g))
  (hPre : ∀ {s} {H : Spec.Mgf1.Hash}, Pre s → Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H →
    PreS pc H.len s)
include hok hTab hPre

/-- The code, from an entry state meeting a precondition that gives the
tables and `PreS`: `Post` for the tables' hash functions. -/
theorem signG_wp (s : State) (h : Pre s) :
    ∃ Hs Gs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some Hs ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some Gs ∧
      WP isa (signG (fnsOf vs) (MdHashTable.RISCV64.fns3 gs) pc) s (Post Hs Gs s) := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨TG, hTG, hhG⟩, hpw⟩ := hTab h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := hpw.sublist (List.sublist_append_right _ _)
  obtain ⟨hmH, hiH⟩ := held_tableOf hhH
  have hH := hashAt_tableOf hiH
  have hG := MdHashTable.RISCV64.hashAt_tableOf (MdHashTable.RISCV64.held_tableOf hhG).2
  have P : PreS pc v.w.l.G.len s := hPre h hH
  have T := tabM_entryS P hcv hpwH hv hhH
  have TG := tabS_entryS P hcg hpwG hw hhG
  have hS := hsh v hv
  refine ⟨v.w.l.G, w.w.l.G, hH, hG, ?_⟩
  refine WP.seq (WP.mono (idxLoad_wp P) fun u ⟨hu, e5⟩ => ?_)
  refine byIdx_ok (I := idx v) (idx_lt hS) (F := fun u => Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v))
    (fun _ h => h.2) (fun t t' ⟨h, e⟩ o y => ⟨h.trans ⟨o.mono fun r hr => by revert r; decide, y⟩,
      by rw [o.get .t5, e]⟩)
    (fun u ⟨hu, _⟩ => ?_) hS.1 (fun x hx => (idx_certs x hx).1) u ⟨hu, by rw [e5, hiH]⟩
  rw [shape_codeS hS]
  exact WP.mono (code_ok (hu.preS P) v.w.l.ok v.w.l.fits (hu.tabMS T) v.w.l.hash v.w.l.len v.w.l.valid w.w.l.ok
    w.w.l.fits (hu.tabSS TG) w.w.l.hash w.w.l.len w.w.l.valid) fun s' q => hu.postS q

end

/-- The code, from an entry state meeting the contract. -/
theorem code_correct {vs : List MVar} {gs : List MVar} (hok : OK vs gs) (s : State)
    (h : (signSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pre s) :
    ∃ t s', Exec isa (sign (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) s t s' ∧ abiPreserved s s' ∧
      (signSpec (tables vs) (MdHashTable.RISCV64.tables gs)).post s s' := by
  obtain ⟨Hs, Gs, hH, hG, key⟩ := signG_wp hok spec_tabS preS_of s h
  obtain ⟨t, s', he, habi, hr⟩ := key
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes false = 3471 + 1 := rfl
  unfold signSpec
  rw [e]
  sig_post [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, 
    Abi.withTables, abi, argRegs, stackArgs_sixteen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

/-! ## Constant time -/

theorem idxA_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp .t5 (8 * 14), .load .d .t5 .t5 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

section
variable {pc : Bool} {vs : List MVar} {gs : List MVar} (hok : OK vs gs) {Pre : State → Prop}
  {Pub : State → State → Prop}
  (hTab : ∀ {s}, Pre s →
    (∃ T ∈ tables vs, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ MdHashTable.RISCV64.tables gs, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (((tables vs).map (fun T : FnTable => T.fns)).flatten ++
        ((MdHashTable.RISCV64.tables gs).map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g))
  (hPre : ∀ {s} {H : Spec.Mgf1.Hash}, Pre s → Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H →
    PreS pc H.len s)
  (hPub : ∀ {s₁ s₂}, Pub s₁ s₂ → PubS pc s₁ s₂ ∧
      (∀ f ∈ ((tables vs).map (fun T : FnTable => T.fns)).flatten ++
          ((MdHashTable.RISCV64.tables gs).map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tables vs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ MdHashTable.RISCV64.tables gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)))
include hok hTab hPre hPub

/-- The code is constant time, for a contract that gives the tables, `PreS`
and `PubS`. -/
theorem code_constantTimeG :
    ConstantTime isa Pre Pub (signG (fnsOf vs) (MdHashTable.RISCV64.fns3 gs) pc) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨TG, hTG, hhG₁⟩, hpw₁⟩ := hTab h₁
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTG
  obtain ⟨p, hsy, iffH, iffG⟩ := hPub hp
  have hhH₂ := (iffH _ hTH).mp hhH₁
  have hhG₂ := (iffG _ hTG).mp hhG₁
  have hpw₂ := (hTab h₂).2.2
  obtain ⟨hcv, hcg, hsh, -⟩ := hok
  have hS := hsh v hv
  let W := vtOf vs gs v w
  let D := v.w.l.G.len
  have ent : ∀ {s : State}, Pre s →
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (tableOf v)) →
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (MdHashTable.RISCV64.tableOf w)) →
      (names vs ++ MdHashTable.RISCV64.names gs).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) →
      PreST pc D W s ∧ s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v) :=
    fun {s} h hh hg hpw => by
      have hH := hashAt_tableOf (held_tableOf hh).2
      have P : PreS pc D s := hPre h hH
      exact ⟨⟨P, tabM_entryS P hcv (hpw.sublist (List.sublist_append_left _ _)) hv hh,
        tabS_entryS P hcg (hpw.sublist (List.sublist_append_right _ _)) hw hg⟩, (held_tableOf hh).2⟩
  obtain ⟨P₁, i₁⟩ := ent h₁ hhH₁ hhG₁ hpw₁
  obtain ⟨P₂, i₂⟩ := ent h₂ hhH₂ hhG₂ hpw₂
  have hk : ∀ {s : State}, PreST pc D W s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.1.k1
  let Φ₀ := fun (a s : State) => PreST pc D W s ∧ PubST pc W a s ∧
    s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (idx v)
  let Φ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = BitVec.ofNat 64 (idx v)
  have hct : RelCT isa (Two Φ₀) (signG (fnsOf vs) (MdHashTable.RISCV64.fns3 gs) pc) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := Φ) ?_ fun a s hs => WP.mono (idxLoad_wp hs.1.1) fun u ⟨h, e⟩ =>
      ⟨s, hs, h, by rw [e, hs.2.2]⟩) ?_
    · let Ψ := fun (a u : State) => ∃ s, Φ₀ a s ∧ Sim s u ∧ u.gpr .t5 = stackArg a 14
      show RelCT isa _ (.block ([.addSp .t5 (8 * 14), .load .d .t5 .t5 0] ++ [.load .d .t5 .t5 40])) _
      refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ) (idxA_taint fun a s₁ s₂ h₁ h₂ =>
          ⟨h₁.2.1.1.1.sp.trans h₂.2.1.1.1.sp.symm, fun _ h => nomatch h⟩)
        fun a s hs => WP.mono (idxA_wp hs.1.1 ⟨Only.refl _ s, rfl⟩) fun u ⟨h, e⟩ =>
          ⟨s, hs, h, by rw [e, hs.2.1.1.1.args 14 (by decide)]⟩)
        (VG.Proof.RsaPss.RISCV64.idxB_taint fun a u₁ u₂ ⟨s₁, x₁, k₁, f₁⟩ ⟨s₂, x₂, k₂, f₂⟩ => ⟨by
          rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm, fun r hr => by
          rw [List.mem_singleton.mp hr, f₁, f₂]⟩))
    refine byIdx_ct (I := idx v) (idx_lt hS) (fun a u h => let ⟨_, _, _, e⟩ := h; e)
      (fun a u₁ u₂ ⟨s₁, x₁, k₁, _⟩ ⟨s₂, x₂, k₂, _⟩ => by
        rw [k₁.1.sp, k₂.1.sp]; exact x₁.2.1.1.1.sp.trans x₂.2.1.1.1.sp.symm)
      (fun a u u' ⟨s, x, k, e⟩ o y => ⟨s, x, k.trans ⟨o.mono fun r hr => by revert r; decide, y⟩,
        by rw [o.get .t5, e]⟩) ?_ hS.1 idx_certs
    rw [shape_codeS hS]
    refine (code_ct (W := W) v.w.l.ct v.w.l.fits v.w.l.len w.w.l.ok w.w.l.ct w.w.l.fits w.w.l.hash w.w.l.len w.w.l.valid
      v.w.l.hash v.w.l.valid).mono (fun u₁ u₂ ⟨a, ⟨s₁, x₁, k₁, _⟩, ⟨s₂, x₂, k₂, _⟩⟩ => ⟨a, ?_, ?_⟩)
      fun _ _ h => h
    · exact ⟨⟨k₁.preS x₁.1.1, k₁.tabMS x₁.1.2.1, k₁.tabSS x₁.1.2.2⟩, ⟨k₁.pubS x₁.2.1.1.1,
        hk ⟨k₁.preS x₁.1.1, k₁.tabMS x₁.1.2.1, k₁.tabSS x₁.1.2.2⟩⟩, fun n hn => by rw [k₁.2]; exact x₁.2.1.2 n hn⟩
    · exact ⟨⟨k₂.preS x₂.1.1, k₂.tabMS x₂.1.2.1, k₂.tabSS x₂.1.2.2⟩, ⟨k₂.pubS x₂.2.1.1.1,
        hk ⟨k₂.preS x₂.1.1, k₂.tabMS x₂.1.2.1, k₂.tabSS x₂.1.2.2⟩⟩, fun n hn => by rw [k₂.2]; exact x₂.2.1.2 n hn⟩
  exact hct s₁ s₂ t₁ t₂ s₁' s₂' ⟨s₁, ⟨P₁, ⟨⟨pubS_refl pc s₁, hk P₁⟩, fun _ _ => rfl⟩, i₁⟩,
    ⟨P₂, ⟨⟨p, hk P₂⟩, fun n hn => (hsy n (vt_names hv hw n hn)).symm⟩, i₂⟩⟩ e₁ e₂

end

theorem code_constantTime {vs : List MVar} {gs : List MVar} (hok : OK vs gs) :
    ConstantTime isa (signSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (signSpec (tables vs) (MdHashTable.RISCV64.tables gs)).pub (sign (fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) :=
  code_constantTimeG hok spec_tabS preS_of pubS_of

end VG.Proof.RsaPss.RISCV64.Sg
