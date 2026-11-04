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
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Pre

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
abbrev M (D : Nat) (W : VT) (a t : State) : Prop := BP D W a t ∧ Ck D a

section
variable {D : Nat} {W : VT}

/-- The saved arguments of an entry state, as the anchor's. -/
theorem Spilled.anchor {a s : State} (p : PubK a s) {m : Mem} (h : Spilled s m) : Spilled a m := by
  have e : Ss s = Ss a := p.1.args 12 (by decide)
  obtain ⟨hn, he, hel, hp, hpl, hc⟩ := h
  rw [e] at hn he hel hp hpl hc
  rw [p.1.byte p.2] at hc
  exact ⟨by rw [hn, p.1.g .a2 (by decide)], by rw [he, p.1.g .a4 (by decide)], by rw [hel, p.1.g .a5 (by decide)],
    by rw [hp, p.1.g .a6 (by decide)], by rw [hpl, p.1.g .a7 (by decide)], hc⟩

theorem Spilled.ofAnchor {a s : State} (p : PubK a s) {m : Mem} (h : Spilled a m) : Spilled s m := by
  have e : Ss s = Ss a := p.1.args 12 (by decide)
  obtain ⟨hn, he, hel, hp, hpl, hc⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [e]
  · rw [hn, p.1.g .a2 (by decide)]
  · rw [he, p.1.g .a4 (by decide)]
  · rw [hel, p.1.g .a5 (by decide)]
  · rw [hp, p.1.g .a6 (by decide)]
  · rw [hpl, p.1.g .a7 (by decide)]
  · rw [hc, p.1.byte p.2]

theorem ss_eq {a s : State} (p : PubK a s) : Ss s = Ss a := p.1.args 12 (by decide)

theorem ck_s {a s : State} (p : PubK a s) (C : Ck D a) :
    s.mem (s.gpr .a2) ≠ 0 ∧ D + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by
  rw [p.1.byte p.2, p.1.pLoN p.2, p.1.pKk, p.1.args 11 (by decide)]; exact ⟨C.h0, C.fit⟩

/-- A step keeping `Base` and the saved arguments, from the entry state of a
run, and `Q`. -/
theorem M.lift {c : Prog isa} {a t : State} (h : M D W a t) {Q : State → Prop}
    (k : ∀ s, PreS D s → PubK a s → Base Ss vS s t → Spilled s t.mem → s.mem (s.gpr .a2) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s →
      WP isa c t fun t' => (Base Ss vS s t' ∧ Spilled s t'.mem) ∧ Q t') :
    WP isa c t fun t' => M D W a t' ∧ Q t' :=
  let ⟨⟨s, P, p, b, sp, y⟩, C⟩ := h
  WP.mono_syms (k s P.1 p.1 b sp (ck_s p.1 C).1 (ck_s p.1 C).2) fun _ ⟨⟨b', sp'⟩, q⟩ y' =>
    ⟨⟨⟨s, P, p, b', sp', y'.trans y⟩, C⟩, q⟩

/-- A step keeping `Base` and the saved arguments, from the entry state of a
run. -/
theorem M.step {c : Prog isa} {a t : State} (h : M D W a t)
    (k : ∀ s, PreS D s → PubK a s → Base Ss vS s t → Spilled s t.mem → s.mem (s.gpr .a2) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s → WP isa c t fun t' => Base Ss vS s t' ∧ Spilled s t'.mem) :
    WP isa c t (M D W a) :=
  WP.mono (h.lift (Q := fun _ => True) fun s P p b sp h0 hf => WP.mono (k s P p b sp h0 hf) fun _ q => ⟨q, trivial⟩)
    fun _ q => q.1

theorem mpin {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BS D W (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs :=
  pins_of (signOkT D W) h rs hrs

/-- `a4`, `a1` and `a5` as functions of the anchor. -/
theorem pins3 {α : Type} {Φ : α → State → Prop} {an : α → State} (hb : ∀ x t, Φ x t → BS D W (an x) t)
    (v4 v1 v5 : α → BitVec 64) (hv : ∀ x t, Φ x t → t.gpr .a4 = v4 x ∧ t.gpr .a1 = v1 x ∧ t.gpr .a5 = v5 x) :
    Pins Φ [.a4, .a1, .a5] := fun x t₁ t₂ h₁ h₂ => by
  obtain ⟨a₁, b₁, c₁⟩ := hv x t₁ h₁
  obtain ⟨a₂, b₂, c₂⟩ := hv x t₂ h₂
  refine ⟨((hb x t₁ h₁).sp (signOkT D W)).trans ((hb x t₂ h₂).sp (signOkT D W)).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm]

/-- `copySalt` to `S + d a`, in both runs. -/
theorem copySalt_ct (d : State → Nat) :
    RelCT isa (Two fun a t => M D W a t ∧ t.gpr .a1 = off (Ss a) (d a)) copySalt fun _ _ => True := by
  unfold copySalt
  refine two_seq (Ψ := fun a t => M D W a t ∧ t.gpr .a4 = stackArg a 10 ∧ t.gpr .a1 = off (Ss a) (d a) ∧
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
theorem mPrime_ct : RelCT isa (Two (M D W)) (mPrime H) fun _ _ => True := by
  have hY : oY = 2048 := rfl
  have hP : oP = 1352 := rfl
  have hR : oRsa = 8192 := rfl
  unfold mPrime
  refine two_seq (Ψ := M D W) (zeros8_taint (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.step fun s P p b sp _ _ => WP.mono (zeros_ok P b) fun _ ⟨b', m'⟩ =>
      ⟨b', by rw [m']; exact sp.wb (.inr (by omega)) (by rw [List.length_replicate]; omega)⟩) ?_
  let Ψ := fun (a t : State) => M D W a t ∧ t.gpr .a4 = stackArg a 8 ∧ t.gpr .a1 = off (Ss a) (oY + 8) ∧
    t.gpr .a5 = BitVec.ofNat 64 D
  have hΨ : ∀ a t, M D W a t →
      WP isa (.block (([argBase, .load .d .a4 .t6 64] : List Instr) ++ yBase .a1 ++
        ([.addi .a1 .a1 8, .li .a5 H.D] : List Instr))) t (Ψ a) :=
    fun a t h => h.lift fun s P p b sp _ _ => WP.mono (digArgs_ok P hD hD64 b) fun t' ⟨o, e4, e1, e5⟩ =>
      ⟨⟨b.only (fits P) o, by rw [o.mem]; exact sp⟩, by rw [e4, p.1.args 8 (by decide)], by rw [e1, ss_eq p], e5⟩
  refine two_seq (Ψ := M D W) (two_seq (Ψ := Ψ) (digArgs_taint H (mpin (fun _ _ h => h.1.bs) [.s0])) hΨ
      (copy_taint (pins3 (fun _ _ h => h.1.1.bs) _ _ _ fun _ _ h => h.2)))
    (fun a t h => WP.seq (WP.mono (hΨ a t h) fun t' ⟨m, e4, e1, e5⟩ =>
      m.step fun s P p b sp _ _ =>
      WP.mono (digCopy_ok P hD0 hD64 b (by rw [e4, p.1.args 8 (by decide)]) (by rw [e1, ss_eq p]) e5)
        fun _ ⟨b', m'⟩ => ⟨b', by
          rw [m']; exact sp.wb (.inr (by omega)) (by rw [bytesAt_length]; omega)⟩)) ?_
  refine two_seq (Ψ := fun a t => M D W a t ∧ t.gpr .a1 = off (Ss a) (oY + 8 + D))
    (saltDst_taint H (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.lift fun s P p b sp _ _ => WP.mono (saltDst_ok hD hD64 b) fun t' ⟨o, e⟩ =>
      ⟨⟨b.only (fits P) o, by rw [o.mem]; exact sp⟩, by rw [e, ss_eq p]⟩) ?_
  exact copySalt_ct (fun _ => oY + 8 + D)

theorem mPrime_wp {a t : State} (h : M D W a t) : WP isa (mPrime H) t (M D W a) := by
  have hY : oY = 2048 := rfl
  have hP : oP = 1352 := rfl
  have hR : oRsa = 8192 := rfl
  exact h.step fun s P p b sp _ hf => WP.mono (mPrime_ok P hD hD0 hD64 b (by have := P.k2; unfold kk at hf; omega))
    fun _ ⟨b', m'⟩ => ⟨b', by
      have := P.k2; unfold kk at hf
      rw [m']
      exact ((sp.wb (.inr (by omega)) (by rw [List.length_replicate]; omega)).wb (.inr (by omega))
        (by rw [bytesAt_length]; omega)).wb (.inr (by omega)) (by rw [bytesAt_length]; omega)⟩

omit hD0 in
/-- `0x01` and the salt in `EM`, in both runs. -/
theorem putSalt_ct : RelCT isa (Two (M D W)) (putSalt H) fun _ _ => True := by
  unfold putSalt
  let d := fun (a : State) => kk a - (stackArg a 11).toNat - D - 1
  refine two_seq (Ψ := fun a t => M D W a t ∧ t.gpr .a1 = off (Ss a) (d a))
    (saltHead_taint H (mpin (fun _ _ h => h.1.bs) [.s0, .s1, .s4]))
    (fun a t h => h.lift fun s P p b sp _ hf => ?_) (copySalt_ct d)
  have := loN_le s
  have k2 : kk s ≤ 1024 := P.k2
  have hP : oP = 1352 := rfl
  exact WP.mono (saltHead_ok P hD hD64 b (by omega)) fun t' ⟨b', m', a1⟩ =>
    ⟨⟨b', by rw [m']; exact sp.w8 (by omega) _⟩, by rw [a1, ss_eq p, p.1.pKk, p.1.args 11 (by decide)]⟩

omit hD0 in
theorem putSalt_wp {a t : State} (h : M D W a t) : WP isa (putSalt H) t (M D W a) :=
  h.step fun s P p b sp _ hf => WP.mono (putSalt_ok P hD hD64 b (by have := loN_le s; omega)) fun _ ⟨b', m'⟩ =>
    ⟨b', by
      have k2 : kk s ≤ 1024 := P.k2
      have hP : oP = 1352 := rfl
      have hR : oRsa = 8192 := rfl
      rw [m']
      exact (sp.w8 (by omega) _).wb (.inl (by rw [bytesAt_length]; omega)) (by rw [bytesAt_length]; omega)⟩

end

/-- MGF1's arguments for `DB`, of the anchor. -/
abbrev qD (D : Nat) (a : State) : Nat × Nat × Nat × Nat := (kk a - D - 1, D, loN a, kk a - loN a - D - 1)

theorem qD_fit {D : Nat} {a : State} (C : Ck D a) : MFit (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 := by
  have := C.fit; have := C.k2; have := loN_le a
  show MFit (kk a - D - 1) D (loN a) (kk a - loN a - D - 1)
  exact ⟨by omega, by omega, .inr (by omega), by omega⟩

/-- MGF1's arguments, in a run. -/
abbrev MA (D : Nat) (W : VT) (a t : State) : Prop :=
  MgfAT Ss vS (PreST D W) (PubST W) (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 a t

/-- Before MGF1: its arguments, the saved arguments and the checks. -/
def MgfS (D : Nat) (W : VT) (a t : State) : Prop :=
  MA D W a t ∧ (∃ s, PreS D s ∧ PubK a s ∧ Spilled s t.mem) ∧ Ck D a

section
variable {W : VT} (cH : HashCT W.hH) (hF : W.H.F ≤ 208) {Hs : Spec.Mgf1.Hash} (hHl : Hs.len = W.H.D)
  (hG : HashOK W.G) (cG : HashCT hG) (hFG : W.G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = W.G.D) (hGv : Proof.Mgf1.Valid Gs)

include cG hFG hGh hGl hGv in
/-- `mgfXorT` with the anchor's arguments. -/
theorem mgf_ct : RelCT isa (Two fun a t => MA Hs.len W a t ∧ Ck Hs.len a) (mgfXorT W.g 15) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT Ss vS (PreST Hs.len W) (PubST W) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct (signOkT Hs.len W) hG cG hFG x.2 hGh hGl hGv (sTabG Hs.len W)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qD Hs.len a, qD_fit h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem main_ct : RelCT isa (Two (M Hs.len W)) (signMain W.H W.M.be W.f W.g) fun _ _ => True := by
  have hD0 : 0 < Hs.len := hHl ▸ W.hH.hD0
  have hD64 : Hs.len ≤ 64 := hHl ▸ W.hH.hD64
  have Fh := hfits W.hH
  obtain ⟨hE, hSt, hDg, hCt, hR⟩ := offs
  have hP : oP = 1352 := rfl
  have hCs : Impl.RsaPss.RISCV64.oCs = 1664 := rfl
  unfold signMain
  refine two_seq (Ψ := M Hs.len W) (mPrime_ct hHl.symm hD0 hD64) (fun a t h => mPrime_wp hHl.symm hD0 hD64 h) ?_
  -- `H`.
  refine two_seq (Ψ := M Hs.len W)
    (two_seq (Ψ := fun a t => M Hs.len W a t ∧ t.gpr .s6 = stackArg a 11)
      (hashArg_taint (mpin (fun _ _ h => h.1.bs) []))
      (fun a t h => h.lift fun s P p b sp _ _ => wp_mov fun t₁ o₁ e₁ => wp_nil
        ⟨⟨b.only (fits P) o₁, by rw [o₁.mem]; exact sp⟩, by rw [e₁, Base.ssl b, p.1.args 11 (by decide)]⟩)
      ((hashFixedG_ct (signOkT Hs.len W).s (sTab Hs.len W) cH hF (fun P => P.1.als) (fun a => stackArg a 11)).mono
        (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1.1.bt, h₁.2, by have := h₁.1.2.fit; have := h₁.1.2.k2; omega⟩,
          ⟨h₂.1.1.bt, h₂.2, by have := h₂.1.2.fit; have := h₂.1.2.k2; omega⟩⟩) fun _ _ h => h))
    (fun a t ⟨⟨s, P, p, b, sp, y⟩, C⟩ => by
      have hf := (ck_s p.1 C).2
      unfold hashM
      exact WP.seq (WP.of_syms (wp_mov fun t₁ o₁ e₁ => wp_nil fun y₁ => WP.mono
        (hashFixedG_ok (fits P.1) hF P.2.1 P.1.als hHl.symm (sl := (stackArg s 11).toNat)
          (by rw [e₁, Base.ssl b, ofNat_toNat]) (b.only (fits P.1) o₁) (y₁.trans y)
          (by have := P.1.k2; unfold kk at hf; omega)) fun _ ⟨⟨b', _, s', _⟩, y'⟩ =>
          ⟨⟨s, P, p, b', (show Spilled s t₁.mem by rw [o₁.mem]; exact sp).same s' (by
            have := Fh.1; have hY : oY = 2048 := rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
            omega), y'⟩, C⟩))) ?_
  -- `EM`.
  refine two_seq (Ψ := M Hs.len W) (clearEm_taint (mpin (fun _ _ h => h.1.bs) [.s0]))
    (fun a t h => h.step fun s P p b sp _ _ => WP.mono (clearEm_ok P b) fun _ ⟨b', m'⟩ =>
      ⟨b', by
        rw [m']
        exact sp.wb (.inl (by rw [List.length_replicate]; omega)) (by rw [List.length_replicate]; omega)⟩) ?_
  refine two_seq (Ψ := M Hs.len W) (putSalt_ct hHl.symm hD64) (fun a t h => putSalt_wp hHl.symm hD64 h) ?_
  refine two_seq (Ψ := M Hs.len W) (putH_taint W.H (mpin (fun _ _ h => h.1.bs) [.s0, .s1]))
    (fun a t h => h.step fun s P p b sp _ hf => WP.mono (putH_ok P hHl.symm hD0 hD64 b (by omega))
      fun _ ⟨b', m'⟩ => ⟨b', by
        have k2 : kk s ≤ 1024 := P.k2
        rw [m']
        exact (sp.wb (.inl (by rw [bytesAt_length]; omega)) (by rw [bytesAt_length]; omega)).w8 (by omega) _⟩) ?_
  -- `maskedDB`.
  refine two_seq (Ψ := MgfS Hs.len W) (dbArgs_taint W.H (mpin (fun _ _ h => h.1.bs) []))
    (fun a t ⟨⟨s, P, p, b, sp, y⟩, C⟩ => ?_) ?_
  · have h0 := (ck_s p.1 C).1
    have hf := (ck_s p.1 C).2
    exact WP.mono_syms (dbArgs_ok P.1 hHl.symm hD64 b h0 (by omega)) fun t' ⟨b', m', e6, e7, e8, e9⟩ y' =>
      ⟨⟨s, P, p, b', y'.trans y, by rw [e6, ss_eq p.1, p.1.1.pKk], e7, by rw [e8, ss_eq p.1, p.1.1.pLoN p.1.2],
        by rw [e9, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩, ⟨s, P.1, p.1, by rw [m']; exact sp⟩, C⟩
  refine two_seq (Ψ := M Hs.len W) ((mgf_ct hG cG hFG hGh hGl hGv).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1, h₁.2.2⟩, ⟨h₂.1, h₂.2.2⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, P, p, b, y, h6, h7, h8, h9⟩, ⟨s', P', p', sp⟩, C⟩ => WP.mono (mgfXorT_ok (fits P.1) hG hFG P.2.2
      hGh hGl hGv (qD_fit C) b y (by rw [h6, ss_eq p.1]) h7 (by rw [h8, ss_eq p.1]) h9) fun t'' ⟨⟨b'', v''⟩, y''⟩ =>
        ⟨⟨s, P, p, b'', ((sp.anchor p').ofAnchor p.1).mix v''
          (by show loN a + (kk a - loN a - Hs.len - 1) ≤ oP; have := C.k2; have := loN_le a; omega), y''⟩, C⟩) ?_
  refine two_seq (Ψ := M Hs.len W) (clearTop_taint (mpin (fun _ _ h => h.1.bs) [.s0, .s3]))
    (fun a t h => h.step fun s P p b sp h0 _ => WP.mono (clearTop_ok P b sp h0) fun _ ⟨b', m'⟩ =>
      ⟨b', by have := loN_le s; rw [m']; exact sp.w8 (by omega) _⟩) ?_
  -- The private operation.
  exact priv_ct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- After the prologue, from an entry state with the anchor's public data. -/
abbrev Pr (D : Nat) (W : VT) (a t : State) : Prop := ∃ s, PreST D W s ∧ PubST W a s ∧ Pro s t ∧ t.syms = s.syms

/-- After the spills, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (W : VT) (a t : State) : Prop :=
  ∃ s, PreST D W s ∧ PubST W a s ∧ Entered s t ∧ t.syms = s.syms

include cH hF hHl hG cG hFG hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En Hs.len W)) (checks W.H W.M.be W.f W.g) fun _ _ => True := by
  have hD64 : W.H.D ≤ 64 := W.hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Hs.len W a t) → ∀ rs : List Reg,
      (∀ r ∈ rs, r ∈ Reg.s0 :: fx) → Pins Φ rs := fun h rs hrs =>
    mpin (an := id) (fun a t hp => let ⟨s, P, p, E, _⟩ := h a t hp; ⟨s, P, p, E.base⟩) rs hrs
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.t1, E₂.t1, n0S, n0S, p₁.1.1.byte p₁.1.2, p₂.1.1.byte p₂.1.2])
    (fail_taint (pin (fun _ _ h => h.1) _ (by decide))) ?_
  let E1 := fun (a t : State) => ∃ s, PreST Hs.len W s ∧ PubST W a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a2) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < W.H.D + 2))
    (chkEm_taint W.H (pin (fun _ _ h => h.1) [] (by decide))) (fun a t ⟨⟨s, P, p, E, y⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hD64 E h0) fun t' ⟨E', r3⟩ y' =>
      ⟨⟨s, P, p, E', y'.trans y, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, y, _⟩ := h.1.1; ⟨s, P, p, E, y⟩) _ (by decide))) ?_
  let E2 := fun (a t : State) => ∃ s, PreST Hs.len W s ∧ PubST W a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .a2) ≠ 0 ∧ W.H.D + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < W.H.D + 2)) ∧
      isa.eval (.nonzero .a0) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, y, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < W.H.D + 2 := by simpa using hc
    exact ⟨s, P, p, E, y, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega⟩
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
      isa.eval (.nonzero .a0) t = some false → M Hs.len W a t :=
    fun {a t} ⟨⟨⟨s, P, p, E, y, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (W.H.D + 2) < (stackArg a 11).toNat := by simpa using hc
    have k2 : kk s ≤ 1024 := P.1.k2
    rw [p.1.1.byte p.1.2, p.1.1.pKk, p.1.1.pLoN p.1.2] at *
    exact ⟨⟨s, P, p, E.base, E.sp, y⟩, ⟨h0, by rw [hHl]; omega, k2⟩⟩
  exact (main_ct cH hF hHl hG cG hFG hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

variable {Hh : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = W.hH.SH.H.hash x) (hHv : Proof.Mgf1.Valid Hs)

include cH hF hHl hG cG hFG hGh hGl hGv hHh hHv in
/-- Two runs of the code for the hash function `W.H` from entry states with
the same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreST Hs.len W s ∧ PubST W a s) (signFor W.H W.M.be W.f W.g)
    fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine two_seq (Ψ := Pr Hs.len W)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by
      rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.2.1.1.sp, h₂.2.1.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by
      subst e; exact WP.mono_syms (pro_ok P.1) fun t E y => ⟨s, P, p, E, y.trans rfl⟩) ?_
  refine two_seq (Ψ := En Hs.len W)
    (spill_taint fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => ⟨by
      rw [E₁.sv.sp, E₂.sv.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [E₁.s0, E₂.s0, ss_eq p₁.1, ss_eq p₂.1]
        · rw [E₁.args .a2 (by decide), E₂.args .a2 (by decide), p₁.1.1.g .a2 (by decide),
            p₂.1.1.g .a2 (by decide)]⟩)
    (fun a t ⟨s, P, p, E, y⟩ => WP.mono_syms (spill_ok P.1 E) fun t' E' y' => ⟨s, P, p, E', y'.trans y⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreST Hs.len W s ∧ PubST W a s ∧ Saves s t)
    (checks_ct cH hF hHl hG cG hFG hGh hGl hGv) fun a t ⟨s, P, p, E, y⟩ =>
      WP.mono (checks_done P.1 W.hH hF P.2.1 hHh hHl hHv hG hFG P.2.2 hGh hGl hGv E y) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.RISCV64.Sg
