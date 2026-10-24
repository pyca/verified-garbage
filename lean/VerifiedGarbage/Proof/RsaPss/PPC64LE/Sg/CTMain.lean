module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTPriv
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgf
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Em
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Blocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Mgf
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBase
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks

/-!
# RSASSA-PSS signing on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike (`code_ct`): the code between the
calls by the taint analysis (`CTBlocks`), split where it uses a pointer it
loads from the stack, with that pointer and the lengths the anchor's; the
checks' branches by `two_ite`, on values both runs compute from the public
data (the modulus' first byte, its length and the salt length); the hash of
`M'` by `hashFixedG_ct`, MGF1 by `mgfXor_ct`, and the private operation by
`priv_ct`. What each run satisfies between them (`M`: `Base` and the checks
passed, `Ck`) follows from correctness.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa copyLoop restore mgfXor)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base off fx B B.sp B.only pins_of two_seq HashCT MgfA MFit mgfXor_ct mgfXor_ok
  fail_taint restore_taint allocated_sp allocated_gpr fb)
open VG.Proof.RsaPss.PPC64LE (hashFixedG_ct hashFixedG_ok)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_addi wp_nil eval_zero eval_nonzero)

/-- The checks passed, in terms of the anchor. -/
structure Ck (D : Nat) (a : State) : Prop where
  h0 : a.mem (a.gpr .r5) ≠ 0
  fit : D + (stackArg a 10).toNat + 2 ≤ kk a - loN a
  k2 : kk a ≤ 1024

/-- `Base` from an entry state with the anchor's public data, which passed
the checks. -/
abbrev M (D : Nat) (a t : State) : Prop := BS D a t ∧ Ck D a

section
variable {D : Nat}

theorem ss_eq {a s : State} (p : PubK a s) : Ss s = Ss a := p.1.args 11 (by decide)

theorem ck_s {a s : State} (p : PubK a s) (C : Ck D a) :
    s.mem (s.gpr .r5) ≠ 0 ∧ D + (stackArg s 10).toNat + 2 ≤ kk s - loN s := by
  rw [p.1.byte p.2, p.1.pLoN p.2, p.1.pKk, p.1.args 10 (by decide)]; exact ⟨C.h0, C.fit⟩

/-- A step keeping `Base`, from the entry state of a run. -/
theorem M.step {c : Prog isa} {a t : State} (h : M D a t)
    (k : ∀ s, PreS D s → PubK a s → Base Ss vS s t → s.mem (s.gpr .r5) ≠ 0 →
      D + (stackArg s 10).toNat + 2 ≤ kk s - loN s → WP isa c t fun t' => Base Ss vS s t') :
    WP isa c t (M D a) :=
  let ⟨⟨s, P, p, b⟩, C⟩ := h
  WP.mono (k s P p b (ck_s p C).1 (ck_s p C).2) fun _ b' => ⟨⟨s, P, p, b'⟩, C⟩

theorem mpin {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BS D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of (signOk D) h rs hrs

/-- `r4`, `r5` and `r6` as functions of the anchor. -/
theorem pins3 {α : Type} {Φ : α → State → Prop} {an : α → State} (hb : ∀ x t, Φ x t → BS D (an x) t)
    (v4 v5 v6 : α → BitVec 64) (hv : ∀ x t, Φ x t → t.gpr .r4 = v4 x ∧ t.gpr .r5 = v5 x ∧ t.gpr .r6 = v6 x) :
    Pins Φ [.r4, .r5, .r6] := fun x t₁ t₂ h₁ h₂ => by
  obtain ⟨a₁, b₁, c₁⟩ := hv x t₁ h₁
  obtain ⟨a₂, b₂, c₂⟩ := hv x t₂ h₂
  refine ⟨((hb x t₁ h₁).sp (signOk D)).trans ((hb x t₂ h₂).sp (signOk D)).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm]

/-- `copySalt` to `S + d a`, in both runs. -/
theorem copySalt_ct (d : State → Nat) :
    RelCT isa (Two fun a t => M D a t ∧ t.gpr .r5 = off (Ss a) (d a)) copySalt fun _ _ => True := by
  unfold copySalt
  refine two_seq (Ψ := fun a t => M D a t ∧ t.gpr .r4 = stackArg a 9 ∧ t.gpr .r5 = off (Ss a) (d a) ∧
      t.gpr .r6 = stackArg a 10) (saltArgs_taint (mpin (fun _ _ h => h.1.1) []))
    (fun a t ⟨⟨⟨s, P, p, b⟩, C⟩, h5⟩ => WP.mono (saltArgs_ok P b) fun t' ⟨o, e4, e6⟩ =>
      ⟨⟨⟨s, P, p, b.only (fits P) o⟩, C⟩, by rw [e4, p.1.args 9 (by decide)], by rw [o.get .r5, h5],
        by rw [e6, p.1.args 10 (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2.2.2, h₂.2.2.2])
    (copy_taint (pins3 (fun _ _ h => h.1.1.1) _ _ _ fun _ _ h => h.1.2)) (skip_taint (mpin (fun _ _ h => h.1.1.1) []))

theorem copySalt_wp {d : State → Nat} {a t : State} (h : M D a t) (h5 : t.gpr .r5 = off (Ss a) (d a))
    (hd : d a + (stackArg a 10).toNat ≤ oRsa) : WP isa copySalt t (M D a) :=
  h.step fun s P p b _ _ => WP.mono (copySalt_ok P b (d := d a) (by rw [h5, ss_eq p])
    (by rw [p.1.args 10 (by decide)]; exact hd)) fun _ h => h.1

variable {H : Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
include hD hD0 hD64

/-- `M'`, in both runs. -/
theorem mPrime_ct : RelCT isa (Two (M D)) (mPrime H) fun _ _ => True := by
  have hY : oY = 2560 := rfl
  unfold mPrime
  refine two_seq (Ψ := M D) (zeros8_taint (mpin (fun _ _ h => h.1) [.r14]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (zeros_ok P b) fun _ h => h.1) ?_
  let Ψ := fun (a t : State) => M D a t ∧ t.gpr .r4 = stackArg a 8 ∧ t.gpr .r5 = off (Ss a) (oY + 8) ∧
    t.gpr .r6 = BitVec.ofNat 64 D
  have hΨ : ∀ a t, M D a t → WP isa (.block (ldArg .r4 8 ++ [.addi .r5 .r14 (oY + 8), .li .r6 H.D])) t (Ψ a) :=
    fun a t ⟨⟨s, P, p, b⟩, C⟩ => WP.mono (digArgs_ok P hD hD64 b) fun t' ⟨o, e4, e5, e6⟩ =>
      ⟨⟨⟨s, P, p, b.only (fits P) o⟩, C⟩, by rw [e4, p.1.args 8 (by decide)], by rw [e5, ss_eq p], e6⟩
  refine two_seq (Ψ := M D) (two_seq (Ψ := Ψ) (digArgs_taint H (mpin (fun _ _ h => h.1) [])) hΨ
      (copy_taint (pins3 (fun _ _ h => h.1.1) _ _ _ fun _ _ h => h.2)))
    (fun a t h => WP.seq (WP.mono (hΨ a t h) fun t' ⟨⟨⟨s, P, p, b⟩, C⟩, e4, e5, e6⟩ =>
      WP.mono (digCopy_ok P hD0 hD64 b (by rw [e4, p.1.args 8 (by decide)]) (by rw [e5, ss_eq p]) e6)
        fun _ h => ⟨⟨s, P, p, h.1⟩, C⟩)) ?_
  refine two_seq (Ψ := fun a t => M D a t ∧ t.gpr .r5 = off (Ss a) (oY + 8 + D))
    (saltDst_taint H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b⟩, C⟩ => wp_addi (h := by unfold oY; omega) fun t' o e =>
      wp_nil ⟨⟨⟨s, P, p, b.only (fits P) o⟩, C⟩, by rw [e, b.r14, ss_eq p, hD]⟩) ?_
  exact copySalt_ct (fun _ => oY + 8 + D)

theorem mPrime_wp {a t : State} (h : M D a t) : WP isa (mPrime H) t (M D a) :=
  h.step fun s P p b _ hf => WP.mono (mPrime_ok P hD hD0 hD64 b (by have := P.k2; unfold kk at hf; omega))
    fun _ h => h.1

omit hD0 in
/-- `0x01` and the salt in `EM`, in both runs. -/
theorem putSalt_ct : RelCT isa (Two (M D)) (putSalt H) fun _ _ => True := by
  unfold putSalt
  let d := fun (a : State) => oEm + (kk a - (stackArg a 10).toNat - D - 1)
  refine two_seq (Ψ := fun a t => M D a t ∧ t.gpr .r5 = off (Ss a) (d a))
    (putSaltHead_taint H (mpin (fun _ _ h => h.1) [.r14, .r15, .r19]))
    (fun a t ⟨⟨s, P, p, b⟩, C⟩ => ?_) (copySalt_ct d)
  have hf := (ck_s p C).2
  have := loN_le s
  exact WP.mono (saltHead_ok P hD hD64 b (by omega)) fun t' ⟨b', _, _, a5⟩ =>
    ⟨⟨⟨s, P, p, b'⟩, C⟩, by rw [a5, ss_eq p, p.1.pKk, p.1.args 10 (by decide)]⟩

omit hD0 in
theorem putSalt_wp {a t : State} (h : M D a t) : WP isa (putSalt H) t (M D a) :=
  h.step fun s P p b _ hf => WP.mono (putSalt_ok P hD hD64 b (by have := loN_le s; omega)) fun _ h => h.1

end

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)

/-- MGF1's arguments for `DB`, of the anchor. -/
abbrev qD (D : Nat) (a : State) : Nat × Nat × Nat × Nat := (oEm + (kk a - D - 1), D, oEm + loN a, kk a - loN a - D - 1)

theorem qD_fit {D : Nat} {a : State} (C : Ck D a) : MFit (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 := by
  have := C.fit; have := C.k2; have := loN_le a
  have hE : oEm = 0 := rfl
  show MFit (oEm + (kk a - D - 1)) D (oEm + loN a) (kk a - loN a - D - 1)
  exact ⟨by omega, by omega, .inr (by omega), by omega⟩

include cH hGh hGl hGv in
/-- `mgfXor` with the anchor's arguments. -/
theorem mgf_ct : RelCT isa (Two fun a t => MgfA Ss vS (PreS Gs.len) PubK (qD Gs.len a).1 (qD Gs.len a).2.1
    (qD Gs.len a).2.2.1 (qD Gs.len a).2.2.2 a t ∧ Ck Gs.len a) (mgfXor H) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfA Ss vS (PreS Gs.len) PubK x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXor_ct (signOk Gs.len) hH cH x.2 hGh hGl hGv).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qD Gs.len a, qD_fit h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include cH hGh hGl hGv in
theorem main_ct : RelCT isa (Two (M Gs.len)) (signMain H) fun _ _ => True := by
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hE : oEm = 0 := rfl
  unfold signMain
  refine two_seq (Ψ := M Gs.len) (mPrime_ct hGl.symm hD0 hD64) (fun a t h => mPrime_wp hGl.symm hD0 hD64 h) ?_
  -- `H`.
  refine two_seq (Ψ := M Gs.len)
    ((hashFixedG_ct (signOk Gs.len) hH cH hGl.symm (fun a => (stackArg a 10).toNat) fun a => by
      show stackArg a 10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1, by have := h₁.2.fit; have := h₁.2.k2; omega⟩,
        ⟨h₂.1, by have := h₂.2.fit; have := h₂.2.k2; omega⟩⟩) fun _ _ h => h)
    (fun a t h => h.step fun s P p b _ hf => WP.mono (hashFixedG_ok (fits P) hH hGl.symm
      (sl := (stackArg s 10).toNat) (by show stackArg s 10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) b
      (by have := P.k2; unfold kk at hf; omega)) fun _ h => h.1) ?_
  -- `EM`.
  refine two_seq (Ψ := M Gs.len) (clearEm_taint (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (clearEm_ok P b) fun _ h => h.1) ?_
  refine two_seq (Ψ := M Gs.len) (putSalt_ct hGl.symm hD64) (fun a t h => putSalt_wp hGl.symm hD64 h) ?_
  refine two_seq (Ψ := M Gs.len) (putH_taint H (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ hf => WP.mono (putH_ok P hGl.symm hD0 hD64 b (by omega)) fun _ h => h.1) ?_
  -- `maskedDB`.
  refine two_seq (Ψ := fun a t => MgfA Ss vS (PreS Gs.len) PubK (qD Gs.len a).1 (qD Gs.len a).2.1
      (qD Gs.len a).2.2.1 (qD Gs.len a).2.2.2 a t ∧ Ck Gs.len a) (dbArgs_taint H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b⟩, C⟩ => ?_) ?_
  · have h0 := (ck_s p C).1
    have hf := (ck_s p C).2
    exact WP.mono (dbArgs_ok P hGl.symm hD64 b h0 (by omega)) fun t' ⟨b', _, e24, e25, e26, e27⟩ =>
      ⟨⟨s, P, p, b', by rw [e24, ss_eq p, p.1.pKk], e25, by rw [e26, ss_eq p, p.1.pLoN p.2],
        by rw [e27, p.1.pKk, p.1.pLoN p.2]⟩, C⟩
  refine two_seq (Ψ := M Gs.len) (mgf_ct hH cH hGh hGl hGv)
    (fun a t ⟨⟨s, P, p, b, h24, h25, h26, h27⟩, C⟩ => WP.mono (mgfXor_ok (fits P) hH hGh hGl hGv (qD_fit C) b
      (by rw [h24, ss_eq p]) h25 (by rw [h26, ss_eq p]) h27) fun t' ⟨b', _⟩ => ⟨⟨s, P, p, b'⟩, C⟩) ?_
  refine two_seq (Ψ := M Gs.len) (clearTop_taint (mpin (fun _ _ h => h.1) [.r14, .r20, .r23]))
    (fun a t h => h.step fun s P p b h0 _ => WP.mono (clearTop_ok P b h0) fun _ h => h.1) ?_
  -- The private operation.
  exact priv_ct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (a t : State) : Prop := ∃ s, PreS D s ∧ PubK a s ∧ Entered s t

include cH hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En Gs.len)) (checks H) fun _ _ => True := by
  have hD64 : H.D ≤ 64 := hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Gs.len a t) → ∀ rs : List Reg,
      (∀ r ∈ rs, r ∈ Reg.r14 :: fx) → Pins Φ rs := fun h rs hrs =>
    mpin (an := id) (fun a t hp => let ⟨s, P, p, E⟩ := h a t hp; ⟨s, P, p, E.base⟩) rs hrs
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁⟩ ⟨s₂, _, p₂, E₂⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, n0, n0, p₁.1.byte p₁.2, p₂.1.byte p₂.2])
    (fail_taint (pin (fun _ _ h => h.1) _ (by decide))) ?_
  let E1 := fun (a t : State) => ∃ s, PreS Gs.len s ∧ PubK a s ∧ Entered s t ∧ s.mem (s.gpr .r5) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < H.D + 2))
    (chkEm_taint H (pin (fun _ _ h => h.1) [] (by decide))) (fun a t ⟨⟨s, P, p, E⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono (chkEm_ok P hD64 E h0) fun t' ⟨E', r3⟩ =>
      ⟨⟨s, P, p, E', h0⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩) _ (by decide))) ?_
  let E2 := fun (a t : State) => ∃ s, PreS Gs.len s ∧ PubK a s ∧ Entered s t ∧ s.mem (s.gpr .r5) ≠ 0 ∧
    H.D + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < H.D + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < H.D + 2 := by simpa using hc
    exact ⟨s, P, p, E, h0, by rw [p.1.pKk, p.1.pLoN p.2]; omega⟩
  -- The salt's length.
  refine two_seq (Ψ := fun a t => E2 a t ∧
      (t.gpr .r3 != 0) = decide (kk a - loN a - (H.D + 2) < (stackArg a 10).toNat))
    (chkSalt_taint H (pin (fun _ _ h => let ⟨s, P, p, E, _⟩ := e2 h; ⟨s, P, p, E⟩) [] (by decide)))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, h0, hem⟩ := e2 h
    exact WP.mono (chkSalt_ok P hD64 E h0 hem) fun t' ⟨E', r3⟩ =>
      ⟨⟨s, P, p, E', h0, hem⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2, p.1.args 10 (by decide)]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩) _ (by decide))) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧
      (t.gpr .r3 != 0) = decide (kk a - loN a - (H.D + 2) < (stackArg a 10).toNat)) ∧
      isa.eval (.nonzero .d .r3) t = some false → M Gs.len a t := fun {a t} ⟨⟨⟨s, P, p, E, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (H.D + 2) < (stackArg a 10).toNat := by simpa using hc
    have k2 : kk s ≤ 1024 := P.k2
    rw [p.1.byte p.2, p.1.pKk, p.1.pLoN p.2] at *
    exact ⟨⟨s, P, p, E.base⟩, ⟨h0, by omega, k2⟩⟩
  exact (main_ct hH cH hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

include cH hGh hGl hGv in
/-- Two runs of `vg_rsa_pss_<H>_mgf1_<H>_sign` from entry states with the
same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreS Gs.len s ∧ PubK a s) (sign H) fun _ _ => True := by
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.sp.trans h₂.2.1.sp.symm, fun _ h => nomatch h⟩) ?_
  unfold body
  refine two_seq (Ψ := En Gs.len)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.sp,
      h₂.2.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂, allocated_gpr, allocated_gpr, h₁.2.1.g .r5 (by decide),
          h₂.2.1.g .r5 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P) fun t E => ⟨s, P, p, E⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreS Gs.len s ∧ PubK a s ∧ VG.Proof.RsaOaep.PPC64LE.Saves s t)
    (checks_ct hH cH hGh hGl hGv) fun a t ⟨s, P, p, E⟩ =>
      WP.mono (checks_done P hH hGh hGl hGv E) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg
