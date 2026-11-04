module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTPriv
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Em
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Blocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
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
`M'` through the hash function's table by `hashFixedG_ct`, MGF1 through its
table by `mgfXorT_ct`, and the private operation by `priv_ct`; the load of
the hash function's index and the choice by it by `byIdx_ct`. What each run satisfies between them (`M`: `Base` and the checks
passed, `Ck`) follows from correctness.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa copyLoop restore mgfXorT frameBytes arg tword)
open VG.Impl.RsaPss.PPC64LE (oY byIdx idxs shapeOf)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base off fx B B.sp B.only pins_of two_seq HashCT MgfAT MFit mgfXorT_ct mgfXorT_ok
  fail_taint restore_taint allocated_sp allocated_gpr fb BT BT.b TabS TabA Ok)
open VG.Proof.RsaPss.PPC64LE (hashFixedG_ct hashFixedG_ok Tabs MdTabS MdTabA argA_ok wordA_ok byIdx_ct idxs_certs
  twA11_taint twB11_taint tab_sub)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_addi wp_nil eval_zero eval_nonzero)

/-- The checks passed, in terms of the anchor. -/
structure Ck (D : Nat) (a : State) : Prop where
  h0 : a.mem (a.gpr .r5) ≠ 0
  fit : D + (stackArg a 11).toNat + 2 ≤ kk a - loN a
  k2 : kk a ≤ 1024

/-- The tables on entry. -/
def STabsOn (Z : Tabs) (s : State) : Prop :=
  TabS Z.G Z.g gArg Ss s (stackArg s 15) ∧ MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Ss s (stackArg s 14)

/-- The anchor's addresses of the tables' functions. -/
def SymsAg (Z : Tabs) (a s : State) : Prop :=
  s.syms Z.G.initN = a.syms Z.G.initN ∧ s.syms Z.G.updN = a.syms Z.G.updN ∧ s.syms Z.G.finN = a.syms Z.G.finN ∧
    s.syms Z.H.initN = a.syms Z.H.initN ∧ s.syms Z.H.updN = a.syms Z.H.updN ∧
    s.syms Z.H.finN = a.syms Z.H.finN ∧ s.syms Z.cn = a.syms Z.cn ∧ s.syms Z.dn = a.syms Z.dn

/-- An entry state, with the tables. -/
abbrev PreT (Z : Tabs) (D : Nat) (s : State) : Prop := PreS D s ∧ STabsOn Z s

/-- The anchor's public data and addresses of the tables' functions. -/
abbrev PubT (Z : Tabs) (a s : State) : Prop := PubK a s ∧ SymsAg Z a s

theorem tOk {D : Nat} {Z : Tabs} : Ok Ss vS (PreT Z D) (PubT Z) := signOk D (fun P => P.1) (fun p => p.1)

theorem tabG {D : Nat} (Z : Tabs) : TabA Z.G Z.g gArg Ss (PreT Z D) (PubT Z) :=
  ⟨fun P => P.2.1, fun p => p.1.1.args 15 (by decide), fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1⟩

theorem tabH {D : Nat} (Z : Tabs) : MdTabA Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Ss (PreT Z D) (PubT Z) :=
  ⟨fun P => P.2.2, fun p => p.1.1.args 14 (by decide), fun p => p.2.2.2.2.1, fun p => p.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2⟩

/-- `Base` from an entry state with the anchor's public data, which passed
the checks. -/
abbrev M (D : Nat) (Z : Tabs) (a t : State) : Prop := BT Ss vS (PreT Z D) (PubT Z) a t ∧ Ck D a

section
variable {D : Nat} {Z : Tabs}

theorem ss_eq {a s : State} (p : PubK a s) : Ss s = Ss a := p.1.args 12 (by decide)

theorem ck_s {a s : State} (p : PubT Z a s) (C : Ck D a) :
    s.mem (s.gpr .r5) ≠ 0 ∧ D + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by
  rw [p.1.1.byte p.1.2, p.1.1.pLoN p.1.2, p.1.1.pKk, p.1.1.args 11 (by decide)]; exact ⟨C.h0, C.fit⟩

/-- A step keeping `Base`, from the entry state of a run. -/
theorem M.step {c : Prog isa} {a t : State} (h : M D Z a t)
    (k : ∀ s, PreS D s → PubK a s → Base Ss vS s t → s.mem (s.gpr .r5) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s → WP isa c t fun t' => Base Ss vS s t') :
    WP isa c t (M D Z a) :=
  let ⟨⟨s, P, p, b, sy⟩, C⟩ := h
  WP.mono_syms (k s P.1 p.1 b (ck_s p C).1 (ck_s p C).2) fun _ b' y => ⟨⟨s, P, p, b', y.trans sy⟩, C⟩

theorem mpin {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → BT Ss vS (PreT Z D) (PubT Z) (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of tOk (fun x t hx => (h x t hx).b) rs hrs

/-- `r4`, `r5` and `r6` as functions of the anchor. -/
theorem pins3 {α : Type} {Φ : α → State → Prop} {an : α → State}
    (hb : ∀ x t, Φ x t → BT Ss vS (PreT Z D) (PubT Z) (an x) t)
    (v4 v5 v6 : α → BitVec 64) (hv : ∀ x t, Φ x t → t.gpr .r4 = v4 x ∧ t.gpr .r5 = v5 x ∧ t.gpr .r6 = v6 x) :
    Pins Φ [.r4, .r5, .r6] := fun x t₁ t₂ h₁ h₂ => by
  obtain ⟨a₁, b₁, c₁⟩ := hv x t₁ h₁
  obtain ⟨a₂, b₂, c₂⟩ := hv x t₂ h₂
  refine ⟨((hb x t₁ h₁).b.sp tOk).trans ((hb x t₂ h₂).b.sp tOk).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm]

/-- `copySalt` to `S + d a`, in both runs. -/
theorem copySalt_ct (d : State → Nat) :
    RelCT isa (Two fun a t => M D Z a t ∧ t.gpr .r5 = off (Ss a) (d a)) copySalt fun _ _ => True := by
  unfold copySalt
  refine two_seq (Ψ := fun a t => M D Z a t ∧ t.gpr .r4 = stackArg a 10 ∧ t.gpr .r5 = off (Ss a) (d a) ∧
      t.gpr .r6 = stackArg a 11) (saltArgs_taint (mpin (fun _ _ h => h.1.1) []))
    (fun a t ⟨⟨⟨s, P, p, b, sy⟩, C⟩, h5⟩ => WP.mono_syms (saltArgs_ok P.1 b) fun t' ⟨o, e4, e6⟩ y =>
      ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e4, p.1.1.args 10 (by decide)], by rw [o.get .r5, h5],
        by rw [e6, p.1.1.args 11 (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2.2.2, h₂.2.2.2])
    (copy_taint (pins3 (fun _ _ h => h.1.1.1) _ _ _ fun _ _ h => h.1.2)) (skip_taint (mpin (fun _ _ h => h.1.1.1) []))

theorem copySalt_wp {d : State → Nat} {a t : State} (h : M D Z a t) (h5 : t.gpr .r5 = off (Ss a) (d a))
    (hd : d a + (stackArg a 11).toNat ≤ oRsa) : WP isa copySalt t (M D Z a) :=
  h.step fun s P p b _ _ => WP.mono (copySalt_ok P b (d := d a) (by rw [h5, ss_eq p])
    (by rw [p.1.args 11 (by decide)]; exact hd)) fun _ h => h.1

variable {H : Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
include hD hD0 hD64

/-- `M'`, in both runs. -/
theorem mPrime_ct : RelCT isa (Two (M D Z)) (mPrime H) fun _ _ => True := by
  have hY : oY = 2560 := rfl
  unfold mPrime
  refine two_seq (Ψ := M D Z) (zeros8_taint (mpin (fun _ _ h => h.1) [.r14]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (zeros_ok P b) fun _ h => h.1) ?_
  let Ψ := fun (a t : State) => M D Z a t ∧ t.gpr .r4 = stackArg a 8 ∧ t.gpr .r5 = off (Ss a) (oY + 8) ∧
    t.gpr .r6 = BitVec.ofNat 64 D
  have hΨ : ∀ a t, M D Z a t → WP isa (.block (ldArg .r4 8 ++ [.addi .r5 .r14 (oY + 8), .li .r6 H.D])) t (Ψ a) :=
    fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => WP.mono_syms (digArgs_ok P.1 hD hD64 b) fun t' ⟨o, e4, e5, e6⟩ y =>
      ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e4, p.1.1.args 8 (by decide)],
        by rw [e5, ss_eq p.1], e6⟩
  refine two_seq (Ψ := M D Z) (two_seq (Ψ := Ψ) (digArgs_taint H (mpin (fun _ _ h => h.1) [])) hΨ
      (copy_taint (pins3 (fun _ _ h => h.1.1) _ _ _ fun _ _ h => h.2)))
    (fun a t h => WP.seq (WP.mono (hΨ a t h) fun t' ⟨⟨⟨s, P, p, b, sy⟩, C⟩, e4, e5, e6⟩ =>
      WP.mono_syms (digCopy_ok P.1 hD0 hD64 b (by rw [e4, p.1.1.args 8 (by decide)]) (by rw [e5, ss_eq p.1]) e6)
        fun _ h y => ⟨⟨s, P, p, h.1, y.trans sy⟩, C⟩)) ?_
  refine two_seq (Ψ := fun a t => M D Z a t ∧ t.gpr .r5 = off (Ss a) (oY + 8 + D))
    (saltDst_taint H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => WP.of_syms (wp_addi (h := by unfold oY; omega) fun t' o e =>
      wp_nil fun y => ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e, b.r14, ss_eq p.1, hD]⟩)) ?_
  exact copySalt_ct (fun _ => oY + 8 + D)

theorem mPrime_wp {a t : State} (h : M D Z a t) : WP isa (mPrime H) t (M D Z a) :=
  h.step fun s P p b _ hf => WP.mono (mPrime_ok P hD hD0 hD64 b (by have := P.k2; unfold kk at hf; omega))
    fun _ h => h.1

omit hD0 in
/-- `0x01` and the salt in `EM`, in both runs. -/
theorem putSalt_ct : RelCT isa (Two (M D Z)) (putSalt H) fun _ _ => True := by
  unfold putSalt
  let d := fun (a : State) => oEm + (kk a - (stackArg a 11).toNat - D - 1)
  refine two_seq (Ψ := fun a t => M D Z a t ∧ t.gpr .r5 = off (Ss a) (d a))
    (putSaltHead_taint H (mpin (fun _ _ h => h.1) [.r14, .r15, .r19]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) (copySalt_ct d)
  have hf := (ck_s p C).2
  have := loN_le s
  exact WP.mono_syms (saltHead_ok P.1 hD hD64 b (by omega)) fun t' ⟨b', _, _, a5⟩ y =>
    ⟨⟨⟨s, P, p, b', y.trans sy⟩, C⟩, by rw [a5, ss_eq p.1, p.1.1.pKk, p.1.1.args 11 (by decide)]⟩

omit hD0 in
theorem putSalt_wp {a t : State} (h : M D Z a t) : WP isa (putSalt H) t (M D Z a) :=
  h.step fun s P p b _ hf => WP.mono (putSalt_ok P hD hD64 b (by have := loN_le s; omega)) fun _ h => h.1

end

section
variable {Z : Tabs} (hH : HashOK Z.H) (cH : HashCT hH) {Gs : Spec.Mgf1.Hash} (hGl : Gs.len = Z.H.D)
  (hG : HashOK Z.G) (cG : HashCT hG) {Gm : Spec.Mgf1.Hash} (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x)
  (hGml : Gm.len = Z.G.D) (hGmv : Proof.Mgf1.Valid Gm)

/-- MGF1's arguments for `DB`, of the anchor. -/
abbrev qD (D : Nat) (a : State) : Nat × Nat × Nat × Nat := (oEm + (kk a - D - 1), D, oEm + loN a, kk a - loN a - D - 1)

theorem qD_fit {D : Nat} {a : State} (C : Ck D a) : MFit (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 := by
  have := C.fit; have := C.k2; have := loN_le a
  have hE : oEm = 0 := rfl
  show MFit (oEm + (kk a - D - 1)) D (oEm + loN a) (kk a - loN a - D - 1)
  exact ⟨by omega, by omega, .inr (by omega), by omega⟩

/-- MGF1's arguments, from the anchor. -/
abbrev MgfL (D : Nat) (Z : Tabs) (a t : State) : Prop :=
  MgfAT Ss vS (PreT Z D) (PubT Z) (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 a t

include cG hGmh hGml hGmv in
/-- `mgfXorT` with the anchor's arguments. -/
theorem mgf_ct {D : Nat} : RelCT isa (Two fun a t => MgfL D Z a t ∧ Ck D a) (mgfXorT Z.g gArg) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT Ss vS (PreT Z D) (PubT Z) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct tOk hG cG x.2 hGmh hGml hGmv (tabG Z)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qD D a, qD_fit h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include hH cH hGl hG cG hGmh hGml hGmv in
theorem main_ct : RelCT isa (Two (M Gs.len Z)) (signMain Z.H Z.f Z.g) fun _ _ => True := by
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hE : oEm = 0 := rfl
  unfold signMain
  refine two_seq (Ψ := M Gs.len Z) (mPrime_ct hGl.symm hD0 hD64) (fun a t h => mPrime_wp hGl.symm hD0 hD64 h) ?_
  -- `H`.
  refine two_seq (Ψ := M Gs.len Z)
    ((hashFixedG_ct tOk hH cH (tabH Z) hGl.symm (fun a => (stackArg a 11).toNat) fun a => by
      show stackArg a 11 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1, by have := h₁.2.fit; have := h₁.2.k2; omega⟩,
        ⟨h₂.1, by have := h₂.2.fit; have := h₂.2.k2; omega⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) ?_
  · have hf := (ck_s p C).2
    exact WP.mono (hashFixedG_ok (fits P.1) hH P.2.2 hGl.symm (sl := (stackArg s 11).toNat)
      (by show stackArg s 11 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) b sy
      (by have := P.1.k2; unfold kk at hf; omega)) fun _ ⟨h, y⟩ => ⟨⟨s, P, p, h.1, y⟩, C⟩
  -- `EM`.
  refine two_seq (Ψ := M Gs.len Z) (clearEm_taint (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (clearEm_ok P b) fun _ h => h.1) ?_
  refine two_seq (Ψ := M Gs.len Z) (putSalt_ct hGl.symm hD64) (fun a t h => putSalt_wp hGl.symm hD64 h) ?_
  refine two_seq (Ψ := M Gs.len Z) (putH_taint Z.H (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ hf => WP.mono (putH_ok P hGl.symm hD0 hD64 b (by omega)) fun _ h => h.1) ?_
  -- `maskedDB`.
  refine two_seq (Ψ := fun a t => MgfL Gs.len Z a t ∧ Ck Gs.len a) (dbArgs_taint Z.H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) ?_
  · have h0 := (ck_s p C).1
    have hf := (ck_s p C).2
    exact WP.mono_syms (dbArgs_ok P.1 hGl.symm hD64 b h0 (by omega)) fun t' ⟨b', _, e24, e25, e26, e27⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy, by rw [e24, ss_eq p.1, p.1.1.pKk], e25, by rw [e26, ss_eq p.1, p.1.1.pLoN p.1.2],
        by rw [e27, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩, C⟩
  refine two_seq (Ψ := M Gs.len Z) (mgf_ct hG cG hGmh hGml hGmv)
    (fun a t ⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, C⟩ => WP.mono (mgfXorT_ok (fits P.1) hG P.2.1 hGmh hGml hGmv
      (qD_fit C) b sy (by rw [h24, ss_eq p.1]) h25 (by rw [h26, ss_eq p.1]) h27) fun t' ⟨⟨b', _⟩, y'⟩ =>
        ⟨⟨s, P, p, b', y'⟩, C⟩) ?_
  refine two_seq (Ψ := M Gs.len Z) (clearTop_taint (mpin (fun _ _ h => h.1) [.r14, .r20, .r23]))
    (fun a t h => h.step fun s P p b h0 _ => WP.mono (clearTop_ok P b h0) fun _ h => h.1) ?_
  -- The private operation.
  exact (priv_ct (Pre := PreT Z Gs.len) (Pub := PubT Z) (fun P => P.1) (fun p => p.1)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.b, h₂.1.b⟩) fun _ _ h => h

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (Z : Tabs) (a t : State) : Prop := ∃ s, PreT Z D s ∧ PubT Z a s ∧ Entered s t ∧ t.syms = s.syms

include hH cH hGl hG cG hGmh hGml hGmv in
theorem checks_ct : RelCT isa (Two (En Gs.len Z)) (checks Z.H Z.f Z.g) fun _ _ => True := by
  have hD64 : Z.H.D ≤ 64 := hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Gs.len Z a t) → ∀ rs : List Reg,
      (∀ r ∈ rs, r ∈ Reg.r14 :: fx) → Pins Φ rs := fun h rs hrs =>
    mpin (an := id) (fun a t hp => let ⟨s, P, p, E, sy⟩ := h a t hp; ⟨s, P, p, E.base, sy⟩) rs hrs
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, n0, n0, p₁.1.1.byte p₁.1.2, p₂.1.1.byte p₂.1.2])
    (VG.Proof.RsaOaep.PPC64LE.fail_taint (pin (fun _ _ h => h.1) _ (by decide))) ?_
  let E1 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r5) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Z.H.D + 2))
    (chkEm_taint Z.H (pin (fun _ _ h => h.1) [] (by decide))) (fun a t ⟨⟨s, P, p, E, sy⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hD64 E h0) fun t' ⟨E', r3⟩ y =>
      ⟨⟨s, P, p, E', y.trans sy, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (VG.Proof.RsaOaep.PPC64LE.fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩) _ (by decide))) ?_
  let E2 := fun (a t : State) => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r5) ≠ 0 ∧ Z.H.D + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Z.H.D + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, sy, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Z.H.D + 2 := by simpa using hc
    exact ⟨s, P, p, E, sy, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega⟩
  -- The salt's length.
  refine two_seq (Ψ := fun a t => E2 a t ∧
      (t.gpr .r3 != 0) = decide (kk a - loN a - (Z.H.D + 2) < (stackArg a 11).toNat))
    (chkSalt_taint Z.H (pin (fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := e2 h; ⟨s, P, p, E, sy⟩) [] (by decide)))
    (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, sy, h0, hem⟩ := e2 h
    exact WP.mono_syms (chkSalt_ok P.1 hD64 E h0 hem) fun t' ⟨E', r3⟩ y =>
      ⟨⟨s, P, p, E', y.trans sy, h0, hem⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2, p.1.1.args 11 (by decide)]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (VG.Proof.RsaOaep.PPC64LE.fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩) _ (by decide))) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧
      (t.gpr .r3 != 0) = decide (kk a - loN a - (Z.H.D + 2) < (stackArg a 11).toNat)) ∧
      isa.eval (.nonzero .d .r3) t = some false → M Gs.len Z a t :=
    fun {a t} ⟨⟨⟨s, P, p, E, sy, h0, hem⟩, c⟩, hc⟩ => by
      rw [eval_nonzero, c] at hc
      have hn : ¬ kk a - loN a - (Z.H.D + 2) < (stackArg a 11).toNat := by simpa using hc
      have k2 : kk s ≤ 1024 := P.1.k2
      rw [p.1.1.byte p.1.2, p.1.1.pKk, p.1.1.pLoN p.1.2] at *
      exact ⟨⟨s, P, p, E.base, sy⟩, ⟨h0, by omega, k2⟩⟩
  exact (main_ct hH cH hGl hG cG hGmh hGml hGmv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

/-- After the frame's push and the choice by the index, from an entry state. -/
abbrev Ix (Z : Tabs) (D i : Nat) (a u : State) : Prop :=
  ∃ s, (PreT Z D s ∧ PubT Z a s) ∧ Only [.r11, .r12] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i

variable (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hHv : Proof.Mgf1.Valid Gs)

include hH cH hGl hG cG hGmh hGml hGmv hGh hHv in
/-- The frame's body, for the hash function's sizes. -/
theorem body_ct {i : Nat} : RelCT isa (Two (Ix Z Gs.len i)) (body Z.H Z.f Z.g) fun _ _ => True := by
  unfold body
  refine two_seq (Ψ := En Gs.len Z)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => ⟨by rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp,
      h₁.2.1.1.sp, h₂.2.1.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, o₁.get .r5, o₂.get .r5, allocated_gpr, allocated_gpr,
          h₁.2.1.1.g .r5 (by decide), h₂.2.1.1.g .r5 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, o, sy, _⟩ => WP.mono_syms (entry_ok P.1 o) fun t E y => ⟨s, P, p, E, y.trans sy⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT Z Gs.len s ∧ PubT Z a s ∧
      VG.Proof.RsaOaep.PPC64LE.Saves s t)
    (checks_ct hH cH hGl hG cG hGmh hGml hGmv) fun a t ⟨s, P, p, E, sy⟩ =>
      WP.mono (checks_done (Gm := Gm) P.1 hH hGh hGl hHv hG P.2.1 hGmh hGml hGmv P.2.2 E sy) fun t' d =>
        ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

include hH cH hGl hG cG hGmh hGml hGmv hGh hHv in
/-- Two runs of `vg_rsa_pss_sign` from entry states with the same public
data and tables, whose hash function's table holds the index `i` of `H`'s
digest length, leak alike. -/
theorem code_ct {i : Nat} (hi : i ∈ idxs) (hD : (shapeOf i).1.D = Z.H.D) :
    RelCT isa (Two fun a s => (PreT Z Gs.len s ∧ PubT Z a s) ∧
      s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i) (sign Z.f Z.g) fun _ _ => True := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.1.2.1.1.sp.trans h₂.1.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  let A0 := fun (a s : State) => (PreT Z Gs.len s ∧ PubT Z a s) ∧
    s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i
  let A1 := fun (a u : State) => ∃ s, A0 a s ∧ Only [.r11] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = stackArg s 14
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
        rw [List.mem_singleton.mp hr, e₁, e₂, h₁.1.2.1.1.args 14 (by decide),
          h₂.1.2.1.1.args 14 (by decide)]⟩) fun a u ⟨s, h, o, y, e⟩ => ?_))) ?_
  · subst e
    have P := h.1.1.1
    exact WP.of_syms ((argA_ok (j := hArg) (by decide) ⟨aR s, by rw [P.hrd]; simp, in_aR (by decide)⟩
      ((P.ka.sub_left kR_sub).sub_right (in_aR_sub (by decide))).symm).mono fun u' ⟨o', e'⟩ y => ⟨s, h, o', y, e'⟩)
  · have P := h.1.1.1
    exact WP.of_syms ((wordA_ok o e (by decide) ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide)
      (by decide)⟩ ((P.kth.sub_left kR_sub).sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm).mono
        fun u' ⟨o', e'⟩ y' => ⟨s, h, o', y'.trans y, by rw [e']; exact h.2⟩)
  refine byIdx_ct (D := i) (by omega) (Φ := Ix Z Gs.len i)
    (fun _ _ ⟨_, _, _, _, e⟩ => e) (fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => by
      rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp])
    (fun a u u' ⟨s, h, o, y, e⟩ o' y' => ⟨s, h, (o.trans o').mono, y'.trans y, by rw [o'.get .r11]; exact e⟩)
    ?_ hi idxs_certs |>.mono (fun _ _ ⟨a, ⟨s₁, h₁, o₁, y₁, e₁⟩, ⟨s₂, h₂, o₂, y₂, e₂⟩⟩ =>
      ⟨a, ⟨s₁, h₁.1, o₁.mono, y₁, e₁⟩, ⟨s₂, h₂.1, o₂.mono, y₂, e₂⟩⟩) fun _ _ h => h
  rw [body_D hD]
  exact body_ct hH cH hGl hG cG hGmh hGml hGmv hGh hHv

end

end VG.Proof.RsaPss.PPC64LE.Sg
