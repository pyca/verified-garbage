module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTMain
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBase
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivCall
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBlocks
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Em
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Blocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `RsaPss.PPC64LE.Sg.CTMain`, which only this module used -/

section

/-! ### `RsaPss.PPC64LE.Sg.CTPriv`, which only this module used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from states with `Base` for entry states with the same
public data leak alike: its frame's arguments by the taint analysis, and the
call of `vg_rsa_private_checked` by its constant time (`RelCT.callEx`),
whose public data at the call (`priv_pub`) are the entry's: the pointers and
lengths, the modulus and the public exponent.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE (B B.sp pins_of two_seq allocated_sp fb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two two_alloc)

theorem psa_pub {a s : State} (p : PubS pc a s) {i : Nat} (hi : i < nP pc) : psa s i = psa a i := by
  by_cases h12 : i < 12
  · rcases (by omega_using [h12] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [psa, Ss, p.g .r9 (by decide), p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 16),
        p.args _ (by decide : (1 : Nat) < 16), p.args _ (by decide : (2 : Nat) < 16),
        p.args _ (by decide : (3 : Nat) < 16), p.args _ (by decide : (4 : Nat) < 16),
        p.args _ (by decide : (5 : Nat) < 16), p.args _ (by decide : (6 : Nat) < 16),
        p.args _ (by decide : (7 : Nat) < 16), p.args _ (by decide : (12 : Nat) < 16),
        p.args _ (by decide : (13 : Nat) < 16)]
  · cases pc with
    | false => exact absurd hi (by simp only [nP, Bool.false_eq_true, ↓reduceIte]; omega_using [h12])
    | true =>
      rcases (by simp only [nP, ↓reduceIte] at hi; omega_using [h12, hi] : i = 12 ∨ i = 13) with rfl | rfl
      · exact (p.pre rfl).1
      · exact (p.pre rfl).2.1

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (D : Nat) (a u : State) : Prop :=
  ∃ s em, PreS pc D s ∧ (pc = true → PreXS s) ∧ PubK pc a s ∧ AtPriv pc s em u

/-- What two runs share at the call. -/
theorem priv_pub {D : Nat} {a u₁ u₂ : State} (h₁ : APriv pc D a u₁) (h₂ : APriv pc D a u₂) :
    ∃ s₁ s₂ em₁ em₂, PreS pc D s₁ ∧ (pc = true → PreXS s₁) ∧ AtPriv pc s₁ em₁ u₁ ∧ PreS pc D s₂ ∧
      (pc = true → PreXS s₂) ∧ AtPriv pc s₂ em₂ u₂ ∧
      (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < nP pc, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat ∧
      (pc = true → Spec.Rsa.privatePrecomputedLeak (callE pc s₁ u₁).mem (stackArg (callE pc s₁ u₁) 12)
          ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.privatePrecomputedLeak (callE pc s₂ u₂).mem (stackArg (callE pc s₂ u₂) 12)
          ((callE pc s₂ u₂).gpr .r6).toNat) := by
  obtain ⟨s₁, em₁, P₁, X₁, ⟨p₁, _⟩, A₁⟩ := h₁
  obtain ⟨s₂, em₂, P₂, X₂, ⟨p₂, _⟩, A₂⟩ := h₂
  refine ⟨s₁, s₂, em₁, em₂, P₁, X₁, A₁, P₂, X₂, A₂, ?_, fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pub p₁ hi, psa_pub p₂ hi], ?_, ?_, ?_⟩
  · rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp]
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, Ss, Ss, p₁.args 12 (by decide), p₂.args 12 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
    have hb := fun {s u : State} {em : List Byte} (P : PreS pc D s) (A : AtPriv pc s em u) {p : Addr} {len : Nat}
      (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.PPC64LE.SC Ss s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
    rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6,
      hb P₁ A₁ P₁.kn ((P₁.ns.symm).sub_left (sc_sub P₁)) (by have := P₁.wn; omega_using []),
      hb P₂ A₂ P₂.kn ((P₂.ns.symm).sub_left (sc_sub P₂)) (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
    have hb := fun {s u : State} {em : List Byte} (P : PreS pc D s) (A : AtPriv pc s em u) {p : Addr} {len : Nat}
      (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.PPC64LE.SC Ss s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
    rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8,
      hb P₁ A₁ P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega_using []),
      hb P₂ A₂ P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega_using []), p₁.e, p₂.e]
  · intro hpc
    subst hpc
    have hw : ∀ {s u : State} {em : List Byte} (P : PreS true D s) (X : PreXS s) (A : AtPriv true s em u),
        Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
            ((callE true s u).gpr .r6).toNat =
          (Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).map (·.toNat) := by
      intro s u em P X A
      have pwl : Spec.Rsa.precomputedWords (s.gpr .r6).toNat ≤ (stackArg s 17).toNat := by
        rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
      simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
        callE_gpr s u (r := .r6), A.r6]
      congr 1
      have subPre : Region.Sub ⟨stackArg s 16, 8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat⟩ (preR s) :=
        fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
      exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact X.kP.symm.sub_left subPre
        · exact (X.sP.symm.sub_right (sc_sub P)).sub_left subPre)
        (by have := X.wP; omega_using [pwl, this])
    rw [hw P₁ (X₁ rfl) A₁, hw P₂ (X₂ rfl) A₂, (p₁.pre rfl).2.2, (p₂.pre rfl).2.2]

theorem call_ct {D : Nat} : RelCT isa (Two (APriv pc D)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, s₂, em₁, em₂, P₁, _, A₁, P₂, _, A₂, hsp, hr, ha, hn, he, _⟩ := priv_pub h₁ h₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, s₂, em₁, em₂, P₁, X₁, A₁, P₂, X₂, A₂, hsp, hr, ha, hn, he, hp⟩ := priv_pub h₁ h₂
    exact ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ (X₁ rfl) A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ (X₂ rfl) A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr ha hn he (hp rfl),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

/-- The private operation, in both runs, from states with `Base` for entry
states with `PreS` and `PubK`. -/
theorem priv_ct {D : Nat} {Pre : State → Prop} {Pub : State → State → Prop} (hP : ∀ {s}, Pre s → PreS pc D s)
    (hX : ∀ {s}, Pre s → pc = true → PreXS s)
    (hQ : ∀ {a s}, Pub a s → PubK pc a s) : RelCT isa (Two (B Ss vS Pre Pub)) (priv pc) fun _ _ => True := by
  have X := signOk D hP hQ
  unfold priv
  refine two_alloc (R := fun _ _ => True) (pins_of X (an := id) (fun _ _ h => h) []) ?_
  refine two_seq (Ψ := APriv pc D) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.sp X, h₂.sp X], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, b⟩, e⟩ => by
      subst e; exact WP.mono (privArgs_ok (hP P) b rfl) fun u' A => ⟨s, _, hP P, hX P, hQ p, A⟩)
    call_ct

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


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

variable {pc : Bool}

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

/-- The tables on entry, and for the variant, its precomputed values. -/
def STabsOn (pc : Bool) (Z : Tabs) (s : State) : Prop :=
  TabS Z.G Z.g gArg Ss s (stackArg s 15) ∧ MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Ss s (stackArg s 14) ∧
    (pc = true → PreXS s)

/-- The anchor's addresses of the tables' functions. -/
def SymsAg (Z : Tabs) (a s : State) : Prop :=
  s.syms Z.G.initN = a.syms Z.G.initN ∧ s.syms Z.G.updN = a.syms Z.G.updN ∧ s.syms Z.G.finN = a.syms Z.G.finN ∧
    s.syms Z.H.initN = a.syms Z.H.initN ∧ s.syms Z.H.updN = a.syms Z.H.updN ∧
    s.syms Z.H.finN = a.syms Z.H.finN ∧ s.syms Z.cn = a.syms Z.cn ∧ s.syms Z.dn = a.syms Z.dn

/-- An entry state, with the tables. -/
abbrev PreT (pc : Bool) (Z : Tabs) (D : Nat) (s : State) : Prop := PreS pc D s ∧ STabsOn pc Z s

/-- The anchor's public data and addresses of the tables' functions. -/
abbrev PubT (pc : Bool) (Z : Tabs) (a s : State) : Prop := PubK pc a s ∧ SymsAg Z a s

theorem tOk {D : Nat} {Z : Tabs} : Ok Ss vS (PreT pc Z D) (PubT pc Z) := signOk D (fun P => P.1) (fun p => p.1)

theorem tabG {D : Nat} (Z : Tabs) : TabA Z.G Z.g gArg Ss (PreT pc Z D) (PubT pc Z) :=
  ⟨fun P => P.2.1, fun p => p.1.1.args 15 (by decide), fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1⟩

theorem tabH {D : Nat} (Z : Tabs) : MdTabA Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Ss (PreT pc Z D) (PubT pc Z) :=
  ⟨fun P => P.2.2.1, fun p => p.1.1.args 14 (by decide), fun p => p.2.2.2.2.1, fun p => p.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2⟩

/-- `Base` from an entry state with the anchor's public data, which passed
the checks. -/
abbrev M (pc : Bool) (D : Nat) (Z : Tabs) (a t : State) : Prop := BT Ss vS (PreT pc Z D) (PubT pc Z) a t ∧ Ck D a

section
variable {D : Nat} {Z : Tabs}

theorem ss_eq {a s : State} (p : PubK pc a s) : Ss s = Ss a := p.1.args 12 (by decide)

theorem ck_s {a s : State} (p : PubT pc Z a s) (C : Ck D a) :
    s.mem (s.gpr .r5) ≠ 0 ∧ D + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by
  rw [p.1.1.byte p.1.2, p.1.1.pLoN p.1.2, p.1.1.pKk, p.1.1.args 11 (by decide)]; exact ⟨C.h0, C.fit⟩

/-- A step keeping `Base`, from the entry state of a run. -/
theorem M.step {c : Prog isa} {a t : State} (h : M pc D Z a t)
    (k : ∀ s, PreS pc D s → PubK pc a s → Base Ss vS s t → s.mem (s.gpr .r5) ≠ 0 →
      D + (stackArg s 11).toNat + 2 ≤ kk s - loN s → WP isa c t fun t' => Base Ss vS s t') :
    WP isa c t (M pc D Z a) :=
  let ⟨⟨s, P, p, b, sy⟩, C⟩ := h
  WP.mono_syms (k s P.1 p.1 b (ck_s p C).1 (ck_s p C).2) fun _ b' y => ⟨⟨s, P, p, b', y.trans sy⟩, C⟩

theorem mpin {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → BT Ss vS (PreT pc Z D) (PubT pc Z) (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of tOk (fun x t hx => (h x t hx).b) rs hrs

/-- `r4`, `r5` and `r6` as functions of the anchor. -/
theorem pins3 {α : Type} {Φ : α → State → Prop} {an : α → State}
    (hb : ∀ x t, Φ x t → BT Ss vS (PreT pc Z D) (PubT pc Z) (an x) t)
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
    RelCT isa (Two fun a t => M pc D Z a t ∧ t.gpr .r5 = off (Ss a) (d a)) copySalt fun _ _ => True := by
  unfold copySalt
  refine two_seq (Ψ := fun a t => M pc D Z a t ∧ t.gpr .r4 = stackArg a 10 ∧ t.gpr .r5 = off (Ss a) (d a) ∧
      t.gpr .r6 = stackArg a 11) (saltArgs_taint (mpin (fun _ _ h => h.1.1) []))
    (fun a t ⟨⟨⟨s, P, p, b, sy⟩, C⟩, h5⟩ => WP.mono_syms (saltArgs_ok P.1 b) fun t' ⟨o, e4, e6⟩ y =>
      ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e4, p.1.1.args 10 (by decide)], by rw [o.get .r5, h5],
        by rw [e6, p.1.1.args 11 (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2.2.2, h₂.2.2.2])
    (copy_taint (pins3 (fun _ _ h => h.1.1.1) _ _ _ fun _ _ h => h.1.2)) (skip_taint (mpin (fun _ _ h => h.1.1.1) []))

variable {H : Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
include hD hD0 hD64

/-- `M'`, in both runs. -/
theorem mPrime_ct : RelCT isa (Two (M pc D Z)) (mPrime H) fun _ _ => True := by
  have hY : oY = 2560 := rfl
  unfold mPrime
  refine two_seq (Ψ := M pc D Z) (zeros8_taint (mpin (fun _ _ h => h.1) [.r14]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (zeros_ok P b) fun _ h => h.1) ?_
  let Ψ := fun (a t : State) => M pc D Z a t ∧ t.gpr .r4 = stackArg a 8 ∧ t.gpr .r5 = off (Ss a) (oY + 8) ∧
    t.gpr .r6 = BitVec.ofNat 64 D
  have hΨ : ∀ a t, M pc D Z a t → WP isa (.block (ldArg .r4 8 ++ [.addi .r5 .r14 (oY + 8), .li .r6 H.D])) t (Ψ a) :=
    fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => WP.mono_syms (digArgs_ok P.1 hD hD64 b) fun t' ⟨o, e4, e5, e6⟩ y =>
      ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e4, p.1.1.args 8 (by decide)],
        by rw [e5, ss_eq p.1], e6⟩
  refine two_seq (Ψ := M pc D Z) (two_seq (Ψ := Ψ) (digArgs_taint H (mpin (fun _ _ h => h.1) [])) hΨ
      (copy_taint (pins3 (fun _ _ h => h.1.1) _ _ _ fun _ _ h => h.2)))
    (fun a t h => WP.seq (WP.mono (hΨ a t h) fun t' ⟨⟨⟨s, P, p, b, sy⟩, C⟩, e4, e5, e6⟩ =>
      WP.mono_syms (digCopy_ok P.1 hD0 hD64 b (by rw [e4, p.1.1.args 8 (by decide)]) (by rw [e5, ss_eq p.1]) e6)
        fun _ h y => ⟨⟨s, P, p, h.1, y.trans sy⟩, C⟩)) ?_
  refine two_seq (Ψ := fun a t => M pc D Z a t ∧ t.gpr .r5 = off (Ss a) (oY + 8 + D))
    (saltDst_taint H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => WP.of_syms (wp_addi (h := by unfold oY; omega_using [hD, hD64]) fun t' o e =>
      wp_nil fun y => ⟨⟨⟨s, P, p, b.only (fits P.1) o, y.trans sy⟩, C⟩, by rw [e, b.r14, ss_eq p.1, hD]⟩)) ?_
  exact copySalt_ct (fun _ => oY + 8 + D)

theorem mPrime_wp {a t : State} (h : M pc D Z a t) : WP isa (mPrime H) t (M pc D Z a) :=
  h.step fun s P p b _ hf => WP.mono (mPrime_ok P hD hD0 hD64 b (by have := P.k2; unfold kk at hf; omega_using [hf, this]))
    fun _ h => h.1

omit hD0 in
/-- `0x01` and the salt in `EM`, in both runs. -/
theorem putSalt_ct : RelCT isa (Two (M pc D Z)) (putSalt H) fun _ _ => True := by
  unfold putSalt
  let d := fun (a : State) => oEm + (kk a - (stackArg a 11).toNat - D - 1)
  refine two_seq (Ψ := fun a t => M pc D Z a t ∧ t.gpr .r5 = off (Ss a) (d a))
    (putSaltHead_taint H (mpin (fun _ _ h => h.1) [.r14, .r15, .r19]))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) (copySalt_ct d)
  have hf := (ck_s p C).2
  have := loN_le s
  exact WP.mono_syms (saltHead_ok P.1 hD hD64 b (by omega_using [hf])) fun t' ⟨b', _, _, a5⟩ y =>
    ⟨⟨⟨s, P, p, b', y.trans sy⟩, C⟩, by rw [a5, ss_eq p.1, p.1.1.pKk, p.1.1.args 11 (by decide)]⟩

omit hD0 in
theorem putSalt_wp {a t : State} (h : M pc D Z a t) : WP isa (putSalt H) t (M pc D Z a) :=
  h.step fun s P p b _ hf => WP.mono (putSalt_ok P hD hD64 b (by have := loN_le s; omega_using [hf])) fun _ h => h.1

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
  exact ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩

/-- MGF1's arguments, from the anchor. -/
abbrev MgfL (pc : Bool) (D : Nat) (Z : Tabs) (a t : State) : Prop :=
  MgfAT Ss vS (PreT pc Z D) (PubT pc Z) (qD D a).1 (qD D a).2.1 (qD D a).2.2.1 (qD D a).2.2.2 a t

include cG hGmh hGml hGmv in
/-- `mgfXorT` with the anchor's arguments. -/
theorem mgf_ct {D : Nat} : RelCT isa (Two fun a t => MgfL pc D Z a t ∧ Ck D a) (mgfXorT Z.g gArg) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT Ss vS (PreT pc Z D) (PubT pc Z) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ct tOk hG cG x.2 hGmh hGml hGmv (tabG Z)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qD D a, qD_fit h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include hH cH hGl hG cG hGmh hGml hGmv in
theorem main_ct : RelCT isa (Two (M pc Gs.len Z)) (signMain Z.H Z.f Z.g pc) fun _ _ => True := by
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hE : oEm = 0 := rfl
  unfold signMain
  refine two_seq (Ψ := M pc Gs.len Z) (mPrime_ct hGl.symm hD0 hD64) (fun a t h => mPrime_wp hGl.symm hD0 hD64 h) ?_
  -- `H`.
  refine two_seq (Ψ := M pc Gs.len Z)
    ((hashFixedG_ct tOk hH cH (tabH Z) hGl.symm (fun a => (stackArg a 11).toNat) fun a => by
      show stackArg a 11 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁.1, by have := h₁.2.fit; have := h₁.2.k2; omega_arith⟩,
        ⟨h₂.1, by have := h₂.2.fit; have := h₂.2.k2; omega_arith⟩⟩) fun _ _ h => h)
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) ?_
  · have hf := (ck_s p C).2
    exact WP.mono (hashFixedG_ok (fits P.1) hH P.2.2.1 hGl.symm (sl := (stackArg s 11).toNat)
      (by show stackArg s 11 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) b sy
      (by have := P.1.k2; unfold kk at hf; omega_using [hf, this])) fun _ ⟨h, y⟩ => ⟨⟨s, P, p, h.1, y⟩, C⟩
  -- `EM`.
  refine two_seq (Ψ := M pc Gs.len Z) (clearEm_taint (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ _ => WP.mono (clearEm_ok P b) fun _ h => h.1) ?_
  refine two_seq (Ψ := M pc Gs.len Z) (putSalt_ct hGl.symm hD64) (fun a t h => putSalt_wp hGl.symm hD64 h) ?_
  refine two_seq (Ψ := M pc Gs.len Z) (putH_taint Z.H (mpin (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t h => h.step fun s P p b _ hf => WP.mono (putH_ok P hGl.symm hD0 hD64 b (by omega_using [hf])) fun _ h => h.1) ?_
  -- `maskedDB`.
  refine two_seq (Ψ := fun a t => MgfL pc Gs.len Z a t ∧ Ck Gs.len a) (dbArgs_taint Z.H (mpin (fun _ _ h => h.1) []))
    (fun a t ⟨⟨s, P, p, b, sy⟩, C⟩ => ?_) ?_
  · have h0 := (ck_s p C).1
    have hf := (ck_s p C).2
    exact WP.mono_syms (dbArgs_ok P.1 hGl.symm hD64 b h0 (by omega_using [hf])) fun t' ⟨b', _, e24, e25, e26, e27⟩ y =>
      ⟨⟨s, P, p, b', y.trans sy, by rw [e24, ss_eq p.1, p.1.1.pKk], e25, by rw [e26, ss_eq p.1, p.1.1.pLoN p.1.2],
        by rw [e27, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩, C⟩
  refine two_seq (Ψ := M pc Gs.len Z) (mgf_ct hG cG hGmh hGml hGmv)
    (fun a t ⟨⟨s, P, p, b, sy, h24, h25, h26, h27⟩, C⟩ => WP.mono (mgfXorT_ok (fits P.1) hG P.2.1 hGmh hGml hGmv
      (qD_fit C) b sy (by rw [h24, ss_eq p.1]) h25 (by rw [h26, ss_eq p.1]) h27) fun t' ⟨⟨b', _⟩, y'⟩ =>
        ⟨⟨s, P, p, b', y'⟩, C⟩) ?_
  refine two_seq (Ψ := M pc Gs.len Z) (clearTop_taint (mpin (fun _ _ h => h.1) [.r14, .r20, .r23]))
    (fun a t h => h.step fun s P p b h0 _ => WP.mono (clearTop_ok P b h0) fun _ h => h.1) ?_
  -- The private operation.
  exact (priv_ct (Pre := PreT pc Z Gs.len) (Pub := PubT pc Z) (fun P => P.1) (fun P => P.2.2.2) (fun p => p.1)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.b, h₂.1.b⟩) fun _ _ h => h

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (pc : Bool) (D : Nat) (Z : Tabs) (a t : State) : Prop := ∃ s, PreT pc Z D s ∧ PubT pc Z a s ∧ Entered s t ∧ t.syms = s.syms

include hH cH hGl hG cG hGmh hGml hGmv in
theorem checks_ct : RelCT isa (Two (En pc Gs.len Z)) (checks Z.H Z.f Z.g pc) fun _ _ => True := by
  have hD64 : Z.H.D ≤ 64 := hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En pc Gs.len Z a t) → ∀ rs : List Reg,
      (∀ r ∈ rs, r ∈ Reg.r14 :: fx) → Pins Φ rs := fun h rs hrs =>
    mpin (an := id) (fun a t hp => let ⟨s, P, p, E, sy⟩ := h a t hp; ⟨s, P, p, E.base, sy⟩) rs hrs
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁, _⟩ ⟨s₂, _, p₂, E₂, _⟩ => by
      rw [eval_zero, eval_zero, E₁.r9, E₂.r9, n0, n0, p₁.1.1.byte p₁.1.2, p₂.1.1.byte p₂.1.2])
    (VG.Proof.RsaOaep.PPC64LE.fail_taint (pin (fun _ _ h => h.1) _ (by decide))) ?_
  let E1 := fun (a t : State) => ∃ s, PreT pc Z Gs.len s ∧ PubT pc Z a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r5) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Z.H.D + 2))
    (chkEm_taint Z.H (pin (fun _ _ h => h.1) [] (by decide))) (fun a t ⟨⟨s, P, p, E, sy⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono_syms (chkEm_ok P.1 hD64 E h0) fun t' ⟨E', r3⟩ y =>
      ⟨⟨s, P, p, E', y.trans sy, h0⟩, by rw [r3, p.1.1.pKk, p.1.1.pLoN p.1.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (VG.Proof.RsaOaep.PPC64LE.fail_taint (pin (fun _ _ h => let ⟨s, P, p, E, sy, _⟩ := h.1.1; ⟨s, P, p, E, sy⟩) _ (by decide))) ?_
  let E2 := fun (a t : State) => ∃ s, PreT pc Z Gs.len s ∧ PubT pc Z a s ∧ Entered s t ∧ t.syms = s.syms ∧
    s.mem (s.gpr .r5) ≠ 0 ∧ Z.H.D + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .r3 != 0) = decide (kk a - loN a < Z.H.D + 2)) ∧
      isa.eval (.nonzero .d .r3) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, sy, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Z.H.D + 2 := by simpa using hc
    exact ⟨s, P, p, E, sy, h0, by rw [p.1.1.pKk, p.1.1.pLoN p.1.2]; omega_using [this]⟩
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
      isa.eval (.nonzero .d .r3) t = some false → M pc Gs.len Z a t :=
    fun {a t} ⟨⟨⟨s, P, p, E, sy, h0, hem⟩, c⟩, hc⟩ => by
      rw [eval_nonzero, c] at hc
      have hn : ¬ kk a - loN a - (Z.H.D + 2) < (stackArg a 11).toNat := by simpa using hc
      have k2 : kk s ≤ 1024 := P.1.k2
      rw [p.1.1.byte p.1.2, p.1.1.pKk, p.1.1.pLoN p.1.2] at *
      exact ⟨⟨s, P, p, E.base, sy⟩, ⟨h0, by omega_using [hGl, hem, hn], k2⟩⟩
  exact (main_ct hH cH hGl hG cG hGmh hGml hGmv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

/-- After the frame's push and the choice by the index, from an entry state. -/
abbrev Ix (pc : Bool) (Z : Tabs) (D i : Nat) (a u : State) : Prop :=
  ∃ s, (PreT pc Z D s ∧ PubT pc Z a s) ∧ Only [.r11, .r12] (allocated frameBytes s) u ∧ u.syms = s.syms ∧
    u.gpr .r11 = BitVec.ofNat 64 i

variable (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hHv : Proof.Mgf1.Valid Gs)

include hH cH hGl hG cG hGmh hGml hGmv hGh hHv in
/-- The frame's body, for the hash function's sizes. -/
theorem body_ct {i : Nat} : RelCT isa (Two (Ix pc Z Gs.len i)) (body Z.H Z.f Z.g pc) fun _ _ => True := by
  unfold body
  refine two_seq (Ψ := En pc Gs.len Z)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => ⟨by rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp,
      h₁.2.1.1.sp, h₂.2.1.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, o₁.get .r5, o₂.get .r5, allocated_gpr, allocated_gpr,
          h₁.2.1.1.g .r5 (by decide), h₂.2.1.1.g .r5 (by decide)]⟩)
    (fun a u ⟨s, ⟨P, p⟩, o, sy, _⟩ => WP.mono_syms (entry_ok P.1 o) fun t E y => ⟨s, P, p, E, y.trans sy⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreT pc Z Gs.len s ∧ PubT pc Z a s ∧
      VG.Proof.RsaOaep.PPC64LE.Saves s t)
    (checks_ct hH cH hGl hG cG hGmh hGml hGmv) fun a t ⟨s, P, p, E, sy⟩ =>
      WP.mono (checks_done (Gm := Gm) P.1 hH hGh hGl hHv hG P.2.1 hGmh hGml hGmv P.2.2.1 P.2.2.2 E sy) fun t' d =>
        ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.1.sp, p₂.1.1.sp], fun _ h => nomatch h⟩

include hH cH hGl hG cG hGmh hGml hGmv hGh hHv in
/-- Two runs of `vg_rsa_pss_sign` from entry states with the same public
data and tables, whose hash function's table holds the index `i` of `H`'s
digest length, leak alike. -/
theorem code_ct {i : Nat} (hi : i ∈ idxs) (hD : (shapeOf i).1.D = Z.H.D) :
    RelCT isa (Two fun a s => (PreT pc Z Gs.len s ∧ PubT pc Z a s) ∧
      s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i) (signG Z.f Z.g pc) fun _ _ => True := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.1.2.1.1.sp.trans h₂.1.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  let A0 := fun (a s : State) => (PreT pc Z Gs.len s ∧ PubT pc Z a s) ∧
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
    exact WP.of_syms ((argA_ok (j := hArg) (by decide) ⟨aR pc s, by rw [P.hrd]; simp, in_aR (pc := pc) (by decide)⟩
      ((P.ka.sub_left kR_sub).sub_right (in_aR_sub (pc := pc) (by decide))).symm).mono fun u' ⟨o', e'⟩ y => ⟨s, h, o', y, e'⟩)
  · have P := h.1.1.1
    exact WP.of_syms ((wordA_ok o e (by decide) ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide)
      (by decide)⟩ ((P.kth.sub_left kR_sub).sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm).mono
        fun u' ⟨o', e'⟩ y' => ⟨s, h, o', y'.trans y, by rw [e']; exact h.2⟩)
  refine byIdx_ct (D := i) (by omega_using [hi8]) (Φ := Ix pc Z Gs.len i)
    (fun _ _ ⟨_, _, _, _, e⟩ => e) (fun a u₁ u₂ ⟨s₁, h₁, o₁, _⟩ ⟨s₂, h₂, o₂, _⟩ => by
      rw [o₁.sp, o₂.sp, allocated_sp, allocated_sp, h₁.2.1.1.sp, h₂.2.1.1.sp])
    (fun a u u' ⟨s, h, o, y, e⟩ o' y' => ⟨s, h, (o.trans o').mono, y'.trans y, by rw [o'.get .r11]; exact e⟩)
    ?_ hi idxs_certs |>.mono (fun _ _ ⟨a, ⟨s₁, h₁, o₁, y₁, e₁⟩, ⟨s₂, h₂, o₂, y₂, e₂⟩⟩ =>
      ⟨a, ⟨s₁, h₁.1, o₁.mono, y₁, e₁⟩, ⟨s₂, h₂.1, o₂.mono, y₂, e₂⟩⟩) fun _ _ h => h
  rw [body_D hD]
  exact body_ct hH cH hGl hG cG hGmh hGml hGmv hGh hHv

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS on PPC64LE with the tables: `Verified`

Untrusted: everything here is checked by Lean. For variants `vs` and `gs` of `MdHash`
(`Proof/MdHashTable/PPC64LE/Tables.lean`), the hash function's and MGF1's,
whose functions of the same name have the same code: the tables a state meeting verification's or signing's
precondition holds give what the proofs need of them (`tabs_of`);
correctness against the contracts (`code_correct`, by `verify_ok` and
`sign_ok`); constant time (`code_constantTime`, by `code_ct`, the second
run holding the same tables, at the anchor's addresses with the anchor's
addresses of their functions). The families of streaming code (`md5F`,
`sha1F`, `sha256F`, `sha512F`), with the constant time of their compression
functions, from their artifacts' proofs, and of the digest of their hash
values, by the taint analysis; one variant of each hash function of
`Spec.Mgf1.hashes` (`mvars`). States meeting the contracts, with the table
of `MdHash` of a variant at `0x300000`, the table of `MdHash` of a variant at
`0x300100` and the tables' functions at distinct addresses (`verify_sat`,
`sign_sat`, as on x86-64); and `verify_ok'` and `sign_ok'`, which the
registration binds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (TabS)
open VG.Proof.MdHashTable.PPC64LE (MVar digName tabsOf)

section
variable {vs : List MVar} {gs : List MVar}

/-- The tables of a state meeting the precondition: one of `vs`' and one of
`gs`', with what the proofs need of them. -/
theorem tabs_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) {s : State}
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    ∃ w ∈ vs, ∃ w' ∈ gs,
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w')) ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some w.l.G ∧
      s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (MdHashTable.PPC64LE.idx w) ∧
      ∀ {D : Nat}, PreP D s → TabsOn (tabsOf vs gs w w') s := by
  obtain ⟨⟨T, hT, hh⟩, ⟨T', hT', hh'⟩, hpw⟩ := spec_tab h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  have hpH := hpw.sublist (List.sublist_append_left _ _)
  have hpG := hpw.sublist (List.sublist_append_right _ _)
  have hi := (MdHashTable.PPC64LE.held_tableOf hh).2.2.2
  refine ⟨w, hw, w', hw', hh, hh', MdHashTable.PPC64LE.hashAt_tableOf hi, hi, fun P => ⟨?_, ?_⟩⟩
  · refine MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tGR s ∈ s.rd by rw [P.hrd]; simp) P.ktg
      (P.stg.sub_left (sc_sub P)) hc' hpG hw' hh'
  · exact MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tHR s ∈ s.rd by rw [P.hrd]; simp) P.kth
      (P.sth.sub_left (sc_sub P)) hc hpH hw hh

/-- The correctness of `vg_rsa_pss_verify_precomputed`, against its contract,
for the tables of `vs` and `gs`. -/
theorem code_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) (s : State)
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) s t s' ∧
      abiPreserved s s' ∧ (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨w, hw, w', hw', hh, hh', hH, hi, hT⟩ := tabs_of hc hc' h
  have hG := MdHashTable.PPC64LE.hashAt_tableOf (MdHashTable.PPC64LE.held_tableOf hh').2.2.2
  have P := preP_of h hH
  obtain ⟨Tg, T⟩ := hT P
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  obtain ⟨t, s', he, habi, hr⟩ := verify_ok P w.l.ok w.l.hash w.l.len w.l.valid w'.l.ok Tg w'.l.hash w'.l.len
    w'.l.valid T w.F.ok hl w.hN w.hB hi w.sh.1 w.sh.2.1 w.sh.2.2
  refine ⟨t, s', he, habi, ?_⟩
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro H' G' hH' hG' hc
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [hr hc]
  unfold vOut
  split <;> rfl

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) :
    ConstantTime isa (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre
      (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pub
      (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨w, hw, w', hw', hh₁, hh₁', hH₁, hi₁, hT₁⟩ := tabs_of hc hc' h₁
  obtain ⟨p, hsy, hiffH, hiffG⟩ := pubT_of hp
  have hh₂ := (hiffH _ (List.mem_map_of_mem hw)).mp hh₁
  have hh₂' := (hiffG _ (List.mem_map_of_mem hw')).mp hh₁'
  have hi₂ := (MdHashTable.PPC64LE.held_tableOf hh₂).2.2.2
  have hH₂ := MdHashTable.PPC64LE.hashAt_tableOf hi₂
  have P₁ := preP_of h₁ hH₁
  have P₂ := preP_of h₂ hH₂
  have hpw₂ := (spec_tab h₂).2.2
  have T₂ : TabsOn (tabsOf vs gs w w') s₂ :=
    ⟨MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tGR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.ktg
      (P₂.stg.sub_left (sc_sub P₂)) hc' (hpw₂.sublist (List.sublist_append_right _ _)) hw' hh₂',
    MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tHR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.kth
      (P₂.sth.sub_left (sc_sub P₂)) hc (hpw₂.sublist (List.sublist_append_left _ _)) hw hh₂⟩
  have hn := MdHashTable.PPC64LE.mem_names hw
  have hn' := MdHashTable.PPC64LE.mem_names hw'
  have sH : ∀ {f}, f ∈ MdHashTable.PPC64LE.names vs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_left _ hf)).symm
  have sG : ∀ {f}, f ∈ MdHashTable.PPC64LE.names gs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_right _ hf)).symm
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  have hk : ∀ {s}, PreP w.l.G.len s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.k1
  exact code_ct (Z := tabsOf vs gs w w') w.l.ok w.l.ct w.l.hash w.l.len w.l.valid w'.l.ok w'.l.ct w'.l.hash
    w'.l.len w'.l.valid w.F.ok w.F.ct w.F.hcc w.F.hdc hl w.hN w.hB w.sh.1 w.sh.2.1 w.sh.2.2 _ _ _ _ _ _
    ⟨s₁, ⟨⟨⟨P₁, hT₁ P₁⟩, ⟨pubP_refl s₁, hk P₁⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi₁⟩,
      ⟨⟨⟨P₂, T₂⟩, ⟨p, hk P₂⟩, p.args 7 (by decide) (by decide), sG hn'.1, sG hn'.2.1, sG hn'.2.2.1,
        p.args 6 (by decide) (by decide), sH hn.1, sH hn.2.1, sH hn.2.2.1, sH hn.2.2.2.1, sH hn.2.2.2.2⟩, hi₂⟩⟩
    e₁ e₂

/-- `vg_rsa_pss_verify_precomputed` against its contract, for the tables of
`vs` and `gs`, given a state meeting it. -/
theorem verify_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs))
      (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)) :=
  ⟨code_correct hc hc', code_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE


namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE

open VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdHashTable.PPC64LE (digest)

theorem md5_hcc : ConstantTime isa (compressK (P := Impl.Md5.PPC64LE.Stream.params) Proof.Md5.md).pre (compressK (P := Impl.Md5.PPC64LE.Stream.params) Proof.Md5.md).pub Impl.Md5.PPC64LE.compress :=
  Proof.Md5.PPC64LE.compress_verified.2.1

theorem sha1_hcc : ConstantTime isa (compressK (P := Impl.Sha1.PPC64LE.Stream.params) Proof.Sha1.md).pre (compressK (P := Impl.Sha1.PPC64LE.Stream.params) Proof.Sha1.md).pub Impl.Sha1.PPC64LE.compress :=
  Proof.Sha1.PPC64LE.compress_verified.2.1

theorem sha256_hcc : ConstantTime isa (compressK (P := Impl.Sha256.PPC64LE.mdParams) Proof.Sha256.md).pre (compressK (P := Impl.Sha256.PPC64LE.mdParams) Proof.Sha256.md).pub Impl.Sha256.PPC64LE.compress :=
  Proof.Sha256.PPC64LE.compress_verified.2.1

theorem sha512_hcc : ConstantTime isa (compressK (P := Impl.Sha512.PPC64LE.mdParams) Proof.Sha512.md).pre (compressK (P := Impl.Sha512.PPC64LE.mdParams) Proof.Sha512.md).pub Impl.Sha512.PPC64LE.compress :=
  Proof.Sha512.PPC64LE.compress_verified.2.1

def md5F : Fam where
  P := Impl.Md5.PPC64LE.Stream.params
  md := Proof.Md5.md
  cn := "vg_md5_compress"
  cc := Impl.Md5.PPC64LE.compress
  ok := ⟨Proof.Md5.PPC64LE.Stream.dims, Proof.Md5.PPC64LE.Stream.shape, by decide, Proof.Md5.PPC64LE.Stream.callee,
    digest_correct Proof.Md5.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega_using [hj]),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := md5_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha1F : Fam where
  P := Impl.Sha1.PPC64LE.Stream.params
  md := Proof.Sha1.md
  cn := "vg_sha1_compress"
  cc := Impl.Sha1.PPC64LE.compress
  ok := ⟨Proof.Sha1.PPC64LE.Stream.dims, Proof.Sha1.PPC64LE.Stream.shape, by decide, Proof.Sha1.PPC64LE.Stream.callee,
    digest_correct Proof.Sha1.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj]),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha1_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha256F : Fam where
  P := Impl.Sha256.PPC64LE.mdParams
  md := Proof.Sha256.md
  cn := "vg_sha256_compress"
  cc := Impl.Sha256.PPC64LE.compress
  ok := ⟨Proof.Sha256.PPC64LE.Md.dims, Proof.Sha256.PPC64LE.Md.shape, by decide, Proof.Sha256.PPC64LE.Md.callee,
    digest_correct Proof.Sha256.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj]),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha256_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha512F : Fam where
  P := Impl.Sha512.PPC64LE.mdParams
  md := Proof.Sha512.md
  cn := "vg_sha512_compress"
  cc := Impl.Sha512.PPC64LE.compress
  ok := ⟨Proof.Sha512.PPC64LE.Md.dims, Proof.Sha512.PPC64LE.Md.shape, by decide, Proof.Sha512.PPC64LE.Md.callee,
    digest_correct Proof.Sha512.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj]),
    fun n hn => show n < 2 ^ 64 by omega_using [hn]⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha512_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def md5M : MVar where
  H := Md5.hash
  l := Proof.RsaOaep.PPC64LE.md5L
  idx := rfl
  F := md5F
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha1M : MVar where
  H := Sha1.hash
  l := Proof.RsaOaep.PPC64LE.sha1L
  idx := rfl
  F := sha1F
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha224M : MVar where
  H := Sha224.hash
  l := Proof.RsaOaep.PPC64LE.sha224L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha256M : MVar where
  H := Sha256.hash
  l := Proof.RsaOaep.PPC64LE.sha256L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha384M : MVar where
  H := Sha384.hash
  l := Proof.RsaOaep.PPC64LE.sha384L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_384
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512M : MVar where
  H := Sha512.hash
  l := Proof.RsaOaep.PPC64LE.sha512L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m =>
    (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_224M : MVar where
  H := Sha512_224.hash
  l := Proof.RsaOaep.PPC64LE.sha512_224L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_256M : MVar where
  H := Sha512_256.hash
  l := Proof.RsaOaep.PPC64LE.sha512_256L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_256
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

/-- Every hash function's variant. -/
def mvars : List MVar := [md5M, sha1M, sha224M, sha256M, sha384M, sha512M, sha512_224M, sha512_256M]

end VG.Proof.MdHashTable.PPC64LE


namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.MdHashTable.PPC64LE (MVar digName tabsOf)
open VG.Proof.RsaPss.PPC64LE (Tabs)

section
variable {pc : Bool} {vs : List MVar} {gs : List MVar}

/-- The tables, as both contracts give them: the hash function's one of `hs`
at the stack argument 14 and MGF1's one of `gs` at 15, with the functions of
distinct names at distinct addresses. -/
abbrev TabFacts (hs gs : List FnTable) (s : State) : Prop :=
  (∃ T ∈ hs, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
    (∃ T ∈ gs, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
    ((hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten).Pairwise
      (fun f g => f ≠ g → s.syms f ≠ s.syms g)

/-- The tables of a state meeting a precondition: one of `vs`' and one of
`gs`', with what the proofs need of them. -/
theorem tabs_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) {s : State}
    (h : TabFacts (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs) s) :
    ∃ w ∈ vs, ∃ w' ∈ gs,
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w')) ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some w.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w'.l.G ∧
      s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (MdHashTable.PPC64LE.idx w) ∧
      ∀ {D : Nat}, PreS pc D s → (pc = true → PreXS s) → STabsOn pc (tabsOf vs gs w w') s := by
  obtain ⟨⟨T, hT, hh⟩, ⟨T', hT', hh'⟩, hpw⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  have hpH := hpw.sublist (List.sublist_append_left _ _)
  have hpG := hpw.sublist (List.sublist_append_right _ _)
  have hi := (MdHashTable.PPC64LE.held_tableOf hh).2.2.2
  refine ⟨w, hw, w', hw', hh, hh', MdHashTable.PPC64LE.hashAt_tableOf hi,
    MdHashTable.PPC64LE.hashAt_tableOf (MdHashTable.PPC64LE.held_tableOf hh').2.2.2, hi, fun P X => ⟨?_, ?_, X⟩⟩
  · exact MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; simp)
      (in_aR (pc := pc) (by decide)) (in_aR_sub (pc := pc) (by decide)) (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
      (show tGR s ∈ s.rd by rw [P.hrd]; simp) (P.ktg.sub_left kR_sub) (P.stg.sub_left (sc_sub P)) hc' hpG hw' hh'
  · exact MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR pc s) (by rw [P.hrd]; simp)
      (in_aR (pc := pc) (by decide)) (in_aR_sub (pc := pc) (by decide)) (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
      (show tHR s ∈ s.rd by rw [P.hrd]; simp) (P.kth.sub_left kR_sub) (P.sth.sub_left (sc_sub P)) hc hpH hw hh

/-- The correctness of `vg_rsa_pss_sign` and of its variant, from the
tables, `PreS` and, for the variant, `PreXS`: the hash functions' outcome,
given `pre`'s values. -/
theorem correct_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) {s : State}
    (hT : TabFacts (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs) s)
    (hP : ∀ {H : Spec.Mgf1.Hash}, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H → PreS pc H.len s)
    (X : pc = true → PreXS s) :
    ∃ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some G ∧
      ∃ t s', Exec isa (signG (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs) pc) s t s' ∧
        abiPreserved s s' ∧ (HypS pc s →
          Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32) (signOut H G s)) := by
  obtain ⟨w, hw, w', hw', hh, hh', hH, hG, hi, hT⟩ := tabs_of (pc := pc) hc hc' hT
  have P := hP hH
  obtain ⟨Tg, T, -⟩ := hT P X
  obtain ⟨t, s', he, habi, hr⟩ := sign_ok P w.l.ok w.l.hash w.l.len w.l.valid w'.l.ok Tg w'.l.hash w'.l.len
    w'.l.valid T X hi w.sh.1 w.sh.2.1
  exact ⟨_, _, hH, hG, t, s', he, habi, hr⟩

/-- The correctness of `vg_rsa_pss_sign`, against its contract, for the
tables of `vs` and `gs`. -/
theorem code_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) (s : State)
    (h : (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (sign (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) s t s' ∧
      abiPreserved s s' ∧ (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨H, G, hH, hG, t, s', he, habi, hr⟩ :=
    correct_of (pc := false) hc hc' (spec_tabS h) (preS_of h) (fun h => nomatch h)
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes false = 3775 + 1 := rfl
  unfold signSpec
  rw [e]
  sig_post [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, Spec.MdHashTable.param,
    Abi.withTables, abi, argRegs, stackArgs_sixteen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr (fun h => nomatch h)

/-- Constant time, for `vg_rsa_pss_sign` and its variant, from what their
contracts give: the tables of the first run, which the public data makes the
second's, at the same addresses with their functions at the same
addresses. -/
theorem constantTime_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs)
    {Pre : State → Prop} {Pub : State → State → Prop}
    (hT : ∀ {s}, Pre s → TabFacts (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs) s)
    (hP : ∀ {s} {H : Spec.Mgf1.Hash}, Pre s → Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H →
      PreS pc H.len s)
    (hX : ∀ {s}, Pre s → pc = true → PreXS s)
    (hQ : ∀ {s₁ s₂}, Pub s₁ s₂ → PubS pc s₁ s₂ ∧
      (∀ f ∈ ((MdHashTable.PPC64LE.tables vs).map (fun T : FnTable => T.fns)).flatten ++
          ((MdHashTable.PPC64LE.tables gs).map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ MdHashTable.PPC64LE.tables vs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ MdHashTable.PPC64LE.tables gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) :
    ConstantTime isa Pre Pub (signG (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs) pc) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨w, hw, w', hw', hh₁, hh₁', hH₁, -, hi₁, hT₁⟩ := tabs_of (pc := pc) hc hc' (hT h₁)
  obtain ⟨p, hsy, hiffH, hiffG⟩ := hQ hp
  have hh₂ := (hiffH _ (List.mem_map_of_mem hw)).mp hh₁
  have hh₂' := (hiffG _ (List.mem_map_of_mem hw')).mp hh₁'
  have hi₂ := (MdHashTable.PPC64LE.held_tableOf hh₂).2.2.2
  have hH₂ := MdHashTable.PPC64LE.hashAt_tableOf hi₂
  have P₁ := hP h₁ hH₁
  have P₂ := hP h₂ hH₂
  have hpw₂ := (hT h₂).2.2
  have T₂ : STabsOn pc (tabsOf vs gs w w') s₂ :=
    ⟨MdHashTable.PPC64LE.tabS_of (by decide) rfl (A := aR pc s₂) (by rw [P₂.hrd]; simp)
      (in_aR (pc := pc) (by decide)) (in_aR_sub (pc := pc) (by decide)) (P₂.ka.sub_left kR_sub)
      (P₂.sa.sub_left (sc_sub P₂))
      (show tGR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) (P₂.ktg.sub_left kR_sub) (P₂.stg.sub_left (sc_sub P₂)) hc'
      (hpw₂.sublist (List.sublist_append_right _ _)) hw' hh₂',
    MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR pc s₂) (by rw [P₂.hrd]; simp)
      (in_aR (pc := pc) (by decide)) (in_aR_sub (pc := pc) (by decide)) (P₂.ka.sub_left kR_sub)
      (P₂.sa.sub_left (sc_sub P₂))
      (show tHR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) (P₂.kth.sub_left kR_sub) (P₂.sth.sub_left (sc_sub P₂)) hc
      (hpw₂.sublist (List.sublist_append_left _ _)) hw hh₂, hX h₂⟩
  have hn := MdHashTable.PPC64LE.mem_names hw
  have hn' := MdHashTable.PPC64LE.mem_names hw'
  have sH : ∀ {f}, f ∈ MdHashTable.PPC64LE.names vs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_left _ hf)).symm
  have sG : ∀ {f}, f ∈ MdHashTable.PPC64LE.names gs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_right _ hf)).symm
  have hk : ∀ {s}, PreS pc w.l.G.len s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.k1
  exact code_ct (Z := tabsOf vs gs w w') w.l.ok w.l.ct w.l.len w'.l.ok w'.l.ct w'.l.hash w'.l.len w'.l.valid
    w.l.hash w.l.valid w.sh.1 w.sh.2.1 _ _ _ _ _ _
    ⟨s₁, ⟨⟨⟨P₁, hT₁ P₁ (hX h₁)⟩, ⟨pubS_refl s₁, hk P₁⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi₁⟩,
      ⟨⟨⟨P₂, T₂⟩, ⟨p, hk P₂⟩, sG hn'.1, sG hn'.2.1, sG hn'.2.2.1, sH hn.1, sH hn.2.1, sH hn.2.2.1, sH hn.2.2.2.1,
        sH hn.2.2.2.2⟩, hi₂⟩⟩
    e₁ e₂

/-- Constant time: `constantTime_of` with the shared contract's facts. -/
theorem code_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) :
    ConstantTime isa (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre
      (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pub
      (sign (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) :=
  constantTime_of (pc := false) hc hc' spec_tabS (fun h hH => preS_of h hH) (fun _ h => nomatch h) pubS_of

/-- `vg_rsa_pss_sign` against its contract, for the tables of `vs` and
`gs`, given a state meeting it. -/
theorem sign_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (sign (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs))
      (signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)) :=
  ⟨code_correct hc hc', code_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg


namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)
open VG.Proof.MdHashTable.PPC64LE (MVar)

/-- The words `ws` written from `p`. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 8) ws

theorem add8_toNat {p : Addr} (h : p.toNat + 8 < 2 ^ 64) : (p + 8).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 * ws.length ≤ a.toNat) → p.toNat + 8 * ws.length < 2 ^ 64 →
    a.toNat + 8 ≤ 2 ^ 64 → (putWs m p ws).readW a 64 = m.readW a 64
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_out (by rw [h8]; omega_using [h]) (by rw [h8]; omega_using [hp]) ha, readW_sep64 (by omega_using [h]) ha (by omega_using [hp])]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 8 * ws.length < 2 ^ 64 →
    Abi.tableHeld 64 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h8])) (by rw [h8]; omega_using [hp]) (by omega_using [hp]), Mem.readW_writeW_self64]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p w) (p := p + 8) (ws := ws) (by rw [h8]; omega_using [hp]) i
        (by simp at hi; omega_using [hi])
      rw [show p + BitVec.ofNat 64 (64 / 8 * (i + 1)) = p + 8 + BitVec.ofNat 64 (64 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega_using []]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (symsOf ns) ++ T.data

/-- The names of the tables' functions. -/
def allNames (vs : List MVar) (gs : List MVar) : List String := MdHashTable.PPC64LE.names vs ++ MdHashTable.PPC64LE.names gs

/-- The memory `m` with the tables of `w` at `0x300000` and `0x300100`, and
`m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MVar) (gs : List MVar) (w : MVar) (w' : MVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
    (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w')) a

/-- A state with `s`'s registers and regions, the tables of `w` at `0x300000`
and `0x300100`, and `vs`' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List MVar) (w : MVar) (w' : MVar) : State :=
  { s with mem := tabMem s.mem vs gs w w', syms := symsOf (allNames vs gs) }

theorem withTabs_arg (s : State) (vs : List MVar) (gs : List MVar) (w : MVar) (w' : MVar) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTabs s vs gs w w') j = stackArg s j := by
  show (tabMem s.mem vs gs w w').readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, hi]
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {vs : List MVar} {gs : List MVar} {w : MVar} {w' : MVar} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
      (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w'))) p ws) :
    Abi.tableHeld 64 (tabMem m vs gs w w') p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hp, hl, hi, hk]
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) (vs : List MVar) (gs : List MVar) (w : MVar) (w' : MVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300000
      (FnTable.words isa (withTabs s vs gs w w') (MdHashTable.PPC64LE.tableOf w)) := by
  have hl : (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega_using [hi]
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) (vs : List MVar) (gs : List MVar) (w : MVar) (w' : MVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300100
      (FnTable.words isa (withTabs s vs gs w w') (MdHashTable.PPC64LE.tableOf w')) :=
  tabMem_above (by decide) (by simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]))


/-! ## Verification with a precomputed key -/

/-- A state meeting verification's precondition but for the tables: a
512-bit modulus, one-byte `e`, a digest of `dl` bytes, 16 words of `pre` at
`0x5000`, the stack arguments at `0x10060`, and the tables' addresses
`0x300000` and `0x300100`. -/
def verifySatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4600 | .r8 => BitVec.ofNat 64 dl
    | .r9 => 0x4000 | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10072 then 0x02 else bif Nat.beq a.toNat 0x10078 then 0x20
    else bif Nat.beq a.toNat 0x10079 then 0x08 else bif Nat.beq a.toNat 0x10081 then 0x50
    else bif Nat.beq a.toNat 0x10088 then 16 else bif Nat.beq a.toNat 0x10092 then 0x30
    else bif Nat.beq a.toNat 0x10099 then 0x01 else bif Nat.beq a.toNat 0x1009A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩,
    ⟨0x10060, 64⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `verifySatBase dl`. -/
def verifyArgs : Nat → BitVec 64
  | 0 => 0 | 1 => 0 | 2 => 0x20000 | 3 => 2080 | 4 => 0x5000 | 5 => 16 | 6 => 0x300000 | _ => 0x300100

theorem verifySat_args (dl : Nat) : ∀ j < 8, (stackArgAddr (verifySatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, verifySatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (verifySatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 8, stackArg s j = verifyArgs j)
    (hrd : s.rd = (verifySatBase dl).rd) (hwr : s.wr = (verifySatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (verSpec tsH tsG).pre s := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; simp; omega_using [hdl])
    | skip

theorem verify_sat_of {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre (withTabs (verifySatBase dl) vs gs w w') :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (verifySatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem verifySat_b16 : ∀ j < 8, stackArg (verifySatBase 16) j = verifyArgs j := by decide
theorem verifySat_b20 : ∀ j < 8, stackArg (verifySatBase 20) j = verifyArgs j := by decide
theorem verifySat_b28 : ∀ j < 8, stackArg (verifySatBase 28) j = verifyArgs j := by decide
theorem verifySat_b32 : ∀ j < 8, stackArg (verifySatBase 32) j = verifyArgs j := by decide
theorem verifySat_b48 : ∀ j < 8, stackArg (verifySatBase 48) j = verifyArgs j := by decide
theorem verifySat_b64 : ∀ j < 8, stackArg (verifySatBase 64) j = verifyArgs j := by decide

theorem verify_sat {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b16⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b20⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b28⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b32⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b48⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b64⟩

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, a working space of 2080 words, the stack arguments at
`0x10060`, and the tables' addresses `0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4200
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x43
    else bif Nat.beq a.toNat 0x10068 then 1 else bif Nat.beq a.toNat 0x10071 then 0x44
    else bif Nat.beq a.toNat 0x10078 then 1 else bif Nat.beq a.toNat 0x10081 then 0x45
    else bif Nat.beq a.toNat 0x10088 then 1 else bif Nat.beq a.toNat 0x10091 then 0x46
    else bif Nat.beq a.toNat 0x10098 then 1 else bif Nat.beq a.toNat 0x100A1 then 0x41
    else bif Nat.beq a.toNat 0x100A8 then BitVec.ofNat 8 dl else bif Nat.beq a.toNat 0x100B1 then 0x47
    else bif Nat.beq a.toNat 0x100C2 then 0x02 else bif Nat.beq a.toNat 0x100C8 then 0x20
    else bif Nat.beq a.toNat 0x100C9 then 0x08 else bif Nat.beq a.toNat 0x100D2 then 0x30
    else bif Nat.beq a.toNat 0x100D9 then 0x01 else bif Nat.beq a.toNat 0x100DA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10060, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `signSatBase dl`. -/
def signArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4300 | 1 => 1 | 2 => 0x4400 | 3 => 1 | 4 => 0x4500 | 5 => 1 | 6 => 0x4600 | 7 => 1
  | 8 => 0x4100 | 9 => BitVec.ofNat 64 dl | 10 => 0x4700 | 11 => 0 | 12 => 0x20000 | 13 => 2080
  | 14 => 0x300000 | _ => 0x300100

theorem signSat_args (dl : Nat) : ∀ j < 16, (stackArgAddr (signSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 16, stackArg s j = signArgs dl j)
    (hrd : s.rd = (signSatBase dl).rd) (hwr : s.wr = (signSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Sg.signSpec tsH tsG).pre s := by
  have e : Sg.stackBytes false = 3775 + 1 := rfl
  unfold Sg.signSpec
  rw [e]
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; simp; omega_using [hdl])
    | skip

theorem sign_sat_of {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre
      (withTabs (signSatBase dl) vs gs w w') :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (signSatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem signSat_b16 : ∀ j < 16, stackArg (signSatBase 16) j = signArgs 16 j := by decide
theorem signSat_b20 : ∀ j < 16, stackArg (signSatBase 20) j = signArgs 20 j := by decide
theorem signSat_b28 : ∀ j < 16, stackArg (signSatBase 28) j = signArgs 28 j := by decide
theorem signSat_b32 : ∀ j < 16, stackArg (signSatBase 32) j = signArgs 32 j := by decide
theorem signSat_b48 : ∀ j < 16, stackArg (signSatBase 48) j = signArgs 48 j := by decide
theorem signSat_b64 : ∀ j < 16, stackArg (signSatBase 64) j = signArgs 64 j := by decide

theorem sign_sat {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b16⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b20⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b32⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b48⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b64⟩

/-! ## The instances -/

/-- What the registration checks of the variants: their functions of the
same name have the same code, there are some, and not too many names. -/
def OK (vs : List MVar) (gs : List MVar) : Prop :=
  MdHashTable.PPC64LE.Coh vs ∧ MdHashTable.PPC64LE.Coh gs ∧ vs ≠ [] ∧ gs ≠ [] ∧ (allNames vs gs).length < 2 ^ 32

instance (vs : List MVar) (gs : List MVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

theorem ok_mem {vs : List MVar} {gs : List MVar} (h : OK vs gs) : ∃ w, w ∈ vs ∧ ∃ w', w' ∈ gs := by
  obtain ⟨-, -, h1, h2, -⟩ := h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h1
  obtain ⟨w', hw'⟩ := List.exists_mem_of_ne_nil _ h2
  exact ⟨w, hw, w', hw'⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs`. -/
theorem verify_ok' {vs : List MVar} {gs : List MVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs)
      (MdHashTable.PPC64LE.fns3 gs)) (verSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  verify_verified h.1 h.2.1 (verify_sat hw hw' h.2.2.2.2)

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs`. -/
theorem sign_ok' {vs : List MVar} {gs : List MVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.Sign.sign (MdHashTable.PPC64LE.fnsOf vs)
      (MdHashTable.PPC64LE.fns3 gs)) (Spec.RsaPss.signMdTableContract
        (abi.withTables Spec.RsaPss.signMdTableSig [("hash", MdHashTable.PPC64LE.tables vs),
          ("mgf1", MdHashTable.PPC64LE.tables gs)]) 3776) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  Sg.stackBytes_eq ▸ Sg.sign_verified h.1 h.2.1 (sign_sat hw hw' h.2.2.2.2)

end VG.Proof.RsaPss.PPC64LE
