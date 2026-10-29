module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
/-! # Public addressing for shaping the full-width p candidate -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PHashCopyCT.lean`, which only this module imported.
section

/-! # Copy each p hash contribution with a public address trace -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

def PHashCopyBefore (len count : Nat) (p : PHashPublic) (s : State) : Prop :=
  Lay s p.plan.F p.plan.S ∧ (∃ V W, Rep s.mem p.plan.F p.plan.S V W ∧ W 4 = p.plan.output) ∧
    p.plan.len = len ∧ p.plan.count = count

def PHashCopyReady (len count j : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .rsi = off p.plan.S oDig ∧ s.gpr .rdi = off p.plan.output ((count - j) * len) ∧
    s.gpr .rcx = BitVec.ofNat 64 len ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * len)

theorem pSeedHash_copyReady {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = G.D)
    {n k len count j : Nat} {p : PHashPublic} {s : State} (hj : j ≤ count)
    (h : ContributionBefore n H k len count p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pSeedHash G len j) s (PHashCopyBefore len count p) := by
  obtain ⟨⟨W, hw, hs, _⟩, hlenEq, hcountEq⟩ := h
  let q := p.plan.withWords W hw
  have hlen := p.plan.size.2.1
  have hjp : j ≤ p.plan.count := by rw [hcountEq]; exact hj
  have hj' : j < 2 ^ 31 := by omega_using [p.plan.count_le, hjp]
  obtain ⟨V, R⟩ := hs.rep
  have hs := pSeedHash_ok hG hmatch hsize (show p.plan.len < 2 ^ 31 by omega) hj'
    (show p.plan.offset + j < 2 ^ 32 by omega_using [p.plan.carry, hjp])
    hs.layout R hs.hashArgs q.seed_slot q.wrapped_slot q.offset_slot
    hs.seedRead hs.wrappedWrite (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega) (by omega)
      exact p.plan.seed_wrap _ (he ▸ a) b) p.plan.wrapped_sep
  rw [hlenEq] at hs
  exact WP.mono hs fun _ ⟨L, _, _, _, _, ⟨V, R'⟩, _⟩ =>
    ⟨L, ⟨V, W, R', q.output_slot⟩, hlenEq, hcountEq⟩

theorem hashCopyArgs_ct (len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) :
    RelCT isa (Two (PHashCopyBefore len count))
      (.block (Impl.Dsa.X86_64.Generation.hashCopyArgs len count j))
      (Two (PHashCopyReady len count j)) := by
  refine two_post (two_taint [.rsp] ?_ (hc := .block []) (by rfl)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.1.rsp.trans ht.1.rsp.symm
  · intro p s h
    obtain ⟨V, W, R, hout⟩ := h.2.1
    exact WP.mono (hashCopyArgs_ok (j := j) hlen hc h.1 R hout)
      fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩

theorem pHashOne_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (k len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) (hj : j ≤ count) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pHashOne G len count j) (fun _ _ => True) := by
  refine RelCT.seq (two_post (pSeedHash_ct hG n hn H k len count j hlen hj (by omega))
    (fun _ _ h => pSeedHash_copyReady hG hmatch hsize hj h))
    (RelCT.seq (hashCopyArgs_ct len count j hlen hc) ?_)
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.witnessCut_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashSequenceCT.lean`, which only this module imported.
section

/-! # Constant time of the complete p-candidate hash sequence -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashStep_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pHashOne G len count k)
      (Two (ContributionBefore n H (k + 1) len count)) := by
  refine two_post (pHashOne_ct hG n hn H hmatch hsize k len count k hlen hc hk) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs, hf⟩, he⟩ := h
  have hd' : G.D = p.plan.len := hd.trans he.1.symm
  have hk' : k ≤ p.plan.count := by rw [he.2]; exact hk
  have step := hashStep_ok (p := p.plan.withWords W hw) hG hmatch hsize hd' hk' hs
  rw [show (p.plan.withWords W _).len = len from he.1,
    show (p.plan.withWords W _).count = count from he.2] at step
  exact WP.mono step fun t ⟨ht, _, wr, _, _⟩ =>
    ⟨⟨W, hw, ht, hf.congr (ht.layout.rsp.trans hs.layout.rsp.symm) wr⟩, he⟩

theorem hashPrefix_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count + 1) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (Impl.Dsa.X86_64.Generation.pHashPrefix G len count k)
      (Two (ContributionBefore n H k len count)) := by
  induction k with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ k ih =>
    exact RelCT.seq (ih (by omega)) (hashStep_ct hG n hn H hmatch hsize len count k hlen hd hc (by omega))

theorem pHashes_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hc : count ≤ 11) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (Impl.Dsa.X86_64.Generation.pHashes G len count)
      (Two (ContributionBefore n H (count + 1) len count)) :=
  hashPrefix_ct hG n hn H hmatch hsize len count (count + 1) hlen hd hc (Nat.le_refl _)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

def PShapeReady (len count plen : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .rdi = p.plan.W 0 ∧ s.gpr .rsi = off p.plan.output ((count + 1) * len - plen) ∧
    s.gpr .rcx = BitVec.ofNat 64 plen ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * plen)

theorem pShapeArgs_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen))
      (Two (PShapeReady len count plen)) := by
  have args : ∀ p s, ContributionBefore n H k len count p s →
      WP isa (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen)) s
        (PShapeReady len count plen p) := by
    intro p s h
    obtain ⟨⟨W, hw, hs, _⟩, _⟩ := h
    obtain ⟨V, R⟩ := hs.rep
    exact WP.mono (pShapeArgs_ok hs.layout R (hw 0 (by decide)) ((hw 4 (by decide)).trans p.plan.output_slot) hn hl)
      fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩
  apply two_post (hw := args)
  apply RelCT.block_append (M := isa) (l₁ :=
    [.mov .rsi (.mem (Impl.Mgf1.X86_64.sp 32)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 ((count + 1) * len - plen)))])
    (l₂ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 0)), .mov32 .rcx (.imm plen),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * plen)))])
  refine RelCT.seq (two_post (Ψ := fun (p : PHashPublic) s => s.gpr .rsp = p.plan.F)
    (two_taint [.rsp] ?_ (hc := .block []) (by rfl)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨⟨_, _, hs, _⟩, _⟩ := hs
    obtain ⟨⟨_, _, ht, _⟩, _⟩ := ht
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    have total := args p s h
    change WP isa (.block
      ([.mov .rsi (.mem (Impl.Mgf1.X86_64.sp 32)),
        .alu .add .rsi (.imm (BitVec.ofNat 32 ((count + 1) * len - plen)))] ++
       [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 0)), .mov32 .rcx (.imm plen),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (8 * plen)))])) s _ at total
    obtain ⟨⟨_, _, hs, _⟩, _⟩ := h
    exact WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rsi] (WP.block_append_iff.mp total) rfl)
      fun t ⟨_, hk⟩ => (hk.gpr (by decide)).trans hs.layout.rsp
  · exact two_taint [.rsp] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact hs.trans ht.symm) (hc := .block []) (by rfl)

theorem pShape_ct (n : Nat) (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H k len count))
      (Impl.Dsa.X86_64.Generation.pShape len count plen) (fun _ _ => True) := by
  refine RelCT.seq (pShapeArgs_ct n H k len count plen hn hl) ?_
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem pBuild_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count plen : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore n H 0 len count))
      (.seq (Impl.Dsa.X86_64.Generation.pHashes G len count)
        (Impl.Dsa.X86_64.Generation.pShape len count plen)) (fun _ _ => True) := by
  refine RelCT.seq (pHashes_ct hG n hn H hmatch hsize len count hlen hd hc)
    (pShape_ct n H (count + 1) len count plen ?_ hl)
  rcases hlen with rfl | rfl <;> omega

end VG.Proof.Dsa.X86_64.Generation
