module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.AArch64.Generation.PShapeCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PHashCopyCT`, which only this module used -/

section

/-! # Copy each p hash contribution with a public address trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

def PHashCopyBefore (len count : Nat) (p : PHashPublic) (s : State) : Prop :=
  Lay s p.plan.F p.plan.S ∧ (∃ V W, Rep s.mem p.plan.F p.plan.S V W ∧ W 4 = p.plan.output) ∧
    p.plan.len = len ∧ p.plan.count = count

def PHashCopyReady (len count j : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off p.plan.S oDig ∧ s.gpr .x2 = VG.Proof.Bignum.off p.plan.output ((count - j) * len) ∧
    s.gpr .x9 = BitVec.ofNat 64 len

theorem pSeedHash_copyReady {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = G.D)
    {k len count j : Nat} {p : PHashPublic} {s : State} (hj : j ≤ count)
    (h : ContributionBefore H k len count p s) :
    WP isa (Impl.Dsa.AArch64.Generation.pSeedHash G len j) s (PHashCopyBefore len count p) := by
  obtain ⟨⟨W, hw, hs⟩, hlenEq, hcountEq⟩ := h
  let q := p.plan.withWords W hw
  have hlen := p.plan.size.2.1
  have hjp : j ≤ p.plan.count := by rw [hcountEq]; exact hj
  have hj' : j < 4096 := by omega_using [p.plan.count_le, hjp]
  obtain ⟨V, R⟩ := hs.rep
  have hs := pSeedHash_ok hG hmatch hsize (show p.plan.len < 4096 by omega_using [hlen]) hj'
    (show p.plan.offset + j < 2 ^ 32 by omega_using [p.plan.carry, hjp])
    hs.layout R hs.hashArgs q.seed_slot q.wrapped_slot q.offset_slot
    hs.seedRead hs.wrappedWrite (by
      intro i hi l hl he
      have a : Region.Contains ⟨p.plan.seedPtr, p.plan.len⟩ (VG.Proof.Bignum.off p.plan.seedPtr i) 1 :=
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hlen, hi])
      have b : Region.Contains ⟨p.plan.wrapped, p.plan.len⟩ (VG.Proof.Bignum.off p.plan.wrapped l) 1 :=
        Offset.contains_base _ (by omega_using [hl]) (by omega_using [hlen, hl])
      change VG.Proof.Bignum.off p.plan.seedPtr i = VG.Proof.Bignum.off p.plan.wrapped l at he
      exact p.plan.seed_wrap _ (he ▸ a) b) p.plan.wrapped_sep
  rw [hlenEq] at hs
  exact WP.mono hs fun _ ⟨L, _, _, ⟨V, R'⟩, _⟩ =>
    ⟨L, ⟨V, W, R', q.output_slot⟩, hlenEq, hcountEq⟩

theorem hashCopyArgs_ct (len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) :
    RelCT isa (Two (PHashCopyBefore len count))
      (.block (Impl.Dsa.AArch64.Generation.hashCopyArgs len count j))
      (Two (PHashCopyReady len count j)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (hc := .block []) (by rfl)) ?_
  intro p s h
  obtain ⟨V, W, R, hout⟩ := h.2.1
  exact WP.mono (hashCopyArgs_ok (j := j) hlen hc h.1 R hout)
    fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem pHashOne_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (k len count j : Nat) (hlen : len = 20 ∨ len = 32) (hc : count ≤ 11) (hj : j ≤ count) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pHashOne G len count j) (fun _ _ => True) := by
  refine RelCT.seq (two_post (pSeedHash_ct hG H k len count j hlen hj (by omega_using [hc, hj]))
    (fun _ _ h => pSeedHash_copyReady hG hmatch hsize hj h))
    (RelCT.seq (hashCopyArgs_ct len count j hlen hc) ?_)
  exact two_taint [.x12, .x2, .x9] (by
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Public addressing for shaping the full-width p candidate. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/HashSequenceCT.lean`, which only this module imported.
section

/-! # Constant time of the complete p-candidate hash sequence -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hashStep_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pHashOne G len count k)
      (Two (ContributionBefore H (k + 1) len count)) := by
  refine two_post (pHashOne_ct hG H hmatch hsize k len count k hlen hc hk) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs⟩, he⟩ := h
  have hd' : G.D = p.plan.len := hd.trans he.1.symm
  have hk' : k ≤ p.plan.count := by rw [he.2]; exact hk
  have step := hashStep_ok (p := p.plan.withWords W hw) hG hmatch hsize hd' hk' hs
  rw [show (p.plan.withWords W _).len = len from he.1,
    show (p.plan.withWords W _).count = count from he.2] at step
  exact WP.mono step fun t ⟨ht, _, _⟩ => ⟨⟨W, hw, ht⟩, he⟩

theorem hashPrefix_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count k : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hk : k ≤ count + 1) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (Impl.Dsa.AArch64.Generation.pHashPrefix G len count k)
      (Two (ContributionBefore H k len count)) := by
  induction k with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ k ih =>
    exact RelCT.seq (ih (by omega)) (hashStep_ct hG H hmatch hsize len count k hlen hd hc (by omega))

theorem pHashes_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hc : count ≤ 11) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (Impl.Dsa.AArch64.Generation.pHashes G len count)
      (Two (ContributionBefore H (count + 1) len count)) :=
  hashPrefix_ct hG H hmatch hsize len count (count + 1) hlen hd hc (Nat.le_refl _)

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

def PShapeReady (len count plen : Nat) (p : PHashPublic) (s : State) : Prop :=
  s.gpr .x2 = p.plan.W 0 ∧
  s.gpr .x12 = VG.Proof.Bignum.off p.plan.output ((count + 1) * len - plen) ∧
  s.gpr .x9 = BitVec.ofNat 64 plen

theorem pShapeArgs_ct (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 4096) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H k len count))
      (.block (Impl.Dsa.AArch64.Generation.pShapeArgs len count plen))
      (Two (PShapeReady len count plen)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (hc := .block []) (by rfl)) ?_
  intro p s h
  obtain ⟨⟨W, hw, hs⟩, _⟩ := h
  obtain ⟨V, R⟩ := hs.rep
  exact WP.mono (pShapeArgs_ok hs.layout R (hw 0 (by decide))
    ((hw 4 (by decide)).trans p.plan.output_slot) hn hl)
    fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem pShape_ct (H : Spec.Mgf1.Hash) (k len count plen : Nat)
    (hn : (count + 1) * len < 4096) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H k len count))
      (Impl.Dsa.AArch64.Generation.pShape len count plen) (fun _ _ => True) := by
  refine RelCT.seq (pShapeArgs_ct H k len count plen hn hl) (qShape_ct ?_)
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.trans ht.2.2.symm

theorem pBuild_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (len count plen : Nat) (hlen : len = 20 ∨ len = 32) (hd : G.D = len)
    (hc : count ≤ 11) (hl : plen ≤ 1024) :
    RelCT isa (Two (ContributionBefore H 0 len count))
      (.seq (Impl.Dsa.AArch64.Generation.pHashes G len count)
        (Impl.Dsa.AArch64.Generation.pShape len count plen)) (fun _ _ => True) := by
  refine RelCT.seq (pHashes_ct hG H hmatch hsize len count hlen hd hc)
    (pShape_ct H (count + 1) len count plen ?_ hl)
  rcases hlen with rfl | rfl <;> omega_using [hc]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PConstructReadyCT`, which only this module used -/

section

/-! # Preserve public candidate bytes and persistent arguments across hashing -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PBuildValue.lean`, which only this module imported.
section

/-! # Exact public bytes produced by the complete p hash-and-shape stage -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pBuild_value {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p H 0 s)
    {plen : Nat} {op : Addr} (hl : 2 ≤ plen) (hlmax : plen ≤ 1024)
    (hroom : plen ≤ (p.count + 1) * p.len) (hop : p.W 0 = op)
    (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.AArch64.Generation.pShape p.len p.count plen)) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  refine WP.seq (WP.mono (pHashes_ok hG hmatch hsize hd hs)
    fun u ⟨hu, st, _⟩ => ?_)
  exact pShape_value hu hl hlmax hroom hop (fun i hi => st.wr ▸ hout i hi) hsep

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pConstruct_ready {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PConstructPublic} {s : State}
    (h : PConstructBefore H pLen qLen p s) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G qLen ((8 * pLen - 1) / (8 * qLen)))
      (Impl.Dsa.AArch64.Generation.pShape qLen ((8 * pLen - 1) / (8 * qLen)) pLen)) s
      (CandidateWorkspaceBefore (pLen / 8) pLen qLen (p.workspace H)) := by
  obtain ⟨⟨W, hw, hs⟩, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have hl : 2 ≤ q.len ∧ q.len ≤ 1024 ∧ q.len = 8 * (q.len / 8) := by
    change 2 ≤ p.plan.len ∧ p.plan.len ≤ 1024 ∧ p.plan.len = 8 * (p.plan.len / 8)
    rcases p.plan.width with h | h | h <;> omega_using [h]
  have hd' : G.D = q.hash.len := hd.trans hq.symm
  have hv := pBuild_value hG hmatch hsize hd' hs.hash hl.1 hl.2.1 q.hashRoom q.shapedSlot
    hs.shapedWrite q.shapedInput
  have hf := pBuild_ok hG hmatch hsize hd' hs.hash hl.1 hl.2.1 q.hashRoom q.hashCount
    (by simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
    q.shapedSlot hs.shapedWrite q.shapedInput q.shapedHash (Spec.Rsa.os2ip q.qb)
  have step := VG.Proof.Bignum.AArch64.wp_and hv hf
  change WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G p.plan.hash.len p.plan.hash.count)
    (Impl.Dsa.AArch64.Generation.pShape p.plan.hash.len p.plan.hash.count p.plan.len)) s _ at step
  rw [p.plan.hashCount, hp, hq] at step
  refine WP.mono step fun t ⟨bt, _, _, L, ⟨V, R⟩, rd, wr, _, ff⟩ => ?_
  have bt' : Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.plan.hash.W 5) shaped) p.plan.len =
      Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len) := by
    simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide), HashPlan.shapedValue,
      HashPlan.digest] using bt
  have sq := source_of_frame hs.qSource ff q.qHash
    (by rw [q.qLength]; have := q.hash.size; omega_using [this]) rd wr
  refine ⟨?_, hs.scratch.congr wr, ?_, ?_, ?_⟩
  · refine ⟨L.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; exact L.ld (d := 8 * k) (n := 8) (by unfold VG.Impl.RsaOaep.AArch64.frameBytes; omega_using [hk])
    · exact (R.fr 5 (by decide)).trans (hw 5 (by decide))
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        have hi' : i < p.plan.len := by
          simpa only [PConstructPublic.workspace, VG.Proof.Dsa.encodeBE_length] using hi
        obtain ⟨r, hr, hc⟩ := hs.shapedWrite i hi'
        rw [rd, wr]
        refine ⟨r, List.mem_append_right _ hr, ?_⟩
        simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords,
          hw 5 (by decide)] using hc
      · intro i hi
        simp only [PConstructPublic.workspace] at hi ⊢
        rw [List.getElem_eq_getD (0 : Byte), ← bt']
        have hi' : i < p.plan.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
        simp [Spec.Rsa.bytesAt, VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, hi']
      · intro i hi
        exact p.plan.shapedOutside i (by
          simpa only [PConstructPublic.workspace, VG.Proof.Dsa.encodeBE_length] using hi)
    · simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using sq
    · intro i hi
      have hi' : i < q.len := by
        change i < 8 * (p.plan.len / 8) at hi
        rw [hl.2.2]; exact hi
      rw [wr]
      simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using hs.pWrite i hi'
    · intro i hi
      have hi' : i < q.len := by
        change i < 8 * (p.plan.len / 8) at hi
        rw [hl.2.2]; exact hi
      rw [wr]
      simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using hs.exponentWrite i hi'
  · change p.plan.len / 8 = pLen / 8; rw [hp]
  · change (Spec.Dsa.encodeBE p.plan.len _).length = pLen; rw [VG.Proof.Dsa.encodeBE_length, hp]
  · exact p.plan.qLength.trans hq

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Constant time of complete p construction at every supported DSA size -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem pConstruct_ct_of {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) (hq : qLen = 20 ∨ qLen = 32)
    (hc : (8 * pLen - 1) / (8 * qLen) ≤ 11) (hp : pLen ≤ 1024)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace (pLen / 8)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (candidateArguments pLen qLen))) hc₂).isSome = true) :
    RelCT isa (Two (PConstructBefore H pLen qLen)) (pConstruct G pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map PConstructPublic.hash (fun _ _ h => pConstruct_hash h)
    (pBuild_ct hG H hmatch hsize qLen ((8 * pLen - 1) / (8 * qLen)) pLen hq hd hc hp))
    (fun _ _ h => pConstruct_ready hG hmatch hsize hhash hseedsize hd h)) ?_
  exact two_map (fun p => p.workspace H) (fun _ _ h => h) (reduceFromFrame_ct (pLen / 8) pLen qLen ht₁ ht₂)

def GenerationSizes (pLen qLen : Nat) : Prop :=
  (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)

theorem pConstruct_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PConstructBefore H pLen qLen)) (pConstruct G pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact pConstruct_ct_of hG H _ _ hmatch hsize hhash hseedsize hd
      (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
