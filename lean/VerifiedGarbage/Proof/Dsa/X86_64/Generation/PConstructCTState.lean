module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWorkspaceCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! ### `Dsa.X86_64.Generation.PShapeValue`, which this module and modules that import it used -/

section

/-! # The shaped hash bytes are determined by the public seed and offset -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

def HashPlan.shapedValue (p : HashPlan) (H : Spec.Mgf1.Hash) (plen : Nat) : Nat :=
  Spec.Ffdh.candidateOf (8 * plen)
    (VG.Proof.Dsa.Generation.contributions (8 * p.len)
      (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1))

theorem hash_shaped_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat}
    (hl : 2 ≤ plen) (hroom : plen ≤ (p.count + 1) * p.len) :
    Spec.Ffdh.candidateOf (8 * plen) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem
      (off p.output ((p.count + 1) * p.len - plen)) plen)) = p.shapedValue H plen := by
  have hsuf := VG.Proof.Dsa.Generation.bytesAt_suffix_value s.mem p.output ((p.count + 1) * p.len - plen) plen
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, pow256_eq] at hsuf
  change Spec.Ffdh.candidateOf (8 * plen) (Spec.Dsa.decodeBE _) = _
  rw [← hsuf, VG.Proof.Dsa.Generation.candidateOf_mod_width (by omega_using [hl]) (Nat.le_refl _)]
  rfl

theorem pShape_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.X86_64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot p.size.2.2 hlmax)
    fun u ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.2.1, hk.2.2]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega_using [hl] : 9 ≤ 8 * plen) (by omega_using [hlmax]) (by rw [hbl]; omega_using [])
    hsi hdi (by rw [hbl]; exact hcx) hdx hrd
    (fun i hi => by rw [hk.2.2]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨_, hx, _, _⟩ => ?_
  rw [hbl] at hx
  have value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen) = p.shapedValue H plen := by
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) = _
    rw [hx]
    exact hash_shaped_value hs hl hroom
  have encoded := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op plen)
  rw [bytesAt_length, value] at encoded
  exact encoded.symm

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public data connecting p hashing to native reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def PConstructPlan.withWords (p : PConstructPlan) (W : Nat → BitVec 64)
    (hw : ∀ i < 6, W i = p.hash.W i) : PConstructPlan :=
  { p with
    hash := p.hash.withWords W (fun i hi => hw i (by omega_using [hi]))
    base := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.base
    shapedSlot := by simpa only [HashPlan.withWords, hw 0 (by decide), hw 5 (by decide)] using p.shapedSlot
    shapedOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedOutside
    shapedHash := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedHash
    shapedInput := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.shapedInput
    qHash := by simpa only [HashPlan.withWords, HashPlan.changed, hw 5 (by decide)] using p.qHash
    pOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pOutside
    exponentOutside := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.exponentOutside
    pExponent := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.pExponent
    frameArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.frameArithmetic
    hashArithmetic := by simpa only [HashPlan.withWords, hw 5 (by decide)] using p.hashArithmetic }

structure PConstructPublic where
  plan : PConstructPlan
  ws : List Region

def PConstructBefore (n : Nat) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (p : PConstructPublic) (s : State) : Prop :=
  (∃ W, ∃ hw : ∀ i < 6, W i = p.plan.hash.W i,
    PConstructState (p.plan.withWords W hw) H s ∧ FrV n p.plan.hash.F p.ws s) ∧
    p.plan.len = pLen ∧ p.plan.hash.len = qLen

def PConstructPublic.hash (p : PConstructPublic) : PHashPublic := ⟨p.plan.hash, p.ws⟩

theorem pConstruct_hash {n pLen qLen : Nat} {H : Spec.Mgf1.Hash} {p : PConstructPublic} {s : State}
    (h : PConstructBefore n H pLen qLen p s) :
    ContributionBefore n H 0 qLen ((8 * pLen - 1) / (8 * qLen)) p.hash s := by
  obtain ⟨⟨W, hw, hs, hf⟩, hp, hq⟩ := h
  exact ⟨⟨W, (fun i hi => hw i (by omega_using [hi])), hs.hash, hf⟩, hq,
    p.plan.hashCount.trans (by rw [hp, hq])⟩

def PConstructPublic.workspace (p : PConstructPublic) (H : Spec.Mgf1.Hash) : CandidateWorkspacePublic where
  frame := {
    B := p.plan.B
    F := p.plan.hash.F
    arena := p.plan.hash.W 5
    Z := p.plan.Z
    w := p.plan.len / 8
    xb := Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len)
    qb := p.plan.qb
    xLength := by rw [VG.Proof.Dsa.encodeBE_length]; rcases p.plan.width with h | h | h <;> omega_using [h]
    qLength := by
      rw [p.plan.qLength]
      rcases p.plan.width with h | h | h <;> rcases p.plan.hash.width with q | q <;> omega_using [h, q]
    qNonempty := by rw [p.plan.qLength]; rcases p.plan.hash.width with h | h <;> omega_using [h]
    qPositive := p.plan.qPositive
    qFits := p.plan.qFits
    separate := p.plan.frameHeaders
    pOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega_using [h]
      simpa only [he] using p.plan.pOutside
    eOutside := by
      have he : 8 * (p.plan.len / 8) = p.plan.len := by rcases p.plan.width with h | h | h <;> omega_using [h]
      simpa only [he] using p.plan.exponentOutside }
  base := p.plan.base.symm
  room := p.plan.workspaceRoom
  lower := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega_using [h]
  upper := by rcases p.plan.width with h | h | h <;> dsimp only <;> omega_using [h]
  outside := p.plan.frameOutside

end VG.Proof.Dsa.X86_64.Generation
