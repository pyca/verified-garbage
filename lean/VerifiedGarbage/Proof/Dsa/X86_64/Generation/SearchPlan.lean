module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reframe
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Framework.Omega

/-! # Persistent memory for the bounded p search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def searchSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 28]

def searchWrites (p : PPrimalityPlan) (C : Addr) : List Region :=
  ⟨C, 24⟩ :: ⟨p.construct.hash.F, frameBytes⟩ :: p.changed

structure SearchPlan where
  attempt : PPrimalityPlan
  C : Addr
  controlBase : attempt.construct.hash.W 5 + BitVec.ofNat 64 control = C
  controlSeparate : ∀ r ∈ ⟨attempt.construct.hash.F, frameBytes⟩ :: attempt.changed,
    (⟨C, 24⟩ : Region).Disjoint r
  frameControl : (⟨attempt.construct.hash.F, frameBytes⟩ : Region).Disjoint ⟨C, 24⟩
  hashControl : (⟨attempt.construct.hash.S, oRsa⟩ : Region).Disjoint ⟨C, 24⟩
  pControl : (⟨off (attempt.construct.hash.W 5) p, attempt.construct.len⟩ : Region).Disjoint ⟨C, 24⟩
  exponentControl : (⟨off (attempt.construct.hash.W 5) exponent, attempt.construct.len⟩ : Region).Disjoint ⟨C, 24⟩
  seedSeparate : ∀ r ∈ searchWrites attempt C,
    (⟨attempt.construct.hash.seedPtr, attempt.construct.hash.len⟩ : Region).Disjoint r
  qSeparate : ∀ r ∈ searchWrites attempt C,
    (⟨off (attempt.construct.hash.W 5) q, attempt.construct.qb.length⟩ : Region).Disjoint r
  tapeSeparate : ∀ r ∈ searchWrites attempt C,
    (⟨attempt.rp, attempt.rand.length⟩ : Region).Disjoint r

structure SearchMemory (p : SearchPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.attempt.construct.hash.F p.attempt.construct.hash.S
  rep : ∃ V, Rep s.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W
  slots : ∀ k ∈ searchSlots, W k = p.attempt.construct.hash.W k
  label : LabAt s p.attempt.construct.hash.F p.attempt.construct.hash.S
    p.attempt.construct.hash.W p.attempt.construct.hash.wrapped p.attempt.construct.hash.len
  seedRead : ∀ i < p.attempt.construct.hash.len,
    InRegions (s.rd ++ s.wr) (off p.attempt.construct.hash.seedPtr i) 1
  wrappedWrite : ∀ i < p.attempt.construct.hash.len,
    InRegions s.wr (off p.attempt.construct.hash.wrapped i) 1
  hashWrite : ∀ i < (p.attempt.construct.hash.count + 1) * p.attempt.construct.hash.len,
    InRegions s.wr (off p.attempt.construct.hash.output i) 1
  seed : Spec.Rsa.bytesAt s.mem p.attempt.construct.hash.seedPtr p.attempt.construct.hash.len =
    p.attempt.construct.hash.seed
  scratch : Scr s p.attempt.construct.B p.attempt.construct.Z
  qSource : Src s p.attempt.construct.B p.attempt.construct.Z
    (off (p.attempt.construct.hash.W 5) q) p.attempt.construct.qb
  tape : Src s p.attempt.construct.B p.attempt.construct.Z p.attempt.rp p.attempt.rand
  shapedWrite : ∀ i < p.attempt.construct.len,
    InRegions s.wr (off (off (p.attempt.construct.hash.W 5) shaped) i) 1
  pWrite : ∀ i < p.attempt.construct.len,
    InRegions s.wr (off (off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) i) 1
  exponentWrite : ∀ i < p.attempt.construct.len,
    InRegions s.wr (off (off (p.attempt.construct.hash.W 5) exponent) i) 1
  witnessWrite : ∀ i < p.attempt.construct.len,
    InRegions s.wr (off (off (p.attempt.construct.hash.W 5) witness) i) 1

theorem SearchMemory.frame {p : SearchPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : SearchMemory p W s) (L : Lay t p.attempt.construct.hash.F p.attempt.construct.hash.S)
    (R : ∃ V, Rep t.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W')
    (hw : ∀ k ∈ searchSlots, W' k = W k)
    (hf : Frame (searchWrites p.attempt p.C) s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    SearchMemory p W' t where
  layout := L
  rep := R
  slots k hk := (hw k hk).trans (h.slots k hk)
  label := h.label.congr hrd hwr rfl rfl
  seedRead i hi := by rw [hrd, hwr]; exact h.seedRead i hi
  wrappedWrite i hi := by rw [hwr]; exact h.wrappedWrite i hi
  hashWrite i hi := by rw [hwr]; exact h.hashWrite i hi
  seed := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt hf p.seedSeparate (by
      rcases p.attempt.construct.hash.width with hh | hh <;> omega)]
    exact h.seed
  scratch := h.scratch.congr hwr
  qSource := source_of_frame h.qSource hf p.qSeparate (by
    rw [p.attempt.construct.qLength]
    rcases p.attempt.construct.hash.width with hh | hh <;> omega) hrd hwr
  tape := source_of_frame h.tape hf p.tapeSeparate p.attempt.randMax hrd hwr
  shapedWrite i hi := by rw [hwr]; exact h.shapedWrite i hi
  pWrite i hi := by rw [hwr]; exact h.pWrite i hi
  exponentWrite i hi := by rw [hwr]; exact h.exponentWrite i hi
  witnessWrite i hi := by rw [hwr]; exact h.witnessWrite i hi

end VG.Proof.Dsa.X86_64.Generation
