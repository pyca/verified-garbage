module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityPlan
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import Aesop.BuiltinRules

/-! ### `Dsa.X86_64.Generation.AttemptEntry`, which this module and modules that import it used -/

section

/-! # Enter a p attempt from the persistent frame and controller offset -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PAttemptArgs.lean`, which only this module imported.
section

/-! # Frame arguments for a complete p-candidate attempt -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.RsaOaep.X86_64

theorem pAttemptArgs_ok {s : State} {B F S op : Addr} {V : Nat → Byte}
    {W : Nat → BitVec 64} {offset : BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hdi : s.gpr .rdi = B)
    (hread : InRegions (s.rd ++ s.wr) (off B 8) 8)
    (hoff : word s.mem B 8 = offset)
    (hop : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped = op) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 27 (W 3)) ∧
      Outside F 0 224 s.mem t.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hst0 : InRegions s.wr F 8 := by simpa [off] using L.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
      t.mem = ((s.mem.writeW (off F 0) op).writeW (off F 16) offset).writeW
        (off F 216) (W 3)) (by
    xrun [Impl.Dsa.X86_64.Generation.pAttemptArgs, ea_sp, L.rsp, State.ea,
      Impl.Mgf1.X86_64.sp, BitVec.ofInt_natCast, hdr, hdrOff, hdi, hread, hoff,
      L.ld (d := 40) (by decide), L.ld (d := 24) (by decide),
      hst0, L.st (d := 16) (by decide), L.st (d := 216) (by decide),
      R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      R.slot (d := 24) (k := 3) rfl (by decide) rfl,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.shaped < 2 ^ 31), hop]) rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 27 (W 3)) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) op).wf L.geo
      (by decide : 2 < nW) offset).wf L.geo (by decide : 27 < nW) (W 3)
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]
  exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 16) (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ F _ (d := 216) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure AttemptEntry (p : PConstructPlan) (H : Spec.Mgf1.Hash) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.hash.F p.hash.S
  rep : ∃ V, Rep s.mem p.hash.F p.hash.S V W
  words : p.hash.W = upd (upd (upd W 0 (off (W 5) shaped)) 2 (BitVec.ofNat 64 p.hash.offset)) 27 (W 3)
  hashArgs : LabAt s p.hash.F p.hash.S p.hash.W p.hash.wrapped p.hash.len
  seedRead : ∀ i < p.hash.len, InRegions (s.rd ++ s.wr) (off p.hash.seedPtr i) 1
  wrappedWrite : ∀ i < p.hash.len, InRegions s.wr (off p.hash.wrapped i) 1
  outputWrite : ∀ i < (p.hash.count + 1) * p.hash.len, InRegions s.wr (off p.hash.output i) 1
  seed : Spec.Rsa.bytesAt s.mem p.hash.seedPtr p.hash.len = p.hash.seed
  seedFrame : (⟨p.hash.seedPtr, p.hash.len⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  scratch : Scr s p.B p.Z
  qSource : Src s p.B p.Z (off (p.hash.W 5) q) p.qb
  qFrame : (⟨off (p.hash.W 5) q, p.qb.length⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  shapedWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) shaped) i) 1
  pWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) Impl.Dsa.Generation.Layout.p) i) 1
  exponentWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) exponent) i) 1

theorem attemptEntry_ok {p : PConstructPlan} {H : Spec.Mgf1.Hash} {W : Nat → BitVec 64}
    {s : State} {C : Addr} (h : AttemptEntry p H W s)
    (hdi : s.gpr .rdi = C) (hread : InRegions (s.rd ++ s.wr) (off C 8) 8)
    (hoff : word s.mem C 8 = BitVec.ofNat 64 p.hash.offset) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s fun t =>
      PConstructState p H t ∧ Frame [⟨p.hash.F, frameBytes⟩] s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (pAttemptArgs_ok h.layout R hdi hread hoff rfl)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.hash.F, frameBytes⟩] s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.hash.F, frameBytes⟩ (by simp)
    change ¬ ofs p.hash.F a < frameBytes at hn
    unfold frameBytes at hn
    omega_using [hn]
  have hqmax : p.qb.length < 2 ^ 64 := by
    rw [p.qLength]; rcases p.hash.width with hh | hh <;> omega_using [hh]
  refine ⟨⟨⟨Lt, ⟨V, ?_⟩, h.hashArgs.congr kt.2.1 kt.2.2 rfl rfl,
      (fun i hi => by rw [kt.2.1, kt.2.2]; exact h.seedRead i hi),
      (fun i hi => by rw [kt.2.2]; exact h.wrappedWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.outputWrite i hi), ?_, fun j hj => by omega⟩,
      h.scratch.congr kt.2.2,
      source_of_frame h.qSource ff (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.qFrame)
        hqmax kt.2.1 kt.2.2,
      (fun i hi => by rw [kt.2.2]; exact h.shapedWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.pWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.exponentWrite i hi)⟩, ff, kt⟩
  · rw [h.words]; exact Rt
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.seedFrame)
      (by rcases p.hash.width with hh | hh <;> omega_using [hh]), h.seed]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Build each p-attempt's proof state from the retained search frame -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Reframe.lean`, which only this module imported.
section

/-! # Reuse the fixed generation layout at the next offset and witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def HashPlan.reframe (p : HashPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.W 1) (h3 : W 3 = p.W 3) (h4 : W 4 = p.W 4)
    (h2 : W 2 = BitVec.ofNat 64 offset) (hcarry : offset + p.count < 2 ^ 32) : HashPlan :=
  { p with
    W := W
    offset := offset
    seed_slot := h1.trans p.seed_slot
    wrapped_slot := h3.trans p.wrapped_slot
    output_slot := h4.trans p.output_slot
    offset_slot := h2
    carry := hcarry }

def PConstructPlan.reframe (p : PConstructPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.hash.W 1) (h3 : W 3 = p.hash.W 3) (h4 : W 4 = p.hash.W 4)
    (h5 : W 5 = p.hash.W 5) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h0 : W 0 = off (W 5) shaped) (hcarry : offset + p.hash.count < 2 ^ 32) : PConstructPlan :=
  { p with
    hash := p.hash.reframe W offset h1 h3 h4 h2 hcarry
    base := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.base
    shapedSlot := h0
    shapedOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedOutside
    shapedHash := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedHash
    shapedInput := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedInput
    qHash := by dsimp only [HashPlan.reframe]; simpa only [HashPlan.changed, h5] using p.qHash
    pOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pOutside
    exponentOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.exponentOutside
    pExponent := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pExponent
    frameArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.frameArithmetic
    hashArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.hashArithmetic }

def PPrimalityPlan.reframe (p : PPrimalityPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.construct.hash.W 1) (h3 : W 3 = p.construct.hash.W 3)
    (h4 : W 4 = p.construct.hash.W 4) (h5 : W 5 = p.construct.hash.W 5)
    (h13 : W 13 = p.construct.hash.W 13) (h15 : W 15 = p.construct.hash.W 15)
    (h2 : W 2 = BitVec.ofNat 64 offset) (h0 : W 0 = off (W 5) shaped)
    (hcarry : offset + p.construct.hash.count < 2 ^ 32) : PPrimalityPlan :=
  { p with
    construct := p.construct.reframe W offset h1 h3 h4 h5 h2 h0 hcarry
    tapePtr := h13.trans p.tapePtr
    tapeLength := h15.trans p.tapeLength
    bufferSeparate := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferSeparate
    bufferOutside := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferOutside
    tapeBuffer := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeBuffer
    framePrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.framePrime
    hashPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.hashPrime
    pPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.pPrime
    exponentPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.exponentPrime
    arenaBound := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaBound
    tapeArena := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeArena
    arenaFrame := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaFrame
    arenaStack := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaStack
    tapeConstruct := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [PConstructPlan.changed, HashPlan.changed, h5] using p.tapeConstruct }

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def attemptWords (W : Nat → BitVec 64) (offset : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (off (W 5) shaped)) 2 (BitVec.ofNat 64 offset)) 27 (W 3)

theorem attemptWords_slot (W : Nat → BitVec 64) (offset : Nat) {k : Nat} (hk : k ∈ searchSlots) :
    attemptWords W offset k = W k := by
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [attemptWords, upd]

def SearchMemory.attemptPlan {p : SearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p W s) (offset : Nat) (hc : offset + p.attempt.construct.hash.count < 2 ^ 32) : PPrimalityPlan :=
  p.attempt.reframe (attemptWords W offset) offset
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 1 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 3 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 4 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 5 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 13 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 15 (by simp [searchSlots])))
    (by simp [attemptWords, upd]) (by simp [attemptWords, upd]) hc

theorem SearchMemory.entry {p : SearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p W s) (offset : Nat) (hc : offset + p.attempt.construct.hash.count < 2 ^ 32)
    (H : Spec.Mgf1.Hash) : AttemptEntry (h.attemptPlan offset hc).construct H W s := by
  have h5 := h.slots 5 (by simp [searchSlots])
  have h3 := h.slots 3 (by simp [searchSlots])
  have h28 := h.slots 28 (by simp [searchSlots])
  dsimp only [SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
  refine ⟨h.layout, h.rep, rfl, ?_, h.seedRead, h.wrappedWrite, h.hashWrite, h.seed, ?_, h.scratch,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply h.label.congr rfl rfl
    · simp only [attemptWords, upd, ite_true]
      rw [h3, p.attempt.construct.hash.wrapped_slot, h.label.hl]
    · simpa [attemptWords, upd] using h28
  · exact p.seedSeparate _ (by simp [searchWrites])
  · simpa only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 27 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5] using h.qSource
  · simpa only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 27 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5] using
      p.qSeparate _ (by simp [searchWrites])
  · simpa [attemptWords, upd, h5] using h.shapedWrite
  · simpa [attemptWords, upd, h5] using h.pWrite
  · simpa [attemptWords, upd, h5] using h.exponentWrite

end VG.Proof.Dsa.X86_64.Generation
