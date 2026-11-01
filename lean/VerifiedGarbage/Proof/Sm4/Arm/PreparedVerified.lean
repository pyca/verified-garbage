module

public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Init.Data.BitVec.Basic
meta import Init.Data.BitVec.Basic
public import Init.Data.Vector.Basic
meta import Init.Data.Vector.Basic
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
meta import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Proof.Sm4.Arm.Prologue
meta import VerifiedGarbage.Proof.Sm4.Arm.Prologue
public import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared

/-! # SM4 prepared-key helpers on ARMv7 meet their contracts -/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (specDirArm)
open VG.Proof.Sm4.Prepared (Holds Keeps)

theorem prepared_size_eq : layout.size = 4 * slots := rfl

/-- Restrict the working space to the portion the helper uses. -/
abbrev prepNarrow (s : State) (b : BitVec 32) : State := s.withRegions s.rd [⟨State.addr b, 4 * slots⟩]

theorem prep_widen {c : Prog isa} {s s' : State} {b : BitVec 32} {len : Nat} {t : List Leak}
    (hw : s.wr = [⟨State.addr b, len⟩]) (hl : 4 * slots ≤ len)
    (he : Exec isa c (prepNarrow s b) t s') : Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have hc : Covers [⟨State.addr b, 4 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr b, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by change 0 + 4 * slots ≤ len; omega⟩
  have h := Exec.widen he (Covers.append (Covers.refl _) hc) hc
  change Exec isa c s t (s'.withRegions s.rd s.wr) at h
  exact h

theorem prepared_abi {s s' : State} (h : ∀ i < 9, s'.gpr (sreg i) = s.gpr (sreg i))
    (hsp : s'.sp = s.sp) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, hsp⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by omega)
  · exact h 1 (by omega)
  · exact h 2 (by omega)
  · exact h 3 (by omega)
  · exact h 4 (by omega)
  · exact h 5 (by omega)
  · exact h 6 (by omega)
  · exact h 7 (by omega)
  · exact h 8 (by omega)

theorem prepared_keeps_outside {m m' : Mem} {b : BitVec 32} {len : Nat}
    (hf : Frame [⟨State.addr b, 4 * slots⟩] m m') (fit : b.toNat + len * 8 ≤ 2 ^ 32)
    {i : Nat} (hi : i < len * 8) (hout : 4 * slots ≤ i) :
    m' (State.addr b + BitVec.ofNat 64 i) = m (State.addr b + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hc
  rw [Mem.sub_ofNat_toNat _ (by omega)] at hc
  omega

def prepArm : Contract isa where
  pre s :=
    s.rd = [⟨State.addr (s.gpr .r0), 128⟩] ∧
    s.wr = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 8⟩] ∧
    Region.Disjoint ⟨State.addr (s.gpr .r0), 128⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 8⟩ ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ≤ 1 ∧ layout.size ≤ 8 * (s.gpr .r3).toNat
  post s s' :=
    Holds layout s'.mem (State.addr (s.gpr .r2)) (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0)))
      (Proof.Sm4.directionOf (s.gpr .r1).toNat) ∧
    Keeps (State.addr (s.gpr .r2)) (s.gpr .r3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem prepared_prep_correct (s : State) (hs : prepArm.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepArm.post s s' := by
  obtain ⟨rd, wr, sep, fitK, fitW, -, hsz⟩ := hs
  rw [prepared_size_eq] at hsz
  have hl : 4 * slots ≤ (s.gpr .r3).toNat * 8 := by omega
  have hw : ScrIn (prepNarrow s (s.gpr .r2)).wr (s.gpr .r2) := ⟨by simp, by omega⟩
  obtain ⟨t, s', he, hg, -, -, hsp, hf, hwords⟩ := prepareBody_wp hw rfl rfl
    (by simp [prepNarrow, rd]) fitK (sep.sub_right (Region.sub_prefix hl))
  have he' := prep_widen wr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', prepared_abi hg hsp, ?_, fun i hi hout => ?_⟩
  · apply holds_of_words hw.fit
    rw [ofSpecDir_directionOf]
    exact hwords
  · apply prepared_keeps_outside hf fitW (by omega)
    have h := hout (0, 4 * slots) (by simp [layout])
    dsimp only at h
    omega

theorem prepared_prep_ct : ConstantTime isa prepArm.pre prepArm.pub prepareKeys :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      rcases hp with ⟨-, h0, h1, h2, h3⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) (by taint_decide)

def preparedPrepSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r2 => 0x2000 | .r3 => 182 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1456⟩]

theorem prepare_verified : Verified Arm.target prepareKeys (Proof.Sm4.Prepared.prepareContract layout Arm.abi) :=
  Verified.of_correct prepared_prep_correct prepared_prep_ct (by
    sig_implies [Proof.Sm4.Prepared.prepareContract, Proof.Sm4.Prepared.prepareSig, prepArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, prepared_size_eq, slots] [preparedPrepSat]
      using preparedPrepSat)

def cryptArm : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩] ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧ layout.size ≤ 8 * (s.gpr .r1).toNat ∧
    ∃ k d, Holds layout s.mem (State.addr (s.gpr .r0)) k d
  post s s' :=
    (∀ k d, Holds layout s.mem (State.addr (s.gpr .r0)) k d →
      Spec.Sm4.blocksAt s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
    Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

theorem prepared_blocks_of (B : Addr) {m m' : Mem} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : ∀ j < 8, Spec.Sm4.blockAt m' (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
      Proof.Sm4.blockFn k d (Spec.Sm4.blockAt m (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)))) :
    Spec.Sm4.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb k d (Spec.Sm4.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

theorem prepared_crypt_correct (s : State) (hs : cryptArm.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptArm.post s s' := by
  obtain ⟨-, wr, fitW, hsz, k₀, d₀, hH⟩ := hs
  rw [prepared_size_eq] at hsz
  have hl : 4 * slots ≤ (s.gpr .r1).toNat * 8 := by omega
  have hw : ScrIn (prepNarrow s (s.gpr .r0)).wr (s.gpr .r0) := ⟨by simp, by omega⟩
  have hwords := words_of_holds hw.fit hH
  obtain ⟨t, s', he, hg, -, -, hsp, hf, hR, -⟩ :=
    cryptBody_wp hw rfl (readyAt_of_words hwords)
  have he' := prep_widen wr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', prepared_abi hg hsp, fun k d h => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, hb₂⟩ :=
      cryptBody_wp hw rfl (readyAt_of_words (words_of_holds hw.fit h))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    apply prepared_blocks_of
    intro j hj
    have hb := hb₂ j hj
    rw [specDirArm_ofSpecDir] at hb
    exact hb
  · by_cases hi' : i < 4 * slots
    · have hLo := hout (0, 4 * tableSlot) (by simp [layout])
      have hHi := hout (4 * savedSlot, 4 * (slots - savedSlot)) (by simp [layout])
      dsimp only at hLo hHi
      have htable : 384 ≤ i ∧ i < 1408 := by
        rw [slots_eq] at hi'
        rw [tableSlot_eq] at hLo; rw [savedSlot_eq, slots_eq] at hHi
        omega
      have hH' := holds_of_words hw.fit (words_of_readyAt hR)
      have a := hH (384, 1024) (by rw [layout_table]; simp) (i - 384) (by omega)
      have a' := hH' (384, 1024) (by rw [layout_table]; simp) (i - 384) (by omega)
      dsimp only at a a'
      rw [show 384 + (i - 384) = i by omega] at a a'
      exact a'.trans a.symm
    · exact prepared_keeps_outside hf fitW (by omega) (by omega)

theorem prepared_crypt_ct : ConstantTime isa cryptArm.pre cryptArm.pub cryptPrepared :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      rcases hp with ⟨-, h0, h1⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption) (by taint_decide)

def preparedZeroSchedule : Spec.Sm4.Schedule := Vector.replicate 32 0

def preparedCryptSatMem : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2000 + 1456 then
    layout.encode preparedZeroSchedule .encrypt (a.toNat - 0x2000) else 0

theorem preparedCryptSat_holds : Holds layout preparedCryptSatMem 0x2000 preparedZeroSchedule .encrypt := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  have ht : ((0x2000 : Addr) + BitVec.ofNat 64 (384 + i)).toNat = 0x2000 + (384 + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x2000 : Addr).toNat = 0x2000 from rfl]; omega
  have hc : 0x2000 ≤ 0x2000 + (384 + i) ∧ 0x2000 + (384 + i) < 0x2000 + 1456 := ⟨by omega, by omega⟩
  simp only [preparedCryptSatMem, ht, hc, and_self, ↓reduceIte]
  rw [show 0x2000 + (384 + i) - 0x2000 = 384 + i by omega]

def preparedCryptSat : State where
  gpr r := match r with | .r0 => 0x2000 | .r1 => 182 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := preparedCryptSatMem
  rd := []
  wr := [⟨0x2000, 1456⟩]

theorem prepared_crypt_implies : cryptArm.Implies (Proof.Sm4.Prepared.cryptContract layout Arm.abi) where
  pre := by
    sig_implies_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  post := by
    sig_implies_post [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  pub := by
    sig_implies_pub [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, cryptArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  sat := by
    refine ⟨preparedCryptSat, ?_⟩
    sig_pre [Proof.Sm4.Prepared.cryptContract, Proof.Sm4.Prepared.cryptSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, State.addr]
    sig_and_intros
    all_goals first
      | decide
      | exact ⟨_, _, preparedCryptSat_holds⟩
      | (rw [prepared_size_eq, slots_eq]; decide)

theorem crypt_verified : Verified Arm.target cryptPrepared (Proof.Sm4.Prepared.cryptContract layout Arm.abi) :=
  Verified.of_correct prepared_crypt_correct prepared_crypt_ct prepared_crypt_implies

end VG.Proof.Sm4.Arm
