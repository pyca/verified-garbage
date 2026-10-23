module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.CT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.AbsorbCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Finish
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.CmacTripleDes.Stream

/-!
# Streaming TDEA-CMAC on PPC64LE: `Verified`

The contracts the proofs are written against (`initPPC`, `absorbPPC`,
`finishPPC`), with the working space as the last argument, which the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`) imply, with no stack: the
functions and the functions they call keep the return address in the link
register.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- `vg_cmac_triple_des_stream_init(state = r3, key = r4, key_len = r5, scratch = r6)`. -/
def initPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let key : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let scr : Region := ⟨s.gpr .r6, 640⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .r5).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) (Spec.TripleDes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) []
  pub := pub4

/-- `vg_cmac_triple_des_absorb(state = r3, count = r4, data = r5, len = r6, scratch = r7)`. -/
def absorbPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scr : Region := ⟨s.gpr .r7, 688⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 688 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .r3) key msg →
      s.gpr .r4 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .r6).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .r3) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub := pub5

/-- `vg_cmac_triple_des_finish(state = r3, count = r4, out = r5, scratch = r6)`. -/
def finishPPC : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 416⟩
    let out : Region := ⟨s.gpr .r5, 8⟩
    let scr : Region := ⟨s.gpr .r6, 640⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r3).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .r3) key msg →
      s.gpr .r4 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .r5) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub := pub4

theorem pub4_iff (s₁ s₂ : State) : pub4 s₁ s₂ ↔ s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 := by
  simp [Proof.TripleDes.PPC64LE.PublicRegs]

theorem pub5_iff (s₁ s₂ : State) : pub5 s₁ s₂ ↔ s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 := by
  simp [Proof.TripleDes.PPC64LE.PublicRegs]

/-- `count` is the message's length. -/
theorem count_eq {c : BitVec 64} {n : Nat} (h : c = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : c.toNat = n := by
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## Correctness -/

theorem init_correct (s : State) (hs : initPPC.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initPPC.post s s' := by
  obtain ⟨hrd, hwr, dSK, dSW, dKW, fS, -, fW, hv⟩ := hs
  obtain ⟨t, s', he, h1, h2, h3⟩ := init_wp s ⟨hrd, hwr, dSK.symm, dKW, dSW, hv, fS, fW⟩
  exact ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, h3⟩

theorem absorb_correct (s : State) (hs : absorbPPC.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbPPC.post s s' := by
  obtain ⟨hrd, hwr, dSD, dSW, dDW, fS, fD, fW⟩ := hs
  obtain ⟨t, s', he, h1, h2, h3⟩ := absorb_wp s ⟨hrd, hwr, dSD.symm, dDW, dSW, fS, fD, fW⟩
  exact ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, fun key msg hr hc hl => h3 key msg hr (count_eq hc (by omega)).symm⟩

theorem finish_correct (s : State) (hs : finishPPC.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishPPC.post s s' := by
  obtain ⟨hwr, dSO, dSW, dOW, fS, fO, fW⟩ := hs.2
  obtain ⟨t, s', he, h1, h2, h3⟩ := finish_wp s ⟨hwr, dSO, dSW, dOW, fS, fO, fW⟩
  refine ⟨t, s', he, ⟨h1, Exec.sp he, h2⟩, fun key msg hr hc hl => ?_⟩
  rw [h3, count_eq hc hl, finish_spec hr]

/-! ## The contracts -/

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 16 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initPPC.Implies (streamInitScratchContract PPC64LE.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initPPC, pub4_iff, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbPPC.Implies (absorbScratchContract PPC64LE.abi 0) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbPPC, pub5_iff,
    PPC64LE.abi, PPC64LE.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishPPC.Implies (finishScratchContract PPC64LE.abi 0) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishPPC, pub4_iff,
    PPC64LE.abi, PPC64LE.argRegs] [finishSat] using finishSat

theorem init_verified : Verified PPC64LE.target streamInit (streamInitScratchContract PPC64LE.abi 0) :=
  Verified.of_correct init_correct (init_ct _) init_implies

theorem absorb_verified : Verified PPC64LE.target absorb (absorbScratchContract PPC64LE.abi 0) :=
  Verified.of_correct absorb_correct (absorb_ct _) absorb_implies

theorem finish_verified : Verified PPC64LE.target finish (finishScratchContract PPC64LE.abi 0) :=
  Verified.of_correct finish_correct (finish_ct _) finish_implies

end VG.Proof.CmacTripleDes.Stream.PPC64LE
