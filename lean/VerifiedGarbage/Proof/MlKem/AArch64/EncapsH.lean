module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.EncapsFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.EncapsHSat
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# ML-KEM on AArch64: `vg_mlkem768_encaps_h` and `vg_mlkem1024_encaps_h`

`encaps_h` is `encaps` after `hArgs`, which moves its arguments after `ek` to
`encaps`'s registers and ignores `h`: the contract lets it, since `h` is
`H(ek)`, which `encaps` computes. So its proofs are `encaps`'s, of the state
after the moves (`shiftH`): `prefix_correct` and `prefix_ct` put a block that
leaks nothing before a correctness proof and a constant-time proof, of any
contract `k` of the state the block leaves (`afterH k`); `encaps_h`'s
contract implies `afterH` of `encaps`'s internal contract (`impliesH`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.EncapsH

open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! ## A block before a proof -/

section
variable {M : ISA} {b : List M.Instr} {c : Prog M} {f : M.State → M.State}

theorem prefix_exec (hb : ∀ s, execBlock M b s = some (f s, [])) {s : M.State} {t : List Leak} {s' : M.State}
    (h : Exec M c (f s) t s') : Exec M (.seq (.block b) c) s t s' := by
  have e := Exec.seq (Exec.block (hb s)) h
  rwa [List.nil_append] at e

theorem prefix_ct (hb : ∀ s, execBlock M b s = some (f s, [])) {P : M.State → Prop} {Pub : M.State → M.State → Prop}
    (hct : ConstantTime M P Pub c) :
    ConstantTime M (fun s => P (f s)) (fun s t => Pub (f s) (f t)) (.seq (.block b) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      rw [Exec.block_iff, hb] at a₁ a₂
      cases a₁; cases a₂
      rw [List.nil_append, List.nil_append]
      exact hct _ _ _ _ _ _ h₁ h₂ hp b₁ b₂

end

/-- The contract `k` of the state after the block whose result `f` gives. -/
def afterH {M : ISA} (f : M.State → M.State) (k : Contract M) : Contract M where
  pre s := k.pre (f s)
  post s s' := k.post (f s) s'
  pub s t := k.pub (f s) (f t)

/-! ## The moves -/

/-- The state after `hArgs`: `x2`–`x5` in `x1`–`x4`. -/
def shiftH (s : State) : State :=
  { s with gpr := fun r => match r with
    | .x1 => s.gpr .x2 | .x2 => s.gpr .x3 | .x3 => s.gpr .x4 | .x4 => s.gpr .x5 | r => s.gpr r }

theorem hArgs_run (s : State) : execBlock isa hArgs s = some (shiftH s, []) := by
  simp [hArgs, mov, execBlock, isa, exec_addImm_x, addrs, State.write, State.read, shiftH]
  funext r
  cases r <;> rfl

theorem shiftH_abi {s s' : State} (h : abiPreserved (shiftH s) s') : abiPreserved s s' := by
  obtain ⟨g, sp, v⟩ := h
  refine ⟨fun r hr => (g r hr).trans ?_, sp, v⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `k`'s correctness, from the entry state of `encaps_h`. -/
theorem correctH {c : Prog isa} {k : Contract isa}
    (hc : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s') :
    ∀ s, (afterH shiftH k).pre s →
      ∃ t s', Exec isa (.seq (.block hArgs) c) s t s' ∧ abiPreserved s s' ∧ (afterH shiftH k).post s s' :=
  fun s h => by
    obtain ⟨t, s', e, a, p⟩ := hc _ h
    exact ⟨t, s', prefix_exec hArgs_run e, shiftH_abi a, p⟩

theorem ctH {c : Prog isa} {k : Contract isa} (hct : ConstantTime isa k.pre k.pub c) :
    ConstantTime isa (afterH shiftH k).pre (afterH shiftH k).pub (.seq (.block hArgs) c) := by
  show ConstantTime isa (fun s => k.pre (shiftH s)) (fun s t => k.pub (shiftH s) (shiftH t)) _
  exact @prefix_ct isa hArgs c shiftH hArgs_run _ _ hct


/-! ## ML-KEM-768, one Keccak state at a time -/

theorem pre768 {s : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 16).pre s) :
    (afterH shiftH (encapsAArch64 lay768)).pre s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
    AArch64.argRegs] at h
  obtain ⟨h0, rd, wr, d03, d04, d05, -, -, -, d23, d24, d25, d34, d35, d45, b0, -, b2, b3, b4, b5,
    -, -, -, -, -, -, -⟩ := h
  exact ⟨by show _ ∈ s.rd; rw [rd]; exact .head _, by show _ ∈ s.rd; rw [rd]; exact .tail _ (.tail _ (.head _)), wr, d03, d04, d05, d23, d24,
    d25, d34, d35, d45, h0, b0, b2, b3, b4, b5⟩

/-- A state satisfying `encaps_h`'s precondition, with `H(ek)` at `h` (`hMem`). -/
def satH (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x5000 | .x5 => 0x10000 | _ => 0
  sp := 0x100000
  mem := VG.Proof.MlKem.hMem ekLen
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x4000, 32⟩, ⟨0x5000, ctLen⟩, ⟨0x10000, scr⟩]

theorem implies768 : (afterH shiftH (encapsAArch64 lay768)).Implies (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 16) where
  pre _ h := pre768 h
  post s s' _ h := by
    sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hl, g0, -, g2, g3, g4, g5⟩ := h
    exact ⟨g0, g2, g3, g4, g5, hsp, hl⟩
  sat := by
    refine ⟨satH 1184 1088 32768, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
        AArch64.argRegs]
      sig_and_intros
      all_goals first
        | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
           decide +kernel)
        | exact VG.Proof.MlKem.hMem_h (n := 1184) (by decide)

theorem encapsH_verifiedWith {keccak : VG.Proof.Sha3.AArch64.Permutation} :
    Verified AArch64.target (encapsHWith keccak.callee) (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 16) :=
  Verified.of_correct (correctH (Encaps.encaps_correctWith (keccak := keccak)))
    (ctH (Encaps.ct KeyGen.wf768 Encaps.taints768)) implies768


/-! ## ML-KEM-768, the paired instances -/

open VG.Proof.MlKem.AArch64.Hybrid (encapsAArch64S entryContractS)
open VG.Proof.MlKem.AArch64.Optimized (constants)

theorem baseS768 {s : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 128).pre s) :
    (encapsAArch64S lay768).pre (shiftH s) := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
    AArch64.argRegs] at h
  obtain ⟨h0, rd, wr, d03, d04, d05, -, -, -, d23, d24, d25, d34, d35, d45, b0, -, b2, b3, b4, b5,
    -, -, -, -, -, -, -⟩ := h
  exact ⟨by show _ ∈ s.rd; rw [rd]; exact .head _, by show _ ∈ s.rd; rw [rd]; exact .tail _ (.tail _ (.head _)),
    wr, d03, d04, d05, d23, d24, d25, d34, d35, d45, h0, b0, b2, b3, b4, b5⟩


/-- `hMem n` below `0x2020`, and the tables (`tableMem`) above: memory satisfying the precondition of the
paired instances. -/
def tabMemH (n : Nat) : Mem := fun a =>
  if a.toNat < 0x2020 then VG.Proof.MlKem.hMem n a else Optimized.tableMem a

theorem tabMemH_low {n : Nat} : ∀ a : Addr, a.toNat < 0x2020 → tabMemH n a = VG.Proof.MlKem.hMem n a :=
  fun _ h => by simp only [tabMemH, h, ite_true]

theorem tab_high {b : Addr} (hb : 0x200000 ≤ b.toNat ∧ b.toNat ≤ 0x240000) {i j : Nat} (hi : i < 512)
    (hj : j < 8) : ¬ (b + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat < 0x2020 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem tabMemH_held (n : Nat) : Abi.constsHeld (tabMemH n) Optimized.tableSyms constants := by
  intro c hc i hi
  rw [← Optimized.tableMem_held c hc i hi]
  have hs : 0x200000 ≤ (Optimized.tableSyms c.1).toNat ∧ (Optimized.tableSyms c.1).toNat ≤ 0x240000 := by
    simp only [Optimized.tableSyms]
    split
    · decide
    split
    · decide
    split
    · decide
    split
    · decide
    · decide
  have hl : i < 512 := by
    simp only [constants, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Rej8.tableWords_length, Ntt16.Readonly.gamma_length, Ntt16.Readonly.forward_length,
        NttR.tabWordsI_length, NttR.tabWords_length] at hi <;> omega
  refine Mem.readW_congr fun j hj => ?_
  simp only [tabMemH, tab_high hs hl (by omega), ite_false]

/-- The regions `satHT` reads: `satH`'s and the tables. -/
def rdT (ekLen : Nat) : List Region := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩] ++
  Abi.constRegions Optimized.tableSyms constants

/-- A state satisfying the precondition of the paired instances. -/
def satHT (ekLen ctLen scr : Nat) : State :=
  { satH ekLen ctLen scr with mem := tabMemH ekLen, syms := Optimized.tableSyms, rd := rdT ekLen }

theorem strip_satHT (ekLen ctLen scr : Nat) : stripConsts constants (satHT ekLen ctLen scr) =
    { (satH ekLen ctLen scr) with mem := tabMemH ekLen, syms := Optimized.tableSyms } := by
  have hl : (Abi.constRegions Optimized.tableSyms constants).length = constants.length := by
    simp only [Abi.constRegions, List.length_map]
  simp only [stripConsts, satHT, rdT, satH, State.withRegions, List.length_append, hl, Nat.add_sub_cancel,
    List.take_left]

theorem impliesP768 : (afterH shiftH (entryContractS (encapsAArch64S lay768))).Implies
    (Proof.MlKem.Scrubbed.encapsHBodyContract (AArch64.abi.withConsts constants) 128) where
  pre s h := by
    unfold Proof.MlKem.Scrubbed.encapsHBodyContract constants at h
    have hp := pre_consts.mp h
    exact ⟨baseS768 hp.1, hp.2⟩
  post s t h hp := by
    unfold Proof.MlKem.Scrubbed.encapsHBodyContract constants at h ⊢
    show (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 128).post (stripConsts constants s) t
    sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs]
    exact hp
  pub s₁ s₂ h₁ h₂ hp := by
    unfold Proof.MlKem.Scrubbed.encapsHBodyContract constants at h₁ h₂ hp
    have hpp := pub_consts.mp hp
    have hb := hpp.1
    sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs] at hb
    obtain ⟨hsp, hl, g0, -, g2, g3, g4, g5⟩ := hb
    exact ⟨⟨g0, g2, g3, g4, g5, hsp, hl⟩, hpp.2⟩
  sat := by
    refine ⟨satHT 1184 1088 32768, ?_⟩
    unfold Proof.MlKem.Scrubbed.encapsHBodyContract constants
    apply pre_consts.mpr
    constructor
    · change (Proof.MlKem.Scrubbed.encapsHBodyContract AArch64.abi 128).pre (stripConsts constants (satHT 1184 1088 32768))
      rw [strip_satHT]
      sig_pre [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi, AArch64.argRegs]
      and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h_of (n := 1184) (by decide) tabMemH_low
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
    · change ConstsOk constants 128 (satHT 1184 1088 32768)
      refine ⟨?_, tabMemH_held 1184, ?_, ?_⟩
      · rfl
      · intro r hr
        rw [Optimized.constants_regions] at hr
        rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
        all_goals first
          | contradiction
          | (refine ⟨by decide, ?_, ?_⟩
             · intro q hq
               change q ∈ (satH 1184 1088 32768).wr at hq
               simp only [satH, List.mem_cons, List.not_mem_nil, or_false] at hq
               rcases hq with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
             · intro q hq
               change q ∈ [below (0x100000 : Addr) 128] at hq
               rw [List.mem_singleton.mp hq]
               exact Region.disjoint_of_sep (by decide))
      · intro r hr
        rw [Optimized.constants_regions] at hr
        rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
        all_goals first | contradiction | decide

theorem encapsHP768_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target
      (Impl.MlKem.AArch64.Kem16P.encapsH (FixedHash.fixedHash v.callee) (FixedHash.prfW v.callee) lay768)
      (Proof.MlKem.Scrubbed.encapsHBodyContract (AArch64.abi.withConsts constants) 128) :=
  Verified.of_correct (correctH (Kem16P.encapsP768_correct v)) (ctH (Kem16P.encapsP768_ct v)) impliesP768


/-! ## ML-KEM-1024, one Keccak state at a time -/

theorem pre1024 {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 16).pre s) :
    (afterH shiftH (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
    AArch64.argRegs] at h
  obtain ⟨h0, rd, wr, d03, d04, d05, -, -, -, d23, d24, d25, d34, d35, d45, b0, -, b2, b3, b4, b5,
    -, -, -, -, -, -, -⟩ := h
  exact ⟨by show _ ∈ s.rd; rw [rd]; exact .head _, by show _ ∈ s.rd; rw [rd]; exact .tail _ (.tail _ (.head _)), wr, d03, d04, d05, d23, d24,
    d25, d34, d35, d45, h0, b0, b2, b3, b4, b5⟩

theorem implies1024 : (afterH shiftH (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).Implies (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 16) where
  pre _ h := pre1024 h
  post s s' _ h := by
    sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hl, g0, -, g2, g3, g4, g5⟩ := h
    exact ⟨g0, g2, g3, g4, g5, hsp, hl⟩
  sat := by
    refine ⟨satH 1568 1568 49152, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
        AArch64.argRegs]
      sig_and_intros
      all_goals first
        | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
           decide +kernel)
        | exact VG.Proof.MlKem.hMem_h (n := 1568) (by decide)

theorem encapsH1024_verifiedWith {keccak : VG.Proof.Sha3.AArch64.Permutation} :
    Verified AArch64.target (Impl.MlKem1024.AArch64.encapsHWith keccak.callee) (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 16) :=
  Verified.of_correct (correctH (VG.Proof.MlKem1024.AArch64.Encaps.encaps_correctWith (keccak := keccak)))
    (ctH (Encaps.ct VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 VG.Proof.MlKem1024.AArch64.Encaps.taints1024)) implies1024



/-! ## ML-KEM-1024, the paired instances -/

theorem baseS1024 {s : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 128).pre s) :
    (encapsAArch64S Impl.MlKem1024.AArch64.lay1024).pre (shiftH s) := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
    AArch64.argRegs] at h
  obtain ⟨h0, rd, wr, d03, d04, d05, -, -, -, d23, d24, d25, d34, d35, d45, b0, -, b2, b3, b4, b5,
    -, -, -, -, -, -, -⟩ := h
  exact ⟨by show _ ∈ s.rd; rw [rd]; exact .head _, by show _ ∈ s.rd; rw [rd]; exact .tail _ (.tail _ (.head _)),
    wr, d03, d04, d05, d23, d24, d25, d34, d35, d45, h0, b0, b2, b3, b4, b5⟩


theorem impliesP1024 : (afterH shiftH (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024))).Implies
    (Proof.MlKem.Scrubbed.encapsH1024BodyContract (AArch64.abi.withConsts constants) 128) where
  pre s h := by
    unfold Proof.MlKem.Scrubbed.encapsH1024BodyContract constants at h
    have hp := pre_consts.mp h
    exact ⟨baseS1024 hp.1, hp.2⟩
  post s t h hp := by
    unfold Proof.MlKem.Scrubbed.encapsH1024BodyContract constants at h ⊢
    show (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 128).post (stripConsts constants s) t
    sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs]
    exact hp
  pub s₁ s₂ h₁ h₂ hp := by
    unfold Proof.MlKem.Scrubbed.encapsH1024BodyContract constants at h₁ h₂ hp
    have hpp := pub_consts.mp hp
    have hb := hpp.1
    sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs] at hb
    obtain ⟨hsp, hl, g0, -, g2, g3, g4, g5⟩ := hb
    exact ⟨⟨g0, g2, g3, g4, g5, hsp, hl⟩, hpp.2⟩
  sat := by
    refine ⟨satHT 1568 1568 49152, ?_⟩
    unfold Proof.MlKem.Scrubbed.encapsH1024BodyContract constants
    apply pre_consts.mpr
    constructor
    · change (Proof.MlKem.Scrubbed.encapsH1024BodyContract AArch64.abi 128).pre (stripConsts constants (satHT 1568 1568 49152))
      rw [strip_satHT]
      sig_pre [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi, AArch64.argRegs]
      and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h_of (n := 1568) (by decide) tabMemH_low
        | rfl
        | decide
        | exact Region.disjoint_of_sep (by decide)
    · change ConstsOk constants 128 (satHT 1568 1568 49152)
      refine ⟨?_, tabMemH_held 1568, ?_, ?_⟩
      · rfl
      · intro r hr
        rw [Optimized.constants_regions] at hr
        rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
        all_goals first
          | contradiction
          | (refine ⟨by decide, ?_, ?_⟩
             · intro q hq
               change q ∈ (satH 1568 1568 49152).wr at hq
               simp only [satH, List.mem_cons, List.not_mem_nil, or_false] at hq
               rcases hq with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
             · intro q hq
               change q ∈ [below (0x100000 : Addr) 128] at hq
               rw [List.mem_singleton.mp hq]
               exact Region.disjoint_of_sep (by decide))
      · intro r hr
        rw [Optimized.constants_regions] at hr
        rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
        all_goals first | contradiction | decide

theorem encapsHP1024_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target
      (Impl.MlKem.AArch64.Kem16P.encapsH (FixedHash.fixedHash v.callee) (FixedHash.prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
      (Proof.MlKem.Scrubbed.encapsH1024BodyContract (AArch64.abi.withConsts constants) 128) :=
  Verified.of_correct (correctH (Kem16P.encapsP1024_correct v)) (ctH (Kem16P.encapsP1024_ct v)) impliesP1024

end VG.Proof.MlKem.AArch64.EncapsH
