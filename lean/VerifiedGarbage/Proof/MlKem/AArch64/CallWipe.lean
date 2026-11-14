module

public import VerifiedGarbage.Impl.MlKem.AArch64.Wipe
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipeConsts
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.Scrubbed
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
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Final
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.DecapsFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ConstsSat
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig
public meta import Lean.Elab.Tactic.ElabTerm

/-! ### `MlKem.AArch64.EncapsH`, which only this module used -/

section

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
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hb, hi, hj]

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
        NttR.tabWordsI_length, NttR.tabWords_length] at hi <;> omega_using [hi]
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

end

end


/-!
# ML-KEM on AArch64: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/AArch64.lean`) of its code, which zeroes all of
`scratch` with `vg_zeroize` once that code returns, and is verified against
the same contract with 32 more bytes of stack and `scratch` left scrubbed
(`*_scrubbed`, the contracts of `Proof/MlKem/Scrubbed.lean`), since every
byte of it is zero (`Scrubbed.keyGen_wiped`, …): `Verified.callWipe'` for
the instances over the sponge functions, under `abi`, and
`Verified.callWipeC'` for the paired instances, under
`abi.withConsts constants`. `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Wipe

open VG VG.AArch64
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prfW hole)

/-! ## `callWipe` of `vg_zeroize` -/

/-- Under the calling convention `A`, `callWipe` of code verified against a
contract, with `vg_zeroize`, is verified against the contract whose
postcondition `post'` follows from the code's and the zeroed bytes, with 32
more bytes of stack, given `Verified.callWipe'`'s hypotheses. -/
def CallWipeOk (A : Abi isa) : Prop :=
  ∀ {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {name : String} {body : Prog isa} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i : Nat},
    Verified target body (sig.contract A pre post wa stack leak) →
    (sig.words A.ptrBits).length ≤ 8 → Sig.noLists sig.params = true →
    sig.params = ps₁ ++ (nm, .array true e k) :: ps₂ → i = (ps₁.flatMap fun p => p.2.words 64).length →
    n ≤ k * e.size → n < 2 ^ 16 → 16 * body.aarch64Depth ≤ stack →
    (∀ vs m₁ m₂, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) pre vs m₁ → Curry.apply (sig.words A.ptrBits) pre vs m₂) →
    (∀ vs m₁ m₂ m' x, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words A.ptrBits) post vs m₂ m' x) →
    (∀ vs m m₁ m₂ x, vs.length = (sig.words A.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ x) →
    (∀ vs m m' x, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) post vs m m' x →
      Spec.Zeroize.bytesAt m' (vs.getD i 0) n = Spec.Zeroize.zeros n →
        Curry.apply (sig.words A.ptrBits) post' vs m m' x) →
    (∃ s, (sig.contract A pre post' wa (stack + 32) leak).pre s) →
    Sig.LeakLocal A.ptrBits sig leak →
    Verified target (Impl.CallWipe.AArch64.callWipe (argRegs.getD i .x0) n name body "vg_zeroize"
      Impl.Zeroize.AArch64.zeroizeWide) (sig.contract A pre post' wa (stack + 32) leak)

theorem zeroize_depth : 16 * Impl.Zeroize.AArch64.zeroizeWide.aarch64Depth ≤ 0 := by
  rw [Proof.Sha3.AArch64.fdepth_of_noFrames (by decide)]

/-- `Verified.callWipe'`, under `abi`. -/
theorem callWipeOk_abi : CallWipeOk abi :=
  fun h hk hl hps hi hn hn16 hd hpre hpost hpostOut hwiped hsat hleak =>
    Verified.callWipe' h Proof.Zeroize.AArch64.wideVerified hk hl hps hi hn hn16 hd zeroize_depth
      (Nat.zero_le _) hpre hpost hpostOut hwiped hsat hleak

/-- `Verified.callWipeC'`, under `abi.withConsts`. -/
theorem callWipeOk_consts {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))} :
    CallWipeOk (abi.withConsts (c₀ :: cs)) :=
  fun h hk hl hps hi hn hn16 hd hpre hpost hpostOut hwiped hsat hleak =>
    Verified.callWipeC' h Proof.Zeroize.AArch64.wideVerified hk hl hps hi hn hn16 hd zeroize_depth
      (Nat.zero_le _) hpre hpost hpostOut hwiped hsat hleak

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hk, hn, hi]))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega_using [hn])
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega_using [hij, hj]) hj hij hw

/-! ## The functions, under a calling convention for which `callWipe` is verified -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen sfx body) (Scrubbed.keyGenContract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH sfx body) (Scrubbed.encapsHContract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps sfx body) (Scrubbed.encapsContract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps sfx body) (Scrubbed.decapsContract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen1024 sfx body) (Scrubbed.keyGen1024Contract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH1024 sfx body) (Scrubbed.encapsH1024Contract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps1024 sfx body) (Scrubbed.encaps1024Contract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {A : Abi isa} (hA : CallWipeOk A) (sfx : String) {body : Prog isa} {st : Nat}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract A st)) (hd : 16 * body.aarch64Depth ≤ st)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract A (st + 32)).pre s) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps1024 sfx body) (Scrubbed.decaps1024Contract A (st + 32)) :=
  hA (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) h (Nat.le_of_ble_eq_true rfl) (by decide) rfl rfl
    (by decide) (by decide) hd
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

/-! ## The stack the functions use -/

/-- Whether the calls and frames of `c` use at most `k` units of 16 bytes of stack. -/
def adLe (k : Nat) (c : Prog isa) : Bool := Nat.ble c.aarch64Depth k

theorem adLe_spec {k : Nat} {c : Prog isa} (h : adLe k c = true) : c.aarch64Depth ≤ k :=
  Nat.le_of_ble_eq_true h

theorem adLe_of_le {k : Nat} {c : Prog isa} (h : c.aarch64Depth ≤ k) : adLe k c = true :=
  Nat.ble_eq_true_of_le h

theorem adLe_block {k : Nat} (l : List Instr) : adLe k (.block l) = true := rfl

theorem adLe_seq {k : Nat} {a b : Prog isa} (ha : adLe k a = true) (hb : adLe k b = true) :
    adLe k (.seq a b) = true :=
  adLe_of_le (Nat.max_le.2 ⟨adLe_spec ha, adLe_spec hb⟩)

theorem adLe_ite {k : Nat} {f : Cond} {a b : Prog isa} (ha : adLe k a = true) (hb : adLe k b = true) :
    adLe k (.ite f a b) = true :=
  adLe_of_le (Nat.max_le.2 ⟨adLe_spec ha, adLe_spec hb⟩)

theorem adLe_loop {k : Nat} {f : Cond} {a : Prog isa} (ha : adLe k a = true) :
    adLe k (.loop a f) = true :=
  adLe_of_le (adLe_spec ha)

theorem adLe_call {k : Nat} {n : String} {a : Prog isa} (ha : adLe k a = true) :
    adLe k (.call n a) = true :=
  adLe_of_le (adLe_spec ha)

/-- The permutation of `v`, which has no frames. -/
theorem adLe_perm (v : Proof.Sha3.AArch64.Permutation) {k : Nat} : adLe k v.callee.code = true :=
  adLe_of_le (by rw [Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames]; exact Nat.zero_le _)

/-- A function of `v` with a frame of 16 bytes. -/
theorem adLe_one {c : Prog isa} (h : c.aarch64Depth = 1) {k : Nat} (hk : 1 ≤ k) : adLe k c = true :=
  adLe_of_le (by rw [h]; exact hk)

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`: the kernel evaluates only
code that does not call the implementation `v`. -/
elab "closed_in " v:ident : tactic => withMainContext do
  let e ← elabTerm v none
  if (← instantiateMVars (← getMainTarget)).containsFVar e.fvarId! then
    throwError "the goal mentions {e}"

open Lean Meta Elab Tactic in
/-- Puts the code `X` of a goal `adLe k X = true` in weak head normal form, if
that is a `block`, `seq`, `ite`, `loop` or `call`. -/
elab "code_whnf" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, rhs) := t.eq? | throwError "not an equation"
  let lhs := lhs.consumeMData
  let .app f x := lhs | throwError "not an application"
  let x' ← whnf x
  unless [``Code.block, ``Code.seq, ``Code.ite, ``Code.loop, ``Code.call].contains x'.getAppFn.constName do
    throwError "not a `block`, `seq`, `ite`, `loop` or `call`"
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq (.app f x') rhs)]

/-- That code calling the sponge functions of the Keccak implementation `v`
uses at most `k ≥ 1` units of stack (a goal `adLe k _ = true`): the kernel
evaluates its parts that do not call `v`. -/
macro "sponge_depth " v:ident : tactic =>
  `(tactic| repeat' (first
    | (closed_in $v; decide +kernel)
    | with_reducible exact adLe_one (Proof.Sha3.AArch64.Permutation.absorb_depth $v) (by decide)
    | with_reducible exact adLe_one (Proof.Sha3.AArch64.Permutation.pad_depth $v) (by decide)
    | with_reducible exact adLe_one (Proof.Sha3.AArch64.Permutation.squeeze_depth $v) (by decide)
    | with_reducible exact adLe_one (Proof.MlKem.AArch64.sampleNTTWith_fdepth $v) (by decide)
    | with_reducible exact adLe_perm $v
    | (code_whnf; with_reducible exact adLe_block _)
    | (code_whnf; with_reducible apply adLe_seq) | (code_whnf; with_reducible apply adLe_ite)
    | (code_whnf; with_reducible apply adLe_loop) | (code_whnf; with_reducible apply adLe_call)))

/-- At most one unit of stack: `16 * depth ≤ 16`. -/
theorem depth16 {c : Prog isa} (h : adLe 1 c = true) : 16 * c.aarch64Depth ≤ 16 := by
  have := adLe_spec h; omega_using [this]

/-- At most eight units of stack: `16 * depth ≤ 128`. -/
theorem depth128 {c : Prog isa} (h : c.aarch64Depth ≤ 8) : 16 * c.aarch64Depth ≤ 128 := by
  omega_using [h]

section
variable (v : Proof.Sha3.AArch64.Permutation)

/-! The instances over the sponge functions use at most 16 bytes of stack. -/

theorem keyGenS768_depth : 16 * (Impl.MlKem.AArch64.keyGenWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem encapsS768_depth : 16 * (Impl.MlKem.AArch64.encapsWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem encapsHS768_depth : 16 * (Impl.MlKem.AArch64.encapsHWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem decapsS768_depth : 16 * (Impl.MlKem.AArch64.decapsWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem keyGenS1024_depth : 16 * (Impl.MlKem1024.AArch64.keyGenWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem encapsS1024_depth : 16 * (Impl.MlKem1024.AArch64.encapsWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem encapsHS1024_depth : 16 * (Impl.MlKem1024.AArch64.encapsHWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

theorem decapsS1024_depth : 16 * (Impl.MlKem1024.AArch64.decapsWith v.callee).aarch64Depth ≤ 16 :=
  depth16 (by sponge_depth v)

/-! The paired instances use at most 128 bytes of stack: their code with the
permutation's calls erased (`hole`) has that depth, and the permutation no
frames. -/


theorem keyGenP768_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash hole) hole Impl.MlKem.AArch64.lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem encapsP768_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.encaps (fixedHash hole) (prfW hole) Impl.MlKem.AArch64.lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem encapsHP768_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash hole) (prfW hole) Impl.MlKem.AArch64.lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem decapsP768_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.decaps (fixedHash hole) (prfW hole) Impl.MlKem.AArch64.lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem keyGenP1024_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash hole) hole Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem encapsP1024_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.encaps (fixedHash hole) (prfW hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem encapsHP1024_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash hole) (prfW hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

theorem decapsP1024_depth :
    16 * (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 128 :=
  depth128 (Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.decaps (fixedHash hole) (prfW hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel))

end

/-! ## The states satisfying the preconditions, with the frame's 32 more bytes of stack -/

/-- The precondition of a contract under `abi`, built with `Sig.contract`, of
a concrete state (`sig_pre`). -/
macro "wipe_pre " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_pre [$ls,*]
   and_intros
   all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)))

/-- A state satisfying the precondition of a contract under `abi`, built with
`Sig.contract`. -/
macro "wipe_sat " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" " using " w:term : tactic => `(tactic|
  (refine ⟨$w, ?_⟩
   wipe_pre [$ls,*]))

/-- A region apart from each of the concrete regions `l`, by evaluation. -/
theorem disjoint_of_seps {t : Region} {l : List Region} (h : l.all (fun q => Region.sep t q) = true) :
    ∀ q ∈ l, t.Disjoint q :=
  fun q hq => Region.disjoint_of_sep (List.all_eq_true.mp h q hq)

/-- What `abi.withConsts constants` says of the tables, in a state whose
writable regions are `wr` and whose memory holds the tables by `h`, for 160
bytes of stack below `0x100000`. -/
macro "wipe_consts " wr:term " held " h:term : tactic => `(tactic|
  (refine ⟨?_, $h, ?_, ?_⟩
   · rfl
   · intro r hr
     rw [Optimized.constants_regions] at hr
     rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
     all_goals first
       | contradiction
       | (refine ⟨by decide, disjoint_of_seps (l := $wr) (by decide), ?_⟩
          intro q hq
          change q ∈ [below (0x100000 : Addr) 160] at hq
          rw [List.mem_singleton.mp hq]
          exact Region.disjoint_of_sep (by decide))
   · intro r hr
     rw [Optimized.constants_regions] at hr
     rcases hr with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | h⟩⟩⟩⟩
     all_goals first | contradiction | decide))

theorem keyGenS768_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem.AArch64.KeyGen.sat

theorem encapsS768_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem.AArch64.Encaps.sat

theorem decapsS768_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem.AArch64.Decaps.sat

theorem keyGenS1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem1024.AArch64.KeyGen.sat

theorem encapsS1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem1024.AArch64.Encaps.sat

theorem decapsS1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 48).pre s := by
  wipe_sat [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, AArch64.abi, AArch64.argRegs]
    using Proof.MlKem1024.AArch64.Decaps.sat

theorem encapsHS768_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 48).pre s := by
  refine ⟨Proof.MlKem.AArch64.EncapsH.satH 1184 1088 32768, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | exact VG.Proof.MlKem.hMem_h (n := 1184) (by decide)

theorem encapsHS1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 48).pre s := by
  refine ⟨Proof.MlKem.AArch64.EncapsH.satH 1568 1568 49152, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf,
      AArch64.abi, AArch64.argRegs]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | exact VG.Proof.MlKem.hMem_h (n := 1568) (by decide)

theorem keyGenP768_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem.AArch64.KeyGen.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.keyGenBodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.keyGenBodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem.AArch64.KeyGen.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem.keyGenSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem.AArch64.KeyGen.sat)
    wipe_consts (Proof.MlKem.AArch64.KeyGen.sat).wr held Optimized.tableMem_held

theorem encapsP768_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem.AArch64.Encaps.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.encapsBodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.encapsBodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem.AArch64.Encaps.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem.encapsSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem.AArch64.Encaps.sat)
    wipe_consts (Proof.MlKem.AArch64.Encaps.sat).wr held Optimized.tableMem_held

theorem decapsP768_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem.AArch64.Decaps.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.decapsBodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.decapsBodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem.AArch64.Decaps.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem.decapsSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem.AArch64.Decaps.sat)
    wipe_consts (Proof.MlKem.AArch64.Decaps.sat).wr held Optimized.tableMem_held

theorem keyGenP1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem1024.AArch64.KeyGen.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.keyGen1024BodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem1024.AArch64.KeyGen.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem1024.keyGenSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem1024.AArch64.KeyGen.sat)
    wipe_consts (Proof.MlKem1024.AArch64.KeyGen.sat).wr held Optimized.tableMem_held

theorem encapsP1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem1024.AArch64.Encaps.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.encaps1024BodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem1024.AArch64.Encaps.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem1024.encapsSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem1024.AArch64.Encaps.sat)
    wipe_consts (Proof.MlKem1024.AArch64.Encaps.sat).wr held Optimized.tableMem_held

theorem decapsP1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Optimized.addTables Proof.MlKem1024.AArch64.Decaps.sat, ?_⟩
  unfold Proof.MlKem.Scrubbed.decaps1024BodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 160).pre (stripConsts Optimized.constants (Optimized.addTables Proof.MlKem1024.AArch64.Decaps.sat))
    rw [Optimized.strip_addTables]
    wipe_pre [Spec.MlKem1024.decapsSig, abi, argRegs]
  · change ConstsOk Optimized.constants 160 (Optimized.addTables Proof.MlKem1024.AArch64.Decaps.sat)
    wipe_consts (Proof.MlKem1024.AArch64.Decaps.sat).wr held Optimized.tableMem_held

theorem encapsHP768_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Proof.MlKem.AArch64.EncapsH.satHT 1184 1088 32768, ?_⟩
  unfold Proof.MlKem.Scrubbed.encapsHBodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.encapsHBodyContract abi 160).pre
      (stripConsts Optimized.constants (Proof.MlKem.AArch64.EncapsH.satHT 1184 1088 32768))
    rw [Proof.MlKem.AArch64.EncapsH.strip_satHT]
    sig_pre [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi, AArch64.argRegs]
    and_intros
    all_goals first
      | exact VG.Proof.MlKem.hMem_h_of (n := 1184) (by decide) Proof.MlKem.AArch64.EncapsH.tabMemH_low
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk Optimized.constants 160 (Proof.MlKem.AArch64.EncapsH.satHT 1184 1088 32768)
    wipe_consts (Proof.MlKem.AArch64.EncapsH.satH 1184 1088 32768).wr held Proof.MlKem.AArch64.EncapsH.tabMemH_held 1184

theorem encapsHP1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract (abi.withConsts Optimized.constants) 160).pre s := by
  refine ⟨Proof.MlKem.AArch64.EncapsH.satHT 1568 1568 49152, ?_⟩
  unfold Proof.MlKem.Scrubbed.encapsH1024BodyContract Optimized.constants
  apply pre_consts.mpr
  constructor
  · change (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 160).pre
      (stripConsts Optimized.constants (Proof.MlKem.AArch64.EncapsH.satHT 1568 1568 49152))
    rw [Proof.MlKem.AArch64.EncapsH.strip_satHT]
    sig_pre [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, AArch64.abi, AArch64.argRegs]
    and_intros
    all_goals first
      | exact VG.Proof.MlKem.hMem_h_of (n := 1568) (by decide) Proof.MlKem.AArch64.EncapsH.tabMemH_low
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
  · change ConstsOk Optimized.constants 160 (Proof.MlKem.AArch64.EncapsH.satHT 1568 1568 49152)
    wipe_consts (Proof.MlKem.AArch64.EncapsH.satH 1568 1568 49152).wr held Proof.MlKem.AArch64.EncapsH.tabMemH_held 1568

/-! ## The instances -/

section
variable (v : Proof.Sha3.AArch64.Permutation)

/-! Over the sponge functions of `v`, with 48 bytes of stack. -/

theorem keyGenS768_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen v.callee.suffix (Impl.MlKem.AArch64.keyGenWith v.callee))
      (Scrubbed.keyGenContract abi 48) :=
  keyGen_wipe callWipeOk_abi _ (Proof.MlKem.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)) (keyGenS768_depth v) keyGenS768_sat

theorem keyGenS768_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen v.callee.suffix (Impl.MlKem.AArch64.keyGenWith v.callee))
      (Spec.MlKem.keyGenContract abi 48) :=
  keyGenS768_scrubbed v

theorem encapsHS768_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH v.callee.suffix (Impl.MlKem.AArch64.encapsHWith v.callee))
      (Scrubbed.encapsHContract abi 48) :=
  encapsH_wipe callWipeOk_abi _ (Proof.MlKem.AArch64.EncapsH.encapsH_verifiedWith (keccak := v)) (encapsHS768_depth v) encapsHS768_sat

theorem encapsHS768_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH v.callee.suffix (Impl.MlKem.AArch64.encapsHWith v.callee))
      (Spec.MlKem.encapsHContract abi 48) :=
  encapsHS768_scrubbed v

theorem encapsS768_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps v.callee.suffix (Impl.MlKem.AArch64.encapsWith v.callee))
      (Scrubbed.encapsContract abi 48) :=
  encaps_wipe callWipeOk_abi _ (Proof.MlKem.AArch64.Encaps.encaps_verifiedWith (keccak := v)) (encapsS768_depth v) encapsS768_sat

theorem encapsS768_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps v.callee.suffix (Impl.MlKem.AArch64.encapsWith v.callee))
      (Spec.MlKem.encapsContract abi 48) :=
  encapsS768_scrubbed v

theorem decapsS768_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps v.callee.suffix (Impl.MlKem.AArch64.decapsWith v.callee))
      (Scrubbed.decapsContract abi 48) :=
  decaps_wipe callWipeOk_abi _ (Proof.MlKem.AArch64.Decaps.decaps_verifiedWith (keccak := v)) (decapsS768_depth v) decapsS768_sat

theorem decapsS768_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps v.callee.suffix (Impl.MlKem.AArch64.decapsWith v.callee))
      (Spec.MlKem.decapsContract abi 48) :=
  decapsS768_scrubbed v

theorem keyGenS1024_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen1024 v.callee.suffix (Impl.MlKem1024.AArch64.keyGenWith v.callee))
      (Scrubbed.keyGen1024Contract abi 48) :=
  keyGen1024_wipe callWipeOk_abi _ (Proof.MlKem1024.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)) (keyGenS1024_depth v) keyGenS1024_sat

theorem keyGenS1024_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen1024 v.callee.suffix (Impl.MlKem1024.AArch64.keyGenWith v.callee))
      (Spec.MlKem1024.keyGenContract abi 48) :=
  keyGenS1024_scrubbed v

theorem encapsHS1024_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsHWith v.callee))
      (Scrubbed.encapsH1024Contract abi 48) :=
  encapsH1024_wipe callWipeOk_abi _ (Proof.MlKem.AArch64.EncapsH.encapsH1024_verifiedWith (keccak := v)) (encapsHS1024_depth v) encapsHS1024_sat

theorem encapsHS1024_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsHWith v.callee))
      (Spec.MlKem1024.encapsHContract abi 48) :=
  encapsHS1024_scrubbed v

theorem encapsS1024_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsWith v.callee))
      (Scrubbed.encaps1024Contract abi 48) :=
  encaps1024_wipe callWipeOk_abi _ (Proof.MlKem1024.AArch64.Encaps.encaps_verifiedWith (keccak := v)) (encapsS1024_depth v) encapsS1024_sat

theorem encapsS1024_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsWith v.callee))
      (Spec.MlKem1024.encapsContract abi 48) :=
  encapsS1024_scrubbed v

theorem decapsS1024_scrubbed :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.decapsWith v.callee))
      (Scrubbed.decaps1024Contract abi 48) :=
  decaps1024_wipe callWipeOk_abi _ (Proof.MlKem1024.AArch64.Decaps.decaps_verifiedWith (keccak := v)) (decapsS1024_depth v) decapsS1024_sat

theorem decapsS1024_verified :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.decapsWith v.callee))
      (Spec.MlKem1024.decapsContract abi 48) :=
  decapsS1024_scrubbed v

/-! The paired instances, named `sfx`, with 160 bytes of stack. -/

theorem keyGenP768_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen sfx (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768))
      (Scrubbed.keyGenContract (abi.withConsts Optimized.constants) 160) :=
  keyGen_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.KeyGen.keyGenP768_verified v) (keyGenP768_depth v) keyGenP768_sat

theorem keyGenP768_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen sfx (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768))
      (Spec.MlKem.keyGenContract (abi.withConsts Optimized.constants) 160) :=
  keyGenP768_scrubbed v sfx

theorem encapsHP768_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH sfx (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Scrubbed.encapsHContract (abi.withConsts Optimized.constants) 160) :=
  encapsH_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.EncapsH.encapsHP768_verified v) (encapsHP768_depth v) encapsHP768_sat

theorem encapsHP768_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH sfx (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Spec.MlKem.encapsHContract (abi.withConsts Optimized.constants) 160) :=
  encapsHP768_scrubbed v sfx

theorem encapsP768_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps sfx (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Scrubbed.encapsContract (abi.withConsts Optimized.constants) 160) :=
  encaps_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.Kem16P.encapsP768_verified v) (encapsP768_depth v) encapsP768_sat

theorem encapsP768_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps sfx (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Spec.MlKem.encapsContract (abi.withConsts Optimized.constants) 160) :=
  encapsP768_scrubbed v sfx

theorem decapsP768_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps sfx (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Scrubbed.decapsContract (abi.withConsts Optimized.constants) 160) :=
  decaps_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.Kem16P.decapsP768_verified v) (decapsP768_depth v) decapsP768_sat

theorem decapsP768_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps sfx (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768))
      (Spec.MlKem.decapsContract (abi.withConsts Optimized.constants) 160) :=
  decapsP768_scrubbed v sfx

theorem keyGenP1024_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen1024 sfx (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024))
      (Scrubbed.keyGen1024Contract (abi.withConsts Optimized.constants) 160) :=
  keyGen1024_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.KeyGen.keyGenP1024_verified v) (keyGenP1024_depth v) keyGenP1024_sat

theorem keyGenP1024_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.keyGen1024 sfx (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024))
      (Spec.MlKem1024.keyGenContract (abi.withConsts Optimized.constants) 160) :=
  keyGenP1024_scrubbed v sfx

theorem encapsHP1024_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH1024 sfx (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Scrubbed.encapsH1024Contract (abi.withConsts Optimized.constants) 160) :=
  encapsH1024_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.EncapsH.encapsHP1024_verified v) (encapsHP1024_depth v) encapsHP1024_sat

theorem encapsHP1024_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encapsH1024 sfx (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Spec.MlKem1024.encapsHContract (abi.withConsts Optimized.constants) 160) :=
  encapsHP1024_scrubbed v sfx

theorem encapsP1024_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps1024 sfx (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Scrubbed.encaps1024Contract (abi.withConsts Optimized.constants) 160) :=
  encaps1024_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.Kem16P.encapsP1024_verified v) (encapsP1024_depth v) encapsP1024_sat

theorem encapsP1024_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.encaps1024 sfx (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Spec.MlKem1024.encapsContract (abi.withConsts Optimized.constants) 160) :=
  encapsP1024_scrubbed v sfx

theorem decapsP1024_scrubbed (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps1024 sfx (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Scrubbed.decaps1024Contract (abi.withConsts Optimized.constants) 160) :=
  decaps1024_wipe callWipeOk_consts sfx (Proof.MlKem.AArch64.Kem16P.decapsP1024_verified v) (decapsP1024_depth v) decapsP1024_sat

theorem decapsP1024_verified (sfx : String) :
    Verified target (Impl.MlKem.AArch64.Wipe.decaps1024 sfx (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024))
      (Spec.MlKem1024.decapsContract (abi.withConsts Optimized.constants) 160) :=
  decapsP1024_scrubbed v sfx

end

end VG.Proof.MlKem.AArch64.Wipe
