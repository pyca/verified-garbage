module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The key-generation ABI, its inputs and its frame

The wrapper allocates the randomized signer's frame; the stack below it holds
the callees' frames. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem stackArgs_five' (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure GenerateKeyABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outUsed : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  outParams : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  outRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  outArgs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  usedParams : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  usedRand : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  usedScratch : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  usedArgs : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  paramsScratch : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  randScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  retParams : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  stackOut : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  stackUsed : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdx, 8⟩
  stackParams : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  stackRand : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  stackScratch : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  stackArgs : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 40⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  paramsBound : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  randBound : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r9).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 3 * (s.gpr .r9).toNat + 2 * (stackArg s 0).toNat
  paramsLength : (s.gpr .r8).toNat = 2 * (s.gpr .r9).toNat + (stackArg s 0).toNat
  scratchLength : Spec.Dsa.generationScratchWords (s.gpr .r9).toNat ≤ (stackArg s 4).toNat

theorem generateKeyABI_of {extra : Nat} {s : State}
    (h : (Spec.Dsa.generateKeyContract abi (extra + 256)).pre s) : GenerateKeyABI extra s := by
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five',
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five'] at h
  sig_split h
  constructor <;> with_reducible assumption

/-! ## Inputs -/

structure KeygenInput where
  pLen : Nat
  qLen : Nat
  params : List Byte
  rand : List Byte

def keygenInput (s : State) : KeygenInput where
  pLen := (s.gpr .r9).toNat
  qLen := (stackArg s 0).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
  rand := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat

def keygenQBytes (s : State) : List Byte :=
  ((keygenInput s).params.drop (keygenInput s).pLen).take (keygenInput s).qLen

theorem keygen_q_length {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenQBytes s).length = (stackArg s 0).toNat := by
  simp only [keygenQBytes, keygenInput, List.length_take, List.length_drop, bytesAt_length, h.paramsLength]
  omega

theorem keygen_q_decode (s : State) :
    Spec.Dsa.decodeBE (keygenQBytes s) =
      (Spec.Dsa.paramsBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params).q := rfl

/-- The key-generation result, as the wrapper computes it. -/
def keygenResult (s : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params (keygenInput s).rand

/-! ## The frame -/

theorem keygenBase_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (randomBase s).toNat = (s.gpr .rsp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.gpr .rsp).isLt
  omega

theorem keygen_frame_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.gpr .rsp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega)
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega

theorem keygen_alloc_scr {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Scr (allocState Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [keygenBase_toNat h]
  have hb := (s.gpr .rsp).isLt
  unfold Random.frameBytes
  omega

theorem keygen_incoming_read {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (p : Nat × Nat) (hp : p ∈ GenerateKey.incomingSlots) :
    InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 5) :
      InRegions ((allocState Random.frameBytes s).rd ++ (allocState Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 40)
        (by omega) (by omega) (by decide)
  simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)

theorem keygen_frame_ok {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocState Random.frameBytes s) fun t =>
      t.gpr .rsp = randomBase s ∧ t.wr = (allocState Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocState Random.frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩
  have hf : isa.pop (.free Random.frameBytes) (allocState Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem keygen_initial_source {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.rd)
    (hn : n ≤ 2 ^ 64) (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes p (Spec.Rsa.bytesAt s.mem p n) :=
  src_of_region (List.mem_append_left _ hr) hn ((hd.sub_left (keygen_frame_sub h)).symm)

theorem keygen_initial_params {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .rcx) (keygenInput s).params :=
  keygen_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .r8).isLt) h.stackParams

theorem keygen_initial_rand {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes (stackArg s 1) (keygenInput s).rand :=
  keygen_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.stackRand

theorem keygen_initial_q {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocState Random.frameBytes s) (randomBase s) Random.frameBytes
      (s.gpr .rcx + s.gpr .r9) (keygenQBytes s) := by
  have hh := random_src_take (random_src_drop (keygen_initial_params h) (keygenInput s).pLen) (keygenInput s).qLen
  simpa only [keygenQBytes, keygenInput, ofNat_toNat64] using hh

def keygenContextOf {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (m : Mem)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) : RandomContext where
  B := randomBase s
  initialMem := m
  R := stackArg s 1
  Q := s.gpr .rcx + s.gpr .r9
  qBytes := keygenQBytes s
  rand := (keygenInput s).rand
  qlen := by
    rw [keygen_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  randBound := by rw [keygenInput, bytesAt_length]; exact (stackArg s 2).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (keygenQBytes s)).mp hq
    omega

end VG.Proof.Dsa.X86_64
