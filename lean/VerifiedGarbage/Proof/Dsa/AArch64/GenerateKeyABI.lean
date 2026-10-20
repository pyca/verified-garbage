module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key-generation ABI, its inputs and its frame

The wrapper allocates the randomized signer's frame; the stack below it holds
the callees' frames. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygenStackArgs (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

structure GenerateKeyABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.sp).toNat
  stackUpper : (s.sp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 24⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, 8⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]
  outUsed : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 8⟩
  outParams : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  outRand : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  outArgs : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  usedParams : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  usedRand : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  usedScratch : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  usedArgs : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  paramsScratch : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  randScratch : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scratchArgs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  stackOut : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  stackUsed : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x2, 8⟩
  stackParams : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  stackRand : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  stackScratch : (below (s.sp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  stackArgs : (below (s.sp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 24⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .x2).toNat + 8 ≤ 2 ^ 64
  paramsBound : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  randBound : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x5).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 3 * (s.gpr .x5).toNat + 2 * (s.gpr .x6).toNat
  paramsLength : (s.gpr .x4).toNat = 2 * (s.gpr .x5).toNat + (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.generationScratchWords (s.gpr .x5).toNat ≤ (stackArg s 2).toNat

theorem generateKeyABI_of {extra : Nat} {s : State}
    (h : (Spec.Dsa.generateKeyContract abi (extra + 256)).pre s) : GenerateKeyABI extra s := by
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

/-! ## Inputs -/

structure KeygenInput where
  pLen : Nat
  qLen : Nat
  params : List Byte
  rand : List Byte

def keygenInput (s : State) : KeygenInput where
  pLen := (s.gpr .x5).toNat
  qLen := (s.gpr .x6).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
  rand := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

def keygenQBytes (s : State) : List Byte :=
  ((keygenInput s).params.drop (keygenInput s).pLen).take (keygenInput s).qLen

theorem keygen_q_length {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenQBytes s).length = (s.gpr .x6).toNat := by
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
    (randomBase s).toNat = (s.sp).toNat - Random.frameBytes := by
  have hl := h.stackLower
  simp only [randomBase, BitVec.toNat_sub, BitVec.toNat_ofNat, Random.frameBytes]
  have hb := (s.sp).isLt
  omega

theorem keygen_frame_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.sp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega)
  have hl := h.stackLower
  have hb := (s.sp).isLt
  omega

theorem keygen_alloc_scr {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Scr (allocated Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [keygenBase_toNat h]
  have hb := (s.sp).isLt
  unfold Random.frameBytes
  omega

theorem keygen_incoming_read {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (p : Nat × Nat) (hp : p ∈ GenerateKey.incomingSlots) :
    InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
      (off (randomBase s) p.1) 8 := by
  have hj (j : Nat) (hj : j < 3) :
      InRegions ((allocated Random.frameBytes s).rd ++ (allocated Random.frameBytes s).wr)
        (off (randomBase s) (256 + 8 * j)) 8 := by
    rw [random_incoming_address]
    refine ⟨⟨stackArgAddr s 0, 24⟩, List.mem_append_left _ ?_, ?_⟩
    · change _ ∈ s.rd
      rw [h.rd]
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]
    · simp only [stackArgAddr]
      exact Offset.contains _ (d := 8 * j) (n := 8) (e := 0) (k := 24)
        (by omega) (by omega) (by decide)
  simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)

theorem keygen_frame_ok {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocated Random.frameBytes s) fun t =>
      t.sp = randomBase s ∧ t.wr = (allocated Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩
  have hf : isa.pop (.free Random.frameBytes) (allocated Random.frameBytes s) t = some (randomFreed t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, htsp, htwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem keygen_initial_source {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.rd)
    (hn : n ≤ 2 ^ 64) (hd : (below (s.sp) (extra + 256)).Disjoint ⟨p, n⟩) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes p (Spec.Rsa.bytesAt s.mem p n) :=
  src_of_region (List.mem_append_left _ hr) hn ((hd.sub_left (keygen_frame_sub h)).symm)

theorem keygen_initial_params {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x3) (keygenInput s).params :=
  keygen_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x4).isLt) h.stackParams

theorem keygen_initial_rand {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes (s.gpr .x7) (keygenInput s).rand :=
  keygen_initial_source h (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.stackRand

theorem keygen_initial_q {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Src (allocated Random.frameBytes s) (randomBase s) Random.frameBytes
      (s.gpr .x3 + s.gpr .x5) (keygenQBytes s) := by
  have hh := random_src_take (random_src_drop (keygen_initial_params h) (keygenInput s).pLen) (keygenInput s).qLen
  simpa only [keygenQBytes, keygenInput, ofNat_toNat64] using hh

def keygenContextOf {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (m : Mem)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) : RandomContext where
  B := randomBase s
  initialMem := m
  R := s.gpr .x7
  Q := s.gpr .x3 + s.gpr .x5
  qBytes := keygenQBytes s
  rand := (keygenInput s).rand
  qlen := by
    rw [keygen_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  randBound := by rw [keygenInput, bytesAt_length]; exact (stackArg s 0).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (keygenQBytes s)).mp hq
    omega

end VG.Proof.Dsa.AArch64
