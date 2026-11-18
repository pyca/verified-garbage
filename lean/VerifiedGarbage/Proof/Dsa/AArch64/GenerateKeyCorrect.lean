module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCheckedVerified
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.DomainChecked
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.AArch64.GenerateKeySample`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyState`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyCheck`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyABI`, which this module and modules that import it used -/

section

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
  omega_using []

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
  omega_using [hl]

theorem keygen_frame_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.sp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega_using [])
  have hl := h.stackLower
  have hb := (s.sp).isLt
  omega_using [hl]

theorem keygen_alloc_scr {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Scr (allocated Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [keygenBase_toNat h]
  have hb := (s.sp).isLt
  unfold Random.frameBytes
  omega_using []

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
        (by omega_using []) (by omega_using [hj]) (by decide)
  simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)

theorem keygen_frame_ok {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocated Random.frameBytes s) fun t =>
      ∀ m u, Frame [⟨randomBase s, Random.frameBytes⟩] t.mem m →
        Q { randomFreed t with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  have hl := h.stackLower
  exact WP.alloc ⟨by decide, by decide, by decide⟩ (by unfold Random.frameBytes; omega_using [hl]) hb

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
    omega_using [hl]
  randBound := by rw [keygenInput, bytesAt_length]; exact (stackArg s 0).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (keygenQBytes s)).mp hq
    omega_using [hh]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyEntry`, which this module and modules that import it used -/

section

/-! Save the key-generation ABI arguments in the private stack frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenEntryHeaderMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B Random.oOut) (s.gpr .x0)).writeW (off B Random.oOutLen) (s.gpr .x1)).writeW (off B Random.oUsedPtr) (s.gpr .x2)).writeW (off B Random.oKey) (s.gpr .x3)).writeW (off B Random.oKeyLen) (s.gpr .x4)).writeW (off B Random.oPLen) (s.gpr .x5)).writeW (off B Random.oQLen) (s.gpr .x6)).writeW (off B Random.oRand) (s.gpr .x7)).writeW (off B RandomSign.oLink) (s.gpr .x30)).writeW (off B Random.oQ) (s.gpr .x3 + s.gpr .x5)).writeW (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oStatus) (0 : BitVec 64))

theorem keygen_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block GenerateKey.entryHeader) s fun t =>
      t.mem = keygenEntryHeaderMem s B ∧ Keep [.x0, .x4, .x15] s t := by
  refine WP.keep [.x0, .x4, .x15] (Q := fun t => t.mem = keygenEntryHeaderMem s B) ?_ rfl rfl rfl
  unfold GenerateKey.entryHeader Random.store keygenEntryHeaderMem
  brun [hsp,
    exec_addSp (show Random.oOut < 4096 by decide), hs.st (d := Random.oOut) (by decide),
    exec_addSp (show Random.oOutLen < 4096 by decide), hs.st (d := Random.oOutLen) (by decide),
    exec_addSp (show Random.oUsedPtr < 4096 by decide), hs.st (d := Random.oUsedPtr) (by decide),
    exec_addSp (show Random.oKey < 4096 by decide), hs.st (d := Random.oKey) (by decide),
    exec_addSp (show Random.oKeyLen < 4096 by decide), hs.st (d := Random.oKeyLen) (by decide),
    exec_addSp (show Random.oPLen < 4096 by decide), hs.st (d := Random.oPLen) (by decide),
    exec_addSp (show Random.oQLen < 4096 by decide), hs.st (d := Random.oQLen) (by decide),
    exec_addSp (show Random.oRand < 4096 by decide), hs.st (d := Random.oRand) (by decide),
    exec_addSp (show RandomSign.oLink < 4096 by decide), hs.st (d := RandomSign.oLink) (by decide),
    exec_addSp (show Random.oQ < 4096 by decide), hs.st (d := Random.oQ) (by decide),
    exec_addSp (show Random.oUsed < 4096 by decide), hs.st (d := Random.oUsed) (by decide),
    exec_addSp (show Random.oStatus < 4096 by decide), hs.st (d := Random.oStatus) (by decide)]
  rfl

theorem keygen_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hr : ∀ p ∈ GenerateKey.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block GenerateKey.entry) s fun t =>
      t.mem = randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots ∧
      Keep [.x0, .x4, .x15] s t := by
  unfold GenerateKey.entry
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  refine WP.mono (random_copySlots_ok GenerateKey.incomingSlots
    (hku.sp.trans hsp)
    (by intro p hp; simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp;
        rcases hp with rfl | rfl | rfl <;> decide)
    (fun p hp => by rw [hku.rd, hku.wr]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum], (hku.trans hkt).mono (by decide)⟩

private theorem extend_entry_frame {B : Addr} {m m' : Mem} {d : Nat} (v : BitVec 64)
    (h : Outside B 0 Random.frameBytes m m') (hd : d + 8 ≤ Random.frameBytes) :
    Outside B 0 Random.frameBytes m (m'.writeW (off B d) v) :=
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega_using [hd])).mono (Nat.zero_le _) hd)

theorem keygen_entryHeader_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem (keygenEntryHeaderMem s B) := by
  unfold keygenEntryHeaderMem
  repeat' apply extend_entry_frame _ _ (by decide)
  exact Outside.refl _ _ _ _

theorem keygen_entry_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem
      (randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots) :=
  (keygen_entryHeader_outside s B).trans (random_slots_outside _ _ _ _ _ (by
    intro p hp
    simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide))

def keygenEntryMem (s : State) (B : Addr) : Mem :=
  randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots

/-- The saved arguments: the frame's words the calls and the finish read. -/
def keygenSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (112, s.gpr .x7),
    (120, stackArg s 0), (128, stackArg s 1), (136, stackArg s 2)]

def KeygenSaved (s : State) (m : Mem) : Prop :=
  ∀ p ∈ keygenSavedValues s, word m (randomBase s) p.1 = p.2

theorem keygen_saved_bound {s : State} {p : Nat × BitVec 64} (hp : p ∈ keygenSavedValues s) :
    40 ≤ p.1 ∧ p.1 + 8 ≤ 144 := by
  simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem KeygenSaved.congr {s : State} {m m' : Mem} (h : KeygenSaved s m)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 144 → word m' (randomBase s) d = word m (randomBase s) d) : KeygenSaved s m' :=
  fun p hp => (hw _ (keygen_saved_bound hp).1 (keygen_saved_bound hp).2).trans (h p hp)

def keygenEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (112, s.gpr .x7),
    (232, s.gpr .x30), (168, s.gpr .x3 + s.gpr .x5), (144, 0), (192, 0),
    (120, word s.mem B 256), (128, word s.mem B 264), (136, word s.mem B 272)]

theorem keygen_entry_values (s : State) (B : Addr) :
    ∀ p ∈ keygenEntryValues s B, word (keygenEntryMem s B) B p.1 = p.2 := by
  simp only [keygenEntryMem, GenerateKey.incomingSlots, randomSlotsMem, keygenEntryHeaderMem,
      RandomSign.oLink, Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oStatus, Random.oQLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [keygenEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

theorem keygen_saved_entry (s : State) :
    KeygenSaved s (keygenEntryMem (allocated Random.frameBytes s) (randomBase s)) := by
  have hv := keygen_entry_values (allocated Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ keygenSavedValues s, p ∈ keygenEntryValues (allocated Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [keygenEntryValues, allocated, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.AArch64

end

end

/-! # Key generation's call of the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenCheckName (v : Backend) : String := "vg_dsa_check_parameters" ++ v.suffix
/-- Key generation derives with `Generate.deriveChecked`, an internal function. -/
def keygenDeriveName (v : Backend) : String := "vg_dsa_derive_key_checked" ++ v.suffix

theorem keygenStackBase_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (randomStackBase extra s).toNat = (s.sp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [hl]

theorem keygenStack_offset_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hk := keygenStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hd, hl, hk]

theorem keygen_callee_sub {extra : Nat} {s : State} (_h : GenerateKeyABI extra s) :
    Region.Sub (below (randomBase s) extra) (below s.sp (extra + 256)) :=
  random_calleeFrame_sub extra s

theorem keygen_checkArgs_ok {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.checkArgs) t fun u =>
      u.gpr .x0 = s.gpr .x3 ∧ u.gpr .x1 = s.gpr .x4 ∧ u.gpr .x2 = s.gpr .x5 ∧
      u.gpr .x3 = s.gpr .x6 ∧ u.gpr .x4 = stackArg s 1 ∧ u.gpr .x5 = stackArg s 2 ∧
      u.mem = t.mem ∧ Keep [.x0, .x1, .x2, .x3, .x4, .x5] t u := by
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5] (Q := fun u =>
      u.gpr .x0 = s.gpr .x3 ∧ u.gpr .x1 = s.gpr .x4 ∧ u.gpr .x2 = s.gpr .x5 ∧
      u.gpr .x3 = s.gpr .x6 ∧ u.gpr .x4 = stackArg s 1 ∧ u.gpr .x5 = stackArg s 2 ∧
      u.mem = t.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨h1, h2, h3, h4, h5, h6, hm⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, h6, hm, hk⟩
  unfold GenerateKey.checkArgs
  brun [exec_ldrSp_x', hsp, hs.ld (d := Random.oKey) (by decide), hs.ld (d := Random.oKeyLen) (by decide),
    hs.ld (d := Random.oPLen) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oScratch) (by decide), hs.ld (d := Random.oScratchLen) (by decide),
    hv (64, s.gpr .x3) (by simp [keygenSavedValues]), hv (72, s.gpr .x4) (by simp [keygenSavedValues]),
    hv (80, s.gpr .x5) (by simp [keygenSavedValues]), hv (88, s.gpr .x6) (by simp [keygenSavedValues]),
    hv (128, stackArg s 1) (by simp [keygenSavedValues]), hv (136, stackArg s 2) (by simp [keygenSavedValues])]
  exact ⟨hv (64, s.gpr .x3) (by simp [keygenSavedValues]),
    hv (72, s.gpr .x4) (by simp [keygenSavedValues]),
    hv (80, s.gpr .x5) (by simp [keygenSavedValues]),
    hv (88, s.gpr .x6) (by simp [keygenSavedValues]),
    hv (128, stackArg s 1) (by simp [keygenSavedValues]),
    hv (136, stackArg s 2) (by simp [keygenSavedValues])⟩

def keygenCheckRd (s : State) : List Region := [⟨s.gpr .x3, (s.gpr .x4).toNat⟩]
def keygenCheckWr (s : State) : List Region := [⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

theorem keygen_check_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenCheckRd s ++ keygenCheckWr s) (t.rd ++ t.wr) ∧ Covers (keygenCheckWr s) t.wr := by
  have hs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (keygenCheckWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [keygenCheckWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [keygenCheckRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩

theorem keygen_check_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2) :
    (Proof.Dsa.checkParametersContract abi extra).pre
      (t.callEntry.withRegions (keygenCheckRd s) (keygenCheckWr s)) := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp, keygenCheckRd, keygenCheckWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hk := keygenStackBase_toNat h
  have hs := h.scratchLength
  have hsmall : Spec.Dsa.scratchWords (s.gpr .x5).toNat ≤ (stackArg s 2).toNat := by
    unfold Spec.Dsa.generationScratchWords at hs
    unfold Spec.Dsa.scratchWords
    omega_using [hs]
  cases extra with
  | zero => exact ⟨trivial, trivial, trivial, h.paramsScratch, trivial, h.paramsBound, h.scratchBound,
      h.lengths, h.paramsLength, hsmall⟩
  | succ n => exact ⟨by
      simp only
      have := keygenBase_toNat h
      unfold Random.frameBytes at this
      omega_using [hl, this],
      trivial, trivial, h.paramsScratch, ⟨h.stackParams.sub_left (keygen_callee_sub h),
      h.stackScratch.sub_left (keygen_callee_sub h)⟩, h.paramsBound, h.scratchBound,
      h.lengths, h.paramsLength, hsmall⟩

theorem keygen_check_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.mul)) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (keygenCheckWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat =
        (if Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen
          (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat) then 1 else 0) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  obtain ⟨hc, hcw⟩ := keygen_check_covers h hrd hwr
  have hd := v.parametersDepth
  have hb := v.stackBound
  refine WP.callFV v.parametersVerified.1 (keygen_check_pre h hsp hdi hsi hdx hcx h8 h9)
    hc hcw (fun u hur huw husp hf huc hv hp => ?_) (by omega_using [hd, hb])
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at hp
  simp only [hdi, hsi, hdx, hcx] at hp
  refine ⟨hur, huw, husp, huc, ?_, hp, hv⟩
  rw [hsp] at hf
  exact Frame.below_mono hf hd (by omega_using [hb])

end VG.Proof.Dsa.AArch64

end

end

/-! # Key generation's frame state, through its entry and the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A callee keeps every byte of the wrapper's frame. -/
theorem keygen_call_frameBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem}
    (h : GenerateKeyABI extra s)
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hf : Frame (wr ++ [below (randomBase s) extra]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 256 ≤ 2 ^ 64; decide) hi
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega_using [hl])

/-- A callee keeps a buffer apart from what it writes and from the stack. -/
theorem keygen_call_inputBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (wr ++ [below (randomBase s) extra]) m m')
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨p, n⟩)
    (hstack : (below (s.sp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply hf.bytes (R := ⟨p, n⟩) _ hn (List.mem_range.mp hi)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact (hstack.sub_left (random_calleeFrame_sub extra s)).symm

theorem keygen_call_source {extra : Nat} {s t u : State} {wr : List Region} {p : Addr} {bs : List Byte}
    (hsrc : Src t (randomBase s) Random.frameBytes p bs)
    (hf : Frame (wr ++ [below (randomBase s) extra]) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hwrs : ∀ r ∈ wr, r.Disjoint ⟨p, bs.length⟩)
    (hstack : (below (s.sp) (extra + 256)).Disjoint ⟨p, bs.length⟩)
    (hn : bs.length ≤ 2 ^ 64) : Src u (randomBase s) Random.frameBytes p bs := by
  refine ⟨fun i hi => by rw [hrd, hwr]; exact hsrc.rd i hi, ?_, hsrc.out⟩
  intro i hi
  have hbytes := keygen_call_inputBytes hf hwrs hstack hn
  have he := congrArg (fun xs : List Byte => xs[i]?) hbytes
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
    hi, Option.map_some] at he
  exact (Option.some.inj he).trans (hsrc.val i hi)

/-- The wrapper's frame between its steps, `used` draws in. -/
structure KeygenState {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (used : Nat) (t : State) : Prop where
  scr : Scr t (randomBase s) Random.frameBytes
  sp : t.sp = randomBase s
  saved : KeygenSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  params : Src t (randomBase s) Random.frameBytes (s.gpr .x3) (keygenInput s).params
  rand : Src t (randomBase s) Random.frameBytes (s.gpr .x7) (keygenInput s).rand
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  link : word t.mem (randomBase s) RandomSign.oLink = s.gpr .x30

/-- After a change of the frame's private words and scratch registers only. -/
theorem KeygenState.of_frame {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : InScr (randomBase s) Random.frameBytes t.mem u.mem)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 152 → word u.mem (randomBase s) d = word t.mem (randomBase s) d)
    (hk : Keep randomVolatile t u)
    (hlink : word u.mem (randomBase s) RandomSign.oLink = word t.mem (randomBase s) RandomSign.oLink) :
    KeygenState h used u :=
  ⟨ht.scr.congr hk.wr, hk.sp.trans ht.sp,
    ht.saved.congr (fun d hd hd' => hw d hd (by omega_using [hd'])), (hw _ (by decide) (by decide)).trans ht.usedWord,
    hk.rd.trans ht.rd, hk.wr.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc => (hk.gpr r (random_saved_not_volatile hc)).trans (ht.callee r hc),
    fun r hc => (hk.vcs r hc).trans (ht.vectors r hc), hlink.trans ht.link⟩

theorem keygen_head {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    WP isa (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (allocated Random.frameBytes s) fun t =>
      KeygenState h 0 t ∧ word t.mem (randomBase s) Random.oStatus = 0 ∧
      word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 ∧ t.gpr .x0 = s.gpr .x3 ∧ t.gpr .x1 = s.gpr .x4 ∧ t.gpr .x2 = s.gpr .x5 ∧
      t.gpr .x3 = s.gpr .x6 ∧ t.gpr .x4 = stackArg s 1 ∧ t.gpr .x5 = stackArg s 2 := by
  have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entry_ok (keygen_alloc_scr h) hsp (keygen_incoming_read h))
    fun u ⟨hum, hku⟩ => ?_
  have hus := (keygen_alloc_scr h).congr hku.wr
  have husp := hku.sp.trans hsp
  have hsaved : KeygenSaved s u.mem := by rw [hum]; exact keygen_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (keygen_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ keygenEntryValues (allocated Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact keygen_entry_values _ _ p hp
  refine WP.mono (keygen_checkArgs_ok hus husp hsaved)
    fun t ⟨h1, h2, h3, h4, h5, h6, htm, hkt⟩ => ?_
  have hk := hku.trans hkt
  have hkv : Keep randomVolatile (allocated Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨⟨hus.congr hkt.wr, hkt.sp.trans husp, by rw [htm]; exact hsaved,
    by rw [htm]; exact hv (144, 0) (by simp [keygenEntryValues]), hk.rd, hk.wr,
    ((keygen_initial_params h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    ((keygen_initial_rand h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    fun r hr => hkv.gpr r (random_saved_not_volatile hr),
    hk.vcs,
    by rw [htm]; exact hv (232, s.gpr .x30) (by simp [keygenEntryValues, allocated])⟩,
    by rw [htm]; exact hv (192, 0) (by simp [keygenEntryValues]),
    by rw [htm]; exact hv (168, _) (by simp [keygenEntryValues, allocated]), h1, h2, h3, h4, h5, h6⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyCheckStep`, which this module and modules that import it used -/

section

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) extra]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (husp : u.sp = t.sp) (huc : ∀ r ∈ preserved, u.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .x4).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 0).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, husp.trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega_using [hd])),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .x4).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 0).isLt),
    fun r hc => (huc r hc).trans (ht.callee r hc),
    fun r hc => (hv r hc).trans (ht.vectors r hc), (hw _ (by decide)).trans ht.link⟩, hw⟩

theorem keygen_restore_ok {s : State} {B : Addr} (hs : Scr s B Random.frameBytes)
    (hsp : s.sp = B) :
    WP isa (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0]) s fun t =>
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧
      t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem ∧ Keep [.x0, .x30] s t := by
  refine WP.mono (WP.keep [.x0, .x30] (Q := fun t =>
    t.gpr .x30 = word s.mem B RandomSign.oLink ∧
    t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hl, hx, hm⟩, hk⟩ => ⟨hl, hx, hm, hk⟩
  brun [exec_ldrSp_x', hsp, hs.ld (d := RandomSign.oLink) (by decide),
    exec_logic, State.read, State.write, BitVec.or_self]

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2) :
    WP isa (.seq (.call (keygenCheckName v) (Generate.checkParameters v.mul))
      (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0])) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      u.gpr .x0 = if keygenChecked s then 1 else 0 := by
  refine WP.seq (WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, husp, huc, hf, hres, hv⟩ => ?_)
  have hscratch : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  have hwrs : ∀ r ∈ keygenCheckWr s, r.Disjoint ⟨randomBase s, Random.frameBytes⟩ := by
    intro r hr
    simp only [keygenCheckWr, List.mem_singleton] at hr
    subst hr
    exact hscratch
  have hul := (random_frame_words (keygen_call_frameBytes h hwrs hf) (d := RandomSign.oLink) (by decide)).trans ht.link
  refine WP.mono (keygen_restore_ok (ht.scr.congr huw) (husp.trans ht.sp))
    fun w ⟨hwl, hwx, hwm, hkw⟩ => ?_
  have hwc : ∀ r ∈ preserved, w.gpr r = t.gpr r := by
    intro r hr
    by_cases hl : r = .x30
    · subst r
      exact (hwl.trans hul).trans (ht.callee .x30 (by decide)).symm
    · exact (hkw.gpr r (by revert hr hl; cases r <;> decide)).trans (huc r hr hl)
  obtain ⟨hw, hwords⟩ := ht.after_call (wr := keygenCheckWr s) hwrs
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    (by rw [hwm]; exact hf) (hkw.rd.trans hur) (hkw.wr.trans huw) (hkw.sp.trans husp) hwc
    (fun r hr => (hkw.vcs r hr).trans (hv r hr))
  refine ⟨hw, hwords, ?_⟩
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
    apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
    intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact ht.params.val i h₂
  rw [hp] at hres
  rw [hwx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth] at hres ⊢
  rw [hres]
  change (if keygenChecked s then 1 else 0) % 2 ^ 64 = (if keygenChecked s then (1 : BitVec 64) else 0).toNat
  cases keygenChecked s <;> rfl

end VG.Proof.Dsa.AArch64

end

end

/-! # Key generation's sampling of x and its derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- An accepted domain has q > 1, as the sampler needs. -/
theorem keygen_q_valid {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    1 < Spec.Dsa.decodeBE (keygenQBytes s) := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenChecked Spec.Dsa.checkParametersBytes at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hb := (VG.Proof.Dsa.supported_bounds hc.2.1).2.1
  rw [keygen_q_decode]
  omega_using [hb]

/-- The sampler's draw, from the start of the tape. -/
abbrev keygenDraw (s : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (keygenQBytes s)) 128 (keygenInput s).rand

/-- Key generation's result after an accepted domain, as the wrapper computes it. -/
theorem keygen_result_checked {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    keygenResult s =
      match (keygenDraw s).scalar with
      | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (keygenDraw s), (keygenDraw s).used, (keygenDraw s).trace⟩
      | some x =>
        let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
          (Spec.Dsa.encodeBE (keygenInput s).qLen x)
        ⟨res, Spec.Dsa.signStatus res, (keygenDraw s).used, (keygenDraw s).trace ++ [if res.isSome then 5 else 6]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = true from hc, ↓reduceIte]
  change (match (keygenDraw s).scalar with
    | none => (⟨none, if (keygenDraw s).trace.getLast? == some 2 then 2 else 0, (keygenDraw s).used,
        (keygenDraw s).trace⟩ : Spec.Dsa.GenerateKeyResult)
    | some x => _) = _
  cases hx : (keygenDraw s).scalar with
  | none => simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
  | some x => rfl

/-- The frame state once the sampler has run, from its own state. -/
theorem KeygenState.of_ready {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {used draws : Nat}
    (ht : KeygenState h 0 t) (hr : RandomReady (keygenContextOf h t.mem hq) used draws u)
    (hk : Keep randomVolatile t u) :
    KeygenState h used u := by
  have fits : ∀ r ∈ randomWriteRanges, r.1 + r.2 ≤ Random.frameBytes := by decide
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := InScr.of_frm hr.frame fits
  refine ⟨hr.scr, hr.sp, ht.saved.congr fun d _ hd => hr.frame.word_eq ?_ (by omega_using [hd]), hr.usedWord,
    hk.rd.trans ht.rd, hk.wr.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc => (hk.gpr r (random_saved_not_volatile hc)).trans (ht.callee r hc),
    fun r hc => (hk.vcs r hc).trans (ht.vectors r hc), ?_⟩
  · intro r hm
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> dsimp only <;> omega_using [hd]
  · apply Eq.trans (hr.frame.word_eq ?_ (by decide)) ht.link
    intro r hm
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide

theorem keygen_prepare {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) :
    WP isa Random.prepare t fun u =>
      u.gpr .x0 = 1 ∧ (∃ draws, RandomReady (keygenContextOf h t.mem hq) 0 draws u) ∧ Keep randomVolatile t u := by
  let C := keygenContextOf h t.mem hq
  have hrl : word t.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, keygenContextOf, keygenInput, bytesAt_length, ofNat_toNat64] using
      ht.saved (120, stackArg s 0) (by simp [keygenSavedValues])
  have hql : word t.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, keygenContextOf, keygen_q_length h, ofNat_toNat64] using
      ht.saved (88, s.gpr .x6) (by simp [keygenSavedValues])
  have hqs : Src t C.B Random.frameBytes C.Q C.qBytes := by
    have hh := random_src_take (random_src_drop ht.params (keygenInput s).pLen) (keygenInput s).qLen
    simpa only [C, keygenContextOf, keygenQBytes, keygenInput, ofNat_toNat64] using hh
  refine WP.mono (WP.keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15]
    (random_prepare_ready (C := C) (draws := (word t.mem C.B Random.oDraws).toNat)
      ht.scr ht.sp (ht.saved (112, s.gpr .x7) (by simp [keygenSavedValues])) hrl ht.usedWord
      (ofNat_toNat64 _).symm hQ hql ht.rand hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl rfl rfl)
    fun u ⟨⟨hax, hr⟩, hk⟩ => ⟨hax, ⟨_, hr⟩, hk.mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeySampled`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDeriveCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDerivePre`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDerive`, which this module and modules that import it used -/

section

/-! # Key generation's call of key derivation, with the sampled x -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenDeriveOutgoing : List (Nat × Nat) := [(Random.oScratchLen, 0)]

theorem keygen_deriveArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block GenerateKey.deriveArgs) s fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] s t := by
  unfold GenerateKey.deriveArgs
  rw [WP.block_append_iff]
  refine WP.mono (random_copySlot_ok Random.oScratchLen 0 hsp (by decide) (by decide)
    (hs.ld (by decide)) (hs.st (by decide))) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧ t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧ t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing) ?_ rfl rfl rfl)
    fun t ⟨ht, hkt⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
      ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.2, (hku.trans hkt).mono (by decide)⟩
  brun [exec_ldrSp_x', exec_addSp (show Random.oNonce < 4096 by decide), husp, hus.ld (d := Random.oOut) (by decide),
    hus.ld (d := Random.oOutLen) (by decide), hus.ld (d := Random.oKey) (by decide),
    hus.ld (d := Random.oKeyLen) (by decide), hus.ld (d := Random.oPLen) (by decide),
    hus.ld (d := Random.oQLen) (by decide), hus.ld (d := Random.oScratch) (by decide)]
  simp only [hum, keygenDeriveOutgoing, randomSlotsMem]
  simp (disch := decide) only [random_word_write_other]
  trivial

theorem keygen_deriveOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 8 m (randomSlotsMem B m keygenDeriveOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  decide

theorem keygen_deriveOutgoing_words (m : Mem) (B : Addr) :
    word (randomSlotsMem B m keygenDeriveOutgoing) B 0 = word m B Random.oScratchLen := by
  exact word_writeW_self _ _ _ _

theorem keygen_deriveArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.deriveArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = stackArg s 1 ∧
      word u.mem (randomBase s) 0 = stackArg s 2 ∧
      KeygenSaved s u.mem ∧ Outside (randomBase s) 0 8 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (keygen_deriveArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 8 t.mem u.mem := by rw [hm]; exact keygen_deriveOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .x0) (by simp [keygenSavedValues])),
    hsi.trans (hv (48, s.gpr .x1) (by simp [keygenSavedValues])),
    hdx.trans (hv (64, s.gpr .x3) (by simp [keygenSavedValues])),
    hcx.trans (hv (72, s.gpr .x4) (by simp [keygenSavedValues])),
    h8.trans (hv (80, s.gpr .x5) (by simp [keygenSavedValues])), h9,
    h6.trans (hv (88, s.gpr .x6) (by simp [keygenSavedValues])),
    h7.trans (hv (128, stackArg s 1) (by simp [keygenSavedValues])),
    by rw [hm, keygen_deriveOutgoing_words]; exact hv (136, stackArg s 2) (by simp [keygenSavedValues]),
    hv.congr (fun d hd hd' => hf.word (Or.inr (by omega_using [hd])) (by omega_using [hd'])), hf, hk⟩

def keygenDeriveRd (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩,
    ⟨randomBase s, 8⟩]

def keygenDeriveWr (s : State) : List Region :=
  [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

theorem keygen_derive_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenDeriveRd s ++ keygenDeriveWr s) (t.rd ++ t.wr) ∧ Covers (keygenDeriveWr s) t.wr := by
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (keygenDeriveWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, ho, 0, zero _, by simp⟩
    · exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [keygenDeriveRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (s.gpr .x6).toNat ≤ 256; omega_using [hq]⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 8 ≤ 256; decide⟩

end VG.Proof.Dsa.AArch64

end

end

/-! Establish the key-derivation contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1) :
    (Spec.Dsa.deriveKeyContract abi extra).pre (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  have hE : stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = stackArg s 2 :=
    (random_call_stackArg hsp _ _ 0).trans hw
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hsp,
    random_call_stackArgAddr hsp, hE]
  simp only [keygenDeriveRd, keygenDeriveWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_using [hh]
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_frameBase extra s, keygenStack_offset_toNat h (by omega_using [])]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 200) := by
    rw [random_nonceBase extra s, keygenStack_offset_toNat h (by omega_using [])]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩
      (below (s.sp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_using [hq])
  have sA : Region.Sub ⟨randomBase s, 8⟩ (below (s.sp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have sK : Region.Sub (below (randomBase s) extra) (below (s.sp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega_using [])
  have dKM : (below (randomBase s) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl, hq])
  have dKA : (below (randomBase s) extra).Disjoint ⟨randomBase s, 8⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])
  refine ⟨?_, by omega_using [hl, hk, hR], trivial, trivial, h.outParams, (h.stackOut.sub_left sM).symm,
    h.outScratch, (h.stackOut.sub_left sA).symm, h.paramsScratch,
    h.stackScratch.sub_left sM, (h.stackScratch.sub_left sA).symm,
    ?_, h.outBound, h.paramsBound, by omega_using [hl, hq, hk, hN], h.scratchBound,
    h.lengths, h.outLength, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_using [hR]
  · cases extra with
    | zero => trivial
    | succ n => exact ⟨h.stackOut.sub_left sK, h.stackParams.sub_left sK, dKM,
        h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_using [hh]

/-- The checked derivation's contract at key generation's call, once the
domain check has passed. -/
theorem keygen_derive_checked_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  refine deriveChecked_of_pre (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) ?_
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (r := .x2) (by decide), State.callEntry_gpr _ (r := .x3) (by decide),
    State.callEntry_gpr _ (r := .x4) (by decide), State.callEntry_gpr _ (r := .x6) (by decide),
    hdx, hcx, h8, h6, hparams]
  exact hc

end VG.Proof.Dsa.AArch64

end

end

/-! # Verified call of key derivation from the generation controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params)
    (hck : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveChecked v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        res.getD (List.replicate (s.gpr .x1).toNat 0) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  obtain ⟨hc, hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveCheckedDepth
  have hb := v.stackBound
  refine WP.callFV v.deriveCheckedVerified.1
    (keygen_derive_checked_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7 hparams hck) hc hcw
    (fun u hur huw husp hf huc hv hp => ?_) (by omega_using [hd, hb])
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6] at hp
  refine ⟨hur, huw, husp, huc, ?_, hp.1, hp.2, hv⟩
  rw [hsp] at hf
  exact Frame.below_mono hf hd (by omega_using [hb])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyGenerate`, which this module and modules that import it used -/

section

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr))) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1 ∧
      Keep [.x4, .x15] t u := by
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1)
    ?_ rfl rfl rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]
  rfl

theorem keygen_writeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0)) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ Keep [.x15] t u := by
  refine WP.keep [.x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0)) ?_ rfl rfl rfl
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega_using [hd'])) (by omega_using [hd'])) hk (hf.word (by decide) (by decide))

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 8 t.mem u.mem)
    (hk : Keep randomVolatile t u) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega_using [hd])) (by omega_arith)) hk
    (hf.word (by decide) (by decide))

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
  apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact ht.params.val i h₂

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .x1).toNat 0))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyDeriveStep`, which only this module used -/

section

/-! # Derive the key and restore the generation controller's state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveChecked v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k)
      KeygenState h used u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat = res.getD (List.replicate (s.gpr .x1).toNat 0) := by
  refine WP.seq (WP.mono (keygen_deriveArgs_saved ht.scr ht.sp ht.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw, _, hargs, hka⟩ => ?_)
  have ha := ht.of_outgoing hargs (hka.mono (by decide))
  have hnA : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k := by
    have hq : (s.gpr .x6).toNat ≤ 32 := by
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega_using [hl]
    exact (random_outside_bytes hargs (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega_using [hq]) (Or.inr (show 0 + 8 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 h6 h7 ha.rd ha.wr
    (keygen_bytes_params ha) hc)
    fun b ⟨hbr, hbw, hbsp, hbc, hf, hst, hout, hvb⟩ => ?_)
  rw [keygen_bytes_params ha, hnA] at hst hout
  have hoF : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackOut.sub_left (keygen_frame_sub h)).symm
  have hsF : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  have hwrs : ∀ r ∈ keygenDeriveWr s, r.Disjoint ⟨randomBase s, Random.frameBytes⟩ := by
    intro r hr
    simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hoF
    · exact hsF
  have hbl := (random_frame_words (keygen_call_frameBytes h hwrs hf) (d := RandomSign.oLink) (by decide)).trans ha.link
  unfold GenerateKey.keepStatus
  rw [WP.block_append_iff]
  refine WP.mono (keygen_restore_ok (ha.scr.congr hbw) (hbsp.trans ha.sp))
    fun c ⟨hcl, hcx, hcm, hkc⟩ => ?_
  have hcc : ∀ r ∈ preserved, c.gpr r = a.gpr r := by
    intro r hr
    by_cases hl : r = .x30
    · subst r
      exact (hcl.trans hbl).trans (ha.callee .x30 (by decide)).symm
    · exact (hkc.gpr r (by revert hr hl; cases r <;> decide)).trans (hbc r hr hl)
  obtain ⟨hc, _⟩ := ha.after_call (wr := keygenDeriveWr s) hwrs
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outParams
      · exact h.paramsScratch.symm)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outRand
      · exact h.randScratch.symm)
    (by rw [hcm]; exact hf) (hkc.rd.trans hbr) (hkc.wr.trans hbw) (hkc.sp.trans hbsp) hcc
    (fun r hr => (hkc.vcs r hr).trans (hvb r hr))
  refine WP.mono (keygen_writeStatus_ok hc.scr hc.sp) fun u ⟨hum, hku⟩ => ?_
  refine ⟨hc.write_status hum (hku.mono (by decide)), ?_, ?_⟩
  · rw [hum, word_writeW_self, hcx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hst ⊢
    rw [hst]
    rfl
  · have hp := random_private_bytes
      (InScr.of_outside (writeW_outside c.mem (randomBase s) (c.gpr .x0)
        (d := Random.oStatus) (by decide)) (by decide)) hoF (Nat.le_of_lt (s.gpr .x1).isLt)
    rw [hum, hp, hcm]
    exact hout

end VG.Proof.Dsa.AArch64

end

end


/-! # Key generation after an accepted domain: the sampler, then the derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

/-- The draw and its status stored: the frame state, the flag for success, and x. -/
theorem keygen_sampled {extra : Nat} {s t b : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {draws : Nat} (ht : KeygenState h 0 t)
    (hrb : RandomReady (keygenContextOf h t.mem hq) 0 draws b) (hkb : Keep randomVolatile t b)
    :
    WP isa (.seq Random.sample (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr)))) b
      fun d =>
        KeygenState h (keygenDraw s).used d ∧
        d.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) - 1 ∧
        word d.mem (randomBase s) Random.oStatus =
          BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) ∧
        (∀ k, (keygenDraw s).scalar = some k →
          Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
            Spec.Dsa.encodeBE (s.gpr .x6).toNat k) := by
  have hd : randomRemaining (keygenContextOf h t.mem hq) 0 128 = keygenDraw s := by
    unfold randomRemaining; rfl
  refine WP.seq (WP.mono (random_sample_encoded hq hrb)
    fun c ⟨hcax, _, _, hnonce, _, ⟨draws', hrc⟩, hkc⟩ => ?_)
  rw [hd, Nat.zero_add] at hrc
  rw [hd] at hcax hnonce
  have hkc' : Keep randomVolatile b c := hkc.mono (by decide)
  have hkt : Keep randomVolatile t c := (hkb.trans hkc').mono (by decide)
  have hsc : KeygenState h (keygenDraw s).used c :=
    ht.of_ready hrc hkt
  refine WP.mono (keygen_storeStatus_ok hsc.scr hsc.sp) fun d ⟨hdm, hdz, hkd⟩ => ?_
  have hsd := hsc.write_status hdm (hkd.mono (by decide))
  rw [hcax] at hdm hdz
  refine ⟨hsd, hdz, by rw [hdm, word_writeW_self], fun k hk => ?_⟩
  have hn := hnonce k hk
  simp only [keygenContextOf, keygen_q_length h] at hn
  have hql : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  rw [hdm]
  exact (random_outside_bytes (writeW_outside _ _ _ (by decide))
    (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hql])
    (Or.inr (by decide))).trans hn

theorem keygen_generate (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hc : keygenChecked s = true) :
    WP isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.mul)) t
      (KeygenGenerated h) := by
  have hq := keygen_q_valid h hc
  have hres := keygen_result_checked h hc
  unfold GenerateKey.generate
  refine WP.seq (WP.mono (keygen_prepare ht hQ hq) fun b ⟨hbz, ⟨draws, hrb⟩, hkb⟩ => ?_)
  refine WP.ite false (by simp [eval, State.read, hbz]) (fun he => Bool.noConfusion he) fun _ => ?_
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_sampled ht hrb hkb) fun d ⟨hsd, hdz, hdw, hnd⟩ => ?_)
  have hlt : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (keygen_sampleStatus_le _) (by decide)
  cases hx : (keygenDraw s).scalar with
  | none =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]; split <;> decide
    refine WP.ite false (by
      change some (d.gpr .x4 == (0#64)) = some false
      rw [hdz]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      apply hs1
      have he' : BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) = 1 :=
        by simpa only [BitVec.sub_eq_iff_eq_add, BitVec.zero_add] using he
      have := congrArg BitVec.toNat he'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this)
      (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.block_nil ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hsd, hdw, fun h1 => absurd h1 hs1⟩
  | some k =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
    rw [hs1] at hdz
    refine WP.ite true (by change some (d.gpr .x4 == (0#64)) = some true; rw [hdz]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (keygen_derive_step v hsd (hnd k hx) hc) fun u ⟨hu, hw, hb⟩ => ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hu, hw, fun _ => hb⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyFinish`, which only this module used -/

section

/-! # Key generation's finish: the status, the key or zeros, and the draws used -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure KeygenBodyPost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  sp : t.sp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.key.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem keygen_finish_result {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    {result : Spec.Dsa.GenerateKeyResult} (hr : KeygenState h result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
      result.key.getD (List.replicate (s.gpr .x1).toNat 0))
    (hbound : result.status ≤ 2) (hkey : result.status ≠ 1 → result.key = none) :
    WP isa RandomSign.finish t (KeygenBodyPost s result) := by
  have houtlen : 0 < (s.gpr .x1).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .x2 :=
    hr.saved (56, s.gpr .x2) (by simp [keygenSavedValues])
  have hframeOut := h.stackOut.sub_left (keygen_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (keygen_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .x0) (s.gpr .x1).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .x2, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono (random_finish_ok (B := randomBase s) (op := s.gpr .x0) (k := (s.gpr .x1).toNat)
    hr.scr hr.sp
    (hr.saved (40, s.gpr .x0) (by simp [keygenSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [keygenSavedValues]))
    houtlen (s.gpr .x1).isLt
    (fun j hj => ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .x2 := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hk.sp.trans hr.sp, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc => (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc),
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .x1).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hkey hs]
      exact keygen_bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- Key generation's status is at most 2, and only success returns a key. -/
theorem keygen_result_bounds {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenResult s).status ≤ 2 ∧ ((keygenResult s).status ≠ 1 → (keygenResult s).key = none) := by
  by_cases hc : keygenChecked s = true
  · rw [keygen_result_checked h hc]
    cases hx : (keygenDraw s).scalar with
    | none => exact ⟨keygen_sampleStatus_le _, fun _ => rfl⟩
    | some k =>
      dsimp only
      unfold Spec.Dsa.signStatus
      cases hd : Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k) with
      | none => exact ⟨by decide, fun _ => rfl⟩
      | some key => exact ⟨by simp, fun hn => absurd (by simp) hn⟩
  · have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
      simp only [keygenInput, bytesAt_length]; exact h.paramsLength
    unfold keygenResult
    rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
      h.lengths hpl]
    simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
      = false from Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Key generation's functional correctness against its shared contract -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/GenerateKeyBody.lean`, which only this module imported.
section

/-! # Key generation's body: entry, the domain check, generation, the finish -/

section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul))
      (allocated Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp [eval, State.read, hax]) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hu (by rw [hw _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp [eval, State.read, hax]) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hu (by rw [hw _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveChecked v.mul)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.key.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveChecked v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht m u f => ?_
  -- The frame's bytes are lost; the outputs are apart from them.
  have hsub := keygen_frame_sub h
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status,
    (List.map_congr_left fun i hi => lost_byte f (h.stackOut.symm.sub_right hsub) (List.mem_range.mp hi)).trans
      ht.output,
    (f.readW (r := ⟨s.gpr .x2, 8⟩) (Region.contains_self _ _)
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact h.stackUsed.symm.sub_right hsub)
      (by decide)).trans ht.used,
    ht.callee, ?_, ht.vectors⟩
  change t.sp + BitVec.ofNat 64 Random.frameBytes = s.sp
  rw [ht.sp, randomBase, BitVec.sub_add_cancel]

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, keygen_shared_post h hp⟩

end VG.Proof.Dsa.AArch64
