module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc

/-! ### `Dsa.X86_64.GenerateKeySample`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyCheckStep`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyCheck`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyABI`, which this module and modules that import it used -/

section

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
  omega_using []

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
  omega_using [hl]

theorem keygen_frame_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s, Random.frameBytes⟩ (below (s.gpr .rsp) (extra + 256)) := by
  apply below_sub (by unfold Random.frameBytes; omega_using [])
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega_using [hl]

theorem keygen_alloc_scr {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Scr (allocState Random.frameBytes s) (randomBase s) Random.frameBytes := by
  apply Scr.of_mem (List.mem_cons_self ..)
  rw [keygenBase_toNat h]
  have hb := (s.gpr .rsp).isLt
  unfold Random.frameBytes
  omega_using []

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
        (by omega_using []) (by omega_using [hj]) (by decide)
  simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hj 0 (by decide)
  · exact hj 1 (by decide)
  · exact hj 2 (by decide)
  · exact hj 3 (by decide)
  · exact hj 4 (by decide)

/-- The frame (`alloc_frame_ok`): the postcondition holds whatever the
frame's bytes hold once released, and whatever the unknowns. -/
theorem keygen_frame_ok {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocState Random.frameBytes s) fun t =>
      t.gpr .rsp = randomBase s ∧ t.wr = (allocState Random.frameBytes s).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩] t.mem m →
        Q { randomFreed t with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  have hl := h.stackLower
  exact alloc_frame_ok (by decide) (by unfold Random.frameBytes; omega_using [hl]) hb

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
    omega_using [hl]
  randBound := by rw [keygenInput, bytesAt_length]; exact (stackArg s 2).isLt
  positive := by
    have hh := (VG.Proof.Dsa.random_valid_scan (keygenQBytes s)).mp hq
    omega_using [hh]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.GenerateKeyEntry`, which this module and modules that import it used -/

section

/-! # Key generation's entry: the arguments saved in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenEntryHeaderMem (s : State) (B : Addr) : Mem :=
  (((((((((s.mem.writeW (off B Random.oOut) (s.gpr .rdi)).writeW
    (off B Random.oOutLen) (s.gpr .rsi)).writeW (off B Random.oUsedPtr) (s.gpr .rdx)).writeW
    (off B Random.oKey) (s.gpr .rcx)).writeW (off B Random.oKeyLen) (s.gpr .r8)).writeW
    (off B Random.oPLen) (s.gpr .r9)).writeW (off B Random.oQ) (s.gpr .rcx + s.gpr .r9)).writeW
    (off B Random.oUsed) (0 : BitVec 64)).writeW (off B Random.oStatus) (0 : BitVec 64))

theorem keygen_entryHeader_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block GenerateKey.entryHeader) s fun t =>
      t.mem = keygenEntryHeaderMem s B ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] (Q := fun t => t.mem = keygenEntryHeaderMem s B) ?_ rfl
  unfold GenerateKey.entryHeader keygenEntryHeaderMem
  xrun [random_ea_sp, hsp, hs.st (d := Random.oOut) (by decide),
    hs.st (d := Random.oOutLen) (by decide), hs.st (d := Random.oUsedPtr) (by decide),
    hs.st (d := Random.oKey) (by decide), hs.st (d := Random.oKeyLen) (by decide),
    hs.st (d := Random.oPLen) (by decide), hs.st (d := Random.oQ) (by decide),
    hs.st (d := Random.oUsed) (by decide), hs.st (d := Random.oStatus) (by decide)]
  rfl

def keygenEntryMem (s : State) (B : Addr) : Mem :=
  randomSlotsMem B (keygenEntryHeaderMem s B) GenerateKey.incomingSlots

theorem keygen_entry_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hr : ∀ p ∈ GenerateKey.incomingSlots, InRegions (s.rd ++ s.wr) (off B p.1) 8) :
    WP isa (.block GenerateKey.entry) s fun t =>
      t.mem = keygenEntryMem s B ∧ Keep [.rax, .rcx] s t := by
  unfold GenerateKey.entry
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entryHeader_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  refine WP.mono (random_copySlots_ok GenerateKey.incomingSlots
    ((hku.gpr (by decide)).trans hsp)
    (fun p hp => by rw [hku.2.1, hku.2.2]; exact hr p hp)
    (fun p hp => hus.st (by
      simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ⟨by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

private theorem extend_entry_frame {B : Addr} {m m' : Mem} {d : Nat} (v : BitVec 64)
    (h : Outside B 0 Random.frameBytes m m') (hd : d + 8 ≤ Random.frameBytes) :
    Outside B 0 Random.frameBytes m (m'.writeW (off B d) v) :=
  h.trans ((writeW_outside _ B _ (by unfold Random.frameBytes at hd; omega_using [hd])).mono (Nat.zero_le _) hd)

theorem keygen_entry_outside (s : State) (B : Addr) :
    Outside B 0 Random.frameBytes s.mem (keygenEntryMem s B) := by
  have hh : Outside B 0 Random.frameBytes s.mem (keygenEntryHeaderMem s B) := by
    unfold keygenEntryHeaderMem
    repeat' apply extend_entry_frame _ _ (by decide)
    exact Outside.refl _ _ _ _
  exact hh.trans (random_slots_outside _ _ _ _ _ (by
    intro p hp
    simp only [GenerateKey.incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide))

/-- The saved arguments: the frame's words the calls and the finish read. -/
def keygenSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (88, stackArg s 0), (112, stackArg s 1),
    (120, stackArg s 2), (128, stackArg s 3), (136, stackArg s 4)]

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
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (168, s.gpr .rcx + s.gpr .r9), (144, 0), (192, 0),
    (88, word s.mem B 256), (112, word s.mem B 264), (120, word s.mem B 272),
    (128, word s.mem B 280), (136, word s.mem B 288)]

theorem keygen_entry_values (s : State) (B : Addr) :
    ∀ p ∈ keygenEntryValues s B, word (keygenEntryMem s B) B p.1 = p.2 := by
  simp only [keygenEntryMem, GenerateKey.incomingSlots, randomSlotsMem, keygenEntryHeaderMem,
      Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oStatus, Random.oQLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen]
  simp (disch := decide) only [random_word_write_other]
  intro p hp
  simp only [keygenEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

theorem keygen_saved_entry (s : State) :
    KeygenSaved s (keygenEntryMem (allocState Random.frameBytes s) (randomBase s)) := by
  have hv := keygen_entry_values (allocState Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ keygenSavedValues s, p ∈ keygenEntryValues (allocState Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [keygenSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [keygenEntryValues, allocState, State.setReg, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2, random_entry_stackWord s 3,
        random_entry_stackWord s 4]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's call of the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenCheckName (v : Backend) : String := "vg_dsa_check_parameters" ++ v.suffix
/-- Key generation derives with `Generate.deriveChecked`, an internal function. -/
def keygenDeriveName (v : Backend) : String := "vg_dsa_derive_key_checked" ++ v.suffix

theorem keygenStackBase_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (randomStackBase extra s).toNat = (s.gpr .rsp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem keygenStack_offset_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- The frame's return slot and the callee's frame lie in the wrapper's stack allowance. -/
theorem keygen_ret_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  rw [random_callBase extra s]
  exact Offset.sub_base _ (by omega_arith)

theorem keygen_callee_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub (below (randomBase s - 8) extra) (below (s.gpr .rsp) (extra + 256)) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  change Region.Sub ⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ _
  rw [random_calleeBase extra s]
  exact Region.sub_prefix (by omega_arith)

theorem keygen_checkArgs_ok {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.checkArgs) t fun u =>
      u.gpr .rdi = s.gpr .rcx ∧ u.gpr .rsi = s.gpr .r8 ∧ u.gpr .rdx = s.gpr .r9 ∧
      u.gpr .rcx = stackArg s 0 ∧ u.gpr .r8 = stackArg s 3 ∧ u.gpr .r9 = stackArg s 4 ∧
      u.mem = t.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.gpr .rdi = s.gpr .rcx ∧ u.gpr .rsi = s.gpr .r8 ∧ u.gpr .rdx = s.gpr .r9 ∧
      u.gpr .rcx = stackArg s 0 ∧ u.gpr .r8 = stackArg s 3 ∧ u.gpr .r9 = stackArg s 4 ∧
      u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨h1, h2, h3, h4, h5, h6, hm⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, h6, hm, hk⟩
  unfold GenerateKey.checkArgs
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oKey) (by decide), hs.ld (d := Random.oKeyLen) (by decide),
    hs.ld (d := Random.oPLen) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oScratch) (by decide), hs.ld (d := Random.oScratchLen) (by decide),
    hv (64, s.gpr .rcx) (by simp [keygenSavedValues]), hv (72, s.gpr .r8) (by simp [keygenSavedValues]),
    hv (80, s.gpr .r9) (by simp [keygenSavedValues]), hv (88, stackArg s 0) (by simp [keygenSavedValues]),
    hv (128, stackArg s 3) (by simp [keygenSavedValues]), hv (136, stackArg s 4) (by simp [keygenSavedValues])]
  exact ⟨hv (64, s.gpr .rcx) (by simp [keygenSavedValues]), hv (72, s.gpr .r8) (by simp [keygenSavedValues]),
    hv (80, s.gpr .r9) (by simp [keygenSavedValues]), hv (88, stackArg s 0) (by simp [keygenSavedValues]),
    hv (128, stackArg s 3) (by simp [keygenSavedValues]), hv (136, stackArg s 4) (by simp [keygenSavedValues])⟩

def keygenCheckRd (s : State) : List Region := [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩]
def keygenCheckWr (s : State) : List Region := [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]

theorem keygen_check_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenCheckRd s ++ keygenCheckWr s) (t.rd ++ t.wr) ∧ Covers (keygenCheckWr s) t.wr := by
  have hs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
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
    (hsp : t.gpr .rsp = randomBase s)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4) :
    (Proof.Dsa.checkParametersContract abi extra).pre
      (t.callEntry.withRegions (keygenCheckRd s) (keygenCheckWr s)) := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp, keygenCheckRd, keygenCheckWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have sR := keygen_ret_sub h
  have sK := keygen_callee_sub h
  refine ⟨?_, trivial, trivial, h.paramsScratch, h.stackParams.sub_left sR, ?_, h.paramsBound, h.scratchBound,
    h.lengths, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_arith
  · cases extra with
    | zero => exact h.stackScratch.sub_left sR
    | succ n => exact ⟨h.stackScratch.sub_left sR, h.stackParams.sub_left sK, h.stackScratch.sub_left sK⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_arith

/-- The bytes of a buffer apart from the wrapper's stack allowance, as the callee reads them. -/
theorem keygen_callEntry_bytes {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s) {p : Addr} {n : Nat}
    (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem p n = Spec.Rsa.bytesAt t.mem p n :=
  random_callEntry_bytes hsp ((hd.sub_left (keygen_ret_sub h)).symm.sep (Region.contains_self _ _)
    (Region.contains_self _ _)) hn

theorem keygen_check_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (keygenCheckWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat =
        (if Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen
          (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat) then 1 else 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := keygen_check_covers h hrd hwr
  have hd := v.parametersDepth
  have hb := v.stackBound
  refine WP.call_sp_mx v.parametersVerified.1 (SpSafe.of_all v.parametersSp) (by omega_arith)
    (keygen_check_pre h hsp hdi hsi hdx hcx h8 h9) hc hcw
    (fun u hur huw huc hf _ ⟨w, hwm, hwg, hp⟩ hmx => ?_)
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at hp
  simp only [hdi, hsi, hdx, hcx, hwg .rax (by decide)] at hp
  refine ⟨hur, huw, huc, ?_, ?_, hmx⟩
  · rw [hsp] at hf
    exact VG.X86_64.Frame.below_mono hf (by omega_arith) (by omega_arith)
  · rw [hp, ← keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt]
    rfl

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.GenerateKeyState`, which this module and modules that import it used -/

section

/-! # Key generation's frame state, through its entry and the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- A callee keeps every byte of the wrapper's frame. -/
theorem keygen_call_frameBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem}
    (h : GenerateKeyABI extra s)
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 248 ≤ 2 ^ 64; decide) hi
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega_using [hl])

/-- A callee keeps a buffer apart from what it writes and from the stack. -/
theorem keygen_call_inputBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) m m')
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨p, n⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
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
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hwrs : ∀ r ∈ wr, r.Disjoint ⟨p, bs.length⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, bs.length⟩)
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
  sp : t.gpr .rsp = randomBase s
  saved : KeygenSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  params : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (keygenInput s).params
  rand : Src t (randomBase s) Random.frameBytes (stackArg s 1) (keygenInput s).rand
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- After a change of the frame's private words and scratch registers only. -/
theorem KeygenState.of_frame {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : InScr (randomBase s) Random.frameBytes t.mem u.mem)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 152 → word u.mem (randomBase s) d = word t.mem (randomBase s) d)
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u :=
  ⟨ht.scr.congr hk.2.2, (hk.gpr (by decide)).trans ht.sp,
    ht.saved.congr (fun d hd hd' => hw d hd (by omega_using [hd'])), (hw _ (by decide) (by decide)).trans ht.usedWord,
    hk.2.1.trans ht.rd, hk.2.2.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc hn => (hk.gpr (random_saved_not_volatile hc)).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩

theorem keygen_head {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    WP isa (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (allocState Random.frameBytes s) fun t =>
      KeygenState h 0 t ∧ word t.mem (randomBase s) Random.oStatus = 0 ∧
      word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rcx ∧ t.gpr .rsi = s.gpr .r8 ∧ t.gpr .rdx = s.gpr .r9 ∧
      t.gpr .rcx = stackArg s 0 ∧ t.gpr .r8 = stackArg s 3 ∧ t.gpr .r9 = stackArg s 4 := by
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := by
    simp only [allocState, State.setReg, ite_true]; rfl
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (keygen_entry_ok (keygen_alloc_scr h) hsp (keygen_incoming_read h))
    fun u ⟨hum, hku⟩ hmxu => ?_
  have hus := (keygen_alloc_scr h).congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hsaved : KeygenSaved s u.mem := by rw [hum]; exact keygen_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (keygen_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ keygenEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact keygen_entry_values _ _ p hp
  refine WP.mono_mx (by decide) (keygen_checkArgs_ok hus husp hsaved)
    fun t ⟨h1, h2, h3, h4, h5, h6, htm, hkt⟩ hmxt => ?_
  have hk := hku.trans hkt
  have hkv : Keep randomVolatile (allocState Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨⟨hus.congr hkt.2.2, (hkt.gpr (by decide)).trans husp, by rw [htm]; exact hsaved,
    by rw [htm]; exact hv (144, 0) (by simp [keygenEntryValues]), hk.2.1, hk.2.2,
    ((keygen_initial_params h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    ((keygen_initial_rand h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    fun r hr hne => by
      rw [hkv.gpr (random_saved_not_volatile hr)]
      simp only [allocState, State.setReg, ite_eq_right hne],
    by rw [hmxt, hmxu]; rfl⟩,
    by rw [htm]; exact hv (192, 0) (by simp [keygenEntryValues]),
    by rw [htm]; exact hv (168, _) (by simp [keygenEntryValues, allocState, State.setReg]), h1, h2, h3, h4, h5, h6⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (huc : ∀ r ∈ calleeSaved, u.gpr r = t.gpr r)
    (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .r8).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 2).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, (huc .rsp (by decide)).trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega_using [hd])),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .r8).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 2).isLt),
    fun r hc hn => (huc r hc).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩, hw⟩

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      ((u.gpr .rax).setWidth 32).toNat = if keygenChecked s then 1 else 0 := by
  refine WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, huc, hf, hres, hmx⟩ => ?_
  have hscratch : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hu, hw⟩ := ht.after_call (wr := keygenCheckWr s)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact hscratch)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    hf hur huw huc hmx
  refine ⟨hu, hw, ?_⟩
  rw [hres]
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
    simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params
  rw [hp]

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's sampling of x and its derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u := by
  have fits : ∀ r ∈ randomWriteRanges, r.1 + r.2 ≤ Random.frameBytes := by decide
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := InScr.of_frm hr.frame fits
  refine ⟨hr.scr, hr.sp, ht.saved.congr fun d _ hd => hr.frame.word_eq ?_ (by omega_using [hd]), hr.usedWord,
    hk.2.1.trans ht.rd, hk.2.2.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc hn => (hk.gpr (random_saved_not_volatile hc)).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩
  intro r hm
  simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> dsimp only <;> omega_using [hd]

theorem keygen_prepare {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) :
    WP isa Random.prepare t fun u =>
      u.gpr .rax = 1 ∧ (∃ draws, RandomReady (keygenContextOf h t.mem hq) 0 draws u) ∧ Keep randomVolatile t u ∧
      u.mxcsr = t.mxcsr := by
  let C := keygenContextOf h t.mem hq
  have hrl : word t.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, keygenContextOf, keygenInput, bytesAt_length, ofNat_toNat64] using
      ht.saved (120, stackArg s 2) (by simp [keygenSavedValues])
  have hql : word t.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, keygenContextOf, keygen_q_length h, ofNat_toNat64] using
      ht.saved (88, stackArg s 0) (by simp [keygenSavedValues])
  have hqs : Src t C.B Random.frameBytes C.Q C.qBytes := by
    have hh := random_src_take (random_src_drop ht.params (keygenInput s).pLen) (keygenInput s).qLen
    simpa only [C, keygenContextOf, keygenQBytes, keygenInput, ofNat_toNat64] using hh
  refine WP.mono_mx (by decide) (WP.keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11]
    (random_prepare_ready (C := C) (draws := (word t.mem C.B Random.oDraws).toNat)
      ht.scr ht.sp (ht.saved (112, stackArg s 1) (by simp [keygenSavedValues])) hrl ht.usedWord
      (ofNat_toNat64 _).symm hQ hql ht.rand hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl)
    fun u ⟨⟨hax, hr⟩, hk⟩ hmx => ⟨hax, ⟨_, hr⟩, hk.mono (by decide), hmx⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.GenerateKeyBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeySampled`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyGenerate`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyDerive`, which this module and modules that import it used -/

section

/-! # Key generation's call of key derivation, with the sampled x -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenDeriveOutgoing : List (Nat × Nat) :=
  [(Random.oQLen, 0), (Random.oScratch, 8), (Random.oScratchLen, 16)]

theorem keygen_deriveArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block GenerateKey.deriveArgs) s fun t =>
      t.gpr .rdi = word s.mem B Random.oOut ∧
      t.gpr .rsi = word s.mem B Random.oOutLen ∧
      t.gpr .rdx = word s.mem B Random.oKey ∧
      t.gpr .rcx = word s.mem B Random.oKeyLen ∧
      t.gpr .r8 = word s.mem B Random.oPLen ∧ t.gpr .r9 = off B Random.oNonce ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] s t := by
  unfold GenerateKey.deriveArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u =>
      u.gpr .rdi = word s.mem B Random.oOut ∧ u.gpr .rsi = word s.mem B Random.oOutLen ∧
      u.gpr .rdx = word s.mem B Random.oKey ∧ u.gpr .rcx = word s.mem B Random.oKeyLen ∧
      u.gpr .r8 = word s.mem B Random.oPLen ∧ u.mem = s.mem)
      (by xrun [random_ea_sp, hsp, hs.ld (d := Random.oOut) (by decide),
        hs.ld (d := Random.oOutLen) (by decide), hs.ld (d := Random.oKey) (by decide),
        hs.ld (d := Random.oKeyLen) (by decide), hs.ld (d := Random.oPLen) (by decide)]) rfl)
    fun u ⟨⟨hud, hus, hux, huc, hu8, hum⟩, hku⟩ => ?_
  have husp := (hku.gpr (by decide)).trans hsp
  refine WP.mono (WP.keep [.r9] (Q := fun v => v.gpr .r9 = off B Random.oNonce ∧ v.mem = u.mem)
      (by unfold Random.address; xrun [husp]; rfl) rfl)
    fun v ⟨⟨hv9, hvm⟩, hkv⟩ => ?_
  have hvk := hku.trans hkv
  have hvs := hs.congr hvk.2.2
  refine WP.mono (random_copySlots_ok keygenDeriveOutgoing ((hvk.gpr (by decide)).trans hsp)
      (fun p hp => hvs.ld (by
        simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> decide))
      (fun p hp => hvs.st (by
        simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ?_
  have hk := hkv.trans hkt
  exact ⟨(hk.gpr (by decide)).trans hud, (hk.gpr (by decide)).trans hus,
    (hk.gpr (by decide)).trans hux, (hk.gpr (by decide)).trans huc,
    (hk.gpr (by decide)).trans hu8, (hkt.gpr (by decide)).trans hv9,
    by rw [htm, hvm, hum], (hku.trans hk).mono (by decide)⟩

theorem keygen_deriveOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 24 m (randomSlotsMem B m keygenDeriveOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem keygen_deriveOutgoing_words (m : Mem) (B : Addr) :
    ∀ p ∈ keygenDeriveOutgoing,
      word (randomSlotsMem B m keygenDeriveOutgoing) B p.2 = word m B p.1 := by
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [keygenDeriveOutgoing, randomSlotsMem, Random.oQLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

def keygenDeriveArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => stackArg s 3
  | _ => stackArg s 4

theorem keygen_saved_outgoing {s : State} {m : Mem} (h : KeygenSaved s m) :
    ∀ i < 3, word (randomSlotsMem (randomBase s) m keygenDeriveOutgoing) (randomBase s) (8 * i) =
      keygenDeriveArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_arith
  rcases cases with rfl | rfl | rfl
  · exact (keygen_deriveOutgoing_words m _ (88, 0) (by decide)).trans
      (h (88, stackArg s 0) (by simp [keygenSavedValues]))
  · exact (keygen_deriveOutgoing_words m _ (128, 8) (by decide)).trans
      (h (128, stackArg s 3) (by simp [keygenSavedValues]))
  · exact (keygen_deriveOutgoing_words m _ (136, 16) (by decide)).trans
      (h (136, stackArg s 4) (by simp [keygenSavedValues]))

theorem keygen_deriveArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.deriveArgs) t fun u =>
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧
      u.gpr .rdx = s.gpr .rcx ∧ u.gpr .rcx = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = off (randomBase s) Random.oNonce ∧
      (∀ i < 3, word u.mem (randomBase s) (8 * i) = keygenDeriveArg s i) ∧
      KeygenSaved s u.mem ∧ Outside (randomBase s) 0 24 t.mem u.mem ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (keygen_deriveArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 24 t.mem u.mem := by rw [hm]; exact keygen_deriveOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .rdi) (by simp [keygenSavedValues])),
    hsi.trans (hv (48, s.gpr .rsi) (by simp [keygenSavedValues])),
    hdx.trans (hv (64, s.gpr .rcx) (by simp [keygenSavedValues])),
    hcx.trans (hv (72, s.gpr .r8) (by simp [keygenSavedValues])),
    h8.trans (hv (80, s.gpr .r9) (by simp [keygenSavedValues])), h9,
    fun i hi => by rw [hm]; exact keygen_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr (by omega_arith)) (by omega_arith)), hf, hk⟩

def keygenDeriveRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩,
    ⟨randomBase s, 24⟩]

def keygenDeriveWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]

theorem keygen_derive_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenDeriveRd s ++ keygenDeriveWr s) (t.rd ++ t.wr) ∧ Covers (keygenDeriveWr s) t.wr := by
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_arith
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
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
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (stackArg s 0).toNat ≤ 248; omega_arith⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 24 ≤ 248; decide⟩

theorem keygen_derive_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce) :
    (Spec.Dsa.deriveKeyContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw i hi)
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide)]
  simp only [keygenDeriveArg, keygenDeriveRd, keygenDeriveWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_arith
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 208) := by
    rw [random_nonceBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩
      (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_arith)
  have sA : Region.Sub ⟨randomBase s, 24⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_arith)
  have sR := keygen_ret_sub h
  have sK := keygen_callee_sub h
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have dRA : (⟨randomBase s - 8, 8⟩ : Region).Disjoint ⟨randomBase s, 24⟩ := by
    rw [random_callBase extra s, random_frameBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have dKM : (below (randomBase s - 8) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  have dKA : (below (randomBase s - 8) extra).Disjoint ⟨randomBase s, 24⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  refine ⟨?_, by omega_arith, trivial, trivial, h.outParams, (h.stackOut.sub_left sM).symm,
    h.outScratch, (h.stackOut.sub_left sA).symm, h.paramsScratch,
    h.stackScratch.sub_left sM, (h.stackScratch.sub_left sA).symm,
    h.stackOut.sub_left sR, h.stackParams.sub_left sR, dRM, h.stackScratch.sub_left sR,
    ?_, h.outBound, h.paramsBound, by omega_arith, h.scratchBound, h.lengths, h.outLength, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_arith
  · cases extra with
    | zero => exact dRA
    | succ n => exact ⟨dRA, h.stackOut.sub_left sK, h.stackParams.sub_left sK, dKM,
        h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_arith

/-- The sampled x, as the callee reads it. -/
theorem keygen_callEntry_nonce {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_arith
  have hk := keygenStackBase_toNat h
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  exact random_callEntry_bytes hsp (dRM.symm.sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by omega_arith)

/-- The checked derivation's contract at key generation's call, once the
domain check has passed. -/
theorem keygen_derive_checked_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  refine deriveChecked_of_pre (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9) ?_
  have hE0 : stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = keygenDeriveArg s 0 :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw 0 (by decide))
  simp only [hE0, State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (r := .r8) (by decide),
    State.callEntry_gpr _ (r := .rdx) (by decide), State.callEntry_gpr _ (r := .rcx) (by decide),
    h8, hdx, hcx, keygenDeriveArg]
  rw [keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt, hparams]
  exact hc

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        res.getD (List.replicate (s.gpr .rsi).toNat 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc', hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveCheckedDepth
  have hb := v.stackBound
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw i hi)
  refine WP.call_sp_mx v.deriveCheckedVerified.1 (SpSafe.of_all v.deriveCheckedSp) (by omega_arith)
    (keygen_derive_checked_pre h hsp hw hdi hsi hdx hcx h8 h9 hparams hc) hc' hcw
    (fun u hur huw huc hf _ ⟨w, hwm, hwg, hp⟩ hmx => ?_)
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), keygenDeriveArg, hwm, hwg .rax (by decide)] at hp
  rw [show t.mem.writeW (t.gpr .rsp - 8) (t.unknowns 0) = t.callEntry.mem from rfl,
    keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt, keygen_callEntry_nonce h hsp] at hp
  refine ⟨hur, huw, huc, ?_, hp.1, hp.2, hmx⟩
  rw [hsp] at hf
  exact VG.X86_64.Frame.below_mono hf (by omega_arith) (by omega_arith)

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)]) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧ u.zf = some (t.gpr .rax == 1) ∧
      Keep [.rax] t u := by
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧
    u.zf = some (t.gpr .rax == 1)) ?_ rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]
  exact sub_beq_zero _ _

theorem keygen_keepStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block GenerateKey.keepStatus) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64) ∧
      Keep [.rax] t u := by
  refine WP.keep [.rax] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64)) ?_ rfl
  unfold GenerateKey.keepStatus
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega_using [hd'])) (by omega_using [hd'])) hk (by rw [hmx])

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 24 t.mem u.mem)
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega_using [hd])) (by omega_arith)) hk
    (by rw [hmx])

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
  simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .rsi).toNat 0))

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k)
      KeygenState h used u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat = res.getD (List.replicate (s.gpr .rsi).toNat 0) := by
  refine WP.seq (WP.mono_mx (by decide) (keygen_deriveArgs_saved ht.scr ht.sp ht.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ hmxa => ?_)
  have ha := ht.of_outgoing hargs (hka.mono (by decide)) hmxa
  have hnA : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k := by
    have hq : (stackArg s 0).toNat ≤ 32 := by
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega_using [hl]
    exact (random_outside_bytes hargs (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega_using [hq]) (Or.inr (show 0 + 24 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 ha.rd ha.wr (keygen_bytes_params ha) hc)
    fun b ⟨hbr, hbw, hbc, hf, hst, hout, hmxb⟩ => ?_)
  rw [keygen_bytes_params ha, hnA] at hst hout
  have hoF : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackOut.sub_left (keygen_frame_sub h)).symm
  have hsF : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hb, _⟩ := ha.after_call (wr := keygenDeriveWr s)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hoF
      · exact hsF)
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
    hf hbr hbw hbc hmxb
  refine WP.mono_mx (by decide) (keygen_keepStatus_ok hb.scr hb.sp) fun u ⟨hum, hku⟩ hmxu => ?_
  refine ⟨hb.write_status hum (hku.mono (by decide)) hmxu, ?_, ?_⟩
  · rw [hum, word_writeW_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using []), ← BitVec.toNat_setWidth, hst]
    exact (Nat.mod_eq_of_lt (by unfold Spec.Dsa.signStatus; split <;> decide)).symm
  · rw [hum, random_writeW_bytes _ (hoF.sep (Region.contains_self _ _)
      (Offset.contains_base (randomBase s) (d := Random.oStatus) (n := 8) (by decide) (by decide)))
      (s.gpr .rsi).isLt]
    exact hout

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation after an accepted domain: the sampler, then the derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

/-- The sampler's state once prepared and past the test of its status. -/
theorem keygen_prepared {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) :
    WP isa (.seq Random.prepare (.block [.alu .cmp .rax (.imm 0)])) t fun b =>
      b.zf = some false ∧ (∃ draws, RandomReady (keygenContextOf h t.mem hq) 0 draws b) ∧
      Keep randomVolatile t b ∧ b.mxcsr = t.mxcsr := by
  refine WP.seq (WP.mono (keygen_prepare ht hQ hq) fun a ⟨hax, ⟨draws, hra⟩, hka, hmxa⟩ => ?_)
  refine WP.mono_mx (by decide) (random_sign_test_zero (t := a)) fun b ⟨⟨hbm, hbz⟩, hkb⟩ hmxb => ?_
  have hkb' : Keep randomVolatile a b := hkb.mono (by decide)
  exact ⟨by rw [hbz, hax]; rfl, ⟨draws, hra.congr hbm hkb⟩, (hka.trans hkb').mono (by decide),
    hmxb.trans hmxa⟩

/-- The draw and its status stored: the frame state, the flag for success, and x. -/
theorem keygen_sampled {extra : Nat} {s t b : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {draws : Nat} (ht : KeygenState h 0 t)
    (hrb : RandomReady (keygenContextOf h t.mem hq) 0 draws b) (hkb : Keep randomVolatile t b)
    (hmxb : b.mxcsr = t.mxcsr) :
    WP isa (.seq Random.sample (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)])) b
      fun d =>
        KeygenState h (keygenDraw s).used d ∧
        d.zf = some (BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) == 1) ∧
        word d.mem (randomBase s) Random.oStatus =
          BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) ∧
        (∀ k, (keygenDraw s).scalar = some k →
          Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
            Spec.Dsa.encodeBE (stackArg s 0).toNat k) := by
  have hd : randomRemaining (keygenContextOf h t.mem hq) 0 128 = keygenDraw s := by
    unfold randomRemaining; rfl
  refine WP.seq (WP.mono_mx (by decide) (random_sample_encoded hq hrb)
    fun c ⟨hcax, _, _, hnonce, _, ⟨draws', hrc⟩, hkc⟩ hmxc => ?_)
  rw [hd, Nat.zero_add] at hrc
  rw [hd] at hcax hnonce
  have hkc' : Keep randomVolatile b c := hkc.mono (by decide)
  have hkt : Keep randomVolatile t c := (hkb.trans hkc').mono (by decide)
  have hsc : KeygenState h (keygenDraw s).used c :=
    ht.of_ready hrc hkt (by rw [hmxc, hmxb])
  refine WP.mono_mx (by decide) (keygen_storeStatus_ok hsc.scr hsc.sp) fun d ⟨hdm, hdz, hkd⟩ hmxd => ?_
  have hsd := hsc.write_status hdm (hkd.mono (by decide)) hmxd
  rw [hcax] at hdm hdz
  refine ⟨hsd, hdz, by rw [hdm, word_writeW_self], fun k hk => ?_⟩
  have hn := hnonce k hk
  simp only [keygenContextOf, keygen_q_length h] at hn
  have hql : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  rw [hdm]
  exact (random_outside_bytes (writeW_outside _ _ _ (by decide))
    (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hql])
    (Or.inr (by decide))).trans hn

theorem keygen_generate (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hc : keygenChecked s = true) :
    WP isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) t
      (KeygenGenerated h) := by
  have hq := keygen_q_valid h hc
  have hres := keygen_result_checked h hc
  unfold GenerateKey.generate
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_prepared ht hQ hq) fun b ⟨hbz, ⟨draws, hrb⟩, hkb, hmxb⟩ => ?_)
  refine WP.ite false (by simp only [eval, hbz]) (fun he => Bool.noConfusion he) fun _ => ?_
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_sampled ht hrb hkb hmxb) fun d ⟨hsd, hdz, hdw, hnd⟩ => ?_)
  have hlt : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (keygen_sampleStatus_le _) (by decide)
  cases hx : (keygenDraw s).scalar with
  | none =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]; split <;> decide
    refine WP.ite false (by
      simp only [eval, hdz]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      apply hs1
      have := congrArg BitVec.toNat he
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
    refine WP.ite true (by simp only [eval, hdz]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (keygen_derive_step v hsd (hnd k hx) hc) fun u ⟨hu, hw, hb⟩ => ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hu, hw, fun _ => hb⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.GenerateKeyFinish`, which only this module used -/

section

/-! # Key generation's finish: the status, the key or zeros, and the draws used -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure KeygenBodyPost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
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
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      result.key.getD (List.replicate (s.gpr .rsi).toNat 0))
    (hbound : result.status ≤ 2) (hkey : result.status ≠ 1 → result.key = none) :
    WP isa RandomSign.finish t (KeygenBodyPost s result) := by
  have houtlen : 0 < (s.gpr .rsi).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .rdx :=
    hr.saved (56, s.gpr .rdx) (by simp [keygenSavedValues])
  have hframeOut := h.stackOut.sub_left (keygen_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (keygen_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .rdi) (s.gpr .rsi).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono_mx (by decide) (random_finish_ok (B := randomBase s) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat)
    hr.scr hr.sp
    (hr.saved (40, s.gpr .rdi) (by simp [keygenSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .rsi) (by simp [keygenSavedValues]))
    houtlen (s.gpr .rsi).isLt
    (fun j hj => ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .rsi).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ hmx => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .rdx := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨(hk.gpr (by decide)).trans hr.sp, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc hn => (hkv.gpr (random_saved_not_volatile hc)).trans (hr.callee r hc hn),
    by rw [hmx]; exact hr.mxcsr, ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .rsi).isLt]
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

end VG.Proof.Dsa.X86_64

end

end


/-! # Key generation's body: entry, the domain check, generation, the finish -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_test_check {t : State} :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (((t.gpr .rax).setWidth 32).toNat == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  rw [sub_beq_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  have hz : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  rw [hz]
  constructor
  · intro he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_setWidth] at hn ⊢
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 32 ≤ 2 ^ 64))] at hn
    exact hn
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, he, Nat.zero_mod]
    rfl

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveChecked v.sq v.mul))
      (allocState Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (keygen_test_check (t := u)) fun w ⟨⟨hwm, hwz⟩, hkw⟩ hmxw => ?_)
  have hsw : KeygenState h 0 w :=
    hu.of_frame (by rw [hwm]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hwm]) (hkw.mono (by decide))
      (by rw [hmxw])
  have hword (d : Nat) (hd : d + 8 ≤ Random.frameBytes) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm]; exact hw d hd
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp only [eval, hwz, hax]; rfl) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hsw (by rw [hword _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp only [eval, hwz, hax]; rfl) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hsw (by rw [hword _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's functional correctness against its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)).all (fun i => !isa.writesSp i) = true := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.all, Bool.and_eq_true]
  repeat' constructor
  all_goals first | with_reducible exact v.parametersSp | with_reducible exact v.deriveCheckedSp | decide

theorem keygen_depth (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)).x86_64Depth ≤ v.stack + 256 := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.x86_64Depth,
    show Random.prepare.x86_64Depth = 0 from rfl,
    show Random.sample.x86_64Depth = 0 from rfl,
    show RandomSign.finish.x86_64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  have hm := Nat.max_le.mpr ⟨Nat.add_le_add_right v.parametersDepth 8, Nat.add_le_add_right v.deriveCheckedDepth 8⟩
  exact Nat.add_le_add_right hm 248

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht => ⟨ht.sp, ht.wr, fun m _ fm => ?_⟩
  -- The frame's bytes, once released, hold anything: the key and `used` lie apart from them.
  have hl := h.stackLower
  have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩
      (below (s.gpr .rsp) (v.stack + 256)) :=
    Offset.sub_below _ (by unfold Random.frameBytes; omega_using []) (by unfold Random.frameBytes; omega_using [])
  have sep : ∀ {B : Region}, (below (s.gpr .rsp) (v.stack + 256)).Disjoint B →
      ∀ q ∈ [(⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩ : Region)], B.Disjoint q :=
    fun hB q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact fun x h₁ h₂ => hB x (hR x h₂) h₁
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ?_, ?_, ?_, ht.mxcsr⟩
  · show Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = _
    rw [Proof.Rsa.rsa_bytes_frame fm (s.gpr .rsi).isLt (sep h.stackOut)]
    exact ht.output
  · show m.readW (s.gpr .rdx) 64 = _
    rw [fm.readW (r := ⟨s.gpr .rdx, 8⟩) (Region.contains_self _ _) (sep h.stackUsed) (by decide)]
    exact ht.used
  intro r hr
  by_cases he : r = .rsp
  · subst r
    change t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes = s.gpr .rsp
    rw [ht.sp, randomBase, BitVec.sub_add_cancel]
  · change (t.setReg .rsp (t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes)).gpr r = _
    simp only [State.setReg, ite_eq_right he]
    exact ht.callee r hr he

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.sq v.mul) (Generate.deriveChecked v.sq v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  refine ⟨trace, t, he, ⟨hp.callee, ?_, hp.mxcsr⟩, keygen_shared_post h hp⟩
  have hd := keygen_depth v
  have hb := v.stackBound
  have hf := Exec.stackFrame (SpSafe.of_all (keygen_sp v)) he (by omega_using [hd, hb])
  have hfb := VG.X86_64.Frame.below_mono hf hd (by omega_using [hb])
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.retOut
    · exact h.retUsed
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by omega_using [hb])

end VG.Proof.Dsa.X86_64
