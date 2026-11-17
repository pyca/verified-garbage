module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RegionsSub

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

theorem keygen_frame_ok {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {body : Prog isa} {Q : State → Prop}
    (hb : WP isa body (allocState Random.frameBytes s) fun t =>
      t.gpr .rsp = randomBase s ∧ t.wr = (allocState Random.frameBytes s).wr ∧ Q (randomFreed t)) :
    WP isa (.frame (.alloc Random.frameBytes) body (.free Random.frameBytes)) s Q := by
  obtain ⟨trace, t, he, htsp, htwr, hq⟩ := hb
  have hl := h.stackLower
  have ha : isa.push (.alloc Random.frameBytes) s = some (allocState Random.frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega_using [hl]⟩
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
