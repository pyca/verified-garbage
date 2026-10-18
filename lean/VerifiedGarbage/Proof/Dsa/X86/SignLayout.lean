module

public import VerifiedGarbage.Proof.Dsa.X86.OutputCall
public import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
public import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers

/-! # Public call layout obtained from installed signing arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def signInputs (pLen qLen digestLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen),
    (.input .x, qLen), (.input .nonce, qLen), (.input .digest, digestLen)]

def signPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 2
  | .input .q => arg s 2 + arg s 4
  | .input .g => arg s 2 + arg s 4 + arg s 6
  | .input .y => arg s 2 + arg s 4 + arg s 6 + arg s 4
  | .input .x => arg s 2 + arg s 4 + arg s 6 + arg s 4 + arg s 4
  | .input .nonce => arg s 5
  | .input .digest => arg s 7
  | _ => 0

def signKey (s : State) : Spec.Dsa.Key := Spec.Dsa.publicKeyBytes (arg s 4).toNat (arg s 6).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

def signLayout (s : State) (A : SigningABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 9
  size := (arg s 10).toNat * 8
  pLen := (arg s 4).toNat
  qLen := (arg s 6).toNat
  p := (signKey s).params.p
  q := (signKey s).params.q
  widths := A.lengths
  extent := A.used
  inputs := signInputs (arg s 4).toNat (arg s 6).toNat (arg s 8).toNat
  pointers := signPointers s
  stable := by
    intro input hi
    simp only [signInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 8).toNat (Spec.Dsa.bitLength (signKey s).params.q / 8)

theorem signInputs_shape (pLen qLen digestLen : Nat) :
    ∀ input ∈ signInputs pLen qLen digestLen, ShapePointer input.1 := by
  intro input hi
  simp only [signInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem signingInstalled_ready {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t) :
    ShapeCallReady (signLayout s A) (arg s 8).toNat t := by
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (2, .p) ∈ Entry.signArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Nonce, _⟩ := I.input (by decide : (5, .nonce) ∈ Entry.signArguments) A.nonceBound
    (by rw [A.rd, A.wr]; simp) A.nonceScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowNonce.symm)
  obtain ⟨D, _⟩ := I.input (by decide : (7, .digest) ∈ Entry.signArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, KeyValue⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr Xptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_, congrArg BitVec.toNat (I.arguments (8, .digestLen) (by decide))⟩
  · intro input hi
    simp only [signLayout, signInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact Y
    · exact X
    · exact Nonce
    · exact D
  · intro input hi
    simp only [signLayout, signInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact I.arguments (2, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.yPointer
    · exact I.xPointer
    · exact I.arguments (5, .nonce) (by decide)
    · exact I.arguments (7, .digest) (by decide)
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.p) KeyValue).symm
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.q) KeyValue).symm

theorem signingInstalled_output {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t) :
    OutputCallReady (signLayout s A) (arg s 0) t := by
  refine ⟨I.scr, I.arguments (0, .out) (by decide), ?_, ?_, ?_, ?_⟩
  · simpa only [signLayout, BitVec.ofNat_toNat, BitVec.setWidth_eq] using I.arguments (6, .qLen) (by decide)
  · have := A.outBound; have := A.outLength
    change (arg s 0).toNat + 2 * (arg s 6).toNat ≤ 2 ^ 32
    omega
  · intro e k he
    change e + k ≤ 2 * (arg s 6).toNat at he
    rw [I.keeps.2.2, A.wr]
    refine ⟨_, List.mem_cons_self, Offset.contains_base _ ?_ ?_⟩
    · have := A.outLength; exact Nat.le_trans he (by omega)
    · have := A.outBound; have := A.outLength; omega
  · change Region.Disjoint _ ⟨argumentPointer s 0, 2 * (arg s 6).toNat⟩
    rw [← A.outLength]
    exact A.outScratch.symm

end VG.Proof.Dsa.X86
