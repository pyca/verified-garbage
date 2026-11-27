module

public import VerifiedGarbage.Proof.Dsa.X86.OutputCall
public import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall

/-! ### `Dsa.X86.VerifyLayout`, which the modules that import this one used -/

section

/-! # Public call layout obtained from installed verification arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def verifyInputs (pLen qLen digestLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen),
    (.input .signature, qLen), (.signatureS, qLen), (.input .digest, digestLen)]

def verifyPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 0
  | .input .q => arg s 0 + arg s 2
  | .input .g => arg s 0 + arg s 2 + arg s 3
  | .input .y => arg s 0 + arg s 2 + arg s 3 + arg s 2
  | .input .signature => arg s 4
  | .signatureS => arg s 4 + arg s 3
  | .input .digest => arg s 6
  | _ => 0

def verifyKey (s : State) : Spec.Dsa.Key := Spec.Dsa.publicKeyBytes (arg s 2).toNat (arg s 3).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

def verifyLayout (s : State) (A : VerifyingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 8
  size := (arg s 9).toNat * 8
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  p := (verifyKey s).params.p
  q := (verifyKey s).params.q
  widths := A.lengths
  extent := A.used
  inputs := verifyInputs (arg s 2).toNat (arg s 3).toNat (arg s 7).toNat
  pointers := verifyPointers s
  stable := by
    intro input hi
    simp only [verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 7).toNat (Spec.Dsa.bitLength (verifyKey s).params.q / 8)

theorem verifyInputs_shape (pLen qLen digestLen : Nat) :
    ∀ input ∈ verifyInputs pLen qLen digestLen, ShapePointer input.1 := by
  intro input hi
  simp only [verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem verifyingInstalled_ready {s t : State} (A : VerifyingABI s)
    (I : Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s t) :
    ShapeCallReady (verifyLayout s A) (arg s 7).toNat t := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (0, .p) ∈ Entry.verifyArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Sig, _⟩ := I.input (by decide : (4, .signature) ∈ Entry.verifyArguments) A.signatureBound
    (by rw [A.rd, A.wr]; simp) A.signatureScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowSignature.symm)
  obtain ⟨D, _⟩ := I.input (by decide : (6, .digest) ∈ Entry.verifyArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, KeyValue⟩ := publicKey_buffers Key L.1 L.2 (by have := A.keyLength; omega_using [this]) KeyBytes Qptr Gptr Yptr
  have Sptr : pointerValue (argumentPointer s 8) t .signatureS =
      pointerValue (argumentPointer s 8) t (.input .signature) + BitVec.ofNat 32 (arg s 3).toNat := by
    change pointerValue (argumentPointer s 8) t (.input .signature) + pointerValue (argumentPointer s 8) t (.input .qLen) = _
    rw [I.arguments (3, .qLen) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have S := Sig.slice L.2 (by have := A.signatureLength; omega_using [this]) Sptr
  have R := Sig.prefix (by have := A.signatureLength; omega_using [this] : (arg s 3).toNat ≤ (arg s 5).toNat)
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_, congrArg BitVec.toNat (I.arguments (7, .digestLen) (by decide))⟩
  · intro input hi
    simp only [verifyLayout, verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact Y
    · exact R
    · exact S
    · exact D
  · intro input hi
    simp only [verifyLayout, verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact I.arguments (0, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.yPointer
    · exact I.arguments (4, .signature) (by decide)
    · change pointerValue (argumentPointer s 8) t (.input .signature) + pointerValue (argumentPointer s 8) t (.input .qLen) = _
      rw [I.arguments (4, .signature) (by decide), I.arguments (3, .qLen) (by decide)]
      rfl
    · exact I.arguments (6, .digest) (by decide)
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.p) KeyValue).symm
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.q) KeyValue).symm

end VG.Proof.Dsa.X86

end

end

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
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
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
    (by have := A.keyLength; omega_using [this]) KeyBytes Qptr Gptr Yptr Xptr
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
    omega_arith
  · intro e k he
    change e + k ≤ 2 * (arg s 6).toNat at he
    rw [I.keeps.2.2, A.wr]
    refine ⟨_, List.mem_cons_self, Offset.contains_base _ ?_ ?_⟩
    · have := A.outLength; exact Nat.le_trans he (by omega_using [this])
    · have := A.outBound; have := A.outLength; omega_using [he]
  · change Region.Disjoint _ ⟨argumentPointer s 0, 2 * (arg s 6).toNat⟩
    rw [← A.outLength]
    exact A.outScratch.symm

end VG.Proof.Dsa.X86
