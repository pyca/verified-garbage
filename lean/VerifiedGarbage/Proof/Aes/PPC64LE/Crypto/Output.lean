module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Batch
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the batch proof is instantiated against the ECB and GCM specifications here.
/-! # POWER8 AES batch results -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (counterBase)

def inputState (ctr : Bool) (icb : Spec.Gcm.Block) (m : Mem) (D : Addr) (i : Nat) : Spec.Aes.State :=
  if ctr then aesState (Nat.repeat Spec.Gcm.inc32 i icb)
  else Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16*i))

def outputState (inverse ctr : Bool) (nr : Nat) (w : List Byte) (icb : Spec.Gcm.Block)
    (m : Mem) (D : Addr) (i : Nat) : Spec.Aes.State :=
  if ctr then aesState (Spec.Gcm.aesWith nr w (Nat.repeat Spec.Gcm.inc32 i icb) ^^^
    Spec.Gcm.blockAt m (D + BitVec.ofNat 64 (16*i)))
  else result inverse nr w (inputState false icb m D i)

theorem counter_readValue (s : State) (icb : Spec.Gcm.Block) (k i : Nat)
    (hb : (s.vpr counterBase).extractLsb' 32 96 = icb.extractLsb' 32 96)
    (hw : (s.gpr .r8).setWidth 32 = icb.extractLsb' 0 32 + BitVec.ofNat 32 k) :
    readValue true s i = Nat.repeat Spec.Gcm.inc32 (k+i) icb := by
  simp only [readValue, ite_true, hb]
  change icb.extractLsb' 32 96 ++ (s.gpr .r8 + BitVec.ofNat 64 i).setWidth 32 = _
  rw [BitVec.setWidth_add _ _ (by decide), hw, BitVec.setWidth_ofNat_of_le (by decide),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    ← VG.Proof.Aes.repeat_inc32_hi icb (k+i), ← VG.Proof.Aes.repeat_inc32_lo icb (k+i),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide), BitVec.extractLsb'_eq_self]

theorem original_blockAt {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : Processed m₀ m D n k F) (hj : k ≤ j) (hjn : j < n) :
    Spec.Gcm.blockAt m (D + BitVec.ofNat 64 (16*j)) =
      Spec.Gcm.blockAt m₀ (D + BitVec.ofNat 64 (16*j)) := by
  apply aesState_inj
  rw [aesState_blockAt, aesState_blockAt]
  exact h.original hj hjn

theorem input_state (ctr : Bool) (s : State) (icb : Spec.Gcm.Block) {m₀ : Mem} {D : Addr}
    {n k N : Nat} {F : Nat → Spec.Aes.State} (hkn : k+N ≤ n)
    (hptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*k)) (hp : Processed m₀ s.mem D n k F)
    (hb : ctr = true → (s.vpr counterBase).extractLsb' 32 96 = icb.extractLsb' 32 96)
    (hw : ctr = true → (s.gpr .r8).setWidth 32 = icb.extractLsb' 0 32 + BitVec.ofNat 32 k)
    {i : Nat} (hi : i < N) :
    aesState (readValue ctr s i) = inputState ctr icb m₀ D (k+i) := by
  cases ctr
  · simp only [readValue, inputState, Bool.false_eq_true, ite_false, hptr, Offset.add_add, load_state]
    rw [show 16*k+16*i = 16*(k+i) by omega]
    exact hp.original (by omega) (by omega)
  · rw [counter_readValue s icb k i (hb rfl) (hw rfl)]
    simp only [inputState, ite_true]

theorem output_state (inverse ctr : Bool) (nr : Nat) (w : List Byte) (icb : Spec.Gcm.Block)
    {m₀ m : Mem} {D : Addr} {n j : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hj : j < n) (hp : Processed m₀ m D n j F)
    (hinv : ctr = true → inverse = false)
    (hv : aesState v = result inverse nr w (inputState ctr icb m₀ D j)) :
    aesState (outputAt ctr v m (D + BitVec.ofNat 64 (16*j))) = outputState inverse ctr nr w icb m₀ D j := by
  cases ctr
  · simpa only [outputAt, outputState, Bool.false_eq_true, ite_false] using hv
  · have hv' : v = Spec.Gcm.aesWith nr w (Nat.repeat Spec.Gcm.inc32 j icb) := by
      apply aesState_inj
      rw [hv, hinv rfl]
      simp only [result, Bool.false_eq_true, ite_false, inputState, ite_true, aesState_aesWith]
    simp only [outputAt, outputState, ite_true]
    rw [hv', read_blockAt, original_blockAt hp (Nat.le_refl _) hj]

end VG.Proof.Aes.PPC64LE.Crypto
