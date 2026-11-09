module

import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Block
import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Proof.Camellia.CtrCipher
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Rounds
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State

/-! # Relating the raw memory kernel to the existing public Camellia cipher -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64

theorem cipher_eq_words {s : State} {B : Addr} {k : Nat × List (BitVec 64)}
    (hb : s.gpr .x5 = B) (h : Ready s.mem B k) :
    Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
      (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) =
    (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (k.1/6) (keyWord s)
      (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (B+BitVec.ofNat 64 768))))).toList := by
  rw [VG.Proof.Camellia.cipher_bytes h.rounds]
  apply congrArg (fun x : BitVec 128 => (Spec.Camellia.encodeBlock x).toList)
  apply VG.Proof.Camellia.Serial.cryptWords_congr _ (by rcases h.rounds with hr | hr <;> simp [hr])
  intro i hi
  rw [keyWord,hb,readBE,h.keys i (by simpa only [Spec.Camellia.scheduleLength] using hi)]

end VG.Proof.Camellia.AArch64.Serial
