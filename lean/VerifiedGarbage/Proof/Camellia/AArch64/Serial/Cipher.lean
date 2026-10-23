module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Block
public import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Proof.Camellia.CtrCipher

/-! # Relating the raw memory kernel to the existing public Camellia cipher -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64

theorem cryptWords_congr (g : Nat) (hg : g = 3 ∨ g = 4)
    (E F : Nat → BitVec 64) (m : BitVec 128)
    (h : ∀ i < 8*g+2, E i = F i) :
    VG.Proof.Camellia.cryptWords g E m = VG.Proof.Camellia.cryptWords g F m := by
  rcases hg with rfl | rfl
  · simp only [VG.Proof.Camellia.cryptWords,VG.Proof.Camellia.groups,
      VG.Proof.Camellia.group,VG.Proof.Camellia.pair,List.range_succ,List.range_zero,
      List.foldl_append,List.foldl_cons,List.foldl_nil,List.nil_append,
      Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]
    simp only [h 0 (by decide),
      h 1 (by decide),
      h 2 (by decide),
      h 3 (by decide),
      h 4 (by decide),
      h 5 (by decide),
      h 6 (by decide),
      h 7 (by decide),
      h 8 (by decide),
      h 9 (by decide),
      h 10 (by decide),
      h 11 (by decide),
      h 12 (by decide),
      h 13 (by decide),
      h 14 (by decide),
      h 15 (by decide),
      h 16 (by decide),
      h 17 (by decide),
      h 18 (by decide),
      h 19 (by decide),
      h 20 (by decide),
      h 21 (by decide),
      h 22 (by decide),
      h 23 (by decide),
      h 24 (by decide),
      h 25 (by decide)]
  · simp only [VG.Proof.Camellia.cryptWords,VG.Proof.Camellia.groups,
      VG.Proof.Camellia.group,VG.Proof.Camellia.pair,List.range_succ,List.range_zero,
      List.foldl_append,List.foldl_cons,List.foldl_nil,List.nil_append,
      Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]
    simp only [h 0 (by decide),
      h 1 (by decide),
      h 2 (by decide),
      h 3 (by decide),
      h 4 (by decide),
      h 5 (by decide),
      h 6 (by decide),
      h 7 (by decide),
      h 8 (by decide),
      h 9 (by decide),
      h 10 (by decide),
      h 11 (by decide),
      h 12 (by decide),
      h 13 (by decide),
      h 14 (by decide),
      h 15 (by decide),
      h 16 (by decide),
      h 17 (by decide),
      h 18 (by decide),
      h 19 (by decide),
      h 20 (by decide),
      h 21 (by decide),
      h 22 (by decide),
      h 23 (by decide),
      h 24 (by decide),
      h 25 (by decide),
      h 26 (by decide),
      h 27 (by decide),
      h 28 (by decide),
      h 29 (by decide),
      h 30 (by decide),
      h 31 (by decide),
      h 32 (by decide),
      h 33 (by decide)]

theorem cipher_eq_words {s : State} {B : Addr} {k : Nat × List (BitVec 64)}
    (hb : s.gpr .x5 = B) (h : Ready s.mem B k) :
    Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
      (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) =
    (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (k.1/6) (keyWord s)
      (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (B+BitVec.ofNat 64 768))))).toList := by
  rw [VG.Proof.Camellia.cipher_bytes h.rounds]
  apply congrArg (fun x : BitVec 128 => (Spec.Camellia.encodeBlock x).toList)
  apply cryptWords_congr _ (by rcases h.rounds with hr | hr <;> simp [hr])
  intro i hi
  rw [keyWord,hb,readBE,h.keys i (by simpa only [Spec.Camellia.scheduleLength] using hi)]

end VG.Proof.Camellia.AArch64.Serial
