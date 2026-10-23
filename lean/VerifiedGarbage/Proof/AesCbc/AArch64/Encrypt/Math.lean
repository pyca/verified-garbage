module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
import VerifiedGarbage.Proof.Cmac.Spec

/-! The indexed ciphertext chain is the existing CBC encryption specification. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Proof.AesCbc.AArch64.Decrypt (vector_listD)

/-- A vector state encoded in the ISA's byte order. -/
def pack (x : Spec.Aes.State) : BitVec 128 := ofVBytes (fun i => x.getD i 0)

theorem st_pack (x : Spec.Aes.State) : st (pack x)=x := by
  apply st_ext
  intro i hi
  rw [getD_st _ hi,pack,vbyte_ofVBytes _ hi]

def chain (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => pack (Spec.Aes.cipher (R s₀) (wK s₀)
      (st (s₀.mem.readW (blk s₀ k) 128 ^^^ chain s₀ k)))

def input (s₀ : State) (k : Nat) : BitVec 128 := s₀.mem.readW (blk s₀ k) 128 ^^^ chain s₀ k

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Spec.Aes.cipher (R s₀) (wK s₀) (st (input s₀ k))

theorem chain_succ (s₀ : State) (k : Nat) : chain s₀ (k+1)=pack (output s₀ k) := rfl

theorem cipher_bytes (nr : Nat) (w : List Byte) (p q : BitVec 128) :
    (Spec.Aes.cipher nr w (st (p ^^^ q))).toList =
      Spec.Cbc.aesWith nr w (Spec.Cbc.xor (st p).toList (st q).toList) := by
  unfold Spec.Cbc.aesWith
  apply congrArg Vector.toList
  apply congrArg (Spec.Aes.cipher nr w)
  apply st_ext
  intro i hi
  rw [getD_st _ hi,vbyte_xor,getD_ofFn hi,xor_eq,Proof.Cmac.getD_xor (by simp) (by simpa using hi)]
  rw [vector_listD _ _ hi,vector_listD _ _ hi,getD_st _ hi,getD_st _ hi]

theorem chain_blocks (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    outK (cbcMode true) s₀ k = (List.range k).map (fun j => (output s₀ j).toList) ∧
      chainK (cbcMode true) s₀ k = (st (chain s₀ k)).toList := by
  induction k with
  | zero =>
    constructor
    · change ([] : List (List Byte))=[]
      rfl
    · change Spec.Aes.bytesAt s₀.mem (Iv s₀) 16=(st (s₀.mem.readW (Iv s₀) 128)).toList
      rw [st_readW]
      exact bytesAt_toList _ _
  | succ k ih =>
    obtain ⟨hout,hchain⟩ := ih (by omega)
    have ht := take_succ_blks s₀ (k:=k) (by omega)
    have hnew : Spec.Cbc.aesWith (R s₀) (wK s₀)
        (Spec.Cbc.xor ((blks s₀)[k]'(by rw [length_blocksAt]; omega))
          (chainK (cbcMode true) s₀ k))=(output s₀ k).toList := by
      rw [hchain,getElem_blocksAt (hk:=by omega),bytesAt_toList,←st_readW,←cipher_bytes]
      rfl
    have hstep : outK (cbcMode true) s₀ (k+1)=
        outK (cbcMode true) s₀ k ++ [(output s₀ k).toList] := by
      change Spec.Cbc.encrypt _ _ _ = _
      rw [ht,encrypt_snoc]
      exact congrArg (fun x => outK (cbcMode true) s₀ k ++ [x]) hnew
    constructor
    · rw [hstep,hout,List.range_succ,List.map_append]; rfl
    · change Spec.Cbc.next _ (outK (cbcMode true) s₀ (k+1))=_
      rw [hstep,next_snoc,chain_succ,st_pack]
end VG.Proof.AesCbc.AArch64.Encrypt
