module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesCbc.AArch64.Encrypt.Rounds`, which only this module used -/

section

/-! CBC's preloaded AESE operand and the unchanged AES rounds. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

abbrev chainRegs : List VReg := [.v31]
theorem chain_regs : BlockRegs chainRegs := ⟨by decide,by decide⟩

theorem rounds_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) {j : Nat} (hI : RInv chainRegs w x j s) :
    ∀ count, j+count+1 ≤ nr →
      WP isa (.block (Impl.AesCbc.AArch64.Encrypt.rounds j count)) s fun t =>
        RInv chainRegs w x (j+count) t ∧ VFrame chainRegs s t
  | 0, _ => by simpa [Impl.AesCbc.AArch64.Encrypt.rounds] using WP.block_nil ⟨hI,VFrame.refl chainRegs s⟩
  | count+1, hc => by
    rw [Impl.AesCbc.AArch64.Encrypt.rounds,List.range_succ,List.flatMap_append,WP.block_append_iff]
    refine WP.mono (rounds_ok hK hI count (by omega_using [hc])) fun t ⟨hi,hf⟩ => ?_
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.round_ok chain_regs (j:=j+count) (by omega_using [hc]) (hK.of_frame hf chain_regs) hi)
      fun u ⟨hi',hf'⟩ => ⟨by simpa only [Nat.add_assoc] using hi',hf.trans hf'⟩

theorem first_ok {nr : Nat} {w : List Byte} {s : State} (hK : Keys nr w s)
    (input : BitVec 128) (h : s.v .v31 ^^^ s.v .v0=input ^^^ s.v .v16) :
    WP isa (.block Impl.AesCbc.AArch64.Encrypt.first) s fun t =>
      RInv chainRegs w (fun _ => st input) 1 t ∧ VFrame chainRegs s t := by
  let value := aesMixColumns (aesMapBytes aesSbox (aesShiftRows (s.v .v31 ^^^ s.v .v0)))
  have he : runBlock isa Impl.AesCbc.AArch64.Encrypt.first s=some (s.setV .v31 value) := by
    simp only [Impl.AesCbc.AArch64.Encrypt.first,runBlock_cons,runStep_some,runBlock_nil,
      isa,exec,VOp.eval,Option.map_some,setV_v_self]
    exact congrArg some (setV_setV s .v31 _ _)
  refine WP.of_runBlock ⟨_,he,?_,?_⟩
  · intro b hb
    have hb' : b=.v31 := List.mem_singleton.mp hb
    subst hb'
    simp only [setV_v_self,value,h]
    exact round_st (hK.full 0 (by have := hK.rounds; omega_using [this])) (rnds_zero w (st input)).symm
  · exact ⟨rfl,rfl,rfl,rfl,rfl,fun r hr => setV_v_of_ne s _ (Ne.symm (fun he => hr (by simpa only [chainRegs,List.mem_singleton] using he.symm)))⟩

def lastValue (v k : BitVec 128) : BitVec 128 := aesMapBytes aesSbox (aesShiftRows (v ^^^ k))

theorem last_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv chainRegs w x (nr-1) s) :
    WP isa (.block [.vop (.aese .v31 .v29)]) s fun t =>
      st (t.v .v31 ^^^ t.v .v30)=Spec.Aes.cipher nr w (x .v31) ∧ VFrame chainRegs s t := by
  refine WP.of_runBlock ⟨s.setV .v31 (lastValue (s.v .v31) (s.v .v29)),?_,?_,?_⟩
  · simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some]
    rfl
  · simp only [setV_v_self,setV_v_of_ne _ _ (by decide : VReg.v30≠.v31),lastValue]
    exact last_st hK.k29 hK.k30 (hI .v31 (by simp [chainRegs]))
  · exact ⟨rfl,rfl,rfl,rfl,rfl,fun r hr => setV_v_of_ne s _ (Ne.symm (fun he => hr (by simpa only [chainRegs,List.mem_singleton] using he.symm)))⟩
end VG.Proof.AesCbc.AArch64.Encrypt

end

end

/-! ### `AesCbc.AArch64.Encrypt.Math`, which only this module used -/

section

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
    obtain ⟨hout,hchain⟩ := ih (by omega_using [hk])
    have ht := take_succ_blks s₀ (k:=k) (by omega_using [hk])
    have hnew : Spec.Cbc.aesWith (R s₀) (wK s₀)
        (Spec.Cbc.xor ((blks s₀)[k]'(by rw [length_blocksAt]; omega_using [hk]))
          (chainK (cbcMode true) s₀ k))=(output s₀ k).toList := by
      rw [hchain,getElem_blocksAt (hk:=by omega_using [hk]),bytesAt_toList,←st_readW,←cipher_bytes]
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

end

end


/-! The resident keys, the incomplete final XOR, and the preloaded next plaintext. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

abbrev live : List VReg := [.v0,.v1,.v31]
theorem live_regs : BlockRegs live := ⟨by decide,by decide⟩

structure Env (s₀ s : State) : Prop where
  keys : Keys (R s₀) (wK s₀) s
  folded : s.v .v7=s.v .v16 ^^^ s.v .v30
  iv : s.gpr .x11=Iv s₀
  frame : Frame [dataR s₀] s₀.mem s.mem
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr

theorem Env.transfer {s₀ s t : State} (h : Env s₀ s)
    (hv : ∀ r,r ∉ live → t.v r=s.v r) (h6 : t.gpr .x6=s.gpr .x6)
    (h7 : t.gpr .x7=s.gpr .x7) (h11 : t.gpr .x11=s.gpr .x11)
    (hm : t.mem=s.mem) (hrd : t.rd=s.rd) (hwr : t.wr=s.wr) : Env s₀ t := by
  refine ⟨h.keys.of_v live_regs hv h6 h7,?_,h11.trans h.iv,?_,hrd.trans h.rd,hwr.trans h.wr⟩
  · rw [hv _ (by decide),hv _ (by decide),hv _ (by decide),h.folded]
  · rw [hm]; exact h.frame

theorem Env.vframe {s₀ s t : State} (h : Env s₀ s) {rs : List VReg}
    (hf : VFrame rs s t) (hr : ∀ r ∈ rs,r ∈ live) : Env s₀ t :=
  h.transfer (fun r h => hf.v r (fun hm => h (hr r hm)))
    (congrFun hf.gpr _) (congrFun hf.gpr _) (congrFun hf.gpr _) hf.mem hf.rd hf.wr

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ N s₀
  env : Env s₀ s
  ptr : s.gpr .x2=blk s₀ k
  count : s.gpr .x3=BitVec.ofNat 64 (N s₀-k)
  chain : s.v .v31 ^^^ s.v .v30=chain s₀ k
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀)
  ready : k < N s₀ → s.v .v0=s₀.mem.readW (blk s₀ k) 128 ^^^ s.v .v7

theorem st_inj {p q : BitVec 128} (h : st p=st q) : p=q := by
  apply ext_vbyte
  intro i hi
  have hh := congrArg (fun x : Spec.Aes.State => x.getD i 0) h
  simpa only [getD_st _ hi] using hh

theorem value_pack {v : BitVec 128} {x : Spec.Aes.State} (h : st v=x) : v=pack x :=
  st_inj (h.trans (st_pack x).symm)

theorem original_read {s₀ s : State} {k j : Nat}
    (hi : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀))
    (hkj : k ≤ j) (hj : j < N s₀) : s.mem.readW (blk s₀ j) 128=s₀.mem.readW (blk s₀ j) 128 := by
  apply st_inj
  rw [st_readW,st_readW]
  exact ecbInv_orig hi hkj hj
end VG.Proof.AesCbc.AArch64.Encrypt
