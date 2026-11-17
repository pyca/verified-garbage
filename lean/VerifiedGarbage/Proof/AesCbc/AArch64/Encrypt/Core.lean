module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks

/-! ### `AesCbc.AArch64.Encrypt.State`, which this module and modules that import it used -/

section

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

end

end

/-! ### `AesCbc.AArch64.Encrypt.Load`, which only this module used -/

section

/-! Read-only lookahead and fixed entry padding. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

def loaded (s : State) (off : Nat) : State :=
  s.setV .v0 (s.mem.readW (s.gpr .x2+BitVec.ofNat 64 off) 128 ^^^ s.v .v7)

theorem load_ok (s : State) (off : Nat) (ho : off%16=0 ∧ off<65536)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa (.block [.ldrq .v0 .x2 off,.vop (.logic .eor .v0 .v0 .v7)]) s fun t =>
      t=loaded s off := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrq ho ha,?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,isa,exec,VOp.eval,Option.map_some,
    setV_v_self,setV_v_of_ne _ _ (by decide : VReg.v7≠.v0)]
  exact ⟨_,rfl,by rw [setV_setV]; rfl⟩

theorem loaded_frame (s : State) (off : Nat) : VFrame [.v0] s (loaded s off) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  exact setV_v_of_ne _ _ (Ne.symm (fun h => hr (by simpa only [List.mem_singleton] using h.symm)))

theorem padding_ok (s : State) (n : Nat) :
    WP isa (.block (List.replicate n (Instr.movz .x .x12 0 0))) s fun t =>
      t.mem=s.mem ∧ t.v=s.v ∧ (∀ r,r≠.x12 → t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨rfl,rfl,fun _ _ => rfl,rfl,rfl⟩
  | succ n ih =>
    rw [List.replicate_succ,WP.block_cons_iff]
    have he : exec (.movz .x .x12 0 0) s=some (s.write .x .x12 0) := by
      simp only [exec,show 16*0 < Size.x.bits by decide,ite_true]
      rfl
    refine ⟨_,he,WP.mono (ih (s.write .x .x12 0)) fun t ⟨hm,hv,hg,hr,hw⟩ => ?_⟩
    exact ⟨hm,hv,fun r hr => (hg r hr).trans (gpr_write_of_ne _ _ _ hr),hr,hw⟩

theorem entry_ok {s₀ s : State} (hp : UPre s₀) (hk : 0 < N s₀)
    (hE : Env s₀ s) (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4)
    (hch : s.v .v31 ^^^ s.v .v30=chain s₀ 0) (hm : s.mem=s₀.mem) :
    WP isa (.block (Impl.AesCbc.AArch64.Encrypt.enter (R s₀))) s (Inv s₀ 0) := by
  rw [Impl.AesCbc.AArch64.Encrypt.enter]
  rw [show ([Instr.ldrq .v0 .x2 0,.vop (.logic .eor .v0 .v0 .v7),.align 5] : List Instr)=
    [.ldrq .v0 .x2 0,.vop (.logic .eor .v0 .v0 .v7)]++[.align 5] from rfl,
    List.append_assoc,WP.block_append_iff]
  refine WP.mono (load_ok s 0 (by decide) (by
    rw [h2,BitVec.add_zero,hE.wr,hp.wr]
    exact ⟨dataR s₀,List.mem_append_right _ (by simp),by simpa only [BitVec.add_zero] using Offset.contains_base (Dp s₀) (d:=0) (n:=16) (k:=16*N s₀) (by omega_using [hk]) (by have := hp.data_wrap; omega_using [])⟩))
    fun t ht => ?_
  subst ht
  simp only [List.singleton_append]
  rw [WP.block_cons_iff]
  refine ⟨_,rfl,WP.mono (padding_ok _ _) fun u ⟨um,uv,ug,ur,uw⟩ => ?_⟩
  have lf := loaded_frame s 0
  have E₁ := hE.vframe lf (by decide)
  have E₂ := E₁.transfer (fun _ _ => congrFun uv _) (ug _ (by decide)) (ug _ (by decide))
    (ug _ (by decide)) um ur uw
  refine ⟨Nat.zero_le _,E₂,?_,?_,?_,?_,?_⟩
  · exact (ug _ (by decide)).trans (by simpa only [loaded,State.setV,blk,Nat.mul_zero,BitVec.add_zero] using h2)
  · rw [ug _ (by decide)]
    exact (by simpa only [loaded,State.setV,Nat.sub_zero] using h3.trans (x4_ofNat s₀))
  · rw [uv]; exact hch
  · intro i hi; rw [um]; change s.mem _=_; rw [hm]; rfl
  · intro _
    rw [uv]
    simp only [loaded,State.setV,reduceCtorEq,ite_true,ite_false,
      blk,Nat.mul_zero,BitVec.add_zero,h2,hm]
end VG.Proof.AesCbc.AArch64.Encrypt

end

end


/-! Stream state between the early count update and the delayed store. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese
open VG.AArch64.RegUpd

structure Core (s₀ : State) (k j : Nat) (s : State) : Prop where
  env : Env s₀ s
  ptr : s.gpr .x2=blk s₀ k
  count : s.gpr .x3=BitVec.ofNat 64 (N s₀-j)
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) k (output s₀)

theorem Inv.core {s₀ s : State} {k : Nat} (h : Inv s₀ k s) : Core s₀ k k s :=
  ⟨h.env,h.ptr,h.count,h.data⟩

theorem Core.vframe {s₀ s t : State} {k j : Nat} {rs : List VReg}
    (h : Core s₀ k j s) (hf : VFrame rs s t) (hr : ∀ r ∈ rs,r ∈ live) : Core s₀ k j t :=
  ⟨h.env.vframe hf hr,by rw [hf.gpr]; exact h.ptr,by rw [hf.gpr]; exact h.count,by rw [hf.mem]; exact h.data⟩

theorem dec_ok {s₀ s : State} {k : Nat} (hk : k < N s₀) (h : Core s₀ k k s) :
    WP isa (.block [.subImm .x .x3 .x3 1]) s fun t => Core s₀ k (k+1) t ∧ t.v=s.v := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm:=1) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨h.env.transfer (fun _ _ => rfl) (gpr_write_of_ne _ _ _ (by decide)) (gpr_write_of_ne _ _ _ (by decide))
      (gpr_write_of_ne _ _ _ (by decide)) rfl rfl rfl,
    by simpa only [gpr_write_of_ne _ _ _ (by decide : Reg.x2≠.x3)] using h.ptr,?_,h.data⟩,rfl⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,ite_true,h.count]
  rw [Offset.ofNat_sub_ofNat (by omega_using [hk]),show N s₀-k-1=N s₀-(k+1) by omega_using []]

theorem first4_ok {s₀ s : State} {k : Nat} (hp : UPre s₀) (hk : k < N s₀)
    (hi : Inv s₀ k s) :
    WP isa (.block (Impl.AesCbc.AArch64.Encrypt.first ++ ([.subImm .x .x3 .x3 1] : List Instr) ++
      Impl.AesCbc.AArch64.Encrypt.rounds 1 4)) s fun t =>
      Core s₀ k (k+1) t ∧ RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 5 t := by
  rw [List.append_assoc,WP.block_append_iff]
  have heq : s.v .v31 ^^^ s.v .v0=input s₀ k ^^^ s.v .v16 := by
    rw [hi.ready hk,hi.env.folded]
    unfold input
    rw [←hi.chain]
    have swap (a b c : BitVec 128) : a ^^^ (b ^^^ c)=b ^^^ (a ^^^ c) := by
      rw [←BitVec.xor_assoc,BitVec.xor_comm a b,BitVec.xor_assoc]
    simp only [BitVec.xor_comm,swap]
  refine WP.mono (first_ok hi.env.keys (input s₀ k) heq) fun s₁ ⟨i₁,f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dec_ok hk (hi.core.vframe f₁ (by decide))) fun s₂ ⟨c₂,v₂⟩ => ?_
  have i₂ : RInv chainRegs (wK s₀) (fun _ => st (input s₀ k)) 1 s₂ := by rw [RInv,v₂]; exact i₁
  exact WP.mono (rounds_ok c₂.env.keys i₂ 4 (by have := hp.rounds; omega_using [this]))
    fun t ⟨it,ft⟩ => ⟨c₂.vframe ft (by decide),it⟩
end VG.Proof.AesCbc.AArch64.Encrypt
