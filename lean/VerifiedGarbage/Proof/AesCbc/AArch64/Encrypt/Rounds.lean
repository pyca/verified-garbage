module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
    refine WP.mono (rounds_ok hK hI count (by omega)) fun t ⟨hi,hf⟩ => ?_
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.round_ok chain_regs (j:=j+count) (by omega) (hK.of_frame hf chain_regs) hi)
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
    exact round_st (hK.full 0 (by have := hK.rounds; omega)) (rnds_zero w (st input)).symm
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
