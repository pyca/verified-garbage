import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem four_packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (hV : ∀j<256,F (coeffAt m input j)<16) {i j : Nat} (hi : i<16) (hj : j<8) :
    byteOf (digits 4 ((List.range 16).map fun k=>F (coeffAt m input (16*i+k)))) j=
      (bitsToBytes (fieldBits 4 (vals F m input)))[8*i+j]! := by
  rw [pack_group (c:=16) (by decide : 0<4) (by decide : 4*16=8*8) (by simp)
    (vals_lt hV) hj (by omega),take_drop_eq _ 0 (by simp;omega)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits 4 L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega)

theorem four_ok (signed : Bool) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<16)
    (hvalues : ∀j<256,inputValue signed 4 s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) 128=
        bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,128⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  have hcode : Impl.MlDsa.AArch64.Optimized.KeygenPack.four signed=
      .seq (.block (fourSetup signed)) (.loop (.block (fourBody signed)) (.nonzero .x .x15)) := by
    simp [Impl.MlDsa.AArch64.Optimized.KeygenPack.four,fourSetup,fourBody,fourGroup,fourShuffle,advance,List.append_assoc]
  rw [hcode]
  refine WP.seq ?_
  refine WP.mono (fourSetup_ok signed s) fun u ⟨hk,hm,h2,hc,hg,hp,hmask,h15⟩=>?_
  refine WP.mono (four_loop signed s (s.gpr .x0) (if signed then s.gpr .x3 else s.gpr .x2)
    (fun j=>F (coeffAt s.mem (s.gpr .x0) j))
    (fun j=>(bitsToBytes (fieldBits 4 (vals F s.mem (s.gpr .x0))))[j]!) hin hout hsep hv hvalues
    (fun i hi j hj=>four_packed_group F s.mem (s.gpr .x0) hv hi hj)
    (hk.get .x0) h2 hm hk.mono hc hg hp hmask h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length 4 _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
