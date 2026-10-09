import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidthLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals vals_lt vals_getD)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_eq!)
open VG.Proof.MlKem.AArch64 (Keep)

theorem packed_group (F : BitVec 32 → Nat) (m : Mem) (input : Addr)
    (d c : Nat) (hs : Shape d c (d*c/8)) (hV : ∀j<256,F (coeffAt m input j)<2^d)
    {i j : Nat} (hi : i<256/c) (hj : j<d*c/8) :
    byteOf (digits d ((List.range c).map fun k=>F (coeffAt m input (c*i+k)))) j=
      (bitsToBytes (fieldBits d (vals F m input)))[d*c/8*i+j]! := by
  obtain ⟨hc,hb⟩ := hs.group hi
  rw [pack_group (c:=c) (by have := hs.d1;omega) hs.dc (by simp) (vals_lt hV) hj (by omega),
    take_drop_eq _ 0 (by simp;omega)]
  apply congrArg (fun L=>BitVec.ofNat 8 (digits d L/2^(8*j)))
  apply List.map_congr_left
  intro k hk
  symm
  exact vals_getD F m input (by have := List.mem_range.mp hk;omega)

theorem width_loop_bytes (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (start : State) (input out : Addr) (F : BitVec 32 → Nat)
    (hin : polyRegion input ∈ start.rd++start.wr) (hout : (⟨out,32*d⟩:Region)∈start.wr)
    (hsep : (polyRegion input).Disjoint ⟨out,32*d⟩)
    (hv : ∀j<256,F (coeffAt start.mem input j)<2^d)
    (hvalues : ∀j<256,inputValue signed b start.mem input j=BitVec.ofNat 64 (F (coeffAt start.mem input j)))
    {s : State} (h0 : s.gpr .x0=input) (h2 : s.gpr .x2=out)
    (hm : s.mem=start.mem) (hk : Keep widthRegs start s)
    (hc : signed=true → Constants b s) (h15 : s.gpr .x15=BitVec.ofNat 64 (256/c)) :
    WP isa (.loop (.block (widthBody signed b d c)) (.nonzero .x .x15)) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem out (32*d)=bitsToBytes (fieldBits d (vals F start.mem input)) ∧
      Frame [⟨out,32*d⟩] start.mem t.mem ∧ Keep widthRegs start t := by
  refine WP.mono (width_loop signed b d c hs hc4 ht start input out
    (fun j=>F (coeffAt start.mem input j))
    (fun j=>(bitsToBytes (fieldBits d (vals F start.mem input)))[j]!)
    hin hout hsep hv hvalues (fun i hi j hj=>packed_group F start.mem input d c hs hv hi hj)
    h0 h2 hm hk hc h15) fun t ⟨hb,hf,hk⟩=>?_
  exact ⟨bytesAt_eq! (pack_length d _ (by simp)) hb,hf,hk⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
