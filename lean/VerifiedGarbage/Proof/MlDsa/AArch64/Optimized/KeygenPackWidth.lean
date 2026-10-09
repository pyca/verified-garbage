import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidthBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.AArch64.Pack (Shape vals)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

theorem counter_ok (n : Nat) (hn : n<2^16) (s : State) :
    WP isa (.block [.movz .x .x15 (BitVec.ofNat 16 n) 0]) s fun t=>
      ((t.gpr .x15=BitVec.ofNat 64 n ∧ t.mem=s.mem) ∧ Keep [.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]

theorem width_ok (signed : Bool) (b d c : Nat) (hs : Shape d c (d*c/8)) (hc4 : c%4=0)
    (ht : TailWidth (d*c/8)) (s : State) (F : BitVec 32 → Nat)
    (hin : polyRegion (s.gpr .x0) ∈ s.rd++s.wr)
    (hout : (⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩:Region)∈s.wr)
    (hsep : (polyRegion (s.gpr .x0)).Disjoint ⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩)
    (hv : ∀j<256,F (coeffAt s.mem (s.gpr .x0) j)<2^d)
    (hvalues : ∀j<256,inputValue signed b s.mem (s.gpr .x0) j=BitVec.ofNat 64 (F (coeffAt s.mem (s.gpr .x0) j))) :
    WP isa (width signed b d c) s fun t=>
      VG.Spec.Sha3.bytesAt t.mem (if signed then s.gpr .x3 else s.gpr .x2) (32*d)=
        bitsToBytes (fieldBits d (vals F s.mem (s.gpr .x0))) ∧
      Frame [⟨if signed then s.gpr .x3 else s.gpr .x2,32*d⟩] s.mem t.mem ∧ Keep widthRegs s t := by
  unfold width
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (setup_ok signed b s) fun a ⟨ka,ma,oa,ca⟩=>?_
  refine WP.mono (counter_ok (256/c) (by have := hs.G;omega) a) fun u ⟨⟨⟨cu,mu⟩,ku⟩,vu⟩=>?_
  have hk : Keep widthRegs s u := (ka.trans ku).mono
  exact width_loop_bytes signed b d c hs hc4 ht s (s.gpr .x0)
    (if signed then s.gpr .x3 else s.gpr .x2) F hin hout hsep hv hvalues
    (by rw [ku.get .x0,ka.get .x0]) (by rw [ku.get .x2,oa]) (mu.trans ma) hk
    (fun h=>⟨by rw [vu];exact (ca h).bias,by rw [vu];exact (ca h).modulus⟩) cu

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
