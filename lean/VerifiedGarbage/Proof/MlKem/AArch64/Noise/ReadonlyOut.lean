module
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutWith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One noise output with 16-bit coefficients, transformed (`nttAtWithW`) if `transform`. -/
theorem readonly_out_okW {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (hoff : off<65536) (hns : ns<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩) (hfw : (polyRegion f).Disjoint (polyRegion w))
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (ht : Ntt16.Readonly.TableReady s "VG_MLKEM_NTT16_ZETAS" Ntt16.tableHalves f w) :
 WP isa (outCodeWith Ntt16.Readonly.nttAtWithW off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 refine out_okWith transform _ hoff hbuf hb hf hbf hc hcw fun v kv sv pv=>?_
 have table := ht.frame sv kv.rd kv.wr kv.frame (by
   intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact ht.output.symm
   · exact ht.scratch.symm)
 have sub : ∀ x ∈ [Region.mk f 512, ⟨w,512⟩], ∃ r ∈ [Region.mk f 1024, ⟨w,1024⟩], Region.Sub x r := by
   intro x hx
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl
   · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
   · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
 refine WP.mono (Ntt16.W.nttAtWithW_ok hoff hns
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hf)
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hw)
   (hfw.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
   pv (by
     rw [kv.wr]
     exact Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head hcw))
       (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail hcw))) Covers.nil))
   table) fun t ⟨kt,pt⟩ => ⟨Kept.sub kt sub, pt⟩
end VG.Proof.MlKem.AArch64.Noise
