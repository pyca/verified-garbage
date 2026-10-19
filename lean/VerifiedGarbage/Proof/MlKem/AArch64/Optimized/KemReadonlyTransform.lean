module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64 VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem readonly_ntt_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
 (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) (ht : Optimized.TransformTables s) :
 WP isa (Ntt16.Readonly.nttAt off) s fun t=>
 KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s.mem t.mem ∧
 PolyIs t.mem (sA L s₀ off) (ntt (polyAt s.mem (sA L s₀ off))) ∧ t.gpr .x24=s.gpr .x24 := by
 have hw := hp.wf
 have hc := covers_cons (cov_s hp hk ho.le) (cov_s hp hk (o:=NS) (l:=1024) (by kom))
 refine WP.mono (Ntt16.Readonly.nttAtWith_ok (by obtain ⟨_,hh⟩:=ho; kom) (by decide)
   (by rw [e28 hk]) (by rw [e28 hk]) (ho.ns hp) ⟨hr,rfl⟩ hc (ht.forward.ready hc)) fun t ⟨kt,pt⟩=>?_
 refine ⟨hk.call kt ?_,kt.frame,pt,kt.cs _ (by decide) (by decide)⟩
 intro r hh
 rcases mem2' hh with rfl|rfl
 · exact ho.safe hp
 · exact safe_scr hp (by kom)

theorem readonly_nttInv_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
 (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) (ht : Optimized.TransformTables s) :
 WP isa (Ntt16.Readonly.nttInvAt off) s fun t=>
 KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s.mem t.mem ∧
 PolyIs t.mem (sA L s₀ off) (nttInv (polyAt s.mem (sA L s₀ off))) ∧ t.gpr .x24=s.gpr .x24 := by
 have hw := hp.wf
 have hc := covers_cons (cov_s hp hk ho.le) (cov_s hp hk (o:=NS) (l:=1024) (by kom))
 refine WP.mono (Ntt16.Readonly.nttInvAtWith_ok (by obtain ⟨_,hh⟩:=ho; kom) (by decide)
   (by rw [e28 hk]) (by rw [e28 hk]) (ho.ns hp) ⟨hr,rfl⟩ hc (ht.inverse.ready hc)) fun t ⟨kt,pt⟩=>?_
 refine ⟨hk.call kt ?_,kt.frame,pt,kt.cs _ (by decide) (by decide)⟩
 intro r hh
 rcases mem2' hh with rfl|rfl
 · exact ho.safe hp
 · exact safe_scr hp (by kom)
end VG.Proof.MlKem.AArch64.Kem
