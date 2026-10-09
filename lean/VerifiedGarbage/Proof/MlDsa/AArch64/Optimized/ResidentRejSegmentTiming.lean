import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegment

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem layout_only {s t : State} {b p : Addr} {n : Nat} {rs : List Reg}
    (h : StreamLayout s b p n) (ht : Only rs s t) : StreamLayout t b p n := by
  refine ⟨h.bound,?_,?_,?_,?_,h.disjoint⟩
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read16 j hj
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read4 j hj
  · intro j hj; rw [ht.wr]; exact h.write4 j hj
  · intro j hj; rw [ht.wr]; exact h.write16 j hj

/-- Segment timing needs equality only for the consumed candidate bytes, not
for preexisting output bytes or the ignored fourth byte of scalar loads. -/
theorem segment_relCT (v k off n : Nat) (hk : k<4) (ho : off<4096) (hn : n<65536)
    {hintSetup hintStore : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x19,.x21]) (.block (setup k off n)) hintSetup).isSome=true)
    (checkStore : (taint.check (Taint.ofRegs [.x19])
      (.block [.str .x .x4 .x19 (counts+8*k)]) hintStore).isSome=true)
    {σ τ : State} {L : List Zq} (hL : L.length≤256) (hmod : n%4=0)
    (hsp : σ.sp=τ.sp) (h19 : σ.gpr .x19=τ.gpr .x19)
    (h21 : σ.gpr .x21=τ.gpr .x21)
    (hs : StreamLayout σ (segmentInput σ k off) (segmentOutput σ k) n)
    (ht : StreamLayout τ (segmentInput τ k off) (segmentOutput τ k) n)
    (hrs : InRegions (σ.rd++σ.wr) (countAddress σ k) 8)
    (hrt : InRegions (τ.rd++τ.wr) (countAddress τ k) 8)
    (hcs : (σ.mem.readW (countAddress σ k) 64).toNat=256-L.length)
    (hct : (τ.mem.readW (countAddress τ k) 64).toNat=256-L.length)
    (hss : Stored σ.mem (segmentOutput σ k) L)
    (hst : Stored τ.mem (segmentOutput τ k) L)
    (hm : InputEq σ τ (segmentInput σ k off) n) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (segment v k off n) (fun _ _ => True) := by
  have hi : segmentInput τ k off=segmentInput σ k off := by simp only [segmentInput,h19]
  have hp : segmentOutput τ k=segmentOutput σ k := by simp only [segmentOutput,h21]
  let P (a : State) (s : State) :=
    Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] a s ∧
      Start s (segmentInput σ k off) (segmentOutput σ k) n L
  have ws : WP isa (.block (setup k off n)) σ (P σ) := by
    refine WP.mono (setup_ok k off n hk ho hn hL hrs hcs) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hss⟩
  have wt : WP isa (.block (setup k off n)) τ (P τ) := by
    refine WP.mono (setup_ok k off n hk ho hn hL hrt hct) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    rw [hi] at h2
    rw [hp] at h3
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem,←hp]; exact hst⟩
  unfold segment
  apply RelCT.seq (R := fun s t => P σ s ∧ P τ t)
  · have hc : RelCT isa (fun s t => s=σ ∧ t=τ) (.block (setup k off n)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x19,.x21])
        (fun s t h => by
          rcases h with ⟨rfl,rfl⟩
          exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,h19,h21]⟩) checkSetup
    exact (hc.wp (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · intro s t tr ur s' t' hh es et
    have ls := layout_only hs hh.1.1
    have lt := layout_only ht hh.2.1
    rw [hi,hp] at lt
    have im : InputEq s t (segmentInput σ k off) n := by
      intro i hb
      rw [hh.1.1.mem,hh.2.1.mem]
      exact hm i hb
    have sp : s.sp=t.sp := hh.1.1.sp.trans (hsp.trans hh.2.1.sp.symm)
    have wpS := parse_ok v ls hmod hL hh.1.2.1 hh.1.2.2.1 hh.1.2.2.2.1
      hh.1.2.2.2.2.1 hh.1.2.2.2.2.2.1 hh.1.2.2.2.2.2.2
    have wpT := parse_ok v lt hmod hL hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
      hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2
    have pc := (parse_relCT v ls lt hh.1.2 hh.2.2 im sp hmod).wp
      (fun a b h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)
    apply RelCT.seq pc ?_ s t tr ur s' t' ⟨rfl,rfl⟩ es et
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x19])
      (fun a b h => ⟨h.2.1.1.sp.trans (sp.trans h.2.2.1.sp.symm),by
        simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
        intro r hr
        subst r
        rw [h.2.1.1.get .x19,h.2.2.1.get .x19,hh.1.1.get .x19,hh.2.1.get .x19]
        exact h19⟩) checkStore

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
