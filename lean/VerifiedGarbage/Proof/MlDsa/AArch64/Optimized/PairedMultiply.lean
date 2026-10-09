import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- The paired schedule keeps differences in temporary registers while
writing the low products directly to their final butterfly destinations. -/
structure MulRegs where
  source : VReg
  dest : VReg
  temp : VReg

def renamedMultiply (ms : List MulRegs) (zr br qr : VReg) : List Instr :=
  ms.map (fun m => .vop (.sqdmulh m.temp m.source br)) ++
  ms.map (fun m => .vop (.mul m.dest m.source zr)) ++
  ms.map (fun m => .vop (.mls m.dest m.temp qr))

structure MulShape (ms : List MulRegs) (zr br qr : VReg) : Prop where
  dest : (ms.map MulRegs.dest).Nodup
  temp : (ms.map MulRegs.temp).Nodup
  sourceDest : ∀ m∈ms,m.source∉ms.map MulRegs.dest
  sourceTemp : ∀ m∈ms,m.source∉ms.map MulRegs.temp
  tempDest : ∀ m∈ms,m.temp∉ms.map MulRegs.dest
  rootDest : zr∉ms.map MulRegs.dest
  rootTemp : zr∉ms.map MulRegs.temp
  recipTemp : br∉ms.map MulRegs.temp
  qDest : qr∉ms.map MulRegs.dest
  qTemp : qr∉ms.map MulRegs.temp

theorem renamedMultiply_ok (ms : List MulRegs) (zr br qr : VReg)
    (h : MulShape ms zr br qr)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v zr) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v br) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v qr) e=8380417#32)
    (k : ∀t,VChg (ms.map MulRegs.temp++ms.map MulRegs.dest) s t →
      (∀m∈ms,∀e<4,vword (t.v m.dest) e=fastMulWord (vword (s.v m.source) e) (z e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (renamedMultiply ms zr br qr++rest)) s Q := by
  unfold renamedMultiply
  rw [List.append_assoc,List.append_assoc]
  have hc : (ms.map (fun m => (m.source,m.temp))).map Prod.snd=ms.map MulRegs.temp := by simp
  have hd : (ms.map (fun m => (m.dest,m.temp))).map Prod.fst=ms.map MulRegs.dest := by simp
  have heq : ms.map (fun m => Instr.vop (.sqdmulh m.temp m.source br))=
      (ms.map (fun m => (m.source,m.temp))).map (fun p => Instr.vop (.sqdmulh p.2 p.1 br)) := by simp
  rw [heq]
  refine high_phase_ok (ms.map (fun m => (m.source,m.temp))) br
    (by simpa only [hc] using h.temp) (by simpa only [hc] using h.recipTemp) ?_
    hz hbw fun a ha hv => ?_
  · intro p hp
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
    simpa only [hc] using h.sourceTemp m hm
  · have ha' : VChg (ms.map MulRegs.temp) s a := by simpa only [hc] using ha
    refine parallel_ok ms MulRegs.dest (fun m => .mul m.dest m.source zr)
      (fun m => VArr.s4.map2 (fun _ x y => x*y) (a.v m.source) (a.v zr)) h.dest ?_
      fun b hb hvb => ?_
    · intro t ht m hm _
      change some (m.dest,VArr.s4.map2 (fun _ x y => x*y) (t.v m.source) (t.v zr))=_
      rw [ht.get m.source (h.sourceDest m hm),ht.get zr h.rootDest]
    · have heq' : ms.map (fun m => Instr.vop (.mls m.dest m.temp qr))=
          (ms.map (fun m => (m.dest,m.temp))).map (fun p => Instr.vop (.mls p.1 p.2 qr)) := by simp
      rw [heq']
      refine reduce_phase_ok (ms.map (fun m => (m.dest,m.temp))) qr
        (by simpa only [hd] using h.dest) (by simpa only [hd] using h.qDest) ?_ fun t hc' hvc => ?_
      · intro p hp
        obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
        simpa only [hd] using h.tempDest m hm
      · have hc'' : VChg (ms.map MulRegs.dest) b t := by simpa only [hd] using hc'
        refine k t (((ha'.trans hb).trans hc'').mono ?_) ?_
        · intro r hr
          simp only [List.mem_append] at *
          grind only
        · intro m hm e he
          have hm1 : (m.dest,m.temp)∈ms.map (fun m => (m.dest,m.temp)) := List.mem_map.mpr ⟨m,hm,rfl⟩
          rw [hvc (m.dest,m.temp) hm1,VG.Proof.MlKem.AArch64.vword_mapWords3 _ _ _ _ he,
            hvb m hm,VG.AArch64.vword_map2 _ _ _ he,
            ha'.get m.source (h.sourceTemp m hm),ha'.get zr h.rootTemp,
            hb.get m.temp (h.tempDest m hm),hv (m.source,m.temp) (List.mem_map.mpr ⟨m,hm,rfl⟩) e he,
            hb.get qr h.qDest,ha'.get qr h.qTemp,hzw e he,hqw e he]
          rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
