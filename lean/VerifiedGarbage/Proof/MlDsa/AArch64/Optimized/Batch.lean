import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Execute one scheduled phase of independent vector results. The evaluation
premise is valid after any permitted destination write; this makes the absence
of hidden read-after-write dependencies an explicit proof obligation. -/
theorem parallel_ok {ι : Type} (items : List ι) (dst : ι → VReg) (op : ι → VOp)
    (value : ι → BitVec 128) (hd : (items.map dst).Nodup)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (he : ∀ t, VChg (items.map dst) s t → ∀ i ∈ items,
      t.v (dst i) = s.v (dst i) → (op i).eval t = some (dst i, value i))
    (k : ∀ t, VChg (items.map dst) s t → (∀ i ∈ items, t.v (dst i) = value i) →
      WP isa (.block rest) t Q) :
    WP isa (.block (items.map (fun i => Instr.vop (op i)) ++ rest)) s Q := by
  induction items generalizing s with
  | nil => exact k s (VChg.refl _ _) (by simp)
  | cons i items ih =>
    have hn : dst i ∉ items.map dst := (List.nodup_cons.mp hd).1
    have ht : (items.map dst).Nodup := (List.nodup_cons.mp hd).2
    change WP isa (.block (.vop (op i) :: (items.map (fun i => Instr.vop (op i)) ++ rest))) s Q
    refine wp_vop (he s (VChg.refl _ _) i (by simp) rfl) fun s₁ h₁ => ?_
    refine ih ht (s := s₁) ?_ fun s₂ h₂ hv => ?_
    · intro t h j hj hv
      apply he t (VChg.mono (h₁.chg.trans h) (by simp)) j (List.mem_cons_of_mem _ hj)
      have hne : dst j ≠ dst i := by
        intro heq
        apply hn
        rw [← heq]
        exact List.mem_map_of_mem hj
      rw [hv, h₁.get (dst j) hne]
    · have hc : VChg ((i :: items).map dst) s s₂ :=
        VChg.mono (h₁.chg.trans h₂) (by simp)
      apply k s₂ hc
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [h₂.get _ hn, h₁.v]
      · exact hv j hj

/-- Scheduled low products, including their in-place source reads. -/
theorem mul_phase_ok (ds : List VReg) (zr : VReg) (hd : ds.Nodup) (hz : zr ∉ ds)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg ds s t →
      (∀ d ∈ ds, t.v d = VArr.s4.map2 (fun _ x y => x * y) (s.v d) (s.v zr)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ds.map (fun d => Instr.vop (.mul d d zr)) ++ rest)) s Q := by
  refine parallel_ok ds id (fun d => .mul d d zr)
    (fun d => VArr.s4.map2 (fun _ x y => x * y) (s.v d) (s.v zr))
    (by simpa using hd) ?_ ?_
  · intro t ht d _ hself
    dsimp only [id] at hself ⊢
    change some (d, VArr.s4.map2 (fun _ x y => x * y) (t.v d) (t.v zr)) = _
    rw [hself, ht.get zr (by simpa using hz)]
  · intro t ht hv
    exact k t (by simpa using ht) hv

/-- All SQDMULH results in a renamed butterfly group are computed before the
corresponding low products. The paired list records input and temporary. -/
theorem high_phase_ok (ps : List (VReg × VReg)) (br : VReg)
    (hd : (ps.map Prod.snd).Nodup) (hb : br ∉ ps.map Prod.snd)
    (ha : ∀ p ∈ ps, p.1 ∉ ps.map Prod.snd)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hbw : ∀ e < 4, vword (s.v br) e = BitVec.ofInt 32 (reciprocal (z e)))
    (k : ∀ t, VChg (ps.map Prod.snd) s t →
      (∀ p ∈ ps, ∀ e < 4, vword (t.v p.2) e =
        BitVec.ofInt 32 ((vword (s.v p.1) e).toInt * reciprocal (z e) / 2147483648)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.map (fun p => Instr.vop (.sqdmulh p.2 p.1 br)) ++ rest)) s Q := by
  let result := fun p : VReg × VReg => ofVWords
    (BitVec.ofInt 32 ((vword (s.v p.1) 0).toInt * reciprocal (z 0) / 2147483648))
    (BitVec.ofInt 32 ((vword (s.v p.1) 1).toInt * reciprocal (z 1) / 2147483648))
    (BitVec.ofInt 32 ((vword (s.v p.1) 2).toInt * reciprocal (z 2) / 2147483648))
    (BitVec.ofInt 32 ((vword (s.v p.1) 3).toInt * reciprocal (z 3) / 2147483648))
  refine parallel_ok ps Prod.snd (fun p => .sqdmulh p.2 p.1 br) result hd ?_ ?_
  · intro t ht p hp _
    have he := reciprocal_eval (s := t) (d := p.2) (a := p.1) (b := br) hz
      (fun e he => by rw [ht.get br hb]; exact hbw e he)
    rw [ht.get p.1 (ha p hp)] at he
    exact he
  · intro t ht hv
    refine k t ht fun p hp e he => ?_
    rw [hv p hp, VG.AArch64.vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

/-- Final MLS phase reads the previously computed high products. -/
theorem reduce_phase_ok (ps : List (VReg × VReg)) (qr : VReg)
    (hd : (ps.map Prod.fst).Nodup) (hq : qr ∉ ps.map Prod.fst)
    (ht : ∀ p ∈ ps, p.2 ∉ ps.map Prod.fst)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (ps.map Prod.fst) s t →
      (∀ p ∈ ps, t.v p.1 = mapWords3 (fun a x y => a - x * y)
        (s.v p.1) (s.v p.2) (s.v qr)) → WP isa (.block rest) t Q) :
    WP isa (.block (ps.map (fun p => Instr.vop (.mls p.1 p.2 qr)) ++ rest)) s Q := by
  refine parallel_ok ps Prod.fst (fun p => .mls p.1 p.2 qr)
    (fun p => mapWords3 (fun a x y => a - x * y) (s.v p.1) (s.v p.2) (s.v qr)) hd ?_ k
  intro t hc p hp hself
  change some (p.1, mapWords3 (fun a x y => a - x * y) (t.v p.1) (t.v p.2) (t.v qr)) = _
  rw [hself, hc.get p.2 (ht p hp), hc.get qr hq]

/-- Full scheduled reciprocal multiplication: all high products, all low
products, then all reductions. Results match the sequential lane operation. -/
theorem multiply_batch_ok (ps : List (VReg × VReg)) (zr br qr : VReg)
    (hd : (ps.map Prod.fst).Nodup) (ht : (ps.map Prod.snd).Nodup)
    (hdt : ∀ p ∈ ps, p.1 ∉ ps.map Prod.snd)
    (htd : ∀ p ∈ ps, p.2 ∉ ps.map Prod.fst)
    (hzb : zr ∉ ps.map Prod.fst) (hzt : zr ∉ ps.map Prod.snd)
    (hbt : br ∉ ps.map Prod.snd)
    (hqb : qr ∉ ps.map Prod.fst) (hqt : qr ∉ ps.map Prod.snd)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v zr) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v br) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v qr) e = 8380417#32)
    (k : ∀ t, VChg (ps.map Prod.snd ++ ps.map Prod.fst) s t →
      (∀ p ∈ ps, ∀ e < 4, vword (t.v p.1) e = fastMulWord (vword (s.v p.1) e) (z e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.map (fun p => Instr.vop (.sqdmulh p.2 p.1 br)) ++
      (ps.map Prod.fst).map (fun d => Instr.vop (.mul d d zr)) ++
      ps.map (fun p => Instr.vop (.mls p.1 p.2 qr)) ++ rest)) s Q := by
  rw [List.append_assoc, List.append_assoc]
  refine high_phase_ok ps br ht hbt hdt hz hbw fun s₁ hc₁ hv₁ => ?_
  refine mul_phase_ok (ps.map Prod.fst) zr hd hzb fun s₂ hc₂ hv₂ => ?_
  refine reduce_phase_ok ps qr hd hqb htd fun s₃ hc₃ hv₃ => ?_
  refine k s₃ (VChg.mono ((hc₁.trans hc₂).trans hc₃) ?_) ?_
  · intro r hr
    simp only [List.mem_append] at *
    grind only
  · intro p hp e he
    rw [hv₃ p hp, VG.Proof.MlKem.AArch64.vword_mapWords3 _ _ _ _ he,
      hv₂ p.1 (List.mem_map_of_mem hp), VG.AArch64.vword_map2 _ _ _ he,
      hc₁.get p.1 (hdt p hp), hc₁.get zr hzt,
      hc₂.get p.2 (htd p hp), hv₁ p hp e he,
      hc₂.get qr hqb, hc₁.get qr hqt, hzw e he, hqw e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized
