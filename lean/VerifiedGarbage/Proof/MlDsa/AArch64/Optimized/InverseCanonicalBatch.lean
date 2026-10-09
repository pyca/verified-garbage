import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def signVector (v : BitVec 128) : BitVec 128 := VArr.s4.map2 (fun _ x _ => x.sshiftRight 31) v 0

def correctedVector (v q : BitVec 128) : BitVec 128 := VArr.s4.map2 (fun _ x y => x+y) v (signVector v &&& q)

def canonicalVector (v q : BitVec 128) : BitVec 128 :=
  let a := correctedVector v q
  VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) a
    (VArr.s4.map2 (fun _ x y => x-y) a q)

def canonicalBatchCode (ps : List (VReg × VReg)) (qr : VReg) : List Instr :=
  (ps.map fun p => Instr.vop (.shift .sshr .s4 p.2 p.1 31)) ++
  (ps.map fun p => Instr.vop (.logic .and p.2 p.2 qr)) ++
  (ps.map fun p => Instr.vop (.add .s4 p.1 p.1 p.2)) ++
  (ps.map fun p => Instr.vop (.sub .s4 p.2 p.1 qr)) ++
  (ps.map fun p => Instr.vop (.umin p.1 p.1 p.2))

/-- The selected inverse normalizes four registers phase-by-phase. Every
cross-phase dependency and untouched source is retained explicitly. -/
theorem canonicalBatch_ok (ps : List (VReg × VReg)) (qr : VReg)
    (hd : (ps.map Prod.fst).Nodup) (ht : (ps.map Prod.snd).Nodup)
    (hdt : ∀ p∈ps, p.1∉ps.map Prod.snd) (htd : ∀ p∈ps, p.2∉ps.map Prod.fst)
    (hqd : qr∉ps.map Prod.fst) (hqt : qr∉ps.map Prod.snd)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (ps.map Prod.snd++ps.map Prod.fst) s t →
      (∀ p∈ps, t.v p.1=canonicalVector (s.v p.1) (s.v qr)) → WP isa (.block rest) t Q) :
    WP isa (.block (canonicalBatchCode ps qr ++ rest)) s Q := by
  simp only [canonicalBatchCode,List.append_assoc]
  refine parallel_ok ps Prod.snd (fun p => .shift .sshr .s4 p.2 p.1 31)
    (fun p => signVector (s.v p.1)) ht ?_ fun s₁ hc₁ hv₁ => ?_
  · intro t hc p hp _
    change some (p.2,signVector (t.v p.1))=_
    rw [hc.get p.1 (hdt p hp)]
  · refine parallel_ok ps Prod.snd (fun p => .logic .and p.2 p.2 qr)
      (fun p => s₁.v p.2 &&& s₁.v qr) ht ?_ fun s₂ hc₂ hv₂ => ?_
    · intro t hc p _ hself
      change some (p.2,t.v p.2 &&& t.v qr)=_
      rw [hself,hc.get qr hqt]
    · refine parallel_ok ps Prod.fst (fun p => .add .s4 p.1 p.1 p.2)
        (fun p => VArr.s4.map2 (fun _ x y => x+y) (s₂.v p.1) (s₂.v p.2)) hd ?_
        fun s₃ hc₃ hv₃ => ?_
      · intro t hc p hp hself
        change some (p.1,VArr.s4.map2 (fun _ x y => x+y) (t.v p.1) (t.v p.2))=_
        rw [hself,hc.get p.2 (htd p hp)]
      · have hadd p (hp : p∈ps) : s₃.v p.1=correctedVector (s.v p.1) (s.v qr) := by
          rw [hv₃ p hp,hc₂.get p.1 (hdt p hp),hc₁.get p.1 (hdt p hp),hv₂ p hp,hv₁ p hp,hc₁.get qr hqt]
          rfl
        refine parallel_ok ps Prod.snd (fun p => .sub .s4 p.2 p.1 qr)
          (fun p => VArr.s4.map2 (fun _ x y => x-y) (s₃.v p.1) (s₃.v qr)) ht ?_
          fun s₄ hc₄ hv₄ => ?_
        · intro t hc p hp _
          change some (p.2,VArr.s4.map2 (fun _ x y => x-y) (t.v p.1) (t.v qr))=_
          rw [hc.get p.1 (hdt p hp),hc.get qr hqt]
        · refine parallel_ok ps Prod.fst (fun p => .umin p.1 p.1 p.2)
            (fun p => VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) (s₄.v p.1) (s₄.v p.2)) hd ?_
            fun t hc₅ hv₅ => ?_
          · intro t hc p hp hself
            change some (p.1,VArr.s4.map2 (fun _ x y => if x.toNat≤y.toNat then x else y) (t.v p.1) (t.v p.2))=_
            rw [hself,hc.get p.2 (htd p hp)]
          · refine k t (VChg.mono ((((hc₁.trans hc₂).trans hc₃).trans hc₄).trans hc₅) ?_) ?_
            · intro r hr
              simp only [List.mem_append] at *
              grind only
            · intro p hp
              rw [hv₅ p hp,hc₄.get p.1 (hdt p hp),hv₄ p hp,hadd p hp,
                hc₃.get qr hqd,hc₂.get qr hqt,hc₁.get qr hqt]
              rfl


theorem canonicalVector_word (v q : BitVec 128) {e : Nat} (he : e<4)
    (hq : vword q e=8380417#32) :
    vword (canonicalVector v q) e=canonicalWord (vword v e) := by
  have ha : vword (correctedVector v q) e=
      vword v e+((vword v e).sshiftRight 31 &&& 8380417#32) := by
    rw [correctedVector,VG.AArch64.vword_map2 _ _ _ he,word_and,hq,
      signVector,VG.AArch64.vword_map2 _ _ _ he]
  rw [canonicalVector,VG.AArch64.vword_map2 _ _ _ he,umin_word,
    VG.AArch64.vword_map2 _ _ _ he,hq,ha]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
