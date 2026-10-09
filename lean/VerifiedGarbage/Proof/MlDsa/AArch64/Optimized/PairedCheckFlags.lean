import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def checkMask (hint : Bool) (raw low : BitVec 128) (c : CheckConstants) (e : Nat) : BitVec 32 :=
  normMask (reduceWord (if hint then vword raw e else vword raw e+vword low e))
    (vword c.lower e) (vword c.width e)

theorem checkStep_flag (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep hint raw out aux c d).flags e=
      vword d.flags e ||| checkMask hint raw (d.mem.read out 16) c e := by
  simp only [checkStep,checkMask,laneVector_word _ he]

theorem checkStep_flag_zero (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep hint raw out aux c d).flags e=0 ↔
      vword d.flags e=0 ∧ checkMask hint raw (d.mem.read out 16) c e=0 := by
  rw [checkStep_flag _ _ _ _ _ _ he]
  exact BitVec.or_eq_zero_iff

/-- Acceptance of a distinct-vector check sequence is exactly acceptance
of every original coefficient check and the incoming accumulator. -/
theorem checkRun_flag_zero_iff (hint : Bool) (v : Values) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) (js : List (Fin 2 × Fin 8))
    (hn : js.Nodup) {e : Nat} (he : e<4) :
    vword (checkRun hint v out aux c d js).flags e=0 ↔
      vword d.flags e=0 ∧ ∀i∈js,
        checkMask hint ((v i.1)[i.2.val]) (d.mem.read (checkAddr out i) 16) c e=0 := by
  induction js generalizing d with
  | nil => simp only [checkRun,List.not_mem_nil,false_implies,implies_true,and_true]
  | cons i js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [checkRun,ih _ hn'.2,checkStep_flag_zero _ _ _ _ _ _ he]
    have hread (j : Fin 2 × Fin 8) (hj : j∈js) :
        (checkStep hint ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read
          (checkAddr out j) 16=d.mem.read (checkAddr out j) 16 :=
      Mem.read_write_sep (checkAddr_sep out (by intro h; subst i; exact hn'.1 hj)) (by decide)
    have ht : (∀j∈js,checkMask hint ((v j.1)[j.2.val])
        ((checkStep hint ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read
          (checkAddr out j) 16) c e=0) ↔
        ∀j∈js,checkMask hint ((v j.1)[j.2.val]) (d.mem.read (checkAddr out j) 16) c e=0 := by
      constructor <;> intro h j hj <;> simpa only [hread j hj] using h j hj
    simp only [checkAddr] at ht ⊢
    rw [ht]
    simp only [List.mem_cons,forall_eq_or_imp,and_assoc]

/-- No subsequent coefficient check can clear a rejection bit. -/
theorem checkRun_flag_zero_initial (hint : Bool) (v : Values) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) (js : List (Fin 2 × Fin 8))
    {e : Nat} (he : e<4) (hz : vword (checkRun hint v out aux c d js).flags e=0) :
    vword d.flags e=0 := by
  induction js generalizing d with
  | nil => exact hz
  | cons i js ih =>
    exact ((checkStep_flag_zero _ _ _ _ _ _ he).mp (ih _ hz)).1

/-- A clean final pass implies the initial accumulator was clean. -/
theorem finalPass_flag_zero_initial (hint : Bool) (work out aux : Addr)
    (c : CheckConstants) (d : CheckData) (u : Nat) {e : Nat} (he : e<4)
    (hz : vword (finalPassData hint work out aux c d u).flags e=0) :
    vword d.flags e=0 := by
  induction u with
  | zero => exact hz
  | succ u ih => exact ih (checkRun_flag_zero_initial _ _ _ _ _ _ _ he hz)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
