import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTimingStep

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Every table-building branch and address is determined by public paired fields. -/
theorem arithmeticTable_relCT (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hc : ArithmeticTableChecks K)
    (hcopy : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), dstOf i≠some r)
    {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E)
      (ArithmeticTable.table K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) := by
  let I := fun j s t => 1≤j ∧ j≤7 ∧ NafTablePair K C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (ArithmeticTable.tableStep K) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → ∃ E', FieldPair K.M base size C.p
        (·∈jacWinSlots K) (nafLive K) E' s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (arithmeticTable_step_relCT certs hL hJ hAl hm hsize hOne (m:=8-j) (by omega) (by omega) hc hcopy).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t hp
        have hp' := hp
        obtain ⟨e,p,s19,t19,s20,t20⟩ := hp
        have cn : 8-(8-j+1)=j-1 := by omega
        rw [cn] at s19 t19
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          have hx : 8-j+1=8 := by omega
          rw [hx] at p
          exact ⟨e,p.sub (nafTableLive_full K)⟩
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          have hx : 8-j+1=8-(j-1) := by omega
          exact hx ▸ hp'
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  unfold ArithmeticTable.table
  apply RelCT.assoc
  apply RelCT.seq (nafTable_init_relCT hL hAl hJ hm ht hc.base)
  exact (RelCT.loop I step 7).mono (fun _ _ ⟨e,p,s19,t19,s20,t20⟩ =>
    ⟨by decide,by decide,e,p,s19,t19,by simpa only [Nat.mul_one] using s20,
      by simpa only [Nat.mul_one] using t20⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64
