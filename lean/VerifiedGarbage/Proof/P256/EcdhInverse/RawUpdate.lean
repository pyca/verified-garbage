import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatch

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem raw_update_ok {P : InvCfg} {base : Addr} {size p : Nat} (hL : InvLay P size) {s : State} (hs : Scr s base size)
    (hM : ModOkA P.M size p s.mem base) {I : Divstep.IState}
    (hF : (wordsVal s.mem base P.sF P.L : Int)%((2^(64*P.L):Nat):Int)=I.f%((2^(64*P.L):Nat):Int))
    (hG : (wordsVal s.mem base P.sG P.L : Int)%((2^(64*P.L):Nat):Int)=I.g%((2^(64*P.L):Nat):Int))
    (hA : (wordsVal s.mem base P.sA P.M.n : Int)=I.a)
    (hB : (wordsVal s.mem base P.sB P.M.n : Int)=I.b)
    (hf1 : I.f%2=1) (hf : |I.f|≤p) (hg : |I.g|≤p) (ha : |I.a|≤p) (hb : |I.b|≤p)
    (hD : s.gpr .x1=BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).d)
    (hU : s.gpr .x4=BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).u)
    (hV : s.gpr .x5=BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).v)
    (hQ : s.gpr .x6=BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).q)
    (hR : s.gpr .x7=BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)).r) :
    WP isa (.block (([.movz .x .x12 0 0] : List Instr)++P.fgUpdate++P.abUpdate)) s fun t =>
      IInv P base (Divstep.batch 59 p P.M.minv.toNat I) t ∧ t.gpr .x19=s.gpr .x19 ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x16,.x17,.x19] s t ∧
      Unch base (batchW P) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨eL,eF,eG,eA,eB,eNF,eNG,eT⟩ := slots P
  have n4 := hL.n4; have htbl := hL.tbl; have htbl8 := hL.tbl8
  have hp : p<2^(64*P.M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain ⟨buv,bqr⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨mf,mg⟩ := Divstep.msteps_mat (d:=I.d) (g:=I.g) hf1 59
  generalize hmat : Divstep.msteps 59 (Divstep.MSt.init I.d I.f I.g)=mat at hD hU hV hQ hR buv bqr mf mg
  change WP isa (.block ((.movz .x .x12 0 0 :: P.fgUpdate)++P.abUpdate)) s _
  rw [update_eq, WP.block_append_iff]
  refine WP.mono (movzI_ok s .x12 0) fun s₃ ⟨c12, k₃⟩ => ?_
  have hs₃ := hs.of_keeps k₃ (by decide)
  have z₃ : s₃.gpr .x12 = 0 := by rw [c12]; rfl
  have m₃ : s₃.mem = s.mem := k₃.mem
  rw [WP.block_append_iff]
  refine WP.mono (fgUpd_ok hL hs₃ hp z₃ (u := mat.u) (v := mat.v) (q := mat.q) (r := mat.r)
    (by rw [k₃.gpr _ (by decide)]; exact hU) (by rw [k₃.gpr _ (by decide)]; exact hV)
    (by rw [k₃.gpr _ (by decide)]; exact hQ) (by rw [k₃.gpr _ (by decide)]; exact hR) buv bqr
    (by rw [m₃]; exact hF) (by rw [m₃]; exact hG) hf hg ⟨_, mf.symm⟩ ⟨_, mg.symm⟩)
    fun s₄ ⟨eF₄, eG₄, k₄, U₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have g₄ : ∀ r ∉ [Reg.x2, .x3, .x8, .x9, .x10, .x16, .x17], s₄.gpr r = s₃.gpr r := k₄.gpr
  have rd₄ : ∀ {d k : Nat}, d + 8 * k ≤ P.sNF → P.sG + 8 * P.L ≤ d → d + 8 * k ≤ size →
      wordsVal s₄.mem base d k = wordsVal s₃.mem base d k := fun h1 h2 h3 =>
    U₄.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
        omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, h1, h2]) (by omega_using [h3, hn])
  have M₄ : ModOkA P.M size p s₄.mem base := ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by
      rw [U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have hmt := hL.mo_tbl
        rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
          omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, hmt, n4]) (by have := hM.mo; omega_using [this, hn]), m₃]
      exact hM.val, hM.inv, hM.red, hM.call⟩
  refine WP.mono (abUpd_ok hL hs₄ M₄ (by rw [g₄ _ (by decide), z₃]) (u := mat.u) (v := mat.v) (q := mat.q) (r := mat.r)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hU) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hV)
    (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hQ) (by rw [g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hR)
    buv bqr (by rw [rd₄ (by omega) (by omega) (by omega), m₃]; exact hA)
    (by rw [rd₄ (by omega) (by omega) (by omega), m₃]; exact hB) ha hb) fun t ⟨eA₅, eB₅, k₅, U₅⟩ => ?_
  have rd₅ : ∀ {d k : Nat}, d + 8 * k ≤ P.sA → d + 8 * k ≤ size →
      wordsVal t.mem base d k = wordsVal s₄.mem base d k := fun h1 h3 =>
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;>
        omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT, h1]) (by omega_using [h3, hn])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [Divstep.batch,hmat]
    rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]; exact hD
  · simp only [Divstep.batch,hmat]
    rw [rd₅ (by omega) (by omega)]; exact eF₄
  · simp only [Divstep.batch,hmat]
    rw [rd₅ (by omega) (by omega)]; exact eG₄
  · simp only [Divstep.batch,hmat]; exact eA₅
  · simp only [Divstep.batch,hmat]; exact eB₅
  · rw [k₅.gpr _ (by decide), g₄ _ (by decide), k₃.gpr _ (by decide)]
  · refine (((Keeps.regs k₃).mono ?_).trans (k₄.mono ?_)).trans (k₅.mono ?_) <;> decide
  · have U := U₄.trans U₅
    rw [m₃] at U
    refine (U.outside fun w hw => ?_).unch
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      omega_using [eL, eF, eG, eA, eB, eNF, eNG, eT]

end VG.Proof.P256.EcdhInverse
