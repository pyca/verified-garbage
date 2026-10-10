import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oSave oX2)

def pReg (p : Nat) : Reg := if p = 0 then .x22 else .x23
def bReg (k : Nat) : Reg := [.x24,.x25,.x26,.x27][k]!

theorem pair_regs : ∀ p < 2,
    pReg p ≠ .x1 ∧ pReg p ≠ .x6 ∧ pReg p ≠ .x7 ∧ bReg (2*p) ≠ .x6 ∧ bReg (2*p) ≠ .x7 ∧
      bReg (2*p+1) ≠ .x6 ∧ bReg (2*p+1) ≠ .x7 ∧ pReg p ∉ X2.clobbered ∧
      bReg (2*p) ∉ X2.clobbered ∧ bReg (2*p+1) ∉ X2.clobbered := by decide

/-- `vg_keccak_f1600_x2`'s working space, and the return address during its calls. -/
def x2R (σ : State) : Region := X2.callR (at' σ oX2)

/-- What a pair's block writes. -/
def blockW (σ : State) (p n : Nat) : List Region :=
  [pairR (stateP σ p),outR (bufAt σ (2*p) n),outR (bufAt σ (2*p+1) n),x2R σ]

/-- The registers a pair's block changes. -/
def blockRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7]

theorem buf_word (σ : State) (k n i : Nat) : outAddr (bufAt σ k n) i = at' σ (oBuf+1008*k+168*n+8*i) := by
  unfold outAddr bufAt at'
  rw [Offset.add_add]

theorem pair_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = at' σ (400*p+16*i) := by
  unfold wordAddr stateP at'
  rw [Offset.add_add]

theorem block_regions_low {σ : State} {p n : Nat} (hp : p < 2) (hn : n < 6) :
    ∀ r ∈ blockW σ p n, Region.Sub r (lowR σ) := by
  intro r hr
  simp only [blockW,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.sub_base (scr σ) (by dsimp only [oSave]; omega)
  · exact Offset.sub_base (scr σ) (by dsimp only [oBuf,oSave]; omega)
  · exact Offset.sub_base (scr σ) (by dsimp only [oBuf,oSave]; omega)
  · exact Offset.sub_base (scr σ) (by dsimp only [oX2,oSave]; omega)

theorem env_regs {s t : State} {rs : List Reg} (h : RegKeep rs s t) (hr : ∀ r ∈ [Reg.x19,.x20,.x21,.x30], r ∉ rs) :
    ∀ r ∈ [Reg.x19,.x20,.x21,.x30], t.gpr r = s.gpr r := fun r hm => h.gpr r (hr r hm)

/-- One pair's permutation and rate output, inside the four-way sampler. -/
theorem pairBlock_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) (he : Env σ s) {p n : Nat} (hpn : p < 2) (hn : n < 6)
    {A B : Spec.Sha3.State}
    (hx : s.gpr (pReg p) = stateP σ p)
    (ha : s.gpr (bReg (2*p)) = bufAt σ (2*p) n)
    (hb : s.gpr (bReg (2*p+1)) = bufAt σ (2*p+1) n)
    (hpair : PairAt s.mem (stateP σ p) A B) :
    WP isa (Impl.MlDsa.AArch64.Sample.Rej4.pairStep sha3 (pReg p) (bReg (2*p)) (bReg (2*p+1))) s
      fun t => Env σ t ∧ RegKeep blockRegs s t ∧
        PairAt t.mem (stateP σ p) (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
        RateAt t.mem (bufAt σ (2*p) n) (Spec.Sha3.keccakF A) ∧
        RateAt t.mem (bufAt σ (2*p+1) n) (Spec.Sha3.keccakF B) ∧
        Frame (blockW σ p n) s.mem t.mem := by
  obtain ⟨hp1,hp6,hp7,ha6,ha7,hb6,hb7,hpc,hac,hbc⟩ := pair_regs p hpn
  have hsw : s.wr = [aR σ,scrR σ] := he.wr.trans hp.wr
  unfold Impl.MlDsa.AArch64.Sample.Rej4.pairStep
  refine WP.seq (WP.mono (X2.call_ok sha3 (q := at' σ oX2) (by decide) hp1 hx
    (by rw [he.x19]; rfl)
    (Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oX2) (k := 136)
      (by dsimp only [oX2]; omega) (by omega) (by decide)) hpair
    (by
      rw [hsw]
      refine Covers.of_sub fun r hr => ⟨scrR σ,by simp,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨400*p,rfl,by dsimp only [pairR,scrR]; omega⟩
      · exact ⟨oX2,rfl,by dsimp only [X2.callR,scrR,oX2]; omega⟩))
    fun t ⟨hk,hf,hpt⟩ => ?_)
  have hkt : RegKeep X2.clobbered s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  have het : Env σ t := he.lowStep hf (fun r hr => block_regions_low hpn hn r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [blockW,List.mem_cons,List.not_mem_nil,or_false]
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inr (.inr rfl))))
    hk.rd hk.wr hk.sp (env_regs hkt (by decide))
  refine WP.mono (X2.squeeze_ok (n := 21) (by decide) ((hkt.gpr _ hpc).trans hx)
    ((hkt.gpr _ hac).trans ha) ((hkt.gpr _ hbc).trans hb)
    hp6 hp7 ha6 ha7 hb6 hb7 hpt
    (Offset.disjoint (scr σ) (d := oBuf+1008*(2*p)+168*n) (n := 168)
      (e := oBuf+1008*(2*p+1)+168*n) (k := 168) (by omega)
      (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega))
    (fun i hi => by rw [pair_word]; exact in_scr_rd hp het.rd het.wr (by omega))
    (fun i hi => by rw [buf_word]; exact in_scr hp het.wr (by dsimp only [oBuf]; omega))
    (fun i hi => by rw [buf_word]; exact in_scr hp het.wr (by dsimp only [oBuf]; omega)))
    fun u ⟨hu,hfu,hau,hbu⟩ => ?_
  have hku : RegKeep [.x6,.x7] t u := ⟨fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hu.gpr r hr.1 hr.2,
    hu.rd,hu.wr,hu.sp⟩
  have hfu' : Frame [outR (bufAt σ (2*p) n),outR (bufAt σ (2*p+1) n)] t.mem u.mem := hfu
  refine ⟨het.lowStep hfu' (fun r hr => block_regions_low hpn hn r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [blockW,List.mem_cons,List.not_mem_nil,or_false]
      rcases hr with rfl | rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))))
    hu.rd hu.wr hu.sp (env_regs hku (by decide)),
    (hkt.trans hku).mono (by decide),?_,hau,hbu,?_⟩
  · intro i hi
    rw [hfu'.read (pair_contains _ hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
          (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)
      · exact Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
          (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)) (by decide)]
    exact hpt i hi
  · refine (hf.mono fun r hr => ?_).trans (hfu'.mono fun r hr => ?_)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [blockW,List.mem_cons,List.not_mem_nil,or_false]
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inr (.inr rfl))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [blockW,List.mem_cons,List.not_mem_nil,or_false]
      rcases hr with rfl | rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
end VG.Proof.MlDsa.AArch64.Sample.Rej4
