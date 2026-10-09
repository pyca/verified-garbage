import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)

structure HighConstants (g : Nat) (s : State) : Prop where
  add : ∀ e<4, vword (s.v .v17) e=BitVec.ofNat 32 127
  mul : ∀ e<4, vword (s.v .v18) e=BitVec.ofNat 32 (hbMul g)
  round : ∀ e<4, vword (s.v .v19) e=BitVec.ofNat 32 (hbAdd g)
  modulus : ∀ e<4, vword (s.v .v20) e=BitVec.ofNat 32 (dMod g)

theorem HighConstants.chg {g : Nat} {s t : State} (h : HighConstants g s)
    {rs : List VReg} (k : VChg rs s t)
    (h17 : VReg.v17∉rs) (h18 : VReg.v18∉rs) (h19 : VReg.v19∉rs) (h20 : VReg.v20∉rs) :
    HighConstants g t :=
  ⟨by rw [k.get _ h17]; exact h.add,by rw [k.get _ h18]; exact h.mul,
   by rw [k.get _ h19]; exact h.round,by rw [k.get _ h20]; exact h.modulus⟩

/-- Each 16-byte load and decomposition computes four exact high words. -/
theorem loadHigh_ok {g : Nat} (hg : IsG g) {d : VReg}
    (hd7 : d≠.v7) (hd17 : d≠.v17) (hd18 : d≠.v18) (hd19 : d≠.v19) (hd20 : d≠.v20)
    {s : State} (hc : HighConstants g s) {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [d,.v7] s t → HighConstants g t →
      (∀ e<4, vword (t.v d) e=highWord g
        (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq d .x0 off :: (hb g d d ++ rest))) s Q := by
  refine wp_ldrq ho rfl hin fun a ha => ?_
  have ca := hc.chg ha.chg (by simpa using Ne.symm hd17) (by simpa using Ne.symm hd18)
    (by simpa using Ne.symm hd19) (by simpa using Ne.symm hd20)
  refine hb_ok hg hd7 hd18 hd19 hd20 ca.add ca.mul ca.round ca.modulus fun t ht hw => ?_
  have hh : VChg [d,.v7] s t := (ha.chg.trans ht).mono (by simp)
  refine k t hh (hc.chg hh ?_ ?_ ?_ ?_) ?_
  · simp [Ne.symm hd17]
  · simp [Ne.symm hd18]
  · simp [Ne.symm hd19]
  · simp [Ne.symm hd20]
  · intro e he
    rw [hw e he,ha.v]

/-- The initialized constants meet the arithmetic kernel's lane contract. -/
theorem constants_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (constants g)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23] s t ∧ HighConstants g t := by
  refine WP.mono (constants_ok s g) fun t h => ⟨h.1,?_,?_,?_,?_⟩
  · intro e he; rw [h.2.2.1]; exact repeatedWord_lane _ he
  · intro e he; rw [h.2.2.2.1,repeatedWord_lane _ he]
    rcases hg with rfl | rfl <;> rfl
  · intro e he; rw [h.2.2.2.2.1,repeatedWord_lane _ he]
    rcases hg with rfl | rfl <;> rfl
  · intro e he; rw [h.2.2.2.2.2.1]; exact repeatedWord_lane _ he


/-- Compose the four interleaved load/decompose kernels used by each loop
iteration, preserving the original input buffer and all setup constants. -/
theorem loadFour_ok {g : Nat} (hg : IsG g) {s : State} (hc : HighConstants g s)
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v1,.v2,.v3,.v7] s t → HighConstants g t →
      (∀ j<4, ∀ e<4, vword (t.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e =
        highWord g (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) =>
      ([.ldrq r .x0 (16*j)] : List Instr) ++ hb g r r) ++ rest)) s Q := by
  change WP isa (.block (.ldrq .v0 .x0 0 :: (hb g .v0 .v0 ++
    (.ldrq .v1 .x0 16 :: (hb g .v1 .v1 ++
    (.ldrq .v2 .x0 32 :: (hb g .v2 .v2 ++
    (.ldrq .v3 .x0 48 :: (hb g .v3 .v3 ++ rest))))))))) s Q
  refine loadHigh_ok hg (by decide) (by decide) (by decide) (by decide) (by decide)
    hc (by decide) (hin 0 (by decide)) fun a0 h0 c0 w0 => ?_
  have in1 : InRegions (a0.rd++a0.wr) (a0.gpr .x0+BitVec.ofNat 64 16) 16 := by
    rw [h0.rd, h0.wr, h0.gpr]
    exact hin 1 (by decide)
  refine loadHigh_ok hg (by decide) (by decide) (by decide) (by decide) (by decide)
    c0 (by decide) in1 fun a1 h1 c1 w1 => ?_
  have in2 : InRegions (a1.rd++a1.wr) (a1.gpr .x0+BitVec.ofNat 64 32) 16 := by
    rw [h1.rd, h1.wr, h1.gpr, h0.rd, h0.wr, h0.gpr]
    exact hin 2 (by decide)
  refine loadHigh_ok hg (by decide) (by decide) (by decide) (by decide) (by decide)
    c1 (by decide) in2 fun a2 h2 c2 w2 => ?_
  have in3 : InRegions (a2.rd++a2.wr) (a2.gpr .x0+BitVec.ofNat 64 48) 16 := by
    rw [h2.rd, h2.wr, h2.gpr, h1.rd, h1.wr, h1.gpr, h0.rd, h0.wr, h0.gpr]
    exact hin 3 (by decide)
  refine loadHigh_ok hg (by decide) (by decide) (by decide) (by decide) (by decide)
    c2 (by decide) in3 fun a3 h3 c3 w3 => ?_
  have hh : VChg [.v0,.v1,.v2,.v3,.v7] s a3 :=
    (((h0.trans h1).trans h2).trans h3).mono (by simp)
  refine k a3 hh c3 ?_
  intro j hj e he
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl
  · change vword (a3.v .v0) e = _
    rw [h3.get .v0 (by decide), h2.get .v0 (by decide), h1.get .v0 (by decide), w0 e he]
  · change vword (a3.v .v1) e = _
    rw [h3.get .v1 (by decide), h2.get .v1 (by decide), w1 e he, h0.mem, h0.gpr]
  · change vword (a3.v .v2) e = _
    rw [h3.get .v2 (by decide), w2 e he, h1.mem, h1.gpr, h0.mem, h0.gpr]
  · change vword (a3.v .v3) e = _
    rw [w3 e he, h2.mem, h2.gpr, h1.mem, h1.gpr, h0.mem, h0.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
