import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg)

def temps : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v26]

 theorem Ready.chg {g : Nat} {s t : State} (h : Ready g s) {rs : List VReg}
    (k : VChg rs s t) (hrs : rs⊆temps) : Ready g t := by
  have hk := k.mono hrs
  refine ⟨⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩,?_,?_,?_⟩
  · intro e he; rw [hk.get .v17 (by decide)]; exact h.add e he
  · intro e he; rw [hk.get .v18 (by decide)]; exact h.mul e he
  · intro e he; rw [hk.get .v19 (by decide)]; exact h.round e he
  · intro e he; rw [hk.get .v20 (by decide)]; exact h.modulus e he
  · rw [hk.get .v28 (by decide)]; exact h.zero
  · rw [hk.get .v29 (by decide)]; exact h.idx29
  · rw [hk.get .v24 (by decide)]; exact h.idx24
  · rw [hk.get .v25 (by decide)]; exact h.idx25
  · intro e he; rw [hk.get .v21 (by decide)]; exact h.factor e he
  · intro e he; rw [hk.get .v22 (by decide)]; exact h.one e he
  · intro e he; rw [hk.get .v23 (by decide)]; exact h.z e he

 def loadFour (g : Nat) : List Instr :=
  ([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j)=>
    Impl.MlDsa.AArch64.Optimized.UseHintPack.four g r (16*j)

 theorem loadFour_ok {g : Nat} (hg : IsG g) {s : State} (hc : Ready g s)
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg temps s t → Ready g t →
      (∀j<4,∀e<4,vword (t.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=value g
        (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16) e)
        (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (loadFour g++rest)) s Q := by
  change WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v0 0 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v1 16 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v2 32 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v3 48 ++ rest))))) s Q
  refine four_ok hg (by decide) hc (by decide) (ha 0 (by decide)) (hh 0 (by decide)) fun a h0 w0=>?_
  have c0 := hc.chg h0 (by decide)
  refine four_ok hg (by decide) c0 (by decide)
    (by rw [h0.rd,h0.wr,h0.gpr]; exact ha 1 (by decide))
    (by rw [h0.rd,h0.wr,h0.gpr]; exact hh 1 (by decide)) fun b h1 w1=>?_
  have k1 := h0.trans h1
  have c1 := c0.chg h1 (by decide)
  refine four_ok hg (by decide) c1 (by decide)
    (by rw [k1.rd,k1.wr,k1.gpr]; exact ha 2 (by decide))
    (by rw [k1.rd,k1.wr,k1.gpr]; exact hh 2 (by decide)) fun c h2 w2=>?_
  have k2 := k1.trans h2
  have c2 := c1.chg h2 (by decide)
  refine four_ok hg (by decide) c2 (by decide)
    (by rw [k2.rd,k2.wr,k2.gpr]; exact ha 3 (by decide))
    (by rw [k2.rd,k2.wr,k2.gpr]; exact hh 3 (by decide)) fun t h3 w3=>?_
  refine k t ((k2.trans h3).mono (by decide)) (c2.chg h3 (by decide)) ?_
  intro j hj e he
  rcases (show j=0∨j=1∨j=2∨j=3 by omega) with rfl|rfl|rfl|rfl
  · change vword (t.v .v0) e=_
    rw [h3.get .v0 (by decide),h2.get .v0 (by decide),h1.get .v0 (by decide),w0 e he]
  · change vword (t.v .v1) e=_
    rw [h3.get .v1 (by decide),h2.get .v1 (by decide),w1 e he,h0.mem,h0.gpr]
  · change vword (t.v .v2) e=_
    rw [h3.get .v2 (by decide),w2 e he,k1.mem,k1.gpr]
  · change vword (t.v .v3) e=_
    rw [w3 e he,k2.mem,k2.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
