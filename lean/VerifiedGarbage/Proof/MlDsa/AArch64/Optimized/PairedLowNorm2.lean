import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowWrap2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (normMask minMask)

theorem norm_word_or (a b : BitVec 128) (e : Nat) :
    vword (a ||| b) e=vword a e ||| vword b e := by
  simp only [vword,BitVec.extractLsb'_or]

def normTwo (r q : VReg) : List Instr :=
 ((normRegs .v24 .v25).zip (normRegs r q)).flatMap fun (x,y) => [x,y]

/-- Both alternating norm checks contribute to the shared rejection flag. -/
theorem normTwo_ok {r q : VReg} (hr25 : r≠.v25)
    (hq25 : q≠.v25) (hq10 : q≠.v10) (hq30 : q≠.v30)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀v,VChg [.v25,q,.v30] s v →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| normMask (vword (s.v .v24) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        normMask (vword (s.v r) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (normTwo r q++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun s1 h1 => wp_vop (d := q) rfl fun s2 h2 =>
    wp_vop (d := .v25) rfl fun s3 h3 => wp_vop (d := q) rfl fun s4 h4 =>
    wp_vop (d := .v25) rfl fun s5 h5 => wp_vop (d := q) rfl fun s6 h6 =>
    wp_vop (d := .v30) rfl fun s7 h7 => wp_vop (d := .v30) rfl fun s8 h8 => ?_
  refine k s8 (((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg |>.mono (by simp)) ?_
  intro e he
  have wa : vword (s5.v .v25) e=normMask (vword (s.v .v24) e) (vword (s.v .v9) e) (vword (s.v .v10) e) := by
    rw [h5.v,VG.AArch64.vword_map2 _ _ _ he,h4.get .v25 (Ne.symm hq25),
      h3.v,VG.AArch64.vword_map2 _ _ _ he,h2.get .v25 (Ne.symm hq25),h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get .v10 (Ne.symm hq10),h3.get .v10 (by decide),h2.get .v10 (Ne.symm hq10),h1.get .v10 (by decide),minMask]
    rfl
  have wb : vword (s6.v q) e=normMask (vword (s.v r) e) (vword (s.v .v9) e) (vword (s.v .v10) e) := by
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,h5.get q hq25,
      h4.v,VG.AArch64.vword_map2 _ _ _ he,h3.get q hq25,h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get r hr25,h1.get .v9 (by decide),
      h5.get .v10 (by decide),h4.get .v10 (Ne.symm hq10),h3.get .v10 (by decide),h2.get .v10 (Ne.symm hq10),h1.get .v10 (by decide),minMask]
    rfl
  rw [h8.v,norm_word_or,h7.v,norm_word_or,
    h7.get q hq30,wb,h6.get .v25 (Ne.symm hq25),wa,
    h6.get .v30 (Ne.symm hq30),h5.get .v30 (by decide),h4.get .v30 (Ne.symm hq30),
    h3.get .v30 (by decide),h2.get .v30 (Ne.symm hq30),h1.get .v30 (by decide)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
