import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowWord

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw)
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def lowHf (g : Nat) (d a : VReg) : List Instr :=
 [.vop (.add .s4 d a .v11),.vop (.shift .ushr .s4 d d 7),
 .vop (.mul d d .v12),.vop (.add .s4 d d .v13),.vop (.shift .ushr .s4 d d (dShift g))]

theorem lowHf_ok {g : Nat} (hg : IsG g) {d a : VReg}
    (hd12 : d ≠ .v12) (hd13 : d ≠ .v13)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀ e < 4, vword (s.v .v11) e = BitVec.ofNat 32 127)
    (h12 : ∀ e < 4, vword (s.v .v12) e = BitVec.ofNat 32 (hbMul g))
    (h13 : ∀ e < 4, vword (s.v .v13) e = BitVec.ofNat 32 (hbAdd g))
    (k : ∀ t, VChg [d] s t →
      (∀ e < 4, vword (t.v d) e = raw g (vword (s.v a) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (lowHf g d a ++ rest)) s Q := by
  have hsh : VShiftOp.ushr.ok VArr.s4.esize (dShift g) = true := by
    rcases hg with rfl | rfl <;> rfl
  refine wp_vop (d := d) rfl fun s1 h1 => wp_vop (d := d) rfl fun s2 h2 =>
    wp_vop (d := d) rfl fun s3 h3 => wp_vop (d := d) rfl fun s4 h4 =>
    wp_vop (d := d) (by simp only [VOp.eval, hsh, ite_true]; rfl) fun t h5 => ?_
  have keep := (((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg
  refine k t (keep.mono (by intro r hr; simpa only [List.mem_append, List.mem_singleton, or_self] using hr)) ?_
  intro e he
  have w1 : vword (s1.v d) e = vword (s.v a) e + BitVec.ofNat 32 127 := by
    rw [h1.v, VG.AArch64.vword_map2 _ _ _ he, h11 e he]
  have w2 : vword (s2.v d) e = (vword (s.v a) e + BitVec.ofNat 32 127) >>> 7 := by
    rw [h2.v, VG.AArch64.vword_map2 _ _ _ he, w1]
    rfl
  have w3 : vword (s3.v d) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
    rw [h3.v, VG.AArch64.vword_map2 _ _ _ he, w2, h2.get .v12 (Ne.symm hd12),
      h1.get .v12 (Ne.symm hd12), h12 e he]
  have w4 : vword (s4.v d) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) +
      BitVec.ofNat 32 (hbAdd g) := by
    rw [h4.v, VG.AArch64.vword_map2 _ _ _ he, w3, h3.get .v13 (Ne.symm hd13),
      h2.get .v13 (Ne.symm hd13), h1.get .v13 (Ne.symm hd13), h13 e he]
  rw [h5.v, VG.AArch64.vword_map2 _ _ _ he, w4]
  rfl


def lowHb (g : Nat) (d a tmp : VReg) : List Instr :=
 lowHf g d a ++
 (if g==261888 then [.vop (.logic .and d d .v14)] else
 [.vop (.sub .s4 tmp d .v14),.vop (.shift .sshr .s4 tmp tmp 31),.vop (.logic .and d d tmp)])

theorem lowHb_ok {g : Nat} (hg : IsG g) {d a tmp : VReg}
    (hdt : d≠tmp) (hd12 : d≠.v12) (hd13 : d≠.v13) (hd14 : d≠.v14)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀u,VChg [d,tmp] s u →
      (∀e<4,vword (u.v d) e=lowHighWord g (vword (s.v a) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (lowHb g d a tmp++rest)) s Q := by
  unfold lowHb
  rw [List.append_assoc]
  refine lowHf_ok hg hd12 hd13 h11 h12 h13 fun u hu hw => ?_
  by_cases heq : g==261888
  · simp only [heq,ite_true]
    refine wp_vop (d := d) rfl fun t ht => k t (hu.trans ht.chg |>.mono ?_) ?_
    · intro r hr
      simp only [List.mem_append,List.mem_singleton,or_self] at hr
      simp [hr]
    · intro e he
      rw [ht.v,Inverse.word_and,hw e he,hu.get .v14 (by simpa using Ne.symm hd14),h14 e he]
      simp only [lowHighWord,heq,ite_true]
  · simp only [heq]
    refine wp_vop (d := tmp) rfl fun t ht => wp_vop (d := tmp) rfl fun v hv =>
      wp_vop (d := d) rfl fun w hw' => k w (((hu.trans ht.chg).trans hv.chg).trans hw'.chg |>.mono ?_) ?_
    · intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only
    · intro e he
      rw [hw'.v,Inverse.word_and,hv.get d hdt,ht.get d hdt,hw e he,hv.v,
        VG.AArch64.vword_map2 _ _ _ he,ht.v,VG.AArch64.vword_map2 _ _ _ he,
        hw e he,hu.get .v14 (by simpa using Ne.symm hd14),h14 e he]
      simp only [lowHighWord,heq,HighPack.highWord]
      rfl

/-- The proved primitives partition the measured lane without changing its instructions. -/
theorem r0Lane_partition (g : Nat) (raw a t h other : VReg) (off : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane g raw a t h other off =
    ([.ldrq other .x15 off,.vop (.sub .s4 a other raw)] : List Instr) ++
    reduceRegs a t ++ lowCadd a t ++ lowHb g h a t ++
    ([.strq h .x15 off,.vop (.mls a h .v15)] : List Instr) ++
    reduceRegs a t ++ ([.strq a .x16 off] : List Instr) ++ normRegs a t := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane,reduceRegs,lowCadd,lowHb,lowHf,
    normRegs,List.append_assoc,List.cons_append,List.nil_append]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
