import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedReduce
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame

/-! ## `PairedLowVec` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Signed correction with the exact registers used by each pipelined lane. -/
def lowCadd (a t : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 t a 31),.vop (.logic .and t t .v31),.vop (.add .s4 a a t)]

theorem lowCadd_ok {a t : VReg} (hat : a≠t) (htq : t≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀u,VChg [t,a] s u →
      (∀e<4,vword (u.v a) e=Inverse.signCorrected (vword (s.v a) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (lowCadd a t++rest)) s Q := by
  refine wp_vop (d:=t) rfl fun u hu => wp_vop (d:=t) rfl fun v hv =>
    wp_vop (d:=a) rfl fun w hw => ?_
  refine k w (((hu.chg.trans hv.chg).trans hw.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hw.v,VG.AArch64.vword_map2 _ _ _ he,hv.get a hat,hu.get a hat,hv.v,Inverse.word_and,
      hu.v,VG.AArch64.vword_map2 _ _ _ he,hu.get .v31 (Ne.symm htq),hq e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowWord` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw highWord)

def lowHighWord (g : Nat) (a : BitVec 32) : BitVec 32 :=
  if g==261888 then raw g a &&& 15#32 else highWord g a

theorem lowHighWord_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) : lowHighWord g a=highWord g a := by
  unfold lowHighWord
  split
  · rename_i h
    have he : g=261888 := by simpa using h
    subst g
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (15#32).toNat=2^4-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod,HighPack.raw_toNat hg ha,HighPack.highWord_toNat hg ha]
    rfl
  · rfl

/-- The pipelined high output is the same field decomposition as the scalar schedule. -/
theorem lowHighWord_spec {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) :
    (lowHighWord g a).toNat=(VG.Spec.MlDsa.highBits g ⟨a.toNat,ha⟩).toNat := by
  rw [lowHighWord_eq hg ha,HighPack.highWord_spec hg ha]

/-- The selected lane uses reduce32 after high-bit subtraction. It gives the
same small signed low part as the reference's centered correction. -/
theorem lowReduced_spec {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) :
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      VG.Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ := by
  rw [lowHighWord_eq hg ha]
  have hhigh := HighPack.highWord_toNat hg ha
  have hraw : (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt=
      (a.toNat:Int)-(hbF g a.toNat%hbM g)*(2*g) := by
    have ht := BitVec.toInt_eq_toNat_cond (a-highWord g a*BitVec.ofNat 32 (2*g))
    simp only [BitVec.toNat_sub,BitVec.toNat_mul,BitVec.toNat_ofNat] at ht
    rw [hhigh] at ht
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hb : -8380417<(a-highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hreduce := Response.reduceWord_int (a-highWord g a*BitVec.ofNat 32 (2*g)) (by omega) (by omega)
  rw [hreduce]
  have hrange := reduce32_bounds (x := (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt) (by omega) (by omega)
  have hmod := reduce32_mod (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt
  have hlow := Response.lowBits_centered hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hlrange := Response.lowBits_bounds hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hgsmall : g≤261888 := by rcases hg with rfl | rfl <;> decide
  change Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ = _ at hlow
  rw [← hraw] at hlow
  split at hlow <;> omega

theorem lowReduced_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) :
    Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))=
      Response.lowWord a (HighPack.highWord g a) (BitVec.ofNat 32 (2*g)) := by
  apply BitVec.eq_of_toInt_eq
  rw [lowReduced_spec hg ha,Response.lowWord_spec hg ha]

/-- Semantic low part of the exact signed product-subtraction pipeline. -/
theorem subLowReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g))).toInt=
      Spec.MlDsa.lowBits g (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)) := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_word hg ha bl bh
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowHigh` -/

section

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

end

/-! ## `PairedLowInput` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowInput (raw a t other : VReg) (off : Nat) : List Instr :=
 ([.ldrq other .x15 off,.vop (.sub .s4 a other raw)] : List Instr) ++
 reduceRegs a t ++ lowCadd a t

def lowInputWord (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
 Inverse.signCorrected (Response.reduceWord
  (vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v raw) e))

/-- The second lane may reuse its raw-product register as a temporary after subtraction. -/
theorem lowInput_ok {raw a t other : VReg} {off : Nat}
    (hat : a≠t) (hor : other≠raw)
    (hregs : ∀r∈[other,a,t],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,VChg [other,a,t] s u →
      (∀e<4,vword (u.v a) e=lowInputWord s raw off e) → WP isa (.block rest) u Q) :
    WP isa (.block (lowInput raw a t other off++rest)) s Q := by
  simp only [lowInput,List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun u hu => wp_vop (d := a) rfl fun v hv => ?_
  have hk : VChg [other,a] s v := (hu.chg.trans hv.chg).mono (by simp)
  have hq' : ∀e<4,vword (v.v .v31) e=8380417#32 := by
    intro e he; rw [hk.get .v31 (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨Ne.symm (hregs other (by simp)).2,Ne.symm (hregs a (by simp)).2⟩)]
    exact hq e he
  have hc' : ∀e<4,vword (v.v .v8) e=4194304#32 := by
    intro e he; rw [hk.get .v8 (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨Ne.symm (hregs other (by simp)).1,Ne.symm (hregs a (by simp)).1⟩)]
    exact hc e he
  refine reduceRegs_ok hat (hregs t (by simp)).2 hq' hc' fun w hw hval => ?_
  have hk' : VChg [other,a,t] s w := (hk.trans hw).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  refine lowCadd_ok hat (hregs t (by simp)).2
    (by intro e he; rw [hk'.get .v31 (by intro hm; exact (hregs .v31 hm).2 rfl)]; exact hq e he)
    fun y hy hcorr => k y ((hk'.trans hy).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  intro e he
  rw [hcorr e he,hval e he,hv.v,VG.AArch64.vword_map2 _ _ _ he,hu.v,hu.get raw (Ne.symm hor)]
  rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowOutput` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_strq vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

/-- Subtract the decomposed high part and reduce, using the selected schedule. -/
def lowMls (a t h : VReg) : List Instr :=
 ([.vop (.mls a h .v15)] : List Instr) ++ reduceRegs a t

theorem lowMls_ok {a t h : VReg} (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,VChg [a,t] s u →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (lowMls a t h++rest)) s Q := by
  simp only [lowMls,List.cons_append,List.nil_append]
  refine wp_vop (d := a) rfl fun u hu => ?_
  refine reduceRegs_ok hat htq
    (by intro e he; rw [hu.get .v31 (Ne.symm haq)]; exact hq e he)
    (by intro e he; rw [hu.get .v8 (Ne.symm hac)]; exact hc e he)
    fun v hv hw => k v ((hu.chg.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  intro e he
  rw [hw e he,hu.v,vword_mapWords3 _ _ _ _ he]

/-- Store the exact reduced low vector and accumulate its norm mask. -/
def lowStoreNorm (a t : VReg) (off : Nat) : List Instr :=
 ([.strq a .x16 off] : List Instr) ++ normRegs a t

theorem lowStoreNorm_ok {a t : VReg} {off : Nat} (htw : t≠.v10) (htf : t≠.v30)
    (hpres : ∀r∈preservedV,r∉[t,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (k : ∀u,StepKeep [t,.v30] s u →
      u.mem=s.mem.write (s.gpr .x16+BitVec.ofNat 64 off) 16 (s.v a) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword (s.v a) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreNorm a t off++rest)) s Q := by
  simp only [lowStoreNorm,List.cons_append,List.nil_append]
  refine wp_strq ho rfl hr fun u hu => normRegs_ok htw htf fun v hv hf => k v ?_ ?_ ?_
  · exact ((StepKeep.ofMem hu).trans (StepKeep.ofChg hv hpres)).mono (by simp)
  · exact hv.mem.trans hu.mem
  · simpa only [hu.v] using hf
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowDecompose` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Round

def lowDecompose (g : Nat) (a t h : VReg) : List Instr :=
 lowHb g h a t ++ lowMls a t h

theorem lowDecompose_ok {g : Nat} (hg : IsG g) {a t h : VReg}
    (hat : a≠t) (hah : a≠h) (hht : h≠t)
    (hregs : ∀r∈[a,t,h],r≠.v8 ∧ r≠.v12 ∧ r≠.v13 ∧ r≠.v14 ∧ r≠.v15 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀u,VChg [a,t,h] s u →
      (∀e<4,vword (u.v h) e=lowHighWord g (vword (s.v a) e)) →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-lowHighWord g (vword (s.v a) e)*vword (s.v .v15) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowDecompose g a t h++rest)) s Q := by
  unfold lowDecompose
  rw [List.append_assoc]
  have hh := hregs h (by simp)
  have ha := hregs a (by simp)
  have ht := hregs t (by simp)
  refine lowHb_ok hg hht hh.2.1 hh.2.2.1 hh.2.2.2.1 h11 h12 h13 h14 fun u hu hw => ?_
  have keep (r : VReg) (hr : r≠h ∧ r≠t) : u.v r=s.v r :=
    hu.get r (by simpa using hr)
  refine lowMls_ok hat ha.2.2.2.2.2 ha.1 ht.2.2.2.2.2
    (by intro e he; rw [keep .v31 ⟨Ne.symm hh.2.2.2.2.2,Ne.symm ht.2.2.2.2.2⟩]; exact hq e he)
    (by intro e he; rw [keep .v8 ⟨Ne.symm hh.1,Ne.symm ht.1⟩]; exact hc e he)
    fun v hv hvw => k v ((hu.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
  · intro e he
    rw [hv.get h (by simp [Ne.symm hah,hht])]
    exact hw e he
  · intro e he
    rw [hvw e he,keep a ⟨hah,hat⟩,hw e he,
      keep .v15 ⟨Ne.symm hh.2.2.2.2.1,Ne.symm ht.2.2.2.2.1⟩]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowStore` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_strq)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowStoreMls (a t h : VReg) (off : Nat) : List Instr :=
 ([.strq h .x15 off] : List Instr) ++ lowMls a t h

/-- Preserve the measured high-store-before-low-reduction schedule. -/
theorem lowStoreMls_ok {a t h : VReg} {off : Nat}
    (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    (hpres : ∀r∈preservedV,r∉[a,t])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,StepKeep [a,t] s u →
      u.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (s.v h) →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreMls a t h off++rest)) s Q := by
  simp only [lowStoreMls,List.cons_append,List.nil_append]
  refine wp_strq ho rfl hr fun u hu => ?_
  refine lowMls_ok hat haq hac htq
    (by simpa only [hu.v] using hq) (by simpa only [hu.v] using hc)
    fun v hv hw => k v ?_ (hv.mem.trans hu.mem) ?_
  · exact ((StepKeep.ofMem hu).trans (StepKeep.ofChg hv hpres)).mono (by simp)
  · simpa only [hu.v] using hw

/-- The complete lane consists of the input, high extraction, high store and low reduction,
then the low store and norm test; this is instruction-list equality, not a rescheduling. -/
theorem r0Lane_blocks (g : Nat) (raw a t h other : VReg) (off : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane g raw a t h other off =
      lowInput raw a t other off ++ lowHb g h a t ++
      lowStoreMls a t h off ++ lowStoreNorm a t off := by
  rw [r0Lane_partition]
  simp only [lowInput,lowStoreMls,lowStoreNorm,lowMls,List.append_assoc,
    List.cons_append,List.nil_append]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowTail` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

/-- Exact two-store suffix, including its accumulated rejection mask. -/
theorem lowTail_ok {a t h : VReg} {off : Nat}
    (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    (hconst : ∀r∈[.v9,.v10,.v30],r∉[a,t])
    (hpres : ∀r∈preservedV,r∉[a,t,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u low,StepKeep [a,t,.v30] s u →
      u.mem=(s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (s.v h)).write
        (s.gpr .x16+BitVec.ofNat 64 off) 16 low →
      (∀e<4,vword low e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword low e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreMls a t h off++lowStoreNorm a t off++rest)) s Q := by
  rw [List.append_assoc]
  refine lowStoreMls_ok hat haq hac htq
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho hr hq hc fun u hu hm hw => ?_
  have h10 := hconst .v10 (by simp)
  have h30 := hconst .v30 (by simp)
  refine lowStoreNorm_ok
    (by intro he; subst t; exact h10 (by simp))
    (by intro he; subst t; exact h30 (by simp))
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho (by rw [hu.keep.wr,hu.keep.get .x16]; exact hl)
    fun v hv hmem hf => k v (u.v a) ((hu.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ hw ?_
  · rw [hmem,hm,hu.keep.get .x16]
  · intro e he
    rw [hf e he,hu.vec .v30 h30,hu.vec .v9 (hconst .v9 (by simp)),hu.vec .v10 h10]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLane` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

/-- Complete measured lane: both output vectors and the rejection mask. -/
theorem r0Lane_ok {g : Nat} (hg : IsG g) {raw a t h other : VReg} {off : Nat}
    (hat : a≠t) (hah : a≠h) (hht : h≠t) (hor : other≠raw)
    (havoid : ∀r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31],r∉[other,a,t,h])
    (hpres : ∀r∈preservedV,r∉[other,a,t,h,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀u high low,StepKeep [other,a,t,h,.v30] s u →
      u.mem=(s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 high).write
        (s.gpr .x16+BitVec.ofNat 64 off) 16 low →
      (∀e<4,vword high e=lowHighWord g (lowInputWord s raw off e)) →
      (∀e<4,vword low e=Response.reduceWord
        (lowInputWord s raw off e-lowHighWord g (lowInputWord s raw off e)*vword (s.v .v15) e)) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword low e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane g raw a t h other off++rest)) s Q := by
  rw [r0Lane_blocks]
  simp only [List.append_assoc]
  have avoid (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31])
      (x : VReg) (hx : x∈[other,a,t,h]) : x≠r := by
    intro he; subst x; exact havoid r hr hx
  refine lowInput_ok hat hor (by
    intro r hr
    exact ⟨avoid .v8 (by simp) r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only),
      avoid .v31 (by simp) r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)⟩)
    ho hread hq hc fun u hu hw => ?_
  have uk (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31]) : u.v r=s.v r :=
    hu.get r (by intro hm; exact havoid r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  refine lowHb_ok hg hht (avoid .v12 (by simp) h (by simp))
    (avoid .v13 (by simp) h (by simp)) (avoid .v14 (by simp) h (by simp))
    (by simpa only [uk .v11 (by simp)] using h11)
    (by simpa only [uk .v12 (by simp)] using h12)
    (by simpa only [uk .v13 (by simp)] using h13)
    (by simpa only [uk .v14 (by simp)] using h14)
    fun v hv hhigh => ?_
  have hkeep : VChg [other,a,t,h] s v := (hu.trans hv).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  have vk (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31]) : v.v r=s.v r :=
    hkeep.get r (havoid r hr)
  have va (e : Nat) (he : e<4) : vword (v.v a) e=lowInputWord s raw off e := by
    rw [hv.get a (by simp [hah,hat])]; exact hw e he
  have vh (e : Nat) (he : e<4) : vword (v.v h) e=lowHighWord g (lowInputWord s raw off e) := by
    rw [hhigh e he,hw e he]
  have hp : ∀r∈preservedV,r∉[other,a,t,h] := by
    intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  have frame := hkeep.keep hp
  refine lowTail_ok hat (avoid .v31 (by simp) a (by simp))
    (avoid .v8 (by simp) a (by simp)) (avoid .v31 (by simp) t (by simp))
    (by
      intro r hr hm
      exact havoid r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho (by rw [frame.wr,frame.get .x15]; exact hr)
    (by rw [frame.wr,frame.get .x16]; exact hl)
    (by simpa only [vk .v31 (by simp)] using hq)
    (by simpa only [vk .v8 (by simp)] using hc)
    fun w low hwkeep hm hlw hf => k w (v.v h) low
      (((StepKeep.ofChg hkeep hp).trans hwkeep).mono (by
        intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ vh ?_ ?_
  · rw [hm,hkeep.mem,frame.get .x15,frame.get .x16]
  · intro e he; rw [hlw e he,va e he,vh e he,vk .v15 (by simp)]
  · intro e he; rw [hf e he,vk .v30 (by simp),vk .v9 (by simp),vk .v10 (by simp)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReduce2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

def reduceTwo (a t b u : VReg) : List Instr :=
 ((reduceRegs a t).zip (reduceRegs b u)).flatMap fun (x,y) => [x,y]

/-- The two reductions execute in the measured alternating instruction order. -/
theorem reduceTwo_ok {a t b u : VReg}
    (hat : a≠t) (hab : a≠b) (hau : a≠u) (htb : t≠b) (htu : t≠u) (hbu : b≠u)
    (hregs : ∀r∈[a,t,b,u],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [a,t,b,u] s v →
      (∀e<4,vword (v.v a) e=Response.reduceWord (vword (s.v a) e)) →
      (∀e<4,vword (v.v b) e=Response.reduceWord (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (reduceTwo a t b u++rest)) s Q := by
  refine wp_vop (d := t) rfl fun s1 h1 => wp_vop (d := u) rfl fun s2 h2 =>
    wp_vop (d := t) rfl fun s3 h3 => wp_vop (d := u) rfl fun s4 h4 =>
    wp_vop (d := a) rfl fun s5 h5 => wp_vop (d := b) rfl fun s6 h6 => ?_
  have hqT := Ne.symm (hregs t (by simp)).2
  have hqU := Ne.symm (hregs u (by simp)).2
  have hqA := Ne.symm (hregs a (by simp)).2
  have hcT := Ne.symm (hregs t (by simp)).1
  refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono ?_) ?_ ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [h6.get a hab,h5.v,vword_mapWords3 _ _ _ _ he,
      h4.get a hau,h3.get a hat,h2.get a hau,h1.get a hat,
      h4.get t htu,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get t htu,h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
  · intro e he
    rw [h6.v,vword_mapWords3 _ _ _ _ he,
      h5.get b (Ne.symm hab),h4.get b hbu,h3.get b (Ne.symm htb),h2.get b hbu,h1.get b (Ne.symm htb),
      h5.get u (Ne.symm hau),h4.v,VG.AArch64.vword_map2 _ _ _ he,
      h3.get u (Ne.symm htu),h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get b (Ne.symm htb),h1.get .v8 hcT,
      h5.get .v31 hqA,h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCadd2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

def caddTwo (a t b u : VReg) : List Instr :=
 ((lowCadd a t).zip (lowCadd b u)).flatMap fun (x,y) => [x,y]

/-- The two signed corrections execute in the measured alternating instruction order. -/
theorem caddTwo_ok {a t b u : VReg}
    (hat : a≠t) (hab : a≠b) (hau : a≠u) (htb : t≠b) (htu : t≠u) (hbu : b≠u)
    (hregs : ∀r∈[a,t,b,u],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀v,VChg [a,t,b,u] s v →
      (∀e<4,vword (v.v a) e=Inverse.signCorrected (vword (s.v a) e)) →
      (∀e<4,vword (v.v b) e=Inverse.signCorrected (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (caddTwo a t b u++rest)) s Q := by
  refine wp_vop (d := t) rfl fun s1 h1 => wp_vop (d := u) rfl fun s2 h2 =>
    wp_vop (d := t) rfl fun s3 h3 => wp_vop (d := u) rfl fun s4 h4 =>
    wp_vop (d := a) rfl fun s5 h5 => wp_vop (d := b) rfl fun s6 h6 => ?_
  have hqT := Ne.symm (hregs t (by simp)).2
  have hqU := Ne.symm (hregs u (by simp)).2
  refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono ?_) ?_ ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [h6.get a hab,h5.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get a hau,h3.get a hat,h2.get a hau,h1.get a hat,
      h4.get t htu,h3.v,Inverse.word_and,
      h2.get t htu,h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v31 hqU,h1.get .v31 hqT,hq e he]
    rfl
  · intro e he
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,
      h5.get b (Ne.symm hab),h4.get b hbu,h3.get b (Ne.symm htb),h2.get b hbu,h1.get b (Ne.symm htb),
      h5.get u (Ne.symm hau),h4.v,Inverse.word_and,
      h3.get u (Ne.symm htu),h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get b (Ne.symm htb),
      h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLoad2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowLoadTwo (r q : VReg) (off : Nat) : List Instr :=
 [.ldrq .v27 .x15 off,.ldrq .v29 .x15 (off+128),
  .vop (.sub .s4 .v24 .v27 r),.vop (.sub .s4 r .v29 q)]

/-- Consume the first raw register before the second lane reuses it. -/
theorem lowLoadTwo_ok {r q : VReg} {off : Nat}
    (hr24 : r≠.v24) (hr27 : r≠.v27) (hr29 : r≠.v29)
    (hq24 : q≠.v24) (hq27 : q≠.v27) (hq29 : q≠.v29)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hread' : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (k : ∀v,VChg [.v27,.v29,.v24,r] s v →
      (∀e<4,vword (v.v .v24) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v r) e) →
      (∀e<4,vword (v.v r) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16) e-vword (s.v q) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowLoadTwo r q off++rest)) s Q := by
  refine wp_ldrq (by omega) rfl hread fun s1 h1 => ?_
  refine wp_ldrq (by omega) rfl (by rw [h1.rd,h1.wr,h1.gpr]; exact hread') fun s2 h2 => ?_
  refine wp_vop (d := .v24) rfl fun s3 h3 => wp_vop (d := r) rfl fun s4 h4 => ?_
  refine k s4 ((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by simp)) ?_ ?_
  · intro e he
    rw [h4.get .v24 (Ne.symm hr24),h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v27 (by decide),h1.v,h2.get r hr29,h1.get r hr27]
  · intro e he
    rw [h4.v,VG.AArch64.vword_map2 _ _ _ he,h3.get .v29 (by decide),h2.v,
      h1.mem,h1.gpr,h3.get q hq24,h2.get q hq29,h1.get q hq27]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
