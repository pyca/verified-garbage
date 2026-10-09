import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem umin_word (a b : BitVec 32) :
    (if a.toNat≤b.toNat then a else b) = BitVec.ofNat 32 (min a.toNat b.toNat) := by
  split
  · rw [Nat.min_eq_left (by assumption),BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [Nat.min_eq_right (by omega),BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem word_and (a b : BitVec 128) (e : Nat) :
    vword (a &&& b) e = vword a e &&& vword b e := by
  simp only [vword,BitVec.extractLsb'_and]

/-- Final five-instruction normalization; the arithmetic range premise is
needed only when converting the exact output word into a canonical residue. -/
theorem canonical_ok {d tmp qr : VReg} (hdt : d≠tmp) (hdq : d≠qr) (htq : tmp≠qr)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀ e<4, vword (s.v qr) e=8380417#32)
    (k : ∀ t, VChg [tmp,d] s t →
      (∀ e<4, vword (t.v d) e=canonicalWord (vword (s.v d) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (([
      .vop (.shift .sshr .s4 tmp d 31),.vop (.logic .and tmp tmp qr),
      .vop (.add .s4 d d tmp),.vop (.sub .s4 tmp d qr),.vop (.umin d d tmp)] : List Instr) ++ rest)) s Q := by
  refine wp_vop (d := tmp) rfl fun a ha => wp_vop (d := tmp) rfl fun b hb =>
    wp_vop (d := d) rfl fun c hc => wp_vop (d := tmp) rfl fun f hf =>
    wp_vop (d := d) rfl fun t ht => ?_
  refine k t (VChg.mono ((((ha.chg.trans hb.chg).trans hc.chg).trans hf.chg).trans ht.chg) ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons] at *
    grind only
  · intro e he
    have hadd : vword (c.v d) e = vword (s.v d) e + ((vword (s.v d) e).sshiftRight 31 &&& 8380417#32) := by
      rw [hc.v,VG.AArch64.vword_map2 _ _ _ he,hb.get d hdt,ha.get d hdt,hb.v]
      rw [word_and]
      rw [ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get qr (Ne.symm htq),hq e he]
      rfl
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,umin_word,hf.get d hdt,hf.v,
      VG.AArch64.vword_map2 _ _ _ he,hc.get qr (Ne.symm hdq),hb.get qr (Ne.symm htq),
      ha.get qr (Ne.symm htq),hq e he,hadd]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
