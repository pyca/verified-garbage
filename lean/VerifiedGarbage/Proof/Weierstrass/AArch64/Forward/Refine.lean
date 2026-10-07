import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Run

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

private theorem readW_byte (m : Mem) (a : Addr) {t : Nat} (ht : t<8) :
    (m.readW a 64).extractLsb' (8*t) 8=m (a+BitVec.ofNat 64 t) := by
  change ((m.read a 8).setWidth 64).extractLsb' (8*t) 8=_
  rw [BitVec.setWidth_eq,Mem.extractLsb'_read _ _ ht]

theorem memory_eq {base : Addr} {size : Nat} (ha : size%8=0)
    {s a b : Mem} {W W' : List (Nat × Nat)}
    (hwa : ∀ w∈W,w.1+w.2≤size) (hwb : ∀ w∈W',w.1+w.2≤size)
    (hua : Unch base W s a) (hub : Unch base W' s b)
    (hw : ∀ off,off%8=0 → off+8≤size → word a base off=word b base off) : a=b := by
  funext x
  by_cases hx : ofs base x<size
  · let q := ofs base x/8*8
    let r := ofs base x%8
    have hr : r<8 := Nat.mod_lt _ (by decide)
    have hq : q%8=0 := by simp [q]
    have arith : ∀ n sz : Nat, sz%8=0 → n<sz → n/8*8+8≤sz := by intros; omega
    have hb : q+8≤size := arith _ _ ha hx
    have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*r) 8) (hw q hq hb)
    rw [readW_byte _ _ hr,readW_byte _ _ hr] at he
    have eq : base+BitVec.ofNat 64 q+BitVec.ofNat 64 r=x := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      have hqr : q+r=ofs base x := by dsimp [q,r]; omega
      rw [hqr]
      change base+BitVec.ofNat 64 (x-base).toNat=x
      rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
    simpa only [off,eq] using he
  · exact (hua x (fun w wh => Or.inr (by have := hwa w wh; omega))).trans
      (hub x (fun w wh => Or.inr (by have := hwb w wh; omega))).symm

theorem post_of_runBlock {is : List Instr} {s t : State} {Q : State → Prop}
    (h : WP isa (.block is) s Q) (hr : runBlock isa is s=some t) : Q t := by
  induction is generalizing s with
  | nil => cases hr; exact WP.block_nil_iff.mp h
  | cons i is ih =>
    obtain ⟨s',hs',hq⟩ := WP.block_cons_iff.mp h
    change exec i s=some s' at hs'
    change (exec i s).bind (runBlock isa is)=some t at hr
    rw [hs'] at hr
    change runBlock isa is s'=some t at hr
    exact ih hq hr

theorem refine_wp {α : Type} {D : Dom α} {v : α → BitVec 64 × Bool}
    {base : Addr} {size cap : Nat} {e e₁ e₂ : Env α} {s : State}
    (hD : D.Sound v) (hs : Scr s base cap) (ha : size%8=0) (hsize : size≤2^64)
    (he : Rel v base size e s) {is js : List Instr}
    (hi : eval D size is e=some e₁) (hj : eval D size js e=some e₂)
    (hEq : ∀ off,off%8=0 → off+8≤size → e₁.slot off=e₂.slot off)
    (hwi : ∀ w∈is.flatMap instrWrites,w.1+w.2≤size)
    (hwj : ∀ w∈js.flatMap instrWrites,w.1+w.2≤size)
    (hci : ∀ i∈is,instrBound i≤cap) (hcj : ∀ i∈js,instrBound i≤cap)
    {Q : State → Prop} (hq : WP isa (.block is) s Q) :
    WP isa (.block js) s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧
      KeepRegs (js.flatMap instrClob) s t := by
  obtain ⟨u,hu,heu,_,_,hmu⟩ := eval_sound hsize hD hs he hi hci
  obtain ⟨t,ht,het,_,hkt,hmt⟩ := eval_sound hsize hD hs he hj hcj
  apply WP.of_runBlock
  refine ⟨t,ht,u,post_of_runBlock hq hu,?_,hkt⟩
  apply memory_eq ha hwj hwi hmt hmu
  intro off ho hb
  exact (het.slot off ho hb).symm.trans ((congrArg (fun z => (v z).1) (hEq off ho hb).symm).trans
    (heu.slot off ho hb))

end VG.Proof.Weierstrass.AArch64.Forward
