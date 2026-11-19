module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Chi
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Sha3.AArch64.Neon.Squeeze`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64 (Upd Mupd wp_str)

structure OutKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem OutKeep.refl (s : State) : OutKeep s s := ⟨fun _ _ _ => rfl,rfl,rfl,rfl,rfl⟩
theorem OutKeep.trans {s t u : State} (h : OutKeep s t) (k : OutKeep t u) : OutKeep s u :=
  ⟨fun r h6 h7 => (k.gpr r h6 h7).trans (h.gpr r h6 h7), k.vec.trans h.vec,
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem OutKeep.upd {s t : State} {r : Reg} {v : BitVec 64}
    (h : Upd s t r v) (hr : r = .x6 ∨ r = .x7) : OutKeep s t :=
  ⟨fun q h6 h7 => h.other q (by rcases hr with h | h <;> subst r <;> with_reducible assumption),h.vec,h.rd,h.wr,h.sp⟩
theorem OutKeep.mem {s t : State} {m : Mem} (h : Mupd s t m) : OutKeep s t :=
  ⟨fun _ _ _ => congrFun h.gpr _,h.vec,h.rd,h.wr,h.sp⟩

def outAddr (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (8*i)
def outR (p : Addr) : Region := ⟨p,168⟩
def RateAt (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 21, m.readW (outAddr p i) 64 = A[i]!

theorem squeeze_step {s : State} {a b : Addr} {ra rb : Reg} {i : Nat} (hi : i < 21)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hwa : InRegions s.wr (outAddr a i) 8) (hwb : InRegions s.wr (outAddr b i) 8) :
    WP isa (.block ([.umov .x .x6 (vreg i) 0,.umov .x .x7 (vreg i) 1,
      .str .x .x6 ra (8*i),.str .x .x7 rb (8*i)] : List Instr)) s fun t =>
      OutKeep s t ∧ t.mem = (s.mem.writeW (outAddr a i) (vdword (s.v (vreg i)) 0)).writeW
        (outAddr b i) (vdword (s.v (vreg i)) 1) := by
  refine WP.cons (s' := s.write .x .x6 (vdword (s.v (vreg i)) 0)) (by rfl) ?_
  have h1 := Upd.write64 s .x6 (vdword (s.v (vreg i)) 0)
  let s1 := s.write .x .x6 (vdword (s.v (vreg i)) 0)
  refine WP.cons (s' := s1.write .x .x7 (vdword (s1.v (vreg i)) 1)) (by rfl) ?_
  have h2 := Upd.write64 s1 .x7 (vdword (s1.v (vreg i)) 1)
  refine wp_str ⟨by omega_using [],by omega_using [hi]⟩
    (by rw [h2.other ra ha7,h1.other ra ha6,ha])
    (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_str ⟨by omega_using [],by omega_using [hi]⟩
    (by rw [h3.gpr,h2.other rb hb7,h1.other rb hb6,hb])
    (by rw [h3.wr,h2.wr,h1.wr]; exact hwb) fun s4 h4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((OutKeep.upd h1 (Or.inl rfl)).trans (OutKeep.upd h2 (Or.inr rfl))).trans
      ((OutKeep.mem h3).trans (OutKeep.mem h4))
  · rw [h4.mem,h3.mem,h3.gpr,h2.gpr,h2.other .x6 (by decide),h1.gpr,h2.mem,h1.mem,h1.vec]
    rfl

/-- Word-wise output is the SHA-3 specification's byte serialization. -/
theorem RateAt.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : RateAt m p A)
    {j : Nat} (hj : j < 168) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega_using [hj])
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega_using [])] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega_using []] at he
  exact he
end VG.Proof.Sha3.AArch64.Neon

end

end

/-! ### `Sha3.AArch64.Neon.HwLanes`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector

def lane (s : State) (e : Nat) : Low := fun r => vdword (s.v r) e

theorem lane_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword,BitVec.extractLsb'_xor]
theorem lane_and (a b : BitVec 128) (e : Nat) : vdword (a &&& b) e = vdword a e &&& vdword b e := by
  simp only [vdword,BitVec.extractLsb'_and]
theorem lane_not (a : BitVec 128) {e : Nat} (he : e < 2) : vdword (~~~a) e = ~~~vdword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not,hi,decide_true,Bool.true_and,
    show 64*e+i < 128 by omega_using [he, hi]]

theorem lane_setV (s : State) (d : VReg) (v : BitVec 128) (e : Nat) :
    lane (s.setV d v) e = put (lane s e) d (vdword v e) := by
  funext r
  simp only [lane,put,RegUpd.v_setV]
  split <;> rfl

theorem op_lane (s : State) (op : Op) {e : Nat} (he : e < 2) :
    lane (opState s op) e = opLow (lane s e) op := by
  rcases (show e = 0 ∨ e = 1 by omega_using [he]) with rfl | rfl
  · exact op_low s op
  · cases op <;> simp only [opState,lane_setV,opLow,lane_xor,lane_and,lane_not _ (by decide : 1 < 2),
      VArr.map2,vdword_ofVDwords_1,lane]

/-- The SHA3 instructions operate independently on both 64-bit lanes. -/
theorem ops_lanes (ops : List Op) (s : State) :
    WP isa (.block (ops.map Op.instr)) s fun t => Keep s t ∧
      ∀ e < 2,lane t e = runLow ops (lane s e) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨Keep.refl _,fun _ _ => rfl⟩
  | cons op ops ih =>
    refine VG.Proof.Sha3.AArch64.WP.cons (op_exec s op)
      (WP.mono (ih (opState s op)) fun t ⟨ht,hl⟩ => ⟨(op_keep s op).trans ht,?_⟩)
    intro e he
    rw [hl e he,op_lane s op he]
    rfl

/-- The existing register schedule's pure mathematics applies to either lane. -/
theorem core_math (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    CLanes (runLow (theta++rhoPi++chi) σ) A := by
  have ht := theta_lanes σ A h
  have hd : DLanes (runLow theta σ) A := theta_d σ A h
  have hr := rho_lanes (runLow theta σ) A ht hd
  have hc := chi_lanes (runLow rhoPi (runLow theta σ)) A hr
  simpa only [runLow,List.foldl_append] using hc
end VG.Proof.Sha3.AArch64.Neon.Hw

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def CPairs (s : State) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25,s.v (vreg i) = ofVDwords (chiWord A i) (chiWord B i)

theorem core2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block ((theta++rhoPi++chi).map Op.instr)) s fun t => Keep s t ∧ CPairs t A B := by
  refine WP.mono (ops_lanes (theta++rhoPi++chi) s) fun t ⟨ht,hl⟩ => ⟨ht,?_⟩
  have ha : ALanes (lane s 0) A := by
    intro i hi
    change vdword (s.v (vreg i)) 0 = _
    rw [hp i hi,vdword_ofVDwords_0,Proof.Sha3.getElem!_eq A hi]
  have hb : ALanes (lane s 1) B := by
    intro i hi
    change vdword (s.v (vreg i)) 1 = _
    rw [hp i hi,vdword_ofVDwords_1,Proof.Sha3.getElem!_eq B hi]
  have hca := core_math (lane s 0) A ha
  have hcb := core_math (lane s 1) B hb
  intro i hi
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    change lane t 0 (vreg i) = _
    rw [hl 0 (by decide)]
    exact hca i hi
  · rw [vdword_ofVDwords_1]
    change lane t 1 (vreg i) = _
    rw [hl 1 (by decide)]
    exact hcb i hi

theorem out_word (A : Spec.Sha3.State) (rc : BitVec 64) {i : Nat} (hi : i < 25) :
    (Proof.Sha3.outState A rc)[i]! = if i = 0 then chiWord A i ^^^ rc else chiWord A i := by
  rw [Proof.Sha3.getElem!_eq _ hi,chiWord_out A rc i hi]

theorem iota2_ok {s : State} {A B : Spec.Sha3.State} (hp : CPairs s A B) (rc : BitVec 64)
    (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun t => VChg allV s t ∧
      Pairs t (Proof.Sha3.outState A rc) (Proof.Sha3.outState B rc) := by
  unfold iota
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  rw [out_word A rc hi,out_word B rc hi]
  by_cases h0 : i = 0
  · subst i
    change t.v .v0 = ofVDwords (chiWord A 0 ^^^ rc) (chiWord B 0 ^^^ rc)
    rw [h2.v,h1.get .v0,h1.v,hc]
    change s.v .v0 ^^^ ofVDwords rc rc = _
    have hp0 : s.v .v0 = ofVDwords (chiWord A 0) (chiWord B 0) := hp 0 (by decide)
    rw [hp0,pair_xor]
  · rw [ite_eq_right h0,ite_eq_right h0,h2.get (vreg i) (by
      change ¬ vreg i = vreg 0
      rw [vreg_inj i (by omega_using [hi]) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem vchg_core {s s' : State} {rs : List VReg} (h : VChg rs s s') : CoreKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r,h.mem,h.rd,h.wr,h.sp⟩

theorem round2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++ chi.map Op.instr ++ iota =
    constant (Spec.Sha3.RC r) ++ (theta++rhoPi++chi).map Op.instr ++ iota by
      simp only [List.map_append,List.append_assoc]]
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s1 ⟨h1,hv1,hrc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (core2_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s2 ⟨h2,hp2⟩ => ?_
  refine WP.mono (iota2_ok hp2 (Spec.Sha3.RC r) (by rw [h2.gpr,hrc,constantLow_RC r hr]))
    fun t ⟨h3,hpt⟩ => ⟨h1.trans (h2.core.trans (vchg_core h3)),?_⟩
  simpa only [Proof.Sha3.outState_eq] using hpt
end VG.Proof.Sha3.AArch64.Neon.Hw
