import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGather
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser

/-! ## From `ResidentRejVec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def candidates (x mask : BitVec 128) : BitVec 128 := gatherValue x &&& mask

def accepted (x q : BitVec 128) : BitVec 128 :=
  let d := VArr.s4.map2 (fun _ a b => a-b) x q
  VArr.s4.map2 (fun _ _ a => a >>> 31) d d

/-- The common four-instruction vector decoder works both on the four-value
path and on each quarter of the sixteen-value path. -/
theorem decode_ok {s : State} {d : VReg}
    (h2 : d≠.v2) (h4 : d≠.v4) (h5 : d≠.v5)
    (hi : s.v .v3=gatherIndex) :
    WP isa (.block [.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
      .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31)]) s fun t =>
      VChg [d,.v2] s t ∧ t.v d=candidates (s.v .v0) (s.v .v4) ∧
      t.v .v2=accepted (candidates (s.v .v0) (s.v .v4)) (s.v .v5) := by
  refine wp_vop (d := d) (x := gatherValue (s.v .v0)) (by
    simp only [VOp.eval,hi]; rfl) fun a ha =>
    wp_vop (d := d) rfl fun b hb => wp_vop (d := .v2) rfl fun c hc =>
    wp_vop (d := .v2) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨(((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg).mono ?_,?_,?_⟩
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · rw [ht.other d h2,hc.other d h2,hb.v,ha.v,ha.other .v4 (Ne.symm h4)]
    rfl
  · rw [ht.v,hc.v,hb.v,ha.v,ha.other .v4 (Ne.symm h4),
      hb.other .v5 (Ne.symm h5),ha.other .v5 (Ne.symm h5)]
    rfl

theorem accepted_word (x modulus : BitVec 128) {e : Nat} (he : e<4)
    (hq : vword modulus e=8380417#32) (hx : (vword x e).toNat<2^23) :
    vword (accepted x modulus) e=if (vword x e).toNat<8380417 then 1 else 0 := by
  simp only [accepted,VG.AArch64.vword_map2 _ _ _ he,hq]
  exact candidate_bit _ hx

/-- The two 64-bit ANDs used by the fast path accept precisely when all four
lane acceptance bits are one. -/
theorem reduce_accept_bits (a b c d : Bool) :
    let x := ofVWords (if a then 1 else 0) (if b then 1 else 0)
      (if c then 1 else 0) (if d then 1 else 0)
    ((vdword x 0 &&& vdword x 1) ^^^ 0x100000001)=0 ↔ a ∧ b ∧ c ∧ d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Exact branch condition of the four-candidate fast path. -/
theorem accepted_all (x modulus : BitVec 128)
    (hq : ∀e<4,vword modulus e=8380417#32)
    (hx : ∀e<4,(vword x e).toNat<2^23) :
    ((vdword (accepted x modulus) 0 &&& vdword (accepted x modulus) 1) ^^^
      0x100000001)=0 ↔ ∀e<4,(vword x e).toNat<8380417 := by
  rw [← ofVWords_vword (accepted x modulus)]
  rw [accepted_word x modulus (by decide) (hq 0 (by decide)) (hx 0 (by decide)),
      accepted_word x modulus (by decide) (hq 1 (by decide)) (hx 1 (by decide)),
      accepted_word x modulus (by decide) (hq 2 (by decide)) (hx 2 (by decide)),
      accepted_word x modulus (by decide) (hq 3 (by decide)) (hx 3 (by decide))]
  have h := reduce_accept_bits
    (decide ((vword x 0).toNat<8380417)) (decide ((vword x 1).toNat<8380417))
    (decide ((vword x 2).toNat<8380417)) (decide ((vword x 3).toNat<8380417))
  simp only [decide_eq_true_eq] at h
  rw [h]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩ e he
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTry.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def reduceRegisterCode (r : VReg) : List Instr :=
 [.umov .x .x6 r 0,.umov .x .x7 r 1,.logic .and .x .x6 .x6 .x7,
  .logic .eor .x .x6 .x6 .x12]

theorem reduceRegister_ok (s : State) (r : VReg) :
    WP isa (.block (reduceRegisterCode r)) s fun t => Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6=(vdword (s.v r) 0 &&& vdword (s.v r) 1) ^^^ s.gpr .x12 := by
  have h : WP isa (.block (reduceRegisterCode r)) s fun t => Only [.x6,.x7] s t ∧
      t.gpr .x6=(vdword (s.v r) 0 &&& vdword (s.v r) 1) ^^^ s.gpr .x12 := by
    let a := s.write .x .x6 (vdword (s.v r) 0)
    let b := a.write .x .x7 (vdword (s.v r) 1)
    have ha : Only [.x6] s a := only_write _ _ _ _
    have hb : Only [.x7] a b := only_write _ _ _ _
    refine WP.cons (s' := a) rfl (WP.cons (s' := b) rfl ?_)
    refine wp_and fun c hc ec => wp_eor fun t ht et => wp_nil ?_
    refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_⟩
    rw [et,ec,hb.get .x6,hc.get .x12,hb.get .x12,ha.get .x12]
    rfl
  exact WP.mono (WP.keepV (by rfl : (reduceRegisterCode r).all (fun i => !writesV i)=true) h)
    fun _ ⟨⟨hk,hv⟩,hvec⟩ => ⟨hk,hvec,hv⟩

def reduceCode : List Instr := reduceRegisterCode .v2

theorem reduce_ok (s : State) :
    WP isa (.block reduceCode) s fun t => Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6=(vdword (s.v .v2) 0 &&& vdword (s.v .v2) 1) ^^^ s.gpr .x12 :=
  reduceRegister_ok s .v2

/-- Complete four-candidate probe, with an exact branch flag and vector
frame suitable for composing probes into the sixteen-candidate path. -/
theorem vectorTry_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hi : s.v .v3=gatherIndex) :
    WP isa (.block vectorTry) s fun t =>
      Keep [.x6,.x7] s t ∧ t.mem=s.mem ∧
      (∀r,r≠.v0 → r≠.v1 → r≠.v2 → t.v r=s.v r) ∧
      t.v .v1=candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4) ∧
      t.gpr .x6=
        (vdword (accepted (candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)) (s.v .v5)) 0 &&&
         vdword (accepted (candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)) (s.v .v5)) 1) ^^^ s.gpr .x12 := by
  refine wp_ldrq (a := s.gpr .x2) (by decide) (ptr_zero _) hr fun a ha => ?_
  rw [show ([Instr.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
      .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
      .umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.logic .and .x .x6 .x6 .x7,
      .logic .eor .x .x6 .x6 .x12] : List Instr) =
      ([.vop (.tbl .v1 .v0 .v3),.vop (.logic .and .v1 .v1 .v4),
      .vop (.sub .s4 .v2 .v1 .v5),.vop (.shift .ushr .s4 .v2 .v2 31)] : List Instr)++reduceCode from rfl,
    WP.block_append_iff]
  refine WP.mono (decode_ok (d := .v1) (by decide) (by decide) (by decide)
    (by rw [ha.other .v3 (by decide)]; exact hi)) fun b ⟨hb,hv,hflag⟩ => ?_
  refine WP.mono (reduce_ok b) fun t ⟨ht,hvec,hx⟩ => ?_
  refine ⟨((ha.chg.keep.trans hb.keep).trans ht.keep).mono (by decide),
    ht.mem.trans (hb.mem.trans ha.mem),?_,?_,?_⟩
  · intro r h0 h1 h2
    rw [hvec,hb.v r (by simpa using And.intro h1 h2),ha.other r h0]
  · rw [hvec,hv,ha.v,ha.other .v4 (by decide)]
  · rw [hx,hflag,ha.v,ha.other .v4 (by decide),ha.other .v5 (by decide),hb.gpr,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
