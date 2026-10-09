import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGather
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

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
