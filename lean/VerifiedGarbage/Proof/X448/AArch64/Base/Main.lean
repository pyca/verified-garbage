import VerifiedGarbage.Proof.X448.AArch64.Base.Finish
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Comb
import VerifiedGarbage.Impl.X448.AArch64.BaseFn
import VerifiedGarbage.Proof.X448.Edwards.Ladder
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# X448 of the base point on AArch64: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X448.x448BaseContract` it uses, stated for
AArch64), and `vg_x448_base`'s correctness against it: the comb leaves `[k] B`
on edwards448, whose `y² / x²` is `X448(k, 5)` (`x448_basePoint`).
-/

namespace VG.Proof.X448

open VG VG.AArch64 VG.Impl.X448.AArch64.Base in
/-- `vg_x448_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static `combSym`. -/
def x448BaseAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let scalar : Region := ⟨s.gpr .x1, 56⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [scalar, ⟨s.syms combSym, 8 * combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ scalar.Disjoint scratch ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧
      Proof.X448.AArch64.Base.CombHeld s [out, scratch]
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .x0) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .x1) 56) Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combSym = s₂.syms combSym

end VG.Proof.X448

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The precondition, by name. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 56⟩, ⟨s.syms combSym, 8 * combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]
  out_sc : (⟨s.gpr .x0, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  scalar_sc : (⟨s.gpr .x1, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  sc_fit : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  held : CombHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]

theorem Pre.of (s : State) (h : Proof.X448.x448BaseAArch64.pre s) : Pre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

/-- The tables, from the precondition. -/
theorem Pre.tbl {s : State} (hp : Pre s) : TblAt s (s.gpr .x2) (s.syms combSym) :=
  hp.held.tblAt (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))) (by simp)

theorem decodeScalar448_lt (kb : List Byte) : Spec.X448.decodeScalar448 kb < 256 ^ 56 := by
  rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
  exact Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

open VG.Proof.Ed448 (Rep baseAff)

theorem correct {sE : State} (hp : Pre sE) :
    WP isa x448Base sE fun s' => (∀ r ∈ preserved, s'.gpr r = sE.gpr r) ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (sE.v r).extractLsb' 0 64) ∧
      Proof.X448.x448BaseAArch64.post sE s' := by
  have hn := hp.sc_fit
  have hw : (⟨sE.gpr .x2, 8192⟩ : Region) ∈ sE.wr := by rw [hp.wr]; simp
  have kr : ∀ q < 56, InRegions (sE.rd ++ sE.wr) (sE.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨sE.gpr .x1, 56⟩, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have kd : ∀ q < 56, 8192 ≤ ofs (sE.gpr .x2) (sE.gpr .x1 + BitVec.ofNat 64 q) :=
    fun q hq => far hp.scalar_sc hq (by decide)
  set base := sE.gpr .x2 with hbase
  set kb := Spec.X448.bytesAt sE.mem (sE.gpr .x1) 56
  set k := Spec.X448.decodeScalar448 kb
  unfold x448Base
  refine WP.seq (WP.mono (setup_ok rfl hw hn rfl kr kd hp.tbl) fun s1 R => ?_)
  refine WP.seq (WP.mono (Ed448.AArch64.Point56.combLoop_ok (by decide) (by decide) (s₀ := s1) R.inv rfl) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (Ed448.AArch64.Point56.combineCall_ok (decodeScalar448_lt kb) h2) fun s3 ⟨f3, r3⟩ => ?_)
  unfold VG.Impl.X448.AArch64.Base.finish
  refine WP.seq (WP.mono (squares_ok f3.scr f3.env) fun s4 ⟨k4, b4, e4⟩ => ?_)
  have hs4 := k4.scr f3.scr
  refine WP.seq (WP.mono (invert_ok hs4 b4) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 : Scr s5 base := hs4.of_keeps k5.regs (by decide)
  simp only [List.cons_append]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.moveOutput_ok s5) fun s6 ⟨x16, m6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  -- The working space outside the slots and the products' working space, from `s1` on.
  have o15 : Outside2 base 64 2816 ACC 1152 s1.mem s5.mem := (f3.mem.trans k4.mem).trans k5.mem
  have o16 : Outside2 base 64 2816 ACC 1152 s1.mem s6.mem := by rw [m6]; exact o15
  have out6 : s6.gpr .x1 = sE.gpr .x0 := by
    rw [x16, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), f3.out, R.out]
  have wr6 : s6.wr = sE.wr := by rw [k6.2.2, k5.regs.2.2, k4.regs.2.2, f3.wr, R.wr]
  have hw6 : ∀ j < 56, InRegions s6.wr (off (sE.gpr .x0) j) 1 := fun j hj =>
    ⟨⟨sE.gpr .x0, 56⟩, by rw [wr6, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have sv6 : Saved base sE.gpr s6.mem := R.saved.outside2 o16 (by decide) (by decide)
  have svx6 : SavedX base sE.gpr s6.mem := R.savedX.outside2 o16 (by decide) (by decide)
  have svV6 : SavedV base sE.v s6.mem := R.savedV.outside2 o16 (by decide) (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok hs6 (by rw [m6]; exact b5) out6 hw6 (fun j hj => far_output hp.out_sc hj)
    sv6 svx6 svV6) fun s' ⟨rb, x20, rx, rv, kf, _, result⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : s'.gpr .x30 = sE.gpr .x30 := by
      rw [kf.1 _ (by decide), k6.1 _ (by decide), k5.regs.1 _ (by decide), k4.regs.1 _ (by decide),
        f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    · exact rx 0 (by decide)
    · exact rx 1 (by decide)
    · exact rx 2 (by decide)
    · exact rx 3 (by decide)
    · exact rx 4 (by decide)
    · exact rx 5 (by decide)
    · exact rx 6 (by decide)
    · exact rx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rv 0 (by decide)
    · exact rv 1 (by decide)
    · exact rv 2 (by decide)
    · exact rv 3 (by decide)
    · exact rv 4 (by decide)
    · exact rv 5 (by decide)
    · exact rv 6 (by decide)
    · exact rv 7 (by decide)
  · change Spec.X448.bytesAt s'.mem (sE.gpr .x0) 56 = _
    rw [result, m6, e5, invEnv_x2, invEnv_eval, e4]
    refine (VG.Proof.X448.Edwards.x448_basePoint kb _ ?_).symm
    have hu := VG.Proof.X448.u_rep r3
    rw [natCast_zsmul] at hu
    rw [← hu, VG.Proof.X448.invert_eq]
    rfl

end VG.Proof.X448.AArch64.Base
