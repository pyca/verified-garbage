import VerifiedGarbage.Proof.Ed448.Arm.BaseInit
import VerifiedGarbage.Proof.Ed448.Arm.BaseBits
import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
import VerifiedGarbage.TCB.Arm.Target

/-!
# Ed448 base-point multiplication on ARMv7: the whole function

`vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)` computes the
encoding of the ladder over the scalar's bits (`scalarBase_ladder`): the
entry, the scalar's bits, the loop (`R` ends as `ladder k 456`), the
inversion of `Z` and the encoding. Every write is in the working space but
the result's, so the scalar is read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (ladder)
open VG.Impl.X448.Arm (slot BITS ACC saved)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition of `vg_ed448_scalar_base`, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 57⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far_ws {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega)
    (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem baseEntry_eq : baseEntry =
    ([.mov .r3 (.reg .r2)] : List Instr) ++ setupHead ++ initSlots := rfl

theorem scalarBase_ladder {s : State} (h : BasePre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s.mem (State.addr (s.gpr .r1)) 57)) 456) := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r2) = b := ⟨_, rfl⟩
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, ← hbase]; simp
  have kd : ∀ j < 57, 8192 ≤ ofs base (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) :=
    fun j hj => far_ws (hbase ▸ h.scalar_ws) hj (by decide)
  have kr : ∀ j < 57, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨State.addr (s.gpr .r1), 57⟩, by rw [h.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  unfold scalarBase
  rw [baseEntry_eq, List.append_assoc, List.singleton_append]
  -- The entry.
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => ?_)
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok (s := u) (base := base) (by rw [hu.gpr, hbase])
    (by rw [hu.wr]; exact hw₀) (by rw [hu.gpr]; exact h.f2)) fun v ⟨hsv, rv, svv, ov, kv⟩ => ?_
  refine WP.mono (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw : Scr w base := hsv.of_keeps kw (by decide)
  have kuw : Keeps [.r3, .r12, .r0, .r6, .r4] s w :=
    (rest_keeps (hu.rest (by decide))).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have r1w : w.gpr .r1 = s.gpr .r1 := kuw.1 _ (by decide)
  have r12w : w.gpr .r12 = s.gpr .r0 := by
    rw [kw.1 _ (by decide), rv, hu.other _ (by decide)]
  have mw : ∀ x, 8192 ≤ ofs base x → w.mem x = s.mem x := fun x hx => by
    rw [ow x (Or.inr (by omega)), ov x (Or.inr (by omega)), hu.mem]
  have bw : bytesAt w.mem (State.addr (s.gpr .r1)) 57 = bytesAt s.mem (State.addr (s.gpr .r1)) 57 := by
    unfold bytesAt; exact List.map_congr_left fun j hj => mw _ (kd j (List.mem_range.mp hj))
  have sn : ∀ i < 8, saved[i]! ≠ .r3 := by decide
  have svw : Saved base s.gpr w.mem := by
    intro i hi
    rw [ow.word (by omega) (by omega), svv i hi]
    exact hu.other _ (sn i hi)
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok (k := State.addr (s.gpr .r1)) hsw (by rw [r1w])
    (by rw [r1w]; exact h.f1) (by rw [kuw.2.1, kuw.2.2]; exact kr) kd)
    fun x ⟨gx, rdx, wrx, ox, bitsx⟩ => ?_)
  have kx : Keeps baseBitRegs w x := ⟨gx, rdx, wrx⟩
  have hsx : Scr x base := hsw.of_keeps kx (by decide)
  have ex : ∀ i : Index, E x.mem base i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E lw i]
    simp only [E, F]
    rw [ox.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega)]
  have bx : BoundedEnv x.mem base := by
    intro i j hj
    rw [ox.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact initSlots_bounded lw i j hj
  rw [bw] at bitsx
  -- The loop.
  refine WP.seq (WP.mono (baseLoop_ok (s₀ := x) (s := x) bitsx (fun s' h1 h2 h3 h4 h5 => ?_))
    fun y hy => ?_)
  · have k' : Keeps (.r11 :: workRegs) x s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hsx.of_keeps k' (by decide), h3 ▸ bx, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [h3]; simp only [pt, ex]
      rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
        show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
        show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
        show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
        Proof.X448.toFe_self, Proof.X448.toFe_self]
      rfl
    · rw [h3]; simp only [pt, ex]
      rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
        show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
        show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
        show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
        Proof.X448.toFe_self, Proof.X448.toFe_self]
    · rw [h3, ex]; exact Proof.X448.toFe_self _
  -- The encoding.
  have r12y : y.gpr .r12 = s.gpr .r0 := by
    rw [hy.regs.1 _ (by decide), gx _ (by decide), r12w]
  have wry : y.wr = s.wr := by rw [hy.regs.2.2, wrx, kuw.2.2]
  have svy : Saved base s.gpr y.mem :=
    (svw.outside ox (by decide)).outside2 hy.mem (by decide) (by decide)
  refine WP.mono (baseEncode_ok hy.scr hy.bounded (q := State.addr (s.gpr .r0)) (by rw [r12y])
    (by rw [r12y]; exact h.f0) (by rw [wry, h.wr]; simp) (hbase ▸ h.out_ws) svy)
    fun t ⟨bt, rt, kt, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt 0 (by decide)
    · exact rt 1 (by decide)
    · exact rt 2 (by decide)
    · exact rt 3 (by decide)
    · exact rt 4 (by decide)
    · exact rt 5 (by decide)
    · exact rt 6 (by decide)
    · exact rt 7 (by decide)
    · rw [kt.1 _ (by decide), hy.regs.1 _ (by decide), gx _ (by decide), kuw.1 _ (by decide)]
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r
