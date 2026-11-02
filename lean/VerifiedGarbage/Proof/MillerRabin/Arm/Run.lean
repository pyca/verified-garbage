module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Top
import VerifiedGarbage.Proof.MillerRabin.Arm.Body
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The Miller–Rabin round on ARMv7: a call's result (`round_ok`) -/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

section
variable {s : State}

/-- The body's regions are within the frame and the caller's writable ones. -/
theorem roundPre.xCovers (h : roundPre s) : Covers (xRegs s) (pcPushed s).wr := by
  obtain ⟨_, wr, fit, _, _, lay, _⟩ := h
  have hw := lay.2.2.2
  have len : 256 ≤ 8 * (s.gpr .r1).toNat := Nat.le_trans (Nat.le_add_right _ _) hw
  have mS : (⟨State.addr (s.gpr .r0), 8 * (s.gpr .r1).toNat⟩ : Region) ∈ (pcPushed s).wr := by
    rw [pushed_wr, wr]; simp
  refine Covers.of_sub fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq rfl⟩
  · exact ⟨_, mS, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq (Nat.zero_add _)⟩
  · refine ⟨_, mS, kOff, ?_, ?_⟩
    · show State.addr ((s.gpr .r0) + BitVec.ofNat 32 kOff) = _
      exact addr_add (by simp only [kOff]; omega_arith)
    · show kOff + (8 * (s.gpr .r1).toNat - kOff) ≤ _
      simp only [kOff]; omega_arith

/-- The callee-saved registers' slots after the push. -/
theorem roundPre.savedE (h : roundPre s) : Spill.Saved (pcPushed s).mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
  pc_push_callee_saved s h.2.2.2.1

/-- A call's result. -/
theorem round_ok (h : roundPre s) (fios : Bool := false) : WP isa (code (fios := fios)) s fun t => abiPreserved s t ∧ roundPost s t := by
  have spLo := h.2.2.2.1
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  have pre := in_x h
  unfold code
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  obtain ⟨tr, v, run, done⟩ := (body_vp (fios := fios)).wp (bodyIn s) (bodyIn s) ⟨rfl, pre, rfl⟩
  have cov := h.xCovers
  have run' := Exec.widen (rd := (pcPushed s).rd) (wr := (pcPushed s).wr) run
    (Covers.append (Covers.refl _) cov) cov
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  refine WP.mono (Q := fun x => x = v.withRegions (pcPushed s).rd (pcPushed s).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  obtain ⟨⟨A, L, V, LS, ks⟩, hr0⟩ := done
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := ks.sp.trans pre.sp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved := by
    intro p hp
    have e := ks.frameWord (o := p.2) (by
      simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [show (mkP s).sp = s.sp - 56 from rfl] at e
    show v.mem.readW _ 32 = _
    rw [e]
    exact h.savedE p hp
  have fit : (v.withRegions (pcPushed s).rd (pcPushed s).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; have := s.sp.isLt; omega_arith
  have read : InRegions ((v.withRegions (pcPushed s).rd (pcPushed s).wr).rd ++
      (v.withRegions (pcPushed s).rd (pcPushed s).wr).wr)
      (State.addr (v.withRegions (pcPushed s).rd (pcPushed s).wr).sp) 56 := by
    refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩, List.mem_append_right _
      (by rw [State.withRegions_wr, pushed_wr]; exact List.mem_cons_self), ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, State.withRegions_sp, vsp]
    exact BitVec.sub_add_cancel _ _
  · -- The result.
    intro b hb
    have eσ := h.pushedWs
    have fits := pre.fits
    have fit : ∀ j < 11, arrAt (mkP s).w j + 8 * (mkP s).w ≤ 8 * (mkP s).len := fun j hj => by
      have l := pre.len
      have : j * (8 * ((mkP s).w + 2)) ≤ 27 * (8 * ((mkP s).w + 2)) := Nat.mul_le_mul_right _ (by omega_arith)
      have : 8 * (mkP s).w ≤ 8 * ((mkP s).w + 2) := by omega_arith
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
      generalize 8 * ((mkP s).w + 2) = S at *
      omega_arith
    have nE : ∀ j < 11, numAt (bodyIn s).mem (State.addr (s.gpr .r0)) (mkP s).w j =
        numAt s.mem (State.addr (s.gpr .r0)) (mkP s).w j := fun j hj => numAt_congr eσ (fit j hj)
    rw [popped_gpr (by decide), ret, hr0]
    have hc : cOf (mkP s) (bodyIn s).mem = numAt s.mem (State.addr (s.gpr .r0)) (mkP s).w 0 := nE 0 (by decide)
    have hX : xOf (mkP s) (bodyIn s) = numAt s.mem (State.addr (s.gpr .r0)) (mkP s).w 5 := nE 5 (by decide)
    have c3 := pre.c3
    have codd := pre.codd
    have cR := pre.c_lt
    have key : fl (mkP s) (bodyIn s) = Proof.MillerRabin.Round.round (cOf (mkP s) (bodyIn s).mem) b := by
      have e1 : rEnd (mkP s) (bodyIn s) = 4 - VG.Proof.RsaKeyGen.sigOf
          (VG.Proof.RsaKeyGen.mrA (cOf (mkP s) (bodyIn s).mem)) := by
        simp only [rEnd, tOf]; rw [VG.Proof.RsaKeyGen.sigOf_mod]
      show (msqs _ _ _ (rEnd (mkP s) (bodyIn s)) 3 (mrun _ _ _ (tp _ _ (xOf (mkP s) (bodyIn s))
        (oOf (mkP s) (bodyIn s))) (eOf (mkP s) (bodyIn s)) _ _) 3).2 = _
      rw [e1]
      exact final_eq codd c3 cR (by rw [hX, hc]; exact hb) pre.one pre.m1
    rw [key, hc]
    show (BitVec.ofNat 32 (Proof.MillerRabin.Round.round (numAt s.mem (State.addr (s.gpr .r0))
      (wOf s.mem (State.addr (s.gpr .r0))) 0) b).toNat).toNat = _
    generalize Proof.MillerRabin.Round.round (numAt s.mem (State.addr (s.gpr .r0)) (wOf s.mem (State.addr (s.gpr .r0))) 0) b = r
    cases r <;> rfl
  · -- What changed.
    have eσ := h.pushedWs
    intro i hi hk hj
    rw [popped_mem, memT, State.withRegions_mem]
    exact (ks.keepsLite i hi hk hj).trans (eσ i hi)

end

end VG.Proof.MillerRabin.Arm

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The body's run, widened to the caller's regions. -/
theorem body_wide {s : State} (h : roundPre s) (fios : Bool := false) :
    ∃ tr v, Exec isa (body (fios := fios)) (bodyIn s) tr v ∧
      Exec isa (body (fios := fios)) (pcPushed s) tr (v.withRegions (pcPushed s).rd (pcPushed s).wr) := by
  obtain ⟨tr, v, run, _⟩ := (body_vp (fios := fios)).wp (bodyIn s) (bodyIn s) ⟨rfl, in_x h, rfl⟩
  have cov := h.xCovers
  have run' := Exec.widen (rd := (pcPushed s).rd) (wr := (pcPushed s).wr) run
    (Covers.append (Covers.refl _) cov) cov
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  exact ⟨tr, v, run, run'⟩

/-- Two calls with the same public parameters leak the same. -/
theorem round_ct (fios : Bool := false) : RelCT isa (fun s t => roundPre s ∧ roundPre t ∧ s.sp = t.sp ∧ mkP s = mkP t) (code (fios := fios))
    (fun _ _ => True) := by
  unfold code
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp, hP⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.2.2.2.1
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.2.2.2.1
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨trB1, w1, runB1, wide1⟩ := body_wide (fios := fios) hs
      obtain ⟨trB2, w2, runB2, wide2⟩ := body_wide (fios := fios) ht
      obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
      have pre1 := in_x hs
      have pre2 := in_x ht
      rw [← hP] at pre2
      have trB := ((body_vp (fios := fios) (P := mkP s0)).ct _ _ _ _ _ _
        ⟨_, _, ⟨rfl, pre1, rfl⟩, ⟨rfl, pre2, by show t0.gpr .r0 = (mkP s0).ws; rw [hP]; rfl⟩⟩ runB1 runB2).1
      have w1sp : w1.sp = s0.sp - BitVec.ofNat 32 56 := by
        obtain ⟨_, _, run, done⟩ := (body_vp (fios := fios)).wp (bodyIn s0) (bodyIn s0) ⟨rfl, pre1, rfl⟩
        obtain ⟨-, rfl⟩ := Exec.det runB1 run
        obtain ⟨⟨_, _, _, _, ks⟩, _⟩ := done
        exact ks.sp.trans pre1.sp
      have w2sp : w2.sp = t0.sp - BitVec.ofNat 32 56 := by
        obtain ⟨_, _, run, done⟩ := (body_vp (fios := fios)).wp (bodyIn t0) (bodyIn t0) ⟨rfl, in_x ht, rfl⟩
        obtain ⟨-, rfl⟩ := Exec.det runB2 run
        obtain ⟨⟨_, _, _, _, ks⟩, _⟩ := done
        exact ks.sp.trans (in_x ht).sp
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [w1sp, w2sp, sp]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

end VG.Proof.MillerRabin.Arm
