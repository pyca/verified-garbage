module

-- separate module: its proofs cost more than its imports, and the satisfiability witness's
-- changes (`DecSat`) need not re-check them

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rsa.Arm.PrivPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls

/-!
# `vg_rsa_oaep_decrypt_precomputed` on ARMv7

`vg_rsa_oaep_decrypt`'s code (`decryptP`) calling
`vg_rsa_private_checked_precomputed` with the key's precomputed values `pre`
and `pre_len`, our arguments 25 and 26, as its stack arguments 16 and 17
(`privArgsP`): the slots `sS` and `sSrc`, until `scratch` goes back to `sS`
after the call (`fixScr`). The layout is `vg_rsa_oaep_decrypt`'s with `pre`
among the buffers read and our two more arguments (`PreP`), and the body's
proofs are `vg_rsa_oaep_decrypt`'s but for the call (`pa2_vp`, `call_vpP`,
`fix_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg copyArg)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- What a layout given `pre` has: `pre` among the buffers read, our two
more arguments, and what the entry state holds of `pre`. -/
structure PreP (P : EP) : Prop where
  x : P.X = [⟨State.addr P.pre, P.prl * 8⟩]
  xa : P.xargs = [P.pre, BitVec.ofNat 32 P.prl]
  prl32 : P.prl < 2 ^ 32
  prlv : P.prl = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  px : P.PX = fun σ => Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) =
      some (Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.prl) ∧
    Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr P.pre) P.K = P.preL

/-- `pre`, a buffer only read. -/
abbrev EP.PRE (P : EP) : Region := ⟨State.addr P.pre, P.prl * 8⟩

theorem PreP.mem {P : EP} (hP : PreP P) : P.PRE ∈ P.lay.ro := by
  simp [hP.x]

/-- Our arguments 25 and 26, `pre` and `pre_len`. -/
theorem argAtX {P : EP} {σ s : State} (hP : PreP P) (hi : In P σ) (hs : P.lay.St σ s) {j : Nat}
    (hj : j = 25 ∨ j = 26) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = P.lay.fr (arg j) ∧
    InRegions (s.rd ++ s.wr) (P.lay.fr (arg j)) 4 ∧
    s.mem.readW (P.lay.fr (arg j)) 32 = P.lay.argv.getD j 0 := by
  have hl : j < P.lay.argv.length := by
    simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil]; omega
  have hA := hi.ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + P.A; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- `pre` and `pre_len` to the call's stack arguments 16 and 17. -/
theorem pa2_wp (P : EP) (hP : PreP P) {σ s : State} (hc : Ctx P.lay P.scr σ s) (hi : In P σ) :
    WP isa (.block [sp0, ld .r4 (arg 25), st .r4 64, ld .r4 (arg 26), st .r4 68]) s
      fun t => t.mem = (s.mem.writeW (P.lay.fr 64) P.pre).writeW (P.lay.fr 68) (BitVec.ofNat 32 P.prl) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r1 = s.gpr .r1 ∧
        t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 := by
  have hg := hi.geo
  obtain ⟨a25, r25, v25⟩ := argAtX hP hi hc.st (j := 25) (.inl rfl)
  obtain ⟨a26, r26, v26⟩ := argAtX hP hi hc.st (j := 26) (.inr rfl)
  replace v25 : s.mem.readW (P.lay.fr (arg 25)) 32 = P.pre := by
    rw [v25]; simp [EP.argv, hP.xa]
  replace v26 : s.mem.readW (P.lay.fr (arg 26)) 32 = BitVec.ofNat 32 P.prl := by
    rw [v26]; simp [EP.argv, hP.xa]
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr (P.lay.fr d) 4 := fun d hd => hc.st.inFr hd
  have rd26 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (P.lay.fr 64) v).readW (P.lay.fr (arg 26)) 32 = m.readW (P.lay.fr (arg 26)) 32 :=
    fun m v => Lay.readW_fr_other _ m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; decide)
      (by decide) (by decide)
  have l25 : arg 25 < 4096 := by decide
  have l26 : arg 26 < 4096 := by decide
  prun [sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, l25, l26, a25, r25, v25, a26, r26, v26, rd26]

/-- Before the call of `vg_rsa_private_checked_precomputed`. -/
abbrev R1P (P : EP) (σ s : State) : Prop :=
  P.lay.St σ s ∧ In P σ ∧
    PrivArgs s (P.scr + BitVec.ofNat 32 oEm) P.n P.e P.ct P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024) ∧
    stackArg s 16 = P.pre ∧ stackArg s 17 = BitVec.ofNat 32 P.prl

theorem pa2_vp (P : EP) (hP : PreP P) :
    VP (R1 P) (.block [sp0, ld .r4 (arg 25), st .r4 64, ld .r4 (arg 26), st .r4 68]) (R1P P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, pa⟩ => ?_
  have hg := hi.geo
  refine WP.mono (pa2_wp P hP hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  have fr : Frame [⟨P.lay.fr 64, 8⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 64) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have rd0 : ∀ (u : State), u.sp = s.sp → ∀ i, i < 18 → stackArg u i = u.mem.readW (P.lay.fr (4 * i)) 32 := by
    intro u hu i hi'
    simp only [stackArg, stackArgAddr, hu, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega)]
  have keep : ∀ i, i < 16 → stackArg t i = stackArg s i := fun i hi' => by
    rw [rd0 t sp i (by omega), rd0 s rfl i (by omega), m, Lay.readW_fr_other _ _ _ (by omega) (by omega) (by decide),
      Lay.readW_fr_other _ _ _ (by omega) (by omega) (by decide)]
  refine ⟨hc.st.write fr (fun r hr => ?_) rd wr sp, hi,
    { pa with
      r0 := t0.trans pa.r0, r1 := t1.trans pa.r1, r2 := t2.trans pa.r2, r3 := t3.trans pa.r3
      a0 := (keep 0 (by decide)).trans pa.a0, a1 := (keep 1 (by decide)).trans pa.a1
      a2 := (keep 2 (by decide)).trans pa.a2, a3 := (keep 3 (by decide)).trans pa.a3
      a4 := (keep 4 (by decide)).trans pa.a4, a5 := (keep 5 (by decide)).trans pa.a5
      a6 := (keep 6 (by decide)).trans pa.a6, a7 := (keep 7 (by decide)).trans pa.a7
      a8 := (keep 8 (by decide)).trans pa.a8, a9 := (keep 9 (by decide)).trans pa.a9
      a10 := (keep 10 (by decide)).trans pa.a10, a11 := (keep 11 (by decide)).trans pa.a11
      a12 := (keep 12 (by decide)).trans pa.a12, a13 := (keep 13 (by decide)).trans pa.a13
      a14 := (keep 14 (by decide)).trans pa.a14, a15 := (keep 15 (by decide)).trans pa.a15 }, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.lay.FR, List.mem_cons_self, Offset.sub_base _ (show 64 + 8 ≤ frameBytes by decide)⟩
  · rw [rd0 t sp 16 (by decide), m, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [rd0 t sp 17 (by decide), m, Mem.readW_writeW_self32]

theorem leak_st {P : EP} (hP : PreP P) {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  have px := hi.pxT
  rw [hP.px] at px
  have le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hP.prlv, Spec.Rsa.privatePrecomputedWords]; omega
  have rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [← px.2]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem key_st {P : EP} (hP : PreP P) {σ s : State} (hi : In P σ) (hs : P.lay.St σ s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K)
      (Spec.Rsa.bytesAt s.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.q) P.ql) =
    some (Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.prl) := by
  have px := hi.pxT
  rw [hP.px] at px
  have rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [nB_at hi hs, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp), rw]
  exact px.1

theorem call_preP {P : EP} (hP : PreP P) {σ s : State} (hr : R1P P σ s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRdP P.B P.n P.e P.ct P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
        (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hs, hi, pa, a16, a17⟩ := hr
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
  have fit := ok.fit
  have hB := ok.B56
  have hA := ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have hPm := hP.mem
  refine priv_preP pa a16 a17 hP.prl32 hs.sp hB (by simp only [frameBytes] at fit; omega) ?_ dIS ?_ ?_ hP.prlv
    (key_st hP hi hs)
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    have ro : ∀ R ∈ P.lay.ro, ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint R := fun R hR w hw =>
      (ok.rw_ro (w := P.SCR) (r := R) (by simp) hR).sub_left hw
    have fr : ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint ⟨State.addr P.B, 72⟩ := fun hw => by
      rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 72)
        (by show 0 + 72 ≤ frameBytes + 56; decide)).symm).sub_left hw
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro P.N (by simp) sI
    · exact ro P.E (by simp) sI
    · exact ro P.CT (by simp) sI
    · exact ro P.PP (by simp) sI
    · exact ro P.QQ (by simp) sI
    · exact ro P.DP (by simp) sI
    · exact ro P.DQ (by simp) sI
    · exact ro P.QI (by simp) sI
    · exact ro P.PRE hPm sI
    · exact fr sI
    · exact ro P.N (by simp) sS'
    · exact ro P.E (by simp) sS'
    · exact ro P.CT (by simp) sS'
    · exact ro P.PP (by simp) sS'
    · exact ro P.QQ (by simp) sS'
    · exact ro P.DP (by simp) sS'
    · exact ro P.DQ (by simp) sS'
    · exact ro P.QI (by simp) sS'
    · exact ro P.PRE hPm sS'
    · exact fr sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact ok.low_buf (R := P.CT) (.inl (by simp))
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · exact ok.low_buf (R := P.PRE) (.inl hPm)
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega
    · exact fs (List.mem_append_left _ hPm)

/-- After the call of `vg_rsa_private_checked_precomputed`: `R2` but for
`scratch`'s slot. -/
abbrev R2P (P : EP) (σ s : State) : Prop :=
  P.lay.St σ s ∧ In P σ ∧ (∀ i < P.K, s.mem (VG.Proof.RsaPss.Arm.sa P.scr i) = V P σ i) ∧ s.gpr .r0 = rV P σ ∧ OcK P σ

/-- `EM` and the result: the call. -/
theorem call_vpP (P : EP) (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1P P) (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (R2P P) := by
  refine VG.Proof.RsaPkcs1Sig.Arm.VP.callC (fun s h => Proof.Rsa.Arm.private_contract_correctP v s h)
    (Proof.Rsa.Arm.private_contract_ctP v) (privCodeP_stack v)
    (privRdP P.B P.n P.e P.ct P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
    (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
    (fun _ _ hr => call_preP hP hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hs, hi, -⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega)⟩
    have wr' : Covers (privWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr := by
      rw [privWr, e1, e2]; exact (inS (by unfold oEm; omega)).cons (inS (by unfold oRsa; omega))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine (hro P.CT (by simp)).cons ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons ((hro P.PRE hP.mem).cons (Covers.cons ?_ Covers.nil)))))))
    rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 72 ≤ frameBytes; decide))).right
  · rw [hr.1.sp]; exact hr.2.1.ok.B56
  · obtain ⟨hs₁, hi₁, pa₁, p16, p17⟩ := h₁
    obtain ⟨hs₂, hi₂, pa₂, q16, q17⟩ := h₂
    exact priv_pubP pa₁ pa₂ (by rw [hs₁.sp, hs₂.sp]) p16 q16 p17 q17
      (by rw [nB_at hi₁ hs₁, nB_at hi₂ hs₂]) (by rw [eB_at hi₁ hs₁, eB_at hi₂ hs₂])
      (by rw [leak_st hP hi₁ hs₁, leak_st hP hi₂ hs₂]) _ _
  · obtain ⟨hs, hi, pa, -, -⟩ := hr
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have st : P.lay.St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    have := priv_postP pa po
    rw [nB_at hi hs, eB_at hi hs, hs.ro (R := P.CT) (by simp), hs.ro (R := P.PP) (by simp),
      hs.ro (R := P.QQ) (by simp), hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp),
      hs.ro (R := P.QI) (by simp)] at this
    obtain ⟨r0, hb, hl⟩ := em_of this
    refine ⟨st, hi, fun i hi' => ?_, r0, hl⟩
    have e := hb i hi'
    rw [e1] at e
    refine Eq.trans ?_ e
    simp only [VG.Proof.RsaPss.Arm.sa, oEm, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

/-- `scratch` back to its slot. -/
theorem fix_vp (P : EP) : VP (R2P P) (.block fixScr) (R2 P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.sp.trans h₂.1.sp.symm) fun σ s ⟨hs, hi, he, r0, hk⟩ => ?_
  have hg := hi.geo
  obtain ⟨a21, r21, v21⟩ := argAt hi hs (j := 21) (by decide)
  replace v21 : s.mem.readW (P.lay.fr (arg 21)) 32 = P.scr := v21
  have hw : WP isa (.block fixScr) s fun t => t.mem = s.mem.writeW (P.lay.fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = s.gpr .r0 := by
    prun [fixScr, sp0, ld, st, hs.sp, a21, r21, v21, slotAt hi (d := sS) (by decide),
      hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0⟩ => ⟨⟨?_, ?_⟩, hi, fun i hi' => ?_, t0.trans r0, hk⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]
  · obtain ⟨σ', ok⟩ := hg.ok
    rw [← he i hi', m]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _) _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hK := hi.k1024
    exact (hg.slot ok (o := i) (n := 1) (d := sS) (k := 4) (by unfold oRsa; omega)
      (by rw [hg.F]; decide)).symm _ (by simpa [VG.Proof.RsaPss.Arm.sa] using Region.contains_self (VG.Proof.RsaPss.Arm.sa P.scr i) 1)

variable (h : OHash)

/-- The body, calling `vg_rsa_private_checked_precomputed` with `pre`. -/
theorem body_vpP (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S P)) (decBodyP f (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (Sy (Fin h.G g.G P)) := by
  have paP : VP (C0 P) (.block privArgsP) (R1P P) := VP.block_append (pa_vp P) (pa2_vp P hP)
  refine VP.cont5 (VP.syms ((start_vp P).seq (paP.seq ((call_vpP P hP v).seq ((fix_vp P).seq (len_vp h P hTL))))))
    (byLen_vp (D := h.H.D) (by have := h.D_le; omega) (fun _ _ hs => hs.1.2)
      (fun σ s v ⟨⟨⟨hc, hi, he, r0, hk⟩, r1⟩, sy⟩ => ⟨⟨⟨hc.regs rfl rfl rfl rfl, hi, he, r0, hk⟩, r1⟩, sy⟩) ?_
      h.lens lens_certs)
  show VP _ (decTail (ofLen h.H.D) f) _
  rw [decTail_D (G := ofLen h.H.D) (G' := h.H) rfl f]
  show VP _ (.seq (.block (decChk h.H)) (.ite .ne decFail (decMain h.H f))) _
  exact VP.seq ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨r2, _⟩, sy⟩ => ⟨r2, sy⟩) fun _ _ x => x) (VP.ite
    (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT hTL fne))

/-! ## The entry -/

/-- The contract, with both hash functions one of the tables `ts`. -/
abbrev specP (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "dec_preP" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, `ep`'s with `pre`. -/
def epP (s : State) (ai au af : BitVec 32) (T : State → Prop) (aiL auL afL : BitVec 32) (TL : State → Prop) : EP :=
  { ep s ai au af T aiL auL afL TL with
    X := [⟨State.addr (stackArg s 21), (stackArg s 22).toNat * 8⟩]
    A := 92
    xargs := [stackArg s 21, BitVec.ofNat 32 (stackArg s 22).toNat]
    pre := stackArg s 21
    prl := (stackArg s 22).toNat
    preL := Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 21)) (stackArg s 0).toNat
    PX := fun σ => Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 5)) (stackArg s 6).toNat) =
        some (Spec.Rsa.wordsAt σ.mem (State.addr (stackArg s 21)) (stackArg s 22).toNat) ∧
      Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr (stackArg s 21)) (stackArg s 0).toNat =
        Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 21)) (stackArg s 0).toNat }

variable {ai au af : BitVec 32} {T : State → Prop} {aiL auL afL : BitVec 32} {TL : State → Prop}

theorem epP_lay (s : State) :
    (epP s ai au af T aiL auL afL TL).lay = layOf frameBytes 92
      ((epP s ai au af T aiL auL afL TL).argv ++ [stackArg s 21, BitVec.ofNat 32 (stackArg s 22).toNat])
      [(epP s ai au af T aiL auL afL TL).N, (epP s ai au af T aiL auL afL TL).E,
        (epP s ai au af T aiL auL afL TL).PP, (epP s ai au af T aiL auL afL TL).QQ,
        (epP s ai au af T aiL auL afL TL).DP, (epP s ai au af T aiL auL afL TL).DQ,
        (epP s ai au af T aiL auL afL TL).QI, (epP s ai au af T aiL auL afL TL).LAB,
        (epP s ai au af T aiL auL afL TL).CT, ⟨State.addr (stackArg s 21), (stackArg s 22).toNat * 8⟩,
        (epP s ai au af T aiL auL afL TL).TABL, (epP s ai au af T aiL auL afL TL).TAB]
      [(epP s ai au af T aiL auL afL TL).OUT, (epP s ai au af T aiL auL afL TL).ML,
        (epP s ai au af T aiL auL afL TL).SCR] s 3440 := rfl

theorem epP_pre {s : State} (h32 : (stackArg s 22).toNat < 2 ^ 32)
    (hl : (stackArg s 22).toNat = Spec.Rsa.privatePrecomputedWords (stackArg s 0).toNat (stackArg s 4).toNat
      (stackArg s 6).toNat) :
    PreP (epP s ai au af T aiL auL afL TL) :=
  ⟨rfl, rfl, h32, hl, rfl⟩

theorem in_of_preP {ts : List FnTable} {s : State} (h : (specP ts).pre s)
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In (epP s ai au af T aiL auL afL TL) (entered frameBytes s) ∧ PreP (epP s ai au af T aiL auL afL TL) := by
  dec_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPr oTL oT oA mN mE mP mQ mDP
    mDQ mQI mL mC mS mPr mTL mT mA nS eS pS qS dpS dqS qiS lS cS sPr sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC
    kS kPr kTL kT kA fO fM fN fE fP fQ fDP fDQ fQI fL fC fS fPr fTL fT kv olk clk el1 elK pl1 plK ql1 qlK dpl qil
    dql slK prl
  have key := h
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  have a16 : stackArg s 16 = stackArg s 0 := BitVec.eq_of_toNat_eq clk
  have a8 : stackArg s 8 = stackArg s 4 := BitVec.eq_of_toNat_eq dpl
  have a12 : stackArg s 12 = stackArg s 4 := BitVec.eq_of_toNat_eq qil
  have a10 : stackArg s 10 = stackArg s 6 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPr oTL oT oA kO fO
  rw [clk] at oC mC cS kC fC hrd
  rw [dpl] at oDP mDP dpS kDP fDP hrd
  rw [qil] at oQI mQI qiS kQI fQI hrd
  rw [dql] at oDQ mDQ dqS kDQ fDQ hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  have bP : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 3)) (stackArg s 4).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below).symm)
      (by show (stackArg s 4).toNat ≤ 2 ^ 64; omega_arith)
  have bQ : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 5)) (stackArg s 6).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5)) (stackArg s 6).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kQ.sub_left below).symm)
      (by show (stackArg s 6).toNat ≤ 2 ^ 64; omega_arith)
  have wPre : ∀ n, n ≤ (stackArg s 22).toNat →
      Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 21)) n =
        Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 21)) n := fun n hn =>
    wordsAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (kPr.sub_left below).symm.sub_left (Region.sub_prefix (len' := (stackArg s 22).toNat * 8) (by omega)))
      (by have := (stackArg s 22).isLt; omega)
  have le : Spec.Rsa.precomputedWords (stackArg s 0).toNat ≤ (stackArg s 22).toNat := by
    rw [prl, Spec.Rsa.privatePrecomputedWords]; omega
  refine ⟨
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      ll32 := (stackArg s 14).isLt
      scl32 := (stackArg s 18).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (stackArg s 0).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 2).toNat ≤ 2 ^ 64; omega_arith)
      tabT := hT
      tabTL := hTL
      A84 := (by decide : 84 ≤ 92)
      pxT := ⟨by rw [bP, bQ, wPre _ (Nat.le_refl _)]; exact key, by
        unfold Spec.Rsa.privatePrecomputedLeak; rw [wPre _ le]⟩ },
    epP_pre (stackArg s 22).isLt prl⟩
  rw [epP_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kPr, kTL, kT, kO, kM, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oPr, oTL, oT, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC, mPr,
      mTL, mT, mA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm, sPr, sTL, sT,
      sA]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨oM, oS⟩, mS, fun _ h => h.elim⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fL, fC, fPr, fTL, fT, fO, fM, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, epP, ep, r1]
    · rfl
    · simp [regArg, epP, ep]
  · intro i hi
    have : i < 23 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨
        i = 21 ∨ i = 22) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
      simp [epP, ep, a8, a10, a12, a16]

/-! ## The whole function -/

open VG.Proof.HashTable.Arm (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered)

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked_precomputed` over `v`, with
both hash functions any of the tables of `vs`. -/
abbrev decCodeP (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  decryptP (fnsOf vs) (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev dspecP : Contract isa := specP (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s'` has them. -/
abbrev epwP (s s' : State) (w w₁ : TVar) : EP :=
  epP s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (stackArg s 20) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
    (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (stackArg s 19) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
      (s'.syms w₁.g.H.finN))

theorem spec_tabP {ts : List FnTable} {s : State} (h : (specP ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 20)) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 19).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 20).toNat + 44 ≤ 2 ^ 32 := by
  dec_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPr oTL oT oA mN mE mP mQ mDP
    mDQ mQI mL mC mS mPr mTL mT mA nS eS pS qS dpS dqS qiS lS cS sPr sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC
    kS kPr kTL kT kA fO fM fN fE fP fQ fDP fDQ fQI fL fC fS fPr fTL fT kv olk clk el1 elK pl1 plK ql1 qlK dpl qil
    dql slK prl
  exact ⟨hheld, hheld2, hpw, fTL, fT⟩

theorem spec_spP {s : State} (hs : (dspecP vs).pre s) : stackBytes ≤ s.sp.toNat := by
  dec_preP at hs
  exact hs.1

/-- The entry state, for the tables of `w` at the stack argument 20 and `w₁`
at 19, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_stateP (hc : Coh vs) {s s' : State} (hs : (dspecP vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 20)) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (epwP (vs := vs) s s' w w₁)) (entered frameBytes s) (entered frameBytes s) ∧
      PreP (epwP (vs := vs) s s' w w₁) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tabP hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_spP hs)
  have ok := (in_of_preP (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs trivial trivial).1.ok
  rw [epP_lay] at ok
  have hn := Proof.HashTable.Arm.mem_names hw
  have hnL := Proof.HashTable.Arm.mem_names hw₁
  have tf := tabFacts_entered ok hsp' (p := stackArg s 20) (by simp [epP, ep]) hfit hc hpw' hw hh
  have tfL := tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [epP, ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  obtain ⟨hi, hP⟩ := in_of_preP (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs tf tfL
  exact ⟨⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩, hP⟩

theorem code_okP (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) {s : State} (hs : (dspecP vs).pre s) :
    WP isa (decCodeP vs v) s fun t => abiPreserved s t ∧ (dspecP vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tabP hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have hidxL := (held_tableOf hfitL hhL).2.1
  obtain ⟨st, hP⟩ := entered_stateP hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_spP hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  let P := epwP (vs := vs) s s w w₁
  have hb := (body_vpP w₁.g P w.g (fun _ x => x) (fun _ x => x) (fne_of hw) hP v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := P.lay.W)
    (Q := fun r m => Res w₁.g.G w.g.G P (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 92) (C := 3440) (argv := P.lay.argv) (ro := P.lay.ro)
      (rw := P.lay.rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl, hashAt_tableOf hfitL hidxL,
      Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 20) = State.addr (stackArg s 20) from rfl, hashAt_tableOf hfit hidx,
      Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ P.lay.ro) =>
      entered_ro (F := frameBytes) (A := 92) (C := 3440) (argv := P.lay.argv) (rw := P.lay.rw) hin.ok hsp' hR
    have hP' : pB P (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat := ro (R := P.PP) (by simp)
    have hQ : qB P (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5)) (stackArg s 6).toNat := ro (R := P.QQ) (by simp)
    have hDP : dpB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 7)) (stackArg s 4).toNat := ro (R := P.DP) (by simp)
    have hDQ : dqB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 9)) (stackArg s 6).toNat := ro (R := P.DQ) (by simp)
    have hQI : qiB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 11)) (stackArg s 4).toNat := ro (R := P.QI) (by simp)
    have hL : labB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 13)) (stackArg s 14).toNat := ro (R := P.LAB) (by simp)
    have hC : ctB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 15)) (stackArg s 0).toNat := ro (R := P.CT) (by simp)
    unfold Res at res
    rw [hP', hQ, hDP, hDQ, hQI, hL, hC] at res
    exact res

theorem code_ctP (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (dspecP vs).pre (dspecP vs).pub (decCodeP vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tabP h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19, a20, a21, a22⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epwP (vs := vs) s₁ s₁ w w₁ = epwP (vs := vs) s₂ s₁ w w₁ := by
    obtain ⟨hl1, hleak⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.Arm.bytesAt_length, a0, a2])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl1) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, a0])
    simp only [epP, ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a9, a11, a13, a14, a15, a17, a18, a19, a20, a21, a22]
    rw [h3, a0] at hn
    rw [a1, a2] at he
    rw [a21, a0] at hleak
    rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
      show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he,
      show State.addr (stackArg s₂ 21) = BitVec.setWidth 64 (stackArg s₂ 21) from rfl, hleak]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_spP h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨st₁, hP⟩ := entered_stateP hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl)
  refine (body_vpP w₁.g (epwP (vs := vs) s₁ s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) hP v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, st₁, by rw [hep]; exact (entered_stateP hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy').1⟩

/-- `vg_rsa_oaep_decrypt_precomputed`, calling
`vg_rsa_private_checked_precomputed` over `v`, with both hash functions any
of the tables of `vs`, meets its contract (satisfiable, `DecSat.lean`). -/
theorem dec_verifiedP (hc : Coh vs) (hsat : ∃ s, (dspecP vs).pre s) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (decCodeP vs v) (dspecP vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_okP hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ctP hc v, hsat⟩

end VG.Proof.RsaOaep.Arm.Dec
