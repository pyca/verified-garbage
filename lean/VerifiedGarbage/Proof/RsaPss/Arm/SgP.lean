module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
public import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rsa.Arm.PrivPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pss_sign_precomputed` on ARMv7

`vg_rsa_pss_sign`'s code (`signP`) calling `vg_rsa_private_checked_precomputed`
with the key's precomputed values `pre` and `pre_len`, our arguments 24 and
25, as its stack arguments 16 and 17 (`privArgsP`): the slots `sS` and `sL`,
which nothing reads after the call. The layout is `vg_rsa_pss_sign`'s with
`pre` among the buffers read and our two more arguments (`PreP`), and the
body's proofs are `vg_rsa_pss_sign`'s but for the call (`pa2_vp`, `call_vpP`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (OHash byLen_vp)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

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

theorem PreP.mem {D : Nat} {P : EP} (hP : PreP P) : P.PRE ∈ (P.lay D).ro := by
  simp [hP.x]

/-- Our arguments 24 and 25, `pre` and `pre_len`. -/
theorem argAtX {D : Nat} {P : EP} {σ s : State} (hP : PreP P) (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat}
    (hj : j = 24 ∨ j = 25) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = (P.lay D).argv.getD j 0 := by
  have hl : j < (P.lay D).argv.length := by
    simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil]; omega_using [hj]
  have hA := hi.ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + P.A; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

variable (h : PssHash)

/-- `pre` and `pre_len` to the call's stack arguments 16 and 17. -/
theorem pa2_wp (P : EP) (hP : PreP P) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64, Impl.RsaPss.Arm.ld .r4 (arg 25), st .r4 68]) s
      fun t => t.mem = (s.mem.writeW ((P.lay h.D).fr 64) P.pre).writeW ((P.lay h.D).fr 68)
          (BitVec.ofNat 32 P.prl) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r1 = s.gpr .r1 ∧
        t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 := by
  have hg := hi.geo
  obtain ⟨a24, r24, v24⟩ := argAtX hP hi hc.st (j := 24) (.inl rfl)
  obtain ⟨a25, r25, v25⟩ := argAtX hP hi hc.st (j := 25) (.inr rfl)
  replace v24 : s.mem.readW ((P.lay h.D).fr (arg 24)) 32 = P.pre := by
    rw [v24]; simp [EP.argv, hP.xa]
  replace v25 : s.mem.readW ((P.lay h.D).fr (arg 25)) 32 = BitVec.ofNat 32 P.prl := by
    rw [v25]; simp [EP.argv, hP.xa]
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  have rd25 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW ((P.lay h.D).fr 64) v).readW ((P.lay h.D).fr (arg 25)) 32 = m.readW ((P.lay h.D).fr (arg 25)) 32 :=
    fun m v => Lay.readW_fr_other _ m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; decide)
      (by decide) (by decide)
  have l24 : arg 24 < 4096 := by decide
  have l25 : arg 25 < 4096 := by decide
  prun [sp0, Impl.RsaPss.Arm.ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, l24, l25, a24, r24, v24, a25, r25, v25,
    rd25]

/-- Before the call of `vg_rsa_private_checked_precomputed`. -/
abbrev R1P (G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop :=
  (P.lay h.D).St σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024) ∧
    stackArg s 16 = P.pre ∧ stackArg s 17 = BitVec.ofNat 32 P.prl

theorem pa2_vp (G : Spec.Mgf1.Hash) (P : EP) (hP : PreP P) :
    VP (R1 h G P) (.block [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64, Impl.RsaPss.Arm.ld .r4 (arg 25),
      st .r4 68]) (R1P h G P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he, pa⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  refine WP.mono (pa2_wp h P hP hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  obtain ⟨σ', ok⟩ := hg.ok
  have fr : Frame [⟨(P.lay h.D).fr 64, 8⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 64) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have rd0 : ∀ (u : State), u.sp = s.sp → ∀ i, i < 18 → stackArg u i = u.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro u hu i hi'
    simp only [stackArg, stackArgAddr, hu, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega_arith)]
  have keep : ∀ i, i < 16 → stackArg t i = stackArg s i := fun i hi' => by
    rw [rd0 t sp i (by omega_using [hi']), rd0 s rfl i (by omega_using [hi']), m, Lay.readW_fr_other _ _ _ (by omega_using [hi']) (by omega_using [hi']) (by decide),
      Lay.readW_fr_other _ _ _ (by omega_using [hi']) (by omega_using [hi']) (by decide)]
  refine ⟨hc.st.write fr (fun r hr => ?_) rd wr sp, hk.keep h fr fun r hr => ?_, fun i hi' => ?_,
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
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 64 + 8 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  · rw [← he i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (d := 64) (k := 8) (by have := hi'; have := hi.k1024; unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  · rw [rd0 t sp 16 (by decide), m, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [rd0 t sp 17 (by decide), m, Mem.readW_writeW_self32]

section
variable {h}

theorem leak_st {P : EP} (hP : PreP P) {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  have px := hi.pxT
  rw [hP.px] at px
  have le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hP.prlv, Spec.Rsa.privatePrecomputedWords]; omega_using []
  have rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [← px.2]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem key_st {P : EP} (hP : PreP P) {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K)
      (Spec.Rsa.bytesAt s.mem (State.addr P.p) P.pl) (Spec.Rsa.bytesAt s.mem (State.addr P.q) P.ql) =
    some (Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.prl) := by
  have px := hi.pxT
  rw [hP.px] at px
  have rw := hs.ro_words (R := P.PRE) hP.mem (n := P.prl) rfl
  dsimp only at rw
  rw [nB_at h hi hs, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp), rw]
  exact px.1

end

theorem call_preP {G : Spec.Mgf1.Hash} {P : EP} (hP : PreP P) {σ s : State} (hr : R1P h G P σ s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRdP P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.pre
        P.K P.el P.pl P.ql P.prl) (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hs, hk, -, pa, a16, a17⟩ := hr
  have hi := hk.1
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  have hA := ok.nargs
  simp only [EP.argv, hP.xa, List.length_append, List.length_cons, List.length_nil] at hA
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  have oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
  have hPm := hP.mem (D := h.D)
  refine priv_preP pa a16 a17 hP.prl32 hs.sp hB (by simp only [frameBytes] at fit; omega_arith) ?_
    (oS.sub_right sS') ?_ ?_ hP.prlv (key_st hP hi hs)
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact oS.sub_right sI
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) hPm
    · rw [q0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := 0) (n := 72) (by show 0 + 72 ≤ frameBytes + 56; decide)).symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
    · exact dIS.symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.PP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QI) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) hPm).sub_left sS'
    · rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 72)
        (by show 0 + 72 ≤ frameBytes + 56; decide)).symm).sub_left sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = (P.lay h.D).LOW := rfl
    rw [low]
    simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · exact ok.low_buf (R := P.PRE) (.inl hPm)
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega_arith
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega_arith
    · exact fs (List.mem_append_left _ hPm)

/-- `out` and the result: the call of `vg_rsa_private_checked_precomputed`. -/
theorem call_vpP (g : RsaOaep.Arm.OHash) (P : EP) (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1P h g.G P) (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (Fin h g.G P) := by
  refine VG.Proof.RsaPkcs1Sig.Arm.VP.callC (fun s h => Proof.Rsa.Arm.private_contract_correctP v s h) (Proof.Rsa.Arm.private_contract_ctP v)
    (privCodeP_stack v)
    (privRdP P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
    (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_preP h hP hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hs, hk, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    have hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega_arith)⟩
    have hout : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    have wr' : Covers (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hout.cons (by rw [e2]; exact inS (by unfold oRsa; omega_arith))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons ((hro P.PRE hP.mem).cons
        (Covers.cons ?_ Covers.nil)))))))
    · rw [e1]; exact (inS (by unfold oEm; omega_arith)).right
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 72 ≤ frameBytes; decide))).right
  · rw [hr.1.sp]; exact hr.2.1.1.ok.B56
  · obtain ⟨hs₁, hk₁, -, pa₁, p16, p17⟩ := h₁
    obtain ⟨hs₂, hk₂, -, pa₂, q16, q17⟩ := h₂
    exact priv_pubP pa₁ pa₂ (by rw [hs₁.sp, hs₂.sp]) p16 q16 p17 q17
      (by rw [nB_at h hk₁.1 hs₁, nB_at h hk₂.1 hs₂]) (by rw [eB_at h hk₁.1 hs₁, eB_at h hk₂.1 hs₂])
      (by rw [leak_st hP hk₁.1 hs₁, leak_st hP hk₂.1 hs₂]) _ _
  · obtain ⟨hs, hk, he, pa, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hi, st⟩, ?_⟩
    have em : Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K =
        (List.range P.K).map (emF h g.G P σ) := by
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have := priv_postP pa po
    rw [nB_at h hi hs, eB_at h hi hs, em, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp),
      hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp), hs.ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h g hi hk.2.1]
    exact this

theorem body_vpP (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hP : PreP P) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signBodyP f fg h.sh (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v))
      (Sy (Fin h g.G P)) := by
  by_cases hP' : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP' ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk h.sh)) (.seq (.block (params ++ saltFits)) (.ite .ne signFail
    (.seq (signEnc f fg h.sh) (.seq (.block (privArgs ++ [sp0, Impl.RsaPss.Arm.ld .r4 (arg 24), st .r4 64,
      Impl.RsaPss.Arm.ld .r4 (arg 25), st .r4 68]))
      (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v))))))) _
  exact (VP.syms (chk_vp h P)).seq ((VP.syms (par_vp h P)).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (((enc_vp h P Q hP').mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩) fun _ _ h => h).seq
      ((VP.syms (VP.block_append (pa_vp h g.G P) (pa2_vp h g.G P hP))).seq (VP.syms (call_vpP h g P hP v))))))

/-- The body for the hash function of the table `hash`, whose shape its
index gives. -/
theorem tab_vpP (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hsh : h.sh = ofIdx (Spec.HashTable.index h.G)) (hidx : Spec.HashTable.index h.G ∈ idxs) (hP : PreP P)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signTabP f fg (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (Sy (Fin h g.G P)) := by
  refine (idx_vp h P Q).seq (byLen_vp (D := Spec.HashTable.index h.G) (by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hidx
    rcases hidx with e | e | e | e | e | e | e | e <;> rw [e] <;> decide)
    (fun _ _ hs => hs.2) (fun σ s v ⟨⟨⟨hi, st⟩, sy⟩, r1⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩, r1⟩) ?_
    hidx idxs_certs)
  rw [← hsh]
  exact (body_vpP h g P Q hP v).mono (fun _ _ hs => hs.1) fun _ _ x => x

/-! ## The entry -/

/-- The contract, with the hash function one of the tables `hs`, MGF1's one of
`ts`, and the stack `vg_rsa_pss_sign` uses. -/
abbrev specP (hs ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "sign_preP" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, `ep`'s with `pre`. -/
def epP (s : State) (hi hc hdg : BitVec 32) (HT : State → Prop) (ai au af : BitVec 32) (T : State → Prop) : EP :=
  { ep s hi hc hdg HT ai au af T with
    X := [⟨State.addr (stackArg s 20), (stackArg s 21).toNat * 8⟩]
    A := 88
    xargs := [stackArg s 20, BitVec.ofNat 32 (stackArg s 21).toNat]
    pre := stackArg s 20
    prl := (stackArg s 21).toNat
    preL := Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat
    PX := fun σ => Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat) =
        some (Spec.Rsa.wordsAt σ.mem (State.addr (stackArg s 20)) (stackArg s 21).toNat) ∧
      Spec.Rsa.privatePrecomputedLeak σ.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat =
        Spec.Rsa.privatePrecomputedLeak s.mem (State.addr (stackArg s 20)) (s.gpr .r3).toNat }

variable {hi hc hdg : BitVec 32} {HT : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem epP_lay (D : Nat) (s : State) :
    (epP s hi hc hdg HT ai au af T).lay D = layOf frameBytes 88
      ((epP s hi hc hdg HT ai au af T).argv D ++ [stackArg s 20, BitVec.ofNat 32 (stackArg s 21).toNat])
      ([(epP s hi hc hdg HT ai au af T).N, (epP s hi hc hdg HT ai au af T).E, (epP s hi hc hdg HT ai au af T).PP,
        (epP s hi hc hdg HT ai au af T).QQ, (epP s hi hc hdg HT ai au af T).DP, (epP s hi hc hdg HT ai au af T).DQ,
        (epP s hi hc hdg HT ai au af T).QI, (epP s hi hc hdg HT ai au af T).DIG D,
        (epP s hi hc hdg HT ai au af T).SALT, ⟨State.addr (stackArg s 20), (stackArg s 21).toNat * 8⟩,
        (epP s hi hc hdg HT ai au af T).HTAB, (epP s hi hc hdg HT ai au af T).TAB])
      [(epP s hi hc hdg HT ai au af T).OUT, (epP s hi hc hdg HT ai au af T).SCR] s 3440 := rfl

theorem epP_pre {s : State} (h32 : (stackArg s 21).toNat < 2 ^ 32)
    (hl : (stackArg s 21).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .r3).toNat (stackArg s 3).toNat
      (stackArg s 5).toNat) :
    PreP (epP s hi hc hdg HT ai au af T) :=
  ⟨rfl, rfl, h32, hl, rfl⟩

theorem in_of_preP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) {D : Nat}
    (hD : (stackArg s 13).toNat = D) (hHT : HT (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (epP s hi hc hdg HT ai au af T) (entered frameBytes s) ∧ PreP (epP s hi hc hdg HT ai au af T) := by
  sign_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA nS eS pS qS dpS dqS qiS
    dS slS sPr sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPr kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPr
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK prl key
  have h3624 : 3624 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = s.gpr .r3 := BitVec.eq_of_toNat_eq olk
  have a7 : stackArg s 7 = stackArg s 3 := BitVec.eq_of_toNat_eq dpl
  have a11 : stackArg s 11 = stackArg s 3 := BitVec.eq_of_toNat_eq qil
  have a9 : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dql
  have a13 : stackArg s 13 = BitVec.ofNat 32 D := by
    apply BitVec.eq_of_toNat_eq; rw [hD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hD]; exact (stackArg s 13).isLt)]
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA kO fO
  rw [dpl] at oDP dpS kDP fDP hrd
  rw [qil] at oQI qiS kQI fQI hrd
  rw [dql] at oDQ dqS kDQ fDQ hrd
  rw [hD] at oD dS kD fD hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (show 56 ≤ stackBytes by decide) (show stackBytes - 56 + 56 ≤ stackBytes by decide)
  have bP : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kP.sub_left below).symm)
      (by show (stackArg s 3).toNat ≤ 2 ^ 64; omega_arith)
  have bQ : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 4)) (stackArg s 5).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
    bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (kQ.sub_left below).symm)
      (by show (stackArg s 5).toNat ≤ 2 ^ 64; omega_arith)
  have wPre : ∀ n, n ≤ (stackArg s 21).toNat →
      Spec.Rsa.wordsAt (entered frameBytes s).mem (State.addr (stackArg s 20)) n =
        Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 20)) n := fun n hn =>
    wordsAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (kPr.sub_left below).symm.sub_left (Region.sub_prefix (len' := (stackArg s 21).toNat * 8) (by omega_using [hn])))
      (by have := (stackArg s 21).isLt; omega_using [hn])
  have le : Spec.Rsa.precomputedWords (s.gpr .r3).toNat ≤ (stackArg s 21).toNat := by
    rw [prl, Spec.Rsa.privatePrecomputedWords]; omega_using []
  refine ⟨
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, pl1 := pl1, plK := plK, ql1 := ql1, qlK := qlK, slK := slK
      sl32 := (stackArg s 15).isLt
      scl32 := (stackArg s 17).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (stackArg s 1).toNat ≤ 2 ^ 64; omega_arith)
      htabT := hHT
      tabT := hT
      A80 := (by decide : 80 ≤ 88)
      pxT := ⟨by rw [bP, bQ, wPre _ (Nat.le_refl _)]; exact key, by
        unfold Spec.Rsa.privatePrecomputedLeak; rw [wPre _ le]⟩ },
    epP_pre (stackArg s 21).isLt prl⟩
  rw [epP_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kPr, kTH, kT, kO, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oPr, oTH, oT, oA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm,
      dqS.symm, qiS.symm, dS.symm, slS.symm, sPr, sTH, sT, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fP, fQ, fDP, fDQ, fQI, fD, fSl, fPr, fTH, fT, fO, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, epP, ep, r1]
    · rfl
    · simp [regArg, epP, ep]
  · intro i hi
    have : i < 22 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨
        i = 21) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp [epP, ep, a7, a9, a11, a13]

/-! ## The whole function -/

section
variable (mvs : List MVar) (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked_precomputed` over `v`. -/
abbrev signCodeP (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  signP (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)

/-- The contract, with those tables. -/
abbrev sspecP : Contract isa := specP (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)

variable {mvs vs}

theorem spec_tabP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 18).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 19).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13) := by
  sign_preP at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPr oTH oT oA nS eS pS qS dpS dqS qiS
    dS slS sPr sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPr kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPr
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK prl key
  exact ⟨hheld, hheld2, hpw, fTH, fT, h⟩

theorem spec_spP {hs ts : List FnTable} {s : State} (h : (specP hs ts).pre s) : stackBytes ≤ s.sp.toNat := by
  sign_preP at h
  exact h.1

/-- The public parameters for the hash function's table of `w` and MGF1's of
`wg`, with their functions where `s'` has them. -/
abbrev epwP (s s' : State) (w : MVar) (wg : TVar) : EP :=
  epP s (s'.syms w.h.H.md.st.initN) (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w))
    (HTab w.h (MdHashTable.Arm.digName w) (MdHashTable.Arm.fnsOf mvs) (stackArg s 18) (s'.syms w.h.H.md.st.initN)
      (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w)))
    (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (RsaOaep.Arm.TabFacts wg.g.H (HashTable.Arm.fnsOf vs) (stackArg s 19) (s'.syms wg.g.H.initN)
      (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN))

theorem entered_stateP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) {s s' : State}
    (hs : (sspecP mvs vs).pre s) {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hhg : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (HashTable.Arm.tableOf wg)))
    (hsy : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s.syms n = s'.syms n) :
    Sy (S w.h (epwP (mvs := mvs) (vs := vs) s s' w wg)) (entered frameBytes s) (entered frameBytes s) ∧
      PreP (epwP (mvs := mvs) (vs := vs) s s' w wg) := by
  obtain ⟨-, -, hpw, hfit, hfitg, hdl⟩ := spec_tabP hs
  have hD := dl_of hfit hh hdl
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_spP hs)
  have ok := (in_of_preP (hi := 0) (hc := 0) (hdg := 0) (HT := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs hD trivial trivial).1.ok
  rw [epP_lay] at ok
  have hn := MdHashTable.Arm.mem_names hw
  have hng := Proof.HashTable.Arm.mem_names hwg
  have ht := MdHashTable.Arm.htab_entered ok hsp' (p := stackArg s 18) (by simp [epP, ep]) hfit hc hpwH hw hh
  have tf := Proof.HashTable.Arm.tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [epP, ep]) hfitg hcg hpwG
    hwg hhg
  rw [hsy _ (List.mem_append_left _ hn.1), hsy _ (List.mem_append_left _ hn.2.1),
    hsy _ (List.mem_append_left _ hn.2.2)] at ht
  rw [hsy _ (List.mem_append_right _ hng.1), hsy _ (List.mem_append_right _ hng.2.1),
    hsy _ (List.mem_append_right _ hng.2.2)] at tf
  obtain ⟨hi, hP⟩ := in_of_preP (hi := s'.syms w.h.H.md.st.initN) (hc := s'.syms w.h.H.md.compN)
    (hdg := s'.syms (MdHashTable.Arm.digName w)) (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN)
    (af := s'.syms wg.g.H.finN) hs hD ht tf
  exact ⟨⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩, hP⟩

/-- What the body needs of the tables of `w` and `wg`. -/
theorem tf_ofP {s s' : State} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs) :
    TF w.h wg.g (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (MdHashTable.Arm.digName w)
      (epwP (mvs := mvs) (vs := vs) s s' w wg) :=
  ⟨fun _ x => x, fun _ x => x, fne_of hw, gne_of hwg⟩

/-- Unfolds the contract's postcondition. -/
macro "sign_postP" : tactic => `(tactic| (
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]))

theorem code_okP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl)
    {s : State} (hs : (sspecP mvs vs).pre s) :
    WP isa (signCodeP mvs vs v) s fun t => abiPreserved s t ∧ (sspecP mvs vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, ⟨Tg, hTg, hhg⟩, -, hfit, hfitg, hdl⟩ := spec_tabP hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  have hidx := (MdHashTable.Arm.held_tableOf hfit hh).2.2.2
  have hidxg := (Proof.HashTable.Arm.held_tableOf hfitg hhg).2.1
  obtain ⟨st, hP⟩ := entered_stateP hc hcg hs hw hwg hh hhg (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_spP hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  let P := epwP (mvs := mvs) (vs := vs) s s w wg
  have hb := (tab_vpP w.h wg.g P (tf_ofP hw hwg) w.shape w.mem hP v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (P.lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G P (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 88) (C := 3440) (argv := (P.lay w.h.D).argv) (ro := (P.lay w.h.D).ro)
      (rw := (P.lay w.h.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sign_postP
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 18) = State.addr (stackArg s 18) from rfl,
      MdHashTable.Arm.hashAt_tableOf hfit hidx, Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl,
      Proof.HashTable.Arm.hashAt_tableOf hfitg hidxg, Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (P.lay w.h.D).ro) =>
      entered_ro (F := frameBytes) (A := 88) (C := 3440) (argv := (P.lay w.h.D).argv) (rw := (P.lay w.h.D).rw) hin.ok
        hsp' hR
    have hP' : pB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
      ro (R := P.PP) (by simp)
    have hQ : qB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
      ro (R := P.QQ) (by simp)
    have hDP : dpB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        (stackArg s 3).toNat := ro (R := P.DP) (by simp)
    have hDQ : dqB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8))
        (stackArg s 5).toNat := ro (R := P.DQ) (by simp)
    have hQI : qiB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10))
        (stackArg s 3).toNat := ro (R := P.QI) (by simp)
    have hDg : digB w.h P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 12)) w.h.D :=
      ro (R := P.DIG w.h.D) (by simp)
    have hS : saltB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 14))
        (stackArg s 15).toNat := ro (R := P.SALT) (by simp)
    unfold Res at res
    rw [hP', hQ, hDP, hDQ, hQI, hDg, hS] at res
    rw [w.h.glen]
    exact res

theorem code_ctP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (sspecP mvs vs).pre (sspecP mvs vs).pub (signCodeP mvs vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, ⟨Tg, hTg, hhg₁⟩, -, -, -, -⟩ := spec_tabP h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, htabg, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19, a20, a21⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhg₂ := (htabg _ _ rfl rfl _ hTg).mp hhg₁
  have hsy' : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by
      rcases List.mem_append.mp hn with e | e
      · exact List.mem_append_left _ e
      · exact List.mem_append_right _ (List.mem_append_left _ e))).symm
  have hep : epwP (mvs := mvs) (vs := vs) s₁ s₁ w wg = epwP (mvs := mvs) (vs := vs) s₂ s₁ w wg := by
    obtain ⟨hl1, hleak⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3, a1])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl1) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3])
    simp only [epP, ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a8, a10, a12, a14, a15, a16, a17, a18, a19, a20, a21]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [a20, h3] at hleak
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
      show State.addr (stackArg s₂ 20) = BitVec.setWidth 64 (stackArg s₂ 20) from rfl, hleak]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_spP h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨st₁, hP⟩ := entered_stateP hc hcg h₁ hw hwg hh₁ hhg₁ (s' := s₁) (fun _ _ => rfl)
  refine (tab_vpP w.h wg.g (epwP (mvs := mvs) (vs := vs) s₁ s₁ w wg) (tf_ofP hw hwg) w.shape w.mem hP v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, st₁, by rw [hep]; exact (entered_stateP hc hcg h₂ hw hwg hh₂ hhg₂ (s' := s₁) hsy').1⟩

/-- `vg_rsa_pss_sign_precomputed`, calling `vg_rsa_private_checked_precomputed` over `v`, with the
hash function any of the tables of `MdHash` of `mvs` and MGF1's any of the
tables of `MdHash` of `vs`, meets its contract (satisfiable, `SgSat.lean`). -/
theorem sign_verifiedP (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs)
    (hsat : ∃ s, (sspecP mvs vs).pre s) (v : Proof.Rsa.Arm.CrtImpl) : Verified target (signCodeP mvs vs v) (sspecP mvs vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_okP hc hcg v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ctP hc hcg v, hsat⟩

end
