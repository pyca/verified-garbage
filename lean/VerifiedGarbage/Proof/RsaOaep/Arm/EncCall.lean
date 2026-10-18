module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncEm
public import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the call

The arguments of `vg_rsa_public_precomputed_checked` (`pa_vp`): `out`, `pre`,
`e`, `EM` (`k` bytes at `scratch + oEm`) as the input, and the rest of
`scratch` from `oRsa` on; the call (`call_vp`, correct and constant time: its
arguments and the public data it reads are the same in two runs), which
writes the public operation of the masked `EM`, that is the encryption
(`encrypt_some`), to `out`, or zeros.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg copyArg)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPss.Arm.Sg (wl wl_cons wl_nil wl_other wl_read wl_frame rdS)

variable (h g : OHash)

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 15) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by omega)

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.scr + BitVec.ofNat 32 oEm, BitVec.ofNat 32 P.K, P.scr + BitVec.ofNat 32 oRsa,
    BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx (P.lay h.H.D) P.scr σ s) (hi : In h.H.D P σ) :
    WP isa (.block pubArgs) s fun t =>
      t.mem = wl (P.lay h.H.D) (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧
      t.gpr .r1 = BitVec.ofNat 32 P.K ∧ t.gpr .r2 = P.pre ∧ t.gpr .r3 = BitVec.ofNat 32 P.rl := by
  have hg := hi.geo
  have hs1 := hi.pubScr.2
  obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 5) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hc.st (j := 12) (by decide)
  obtain ⟨a13, r13, v13⟩ := argAt hi hc.st (j := 13) (by decide)
  obtain ⟨a14, r14, v14⟩ := argAt hi hc.st (j := 14) (by decide)
  replace v0 : s.mem.readW ((P.lay h.H.D).fr (arg 0)) 32 = P.out := v0
  replace v3 : s.mem.readW ((P.lay h.H.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v4 : s.mem.readW ((P.lay h.H.D).fr (arg 4)) 32 = P.e := v4
  replace v5 : s.mem.readW ((P.lay h.H.D).fr (arg 5)) 32 = BitVec.ofNat 32 P.el := v5
  replace v12 : s.mem.readW ((P.lay h.H.D).fr (arg 12)) 32 = BitVec.ofNat 32 P.scl := v12
  replace v13 : s.mem.readW ((P.lay h.H.D).fr (arg 13)) 32 = P.pre := v13
  replace v14 : s.mem.readW ((P.lay h.H.D).fr (arg 14)) 32 = BitVec.ofNat 32 P.rl := v14
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.H.D).fr d) 4 := fun d hd => hc.st.inFr hd
  have q0 : State.addr P.B = (P.lay h.H.D).fr 0 := by simp
  have w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  have rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 15 →
      (m.writeW (State.addr P.B) v).readW ((P.lay h.H.D).fr (arg j)) 32 = m.readW ((P.lay h.H.D).fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  have rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW ((P.lay h.H.D).fr sS) 32 = m.readW ((P.lay h.H.D).fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [pubArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a0, r0, v0, a3, r3, v3, a4, r4, v4, a5, r5, v5, a12, r12, v12, a13, r13, v13, a14, r14, v14, rdArg, rdS, w0,
    rdA0, rdS0, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) (show 1024 ≤ P.scl by omega),
    Nat.reduceMul, wl_cons, wl_nil, Nat.reduceAdd]

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  E1 h g P σ s ∧ PdArgs s P.out P.pre P.e (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K P.el
    P.rl (P.scl - 1024)

theorem pa_vp (P : EP) : VP (E1 h g P) (.block pubArgs) (V1 h g P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
    fun σ s ⟨⟨hc, hi, hf⟩, he⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok'⟩ := hg.ok
  refine WP.mono (pa_wp h P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  have q0 : State.addr P.B = (P.lay h.H.D).fr 0 := by simp
  rw [q0] at m
  have fr : Frame [⟨(P.lay h.H.D).fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  have rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW ((P.lay h.H.D).fr (4 * i)) 32 := by
    intro i hi'
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega)]
  have v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  have v : ∀ i, 1 ≤ i → i < 6 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i (by omega), m, wl_read _ _ _ 1 i h1 (by simp; omega) (by simp)]
  have hK := hi.k1024
  refine ⟨⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf⟩, ?_⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.H.D).FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  · refine sbytes_keep fr (o := oEm) (n := P.K) (fun r hr => ?_) (by oomega) he
    simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok' (by oomega) (by rw [hg.F]; decide)).symm
  obtain ⟨ps, hs1⟩ := hi.pubScr
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), hi.kv, hi.rlK, hi.el1, hi.elK, ps,
    by have := hi.scl32; omega⟩

/-- `EM` and the call's working space, in `scratch`. -/
theorem call_geo {P : EP} {σ : State} (hi : In h.H.D P σ) :
    State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm ∧
    State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa ∧
    Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩ P.SCR ∧
    Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩ P.SCR ∧
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩
      ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩ ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1025 ≤ P.scl ∧ P.K ≤ 1024 := by
  have hf := hi.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hs := hi.pubScr.2
  have hK := hi.k1024
  have e1 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm :=
    addr_add (by unfold oEm; omega)
  have e2 : State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa :=
    addr_add (by unfold oRsa; omega)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, hs, hK⟩
  · rw [e1]; exact Offset.sub_base _ (by unfold oEm; omega)
  · rw [e2]; exact Offset.sub_base _ (by unfold oRsa; omega)
  · rw [e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega) (by unfold oEm; omega)
      (by unfold oRsa; omega)

theorem call_pre {P : EP} {σ s : State} (hr : V1 h g P σ s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e (P.scr + BitVec.ofNat 32 oEm) P.K P.el P.rl)
        (pdWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨⟨⟨hc, hi, -⟩, -⟩, pa⟩ := hr
  have ok := hi.ok
  have hg := hi.geo
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = (P.lay h.H.D).fr 0 := by simp
  have fs := fun {R : Region} (hR : R ∈ (P.lay h.H.D).ro ++ (P.lay h.H.D).rw) => ok.fits R hR
  have hfr : ∀ {R : Region}, R ∈ (P.lay h.H.D).ro ∨ R ∈ (P.lay h.H.D).rw → ∀ {d n : Nat},
      d + n ≤ frameBytes + 56 → Region.Disjoint ⟨(P.lay h.H.D).fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  have dOS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
  refine pd_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega)
    (by have := fs (R := P.OUT) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [hg.scr_lt (by decide)]; unfold oEm; omega)
    (by rw [hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega)
    (ok.rw_ro (w := P.OUT) (r := P.PRE) (by simp) (by simp))
    (ok.rw_ro (w := P.OUT) (r := P.E) (by simp) (by simp))
    (dOS.sub_right sI) (dOS.sub_right sS')
    (by rw [q0]; exact (hfr (R := P.OUT) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm)
    ((ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).symm.sub_right sS')
    ((ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).symm.sub_right sS') dIS
    (by rw [q0]; exact ((hfr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm).sub_left sS') ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = (P.lay h.H.D).LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · exact ok.low_buf (R := P.OUT) (.inr (by simp))
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

theorem emB_length {P : EP} (hf : fits h P) (σ : State) : (emB h g P σ).length = P.K := by
  have hf' : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have hl := lhB_length h P σ
  simp only [emB, Proof.RsaOaep.emOf, List.length_cons, List.length_append, Proof.Mgf1.xorBytes_length,
    Proof.Mgf1.mgf1_length g.valid, hl, Spec.RsaOaep.zeros, List.length_replicate, seedB, Spec.Rsa.bytesAt,
    List.length_map, List.length_range]
  omega

/-- The masked `EM`, as the call reads it. -/
theorem em_bytes {P : EP} {σ s : State} (hr : E1 h g P σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K = emB h g P σ := by
  obtain ⟨⟨-, hi, hf⟩, he⟩ := hr
  have hg := hi.geo
  have hK := hi.k1024
  have hl := emB_length h g hf σ
  rw [← hl]
  refine bytesAt_eq fun i hi' => ?_
  rw [hg.addr (by oomega), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact he i (by omega)

/-- The result: the encryption. -/
theorem res_of {P : EP} {σ : State} (hi : In h.H.D P σ) (hf : fits h P) :
    Spec.Rsa.publicOpChecked P.nB P.eB (emB h g P σ) =
      Spec.RsaOaep.encrypt h.G g.G P.nB P.eB (labB P σ) (msgB P σ) (seedB h P σ) := by
  have hf' : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  rw [Proof.RsaOaep.encrypt_some (by rw [h.glen]; simp [Spec.Rsa.bytesAt])
    (by rw [h.glen, nB_length hi, msgB_length]; exact hf'), nB_length hi, msgB_length, h.glen]

theorem call_vp (P : EP) (c : PdImpl) : VP (V1 h g P) (.call c.name c.code) (Fin h g P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e (P.scr + BitVec.ofNat 32 oEm) P.K P.el P.rl)
    (pdWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_pre h g hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨⟨⟨hc, hi, -⟩, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have q0 : State.addr P.B = (P.lay h.H.D).fr 0 := by simp
    have hro : ∀ R ∈ (P.lay h.H.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega)⟩
    have inO : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    have wr' : Covers (pdWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      Covers.cons inO (by rw [e2]; exact inS (by unfold oRsa; omega))
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [e1]; exact (inS (by unfold oEm; omega)).right
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [hr.1.1.1.st.sp]; exact hr.1.1.2.1.ok.B56
  · exact pd_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp])
      (by rw [(h₁.1.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₁.1.1.2.1.pw,
        (h₂.1.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₂.1.1.2.1.pw])
      (by rw [(h₁.1.1.1.st.ro (R := P.E) (by simp)).trans h₁.1.1.2.1.eB, (h₂.1.1.1.st.ro (R := P.E) (by simp)).trans
        h₂.1.1.2.1.eB]) _ _
  · obtain ⟨he1, pa⟩ := hr
    obtain ⟨⟨hc, hi, hf⟩, he⟩ := he1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    have low : FrameStack.belowA s.sp 56 = (P.lay h.H.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩, (P.lay h.H.D).LOW]
        s.mem s'.mem := fr
    have hct : Ctx (P.lay h.H.D) P.scr σ s' := hc.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.H.D).LOW, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4)
          (by show sS + 4 ≤ frameBytes + 56; decide)).sub_right sS'
      · exact Lay.fr_low (by decide) (by have := ok.B56; have := P.B.isLt; omega)) rd wr sp
    refine ⟨⟨hi, hct.st⟩, fun hp => ?_⟩
    have := pd_post pa po P.nB (nB_length hi) (by rw [(hs.ro_words (R := P.PRE) (by simp) rfl).trans hi.pw]; exact hp)
    rw [(hs.ro (R := P.E) (by simp)).trans hi.eB, em_bytes h g ⟨⟨hc, hi, hf⟩, he⟩, res_of h g hi hf] at this
    exact this

end VG.Proof.RsaOaep.Arm.Enc
