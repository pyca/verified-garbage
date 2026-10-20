module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfChk
public import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the call

The arguments of `vg_rsa_public_precomputed_checked` (`pa_vp`): `EM`'s place
(`oEm`), `pre`, `e`, the signature, and the rest of `scratch` from `oRsa` on;
the call (`call_vp`, correct and constant time: its arguments and the public
data it reads are the same in two runs), which writes RSAVP1 of the
signature to `EM`, or zeros (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (wl wl_cons wl_nil wl_other wl_read wl_frame rdS)

variable (h : PssHash)

/-- `dbLen`. -/
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots after the checks. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧ m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) ∧
    m.readW ((P.lay h.D).fr sAny) 32 = (if P.any = 0 then 0 else 1)

/-- When everything fits. -/
abbrev M0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ fits h P ∧ Bm h P s.mem

theorem m0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : M0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, sa, z⟩ := hc
  have hz : s.z = true := by
    rw [VG.Proof.X25519.Arm.eval_ne] at e
    simpa using e
  have hf : fits h P := of_decide_eq_true (z ▸ hz)
  refine ⟨hc, hi, hf, sc, sl, ?_, sa⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  have := hf.2
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by omega), Offset.ofNat_sub_ofNat (by omega)]
  congr 1

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 13) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega) (by omega)

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.sig, BitVec.ofNat 32 P.K, P.scr + BitVec.ofNat 32 oRsa, BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block pubArgs) s fun t =>
      t.mem = wl (P.lay h.D) (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      t.gpr .r1 = BitVec.ofNat 32 P.K ∧ t.gpr .r2 = P.pre ∧ t.gpr .r3 = BitVec.ofNat 32 P.rl := by
  have hg := hi.geo
  have hs1 := hi.pubScr.2
  obtain ⟨a1, r1, v1⟩ := argAt hi hc.st (j := 1) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 5) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hc.st (j := 10) (by decide)
  obtain ⟨a11, r11, v11⟩ := argAt hi hc.st (j := 11) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hc.st (j := 12) (by decide)
  replace v1 : s.mem.readW ((P.lay h.D).fr (arg 1)) 32 = BitVec.ofNat 32 P.K := v1
  replace v2 : s.mem.readW ((P.lay h.D).fr (arg 2)) 32 = P.e := v2
  replace v3 : s.mem.readW ((P.lay h.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.el := v3
  replace v5 : s.mem.readW ((P.lay h.D).fr (arg 5)) 32 = P.sig := v5
  replace v10 : s.mem.readW ((P.lay h.D).fr (arg 10)) 32 = BitVec.ofNat 32 P.scl := v10
  replace v11 : s.mem.readW ((P.lay h.D).fr (arg 11)) 32 = P.pre := v11
  replace v12 : s.mem.readW ((P.lay h.D).fr (arg 12)) 32 = BitVec.ofNat 32 P.rl := v12
  have wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  have w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  have rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 13 →
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr (arg j)) 32 = m.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  have rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr sS) 32 = m.readW ((P.lay h.D).fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [pubArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a1, r1, v1, a2, r2, v2, a3, r3, v3, a5, r5, v5, a10, r10, v10, a11, r11, v11, a12, r12, v12, rdArg, rdS, w0,
    rdA0, rdS0, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) (show 1024 ≤ P.scl by omega),
    Nat.reduceMul, wl_cons, wl_nil, Nat.reduceAdd]

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  M0 h P σ s ∧ PdArgs s (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.el P.rl
    (P.scl - 1024)

theorem pa_vp (P : EP) : VP (M0 h P) (.block pubArgs) (V1 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hf, hb⟩ => ?_
  have hg := hi.geo
  refine WP.mono (pa_wp h P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  rw [q0] at m
  have fr : Frame [⟨(P.lay h.D).fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  have rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro i hi'
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega)]
  have v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  have v : ∀ i, 1 ≤ i → i < 6 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i (by omega), m, wl_read _ _ _ 1 i h1 (by simp; omega) (by simp)]
  have hK := hi.k1024
  have slots : ∀ d, 64 ≤ d → d + 4 ≤ frameBytes → t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
    fun d h1 h2 => fr.readW (r := slotR (P.lay h.D) d) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by omega) (by unfold frameBytes at h2; omega) (by decide)) (by decide)
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  · rw [slots sC (by decide) (by decide)]; exact hb.1
  · rw [slots sLo (by decide) (by decide)]; exact hb.2.1
  · rw [slots sDb (by decide) (by decide)]; exact hb.2.2.1
  · rw [slots sAny (by decide) (by decide)]; exact hb.2.2.2
  obtain ⟨ps, hs1⟩ := hi.pubScr
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), hi.kv, hi.rlK, hi.el1, hi.elK, ps,
    by have := hi.scl32; omega⟩

/-- What the call writes to `EM` and returns. -/
abbrev CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K r
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ))

/-- After the call. -/
abbrev V2 (P : EP) (σ s : State) : Prop := M0 h P σ s ∧ CR P σ s.mem (s.gpr .r0)

/-- `EM` and the call's working space, in `scratch`. -/
theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
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

theorem call_pre {P : EP} {σ s : State} (hr : V1 h P σ s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
        (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨⟨hc, hi, -, -⟩, pa⟩ := hr
  have ok := hi.ok
  have hg := hi.geo
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by show _ = (⟨State.addr P.sig, P.gl⟩ : Region); rw [hi.glK]
  have fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
  have hfr : ∀ {R : Region}, R ∈ (P.lay h.D).ro ∨ R ∈ (P.lay h.D).rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨(P.lay h.D).fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  refine pd_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega)
    (by rw [hg.scr_lt (by decide)]; unfold oEm; omega)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.SIG) (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; rw [hi.glK] at this; omega)
    (by rw [hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega)
    ((ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sI)
    ((ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sI)
    (by rw [sigR]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sI) dIS
    (by rw [q0]; exact ((hfr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm).sub_left sI)
    ((ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).symm.sub_right sS')
    ((ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).symm.sub_right sS')
    (by rw [sigR]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).symm.sub_right sS')
    (by rw [q0]; exact ((hfr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm).sub_left sS') ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = (P.lay h.D).LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [sigR]; exact ok.low_buf (R := P.SIG) (.inl (by simp))
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'

theorem call_vp (P : EP) (c : PdImpl) : VP (V1 h P) (.call c.name c.code) (V2 h P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
    (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_pre h hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨⟨hc, hi, -, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by show _ = (⟨State.addr P.sig, P.gl⟩ : Region); rw [hi.glK]
    have hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega)⟩
    have wr' : Covers (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      Covers.cons (by rw [e1]; exact inS (by unfold oEm; omega)) (by rw [e2]; exact inS (by unfold oRsa; omega))
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [sigR]; exact hro P.SIG (by simp)
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [hr.1.1.st.sp]; exact hr.1.2.1.ok.B56
  · exact pd_pub h₁.2 h₂.2 (by rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
      (by rw [(h₁.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₁.1.2.1.pw,
        (h₂.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₂.1.2.1.pw])
      (by rw [(h₁.1.1.st.ro (R := P.E) (by simp)).trans h₁.1.2.1.eB, (h₂.1.1.st.ro (R := P.E) (by simp)).trans
        h₂.1.2.1.eB]) _ _
  · obtain ⟨⟨hc, hi, hf, hb⟩, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    have low : FrameStack.belowA s.sp 56 = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩,
        ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩, (P.lay h.D).LOW] s.mem s'.mem := fr
    have hct : Ctx (P.lay h.D) P.scr σ s' := hc.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) (fun r hr => by
      have hg := hi.geo
      obtain ⟨σ', ok'⟩ := hg.ok
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)).sub_right sI
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)).sub_right sS'
      · exact Lay.fr_low (by decide) (by have := ok.B56; have := P.B.isLt; omega)) rd wr sp
    have slots : ∀ d, d + 4 ≤ frameBytes → s'.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => fr'.readW (r := slotR (P.lay h.D) d) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega)).sub_right sI
        · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega)).sub_right sS'
        · exact Lay.fr_low (by unfold frameBytes at hd; omega) (by have := ok.B56; have := P.B.isLt; omega)) (by decide)
    refine ⟨⟨hct, hi, hf, ?_, ?_, ?_, ?_⟩, fun hp => ?_⟩
    · rw [slots sC (by decide)]; exact hb.1
    · rw [slots sLo (by decide)]; exact hb.2.1
    · rw [slots sDb (by decide)]; exact hb.2.2.1
    · rw [slots sAny (by decide)]; exact hb.2.2.2
    have := pd_post pa po P.nB (nB_length hi) (by rw [(hs.ro_words (R := P.PRE) (by simp) rfl).trans hi.pw]; exact hp)
    rw [(hs.ro (R := P.E) (by simp)).trans hi.eB] at this
    have sg : Spec.Rsa.bytesAt s.mem (State.addr P.sig) P.K = sigB P σ := by
      have e := hs.ro (R := P.SIG) (by simp); dsimp only at e; rw [hi.glK] at e; exact e
    rw [sg] at this
    exact this

end VG.Proof.RsaPss.Arm.Vf
