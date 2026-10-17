module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfPieces
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: the call

The call of `vg_rsa_public_precomputed_checked` (`call_vp`, correct and
constant time: its arguments and the public data it reads are the same in
two runs), which writes `EM₁` and returns its status (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- What the call writes to `EM₁` and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.lay.fr oEM1) P.K r (Spec.Rsa.publicOpChecked nB P.eB (sigB P σ))

/-- After the call. -/
def C2 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ CR P σ s.mem (s.gpr .r0)

theorem C1.pdArgs {σ s : State} (h : C1 P σ s) :
    PdArgs s (P.B + BitVec.ofNat 32 oEM1) P.pre P.e P.sig P.scr P.K P.el P.rl P.sl := by
  obtain ⟨⟨hs, -⟩, oa, r0, r1, r2, r3⟩ := h
  have a : ∀ i < 6, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i hi]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (by show 4 * i < frameBytes + 56 + 36; simp only [frameBytes]; omega)]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), h1.kv, h1.rlK, h1.el1, h1.elK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega⟩

/-- `EM₁`, as the call writes it. -/
theorem outA (P : EP) {σ : State} (h : In P σ) : State.addr (P.B + BitVec.ofNat 32 oEM1) = P.lay.fr oEM1 :=
  h.ok.addrB (by show oEM1 < frameBytes + 56 + 36; decide)

theorem call_pre {σ s : State} (h : C1 P σ s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
        (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl)) := by
  have hs := h.1.1
  have hgl := h.1.2
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  have e := outA P hs.1
  have hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
  refine pd_pre h.pdArgs hs.2.sp (by omega) (by simp only [frameBytes] at fit; omega)
    (by rw [show (P.B + BitVec.ofNat 32 oEM1).toNat = P.B.toNat + oEM1 from
          Proof.X25519.Arm.toNat_add_lt (by simp only [oEM1, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega) |>.trans
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)])]
        simp only [oEM1, frameBytes] at fit ⊢; omega)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.SIG) (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega)
    (by have := fs (R := P.SCR) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [e]; exact hfr (R := P.PRE) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega))
    (by rw [e]; exact hfr (R := P.E) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega))
    (by rw [e, sigR]; exact hfr (R := P.SIG) (.inl (by simp)) (by simp only [oEM1, frameBytes]; omega))
    (by rw [e]; exact hfr (R := P.SCR) (.inr (by simp)) (by simp only [oEM1, frameBytes]; omega))
    (by rw [e, q0]; exact Lay.fr_sep (by simp only [oEM1]; omega) (by simp only [oEM1]; omega) (by decide))
    (ok.rw_ro (by simp) (by simp)).symm (ok.rw_ro (by simp) (by simp)).symm
    (by rw [sigR]; exact (ok.rw_ro (by simp) (by simp)).symm)
    (by rw [q0]; exact (hfr (R := P.SCR) (.inr (by simp)) (by decide)).symm) ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = P.lay.LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [sigR]; exact ok.low_buf (R := P.SIG) (.inl (by simp))
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · rw [e]; exact (Lay.fr_low (by simp only [oEM1]; omega)).symm
  · exact ok.low_buf (R := P.SCR) (.inr (by simp))

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.rl = P.pw :=
  (hs.2.ro_words (R := P.PRE) (by simp) rfl).trans hs.1.pw

theorem call_vp (c : PdImpl) : VP (C1 P) (.call c.name c.code) (C2 P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
    (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have hgl := h.1.2
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have e := outA P hs.1
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (pdWr (P.B + BitVec.ofNat 32 oEM1) P.scr P.K P.sl) s.wr := by
      refine Covers.cons ?_ (hrw P.SCR (by simp))
      rw [e]; exact Covers.one (hs.2.inFr (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega))
    have sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by rw [← hgl]
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [sigR]; exact hro P.SIG (by simp)
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · exact pd_pub h₁.pdArgs h₂.pdArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (by rw [h₁.1.1.pw, h₂.1.1.pw])
      (by rw [h₁.1.1.eB, h₂.1.1.eB]) _ _
  · have hh := h
    obtain ⟨⟨hs, hgl⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have e := outA P hs.1
    have low : FrameStack.belowA s.sp 56 = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [⟨State.addr (P.B + BitVec.ofNat 32 oEM1), P.K⟩, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e]; exact ⟨P.lay.FR, by simp, Offset.sub_base _ (by simp only [oEM1, frameBytes]; omega)⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨⟨hs.1, st⟩, hgl⟩, fun nB hn hp => ?_⟩
    have := pd_post hh.pdArgs po nB hn (by rw [hs.pw]; exact hp)
    rw [hs.eB, e, show P.K = P.gl from hgl.symm, hs.2.ro (R := P.SIG) (by simp)] at this
    rw [← hgl]
    exact this

end VG.Proof.RsaPkcs1Sig.Arm.Vf
