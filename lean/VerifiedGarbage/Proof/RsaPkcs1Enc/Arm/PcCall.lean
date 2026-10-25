module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcPieces
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: the call and the masks

The call's arguments (`callArgs_wp`), the call of
`vg_rsa_public_precomputed_checked` (`call_vp`, correct and constant time:
its arguments and the public data it reads are the same in two runs), and
the masks of the result and of `out` by the zero test, and the wipe of `EM`
(`maskArgs_wp` … `wipe_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.B + BitVec.ofNat 32 oEM, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.sl]

def OutA (P : EP) (s : State) : Prop := ∀ i < 6, s.mem.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def G7 (P : EP) (σ s : State) : Prop :=
  G6 P σ s ∧ OutA P s ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.pre ∧
    s.gpr .r3 = BitVec.ofNat 32 P.rl

/-- What the call writes and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.Rsa.publicOpChecked nB P.eB (enc P σ))

/-- After the call. -/
def G8 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ EMok P σ s P.K ∧ CR P σ s.mem (s.gpr .r0)

/-- What the function writes and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r
      (if zf (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none)

/-! ## The call's arguments -/

theorem G6.frame6 {σ s t : State} (h : G6 P σ s) (ht : P.lay.St σ t) {d : Nat} (hd : d + 4 ≤ 24)
    (v : BitVec 32) (hm : t.mem = s.mem.writeW (P.lay.fr d) v) : G6 P σ t := by
  obtain ⟨hs, zs, em⟩ := h
  refine ⟨⟨hs.1, ht⟩, ?_, fun i hi => ?_⟩
  · rw [Zs, hm, Lay.readW_fr_other _ _ _ (by simp only [oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by omega_arith)]
    exact zs
  · have hK := hs.1.k1024
    rw [hm, Lay.byte_fr_other _ _ _ (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith) (by omega_arith)]
    exact em i hi

theorem callArgs_wp {σ s : State} (h : G6 P σ s) : WP isa (.block callArgs) s (G7 P σ) := by
  have hs := h.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  have h0 : G6 P σ t0 := ⟨⟨hs.1, hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem⟩,
    by rw [Zs, u0.mem]; exact h.2.1, fun i hi => by rw [u0.mem]; exact h.2.2 i hi⟩
  have r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine h0.1.2.wp_copyArg (j := 4) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  have h1 := h0.frame6 s1 (by decide) _ m1
  refine s1.wp_copyArg (j := 5) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  have h2 := h1.frame6 s2 (by decide) _ m2
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  have h3 : G6 P σ t3 := ⟨⟨hs.1, s3⟩, by rw [Zs, u3.mem]; exact h2.2.1, fun i hi => by rw [u3.mem]; exact h2.2.2 i hi⟩
  have r12' : t3.gpr .r12 = P.B := by rw [u3.other _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine s3.wp_strFr (d := 8) (by dsimp only; decide) (by decide) r12' fun t4 s4 m4 => ?_
  have h4 := h3.frame6 s4 (by decide) _ m4.mem
  refine s4.wp_copyArg (j := 3) (d := 12) (by rw [m4.gpr, r12']) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t5 s5 v5 g5 m5 => ?_
  have h5 := h4.frame6 s5 (by decide) _ m5
  refine s5.wp_copyArg (j := 10) (d := 16) (by rw [g5 _ (by decide), m4.gpr, r12']) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t6 s6 v6 g6 m6 => ?_
  have h6 := h5.frame6 s6 (by decide) _ m6
  refine s6.wp_copyArg (j := 11) (d := 20) (by rw [g6 _ (by decide), g5 _ (by decide), m4.gpr, r12'])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t7 s7 v7 g7 m7 => ?_
  have h7 := h6.frame6 s7 (by decide) _ m7
  refine s7.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t8 s8 u8 => ?_
  refine s8.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t9 s9 u9 => ?_
  refine s9.wp_arg (j := 12) (by simp) (by dsimp only; decide) fun t10 s10 u10 => ?_
  refine s10.wp_arg (j := 13) (by simp) (by dsimp only; decide) fun t11 s11 u11 => WP.block_nil ?_
  have mm : t11.mem = t7.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem]
  refine ⟨⟨⟨hs.1, s11⟩, by rw [Zs, mm]; exact h7.2.1, fun i hi => by rw [mm]; exact h7.2.2 i hi⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m7]
    have w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 24 → e + 4 ≤ 24 →
        (m.writeW (P.lay.fr e) v).readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
      fun m d e v h hd he => Lay.readW_fr_other _ _ _ h (by omega_arith) (by omega_arith)
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, w _ _ _ _ (by decide) (by decide) (by decide),
        u3.mem, m2, w _ _ _ _ (by decide) (by decide) (by decide), m1]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, w _ _ _ _ (by decide) (by decide) (by decide),
        u3.mem, m2]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, Mem.readW_writeW_self32, u3.gpr, dpVal, g2 _ (by decide),
        g1 _ (by decide), r12]
      rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6]
      exact Mem.readW_writeW_self32 _ _ _
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.gpr]; rfl
  · rw [u11.other _ (by decide), u10.gpr]; rfl
  · rw [u11.gpr]; rfl

end VG.Proof.RsaPkcs1Enc.Arm.Pc

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem G7.pdArgs {σ s : State} (h : G7 P σ s) :
    PdArgs s P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.el P.rl P.sl := by
  obtain ⟨⟨hs, -, -⟩, oa, r0, r1, r2, r3⟩ := h
  have a : ∀ i < 6, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i hi]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (by show 4 * i < frameBytes + 56 + 40; simp only [frameBytes]; omega_arith)]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), h1.kv, h1.rlK, h1.el1, h1.elK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_arith⟩

/-- `EM`, as the call reads it. -/
theorem inpA (P : EP) {σ : State} (h : In P σ) : State.addr (P.B + BitVec.ofNat 32 oEM) = P.lay.fr oEM :=
  h.ok.addrB (by show oEM < frameBytes + 56 + 40; decide)

theorem call_pre {σ s : State} (h : G7 P σ s) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.el P.rl)
        (pdWr P.out P.scr P.K P.sl)) := by
  have hs := h.1.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  have e := inpA P hs.1
  have hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  refine pd_pre h.pdArgs hs.2.sp (by omega_arith) (by simp only [frameBytes] at fit; omega_arith)
    (by have := fs (R := P.OUT) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [show (P.B + BitVec.ofNat 32 oEM).toNat = P.B.toNat + oEM from
          Proof.X25519.Arm.toNat_add_lt (by simp only [oEM, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_arith) |>.trans
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)])]
        simp only [oEM, frameBytes] at fit ⊢; omega_arith)
    (by have := fs (R := P.SCR) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (ok.rw_ro (by simp) (by simp)) (ok.rw_ro (by simp) (by simp))
    (by rw [e]; exact (hfr (R := P.OUT) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm)
    (List.pairwise_pair.mp ok.wrw)
    (by rw [q0]; exact (hfr (R := P.OUT) (.inr (by simp)) (by decide)).symm)
    (ok.rw_ro (by simp) (by simp)).symm (ok.rw_ro (by simp) (by simp)).symm
    (by rw [e]; exact hfr (R := P.SCR) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith))
    (by rw [q0]; exact (hfr (R := P.SCR) (.inr (by simp)) (by decide)).symm) ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = P.lay.LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [e]; exact (Lay.fr_low (by simp only [oEM]; omega_arith)).symm
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · exact ok.low_buf (R := P.OUT) (.inr (by simp))
  · exact ok.low_buf (R := P.SCR) (.inr (by simp))

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.rl = P.pw :=
  (hs.2.ro_words (R := P.PRE) (by simp) rfl).trans hs.1.pw

theorem EMok.bytes {σ s : State} (h : EMok P σ s P.K) (hK : P.pl + P.ml + 3 = P.K) :
    Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = enc P σ := by
  have hl := enc_length P σ
  rw [show P.K = (enc P σ).length by omega_arith]
  exact bytesAt_eq fun i hi => by rw [Offset.add_ofNat_add_ofNat]; exact h i (by omega_arith)

theorem call_vp (c : PdImpl) : VP (G7 P) (.call c.name c.code) (G8 P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.el P.rl)
    (pdWr P.out P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have e := inpA P hs.1
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (pdWr P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [e]; exact (Covers.one (hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith))).right
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · exact pd_pub h₁.pdArgs h₂.pdArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (by rw [h₁.1.1.pw, h₂.1.1.pw])
      (by rw [h₁.1.1.eB, h₂.1.1.eB]) _ _
  · have hh := h
    obtain ⟨⟨hs, zs, em⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have hpl := hs.1.em_len
    have low : FrameStack.belowA s.sp 56 = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    have apart : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [P.OUT, P.SCR, P.lay.LOW],
        Region.Disjoint ⟨P.lay.fr d, n⟩ r := fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; omega_arith)
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; omega_arith)
      · exact Lay.fr_low (by simp only [frameBytes] at hd; omega_arith)
    refine ⟨⟨hs.1, st⟩, ?_, fun i hi => ?_, fun nB hn hp => ?_⟩
    · rw [Zs, fr'.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _) (apart (by decide)) (by decide)]
      exact zs
    · rw [fr'.byte1 (apart (by simp only [oEM, frameBytes]; omega_arith))]
      exact em i hi
    · have := pd_post hh.pdArgs po nB hn (by rw [hs.pw]; exact hp)
      rw [hs.eB, inpA P hs.1, em.bytes hpl] at this
      exact this

/-! ## The masks -/

theorem zf_cases (bs : List Byte) : zf bs = 0 ∨ zf bs = 1 := by
  unfold zf; split <;> simp

theorem masked {m m' : Mem} {a : Addr} {K : Nat} {r z : BitVec 32} {o : Option (List Byte)}
    (hz : z = 0 ∨ z = 1) (hw : Spec.Rsa.written m a K r o)
    (hb : Spec.Rsa.bytesAt m' a K = (Spec.Rsa.bytesAt m a K).map (· &&& (z - 1).setWidth 8)) :
    Spec.Rsa.written m' a K (r &&& (z - 1)) (if z = 0 then o else none) := by
  rcases hz with rfl | rfl
  · simp only [ite_true]
    have e1 : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    have e8 : (BitVec.allOnes 32).setWidth 8 = BitVec.allOnes 8 := by decide
    have hb' : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K := by
      rw [hb, e1, e8]
      exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
    rw [e1, BitVec.and_allOnes]
    cases o with
    | some y => exact ⟨hw.1, hb'.trans hw.2⟩
    | none => exact ⟨hw.1, hb'.trans hw.2⟩
  · simp only [show (1 : BitVec 32) = 0 ↔ False by decide, ite_false]
    have e1 : (1 : BitVec 32) - 1 = 0 := by decide
    have e0 : r &&& (0 : BitVec 32) = 0 := by simp
    rw [e1, e0]
    refine ⟨rfl, ?_⟩
    rw [hb, e1]
    apply List.ext_getElem (by simp [bytesAt_length])
    intro i h₁ h₂
    simp

/-- Before the mask of `out`. -/
def G9 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ EMok P σ s P.K ∧ ∃ rc, CR P σ s.mem rc ∧ s.gpr .r3 = rc &&& (zf (psB P σ) - 1) ∧
    s.gpr .r2 = zf (psB P σ) - 1 ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K

/-- `out` masked. -/
def G10 (P : EP) (σ s : State) : Prop := S P σ s ∧ EMok P σ s P.K ∧ Res P σ s.mem (s.gpr .r3)

/-- Before the wipe of `EM`. -/
def G11 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Res P σ s.mem (s.gpr .r3) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `EM` wiped. -/
def G12 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r3)

/-- The end of the body. -/
def G13 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem maskArgs_wp {σ s : State} (h : G8 P σ s) : WP isa (.block maskArgs) s (G9 P σ) := by
  obtain ⟨hs, zs, em, cr⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_slot (d := oZ) (by show oZ + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r3]) (by simp)) u4.mem
  refine s4.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t6 s6 u6 => WP.block_nil ?_
  have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have z2 : t2.gpr .r3 = zf (psB P σ) := by rw [u2.gpr, u1.mem]; exact zs
  refine ⟨⟨hs.1, s6⟩, fun i hi => by rw [mm]; exact em i hi, s.gpr .r0, by rw [mm]; exact cr, ?_, ?_, ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), u3.gpr, dpVal, z2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, z2]
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem maskOut_wp {σ s : State} (h : G9 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (G10 P σ) := by
  obtain ⟨hs, em, rc, cr, r3, r2, r0, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k64
  have hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by omega_arith) (by have := hs.1.k1024; omega_arith)
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rest⟩ => ?_
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, fun i hi => ?_, fun nB hn hp => ?_⟩
  · rw [fr.byte1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; have := hs.1.k1024; omega_arith))]
    exact em i hi
  · rw [rest.gpr .r3 (by decide), r3]
    rw [r2] at hb
    exact masked (zf_cases _) (cr nB hn hp) hb

theorem wipeArgs_wp {σ s : State} (h : G10 P σ s) : WP isa (.block wipeArgs) s (G11 P σ) := by
  obtain ⟨hs, -, res⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2])
    (by simp)) u4.mem⟩, ?_, ?_, ?_, u4.gpr⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
    exact res
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem wipe_wp {σ s : State} (h : G11 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (G12 P σ) := by
  obtain ⟨hs, res, r0, lr, -⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have e := inpA P hs.1
  have fit := ok.fit
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oEM) (n := P.K) (by have := hs.1.k64; omega_arith)
    (by omega_arith) (by
      rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega_arith),
        BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_arith)
    (by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith)) r0 lr)
    fun t ⟨_, fr, rest⟩ => ?_
  rw [e] at fr
  have st : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith) fr
    rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, fun nB hn hp => ?_⟩
  have hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
    bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_arith)).symm)
      (by omega_arith)
  have w := res nB hn hp
  rw [rest.gpr .r3 (by decide)]
  revert w
  generalize (if zf (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none) = o
  intro w
  cases o with
  | some y => exact ⟨w.1, hb.trans w.2⟩
  | none => exact ⟨w.1, hb.trans w.2⟩

theorem fin_wp {σ s : State} (h : G12 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (G13 P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
    by rw [u.mem, u.gpr]; exact h.2⟩

end VG.Proof.RsaPkcs1Enc.Arm.Pc
