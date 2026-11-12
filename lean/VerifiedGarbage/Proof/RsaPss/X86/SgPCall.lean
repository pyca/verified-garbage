module

public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCallP
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSpT
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
meta import VerifiedGarbage.Impl.RsaPss.X86
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# RSASSA-PSS signing on x86, given `pre`: the call and the body

`vg_rsa_pss_sign_precomputed`'s entry has `vg_rsa_pss_sign`'s layout with
`pre` and `pre_len` after its arguments and `pre` read (`EP.layP`), and
`pre` holds the key's precomputed values (`XP`): a state `vg_rsa_pss_sign`'s
body may start from (`Lay.Ok.prefix`), whose proofs carry `XP` along
(`VP.keep`). After `privArgs`, the arguments 24 and 25 to the call's 20 and
21 (`extras_vp`), and the call of `vg_rsa_private_checked_precomputed`
(`call_vpP`), whose result is `vg_rsa_private_checked`'s: the body
(`body_vpP`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms byLen_vp byLen_noSp)

variable (h : PssHash) (G : Spec.Mgf1.Hash)

/-- `pre`. -/
abbrev preR (pre : BitVec 32) (L : Nat) : Region := ⟨pre.setWidth 64, L * 8⟩

/-- The layout of `vg_rsa_pss_sign_precomputed`'s entry. -/
abbrev EP.layP (P : EP) (D : Nat) (pre : BitVec 32) (L : Nat) : Lay :=
  { P.lay D with argv := P.argv D ++ [pre, BitVec.ofNat 32 L], ro := P.ro D ++ [preR pre L] }

/-- What the entry adds to `vg_rsa_pss_sign`'s: its layout, and `pre` the key's values. -/
structure XP (D : Nat) (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) : Prop where
  ok : (P.layP D pre L).Ok σ
  lenEq : L = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  key : Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) = some (Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L)

/-- The wider layout gives `vg_rsa_pss_sign`'s. -/
theorem okBase {D : Nat} {P : EP} {pre : BitVec 32} {L : Nat} {σ : State} (hk : (P.layP D pre L).Ok σ) :
    (P.lay D).Ok σ :=
  Lay.Ok.prefix (L := P.lay D) [pre, BitVec.ofNat 32 L] [preR pre L] hk

/-- A buffer only read misses what the body writes. -/
theorem lay_ro_apart {Ly : Lay} {σ : State} (hk : Ly.Ok σ) {R : Region} (hR : R ∈ Ly.ro) :
    ∀ r ∈ Ly.W, R.Disjoint r := by
  intro r hr
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((hk.stk R (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (hk.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((hk.stk R (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

variable {P : EP} {pre : BitVec 32} {L : Nat}

/-- A state of `vg_rsa_pss_sign`'s body is one of the wider layout's. -/
theorem stP {σ s : State} (hs : (P.lay h.D).St σ s) (hx : XP h.D P pre L σ) : (P.layP h.D pre L).St σ s :=
  ⟨hx.ok, hs.sp, hs.rd, hs.wr, hs.frame⟩

/-! ## The arguments 20 and 21 -/

/-- Words written at the frame's bytes 80 to 87 keep the call's twenty arguments and the encoding. -/
theorem R1.hi {σ s t : State} (hr : R1 h G P σ s) (hc : Ctx (P.lay h.D) P.scr σ t)
    (hsp : t.gpr .esp = s.gpr .esp) (hf : Frame [⟨(P.lay h.D).fr 80, 8⟩] s.mem t.mem) : R1 h G P σ t := by
  obtain ⟨hc0, hk, he, pa⟩ := hr
  have hi := hk.1
  have hg := hi.geo
  have ok := hi.ok
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  have spB : s.gpr .esp = P.B := hc0.st.sp
  refine ⟨hc, hk, fun i hi' => ?_, { pa with args := fun i hi' => ?_, sp := ?_, fit := ?_ }⟩
  · rw [← he i hi']
    exact hf _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (by have := hi.k1024; unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; unfold frameBytes; omega_arith)).symm _ (Region.contains_self _ _)
  · rw [hsp, ← pa.args i hi']
    have ha : addr (s.gpr .esp) (4 * i) = (P.lay h.D).fr (4 * i) := by
      rw [spB]; exact ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega)
    rw [ha]
    refine hf.readW (r := ⟨(P.lay h.D).fr (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (.inl (by omega)) (by omega) (by omega)
  · rw [hsp]; exact pa.sp
  · rw [hsp]; exact pa.fit

/-- Before the call of `vg_rsa_private_checked_precomputed`. -/
abbrev R1P (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  (R1 h G P σ s ∧ XP h.D P pre L σ) ∧ s.mem.readW ((P.lay h.D).fr 80) 32 = pre ∧
    s.mem.readW ((P.lay h.D).fr 84) 32 = BitVec.ofNat 32 L

theorem frame_hi {m : Mem} {d : Nat} (hd : 80 ≤ d ∧ d + 4 ≤ 88) (v : BitVec 32) :
    Frame [⟨(P.lay h.D).fr 80, 8⟩] m (m.writeW ((P.lay h.D).fr d) v) := by
  refine (slot_frame (P.lay h.D) m d v).sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have e : (P.lay h.D).fr d = (P.lay h.D).fr 80 + BitVec.ofNat 64 (d - 80) := by
    simp only [Lay.fr]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 80 + (d - 80) = d by omega]
  rw [slotR, e]
  exact Offset.sub_base _ (by omega)

theorem extras_wp {σ s : State} (hr : R1 h G P σ s) (hx : XP h.D P pre L σ) :
    WP isa (.block (copyArg 24 20 ++ copyArg 25 21)) s (R1P h G P pre L σ) := by
  have hc := hr.1
  have hg := hr.2.1.1.geo
  have ok := hr.2.1.1.ok
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine (stP h hc.st hx).wp_arg (j := 24) (by simp) (by decide) fun t1 s1 u1 => ?_
  have c1 : Ctx (P.lay h.D) P.scr σ t1 := ⟨⟨ok, s1.sp, s1.rd, s1.wr, s1.frame⟩, (u1.other _ (by decide)).trans hc.ebp⟩
  refine c1.wp_st hg (d := 4 * 20) (by decide) fun t2 c2 m2 => ?_
  refine (stP h c2.st hx).wp_arg (j := 25) (by simp) (by decide) fun t3 s3 u3 => ?_
  have c3 : Ctx (P.lay h.D) P.scr σ t3 := ⟨⟨ok, s3.sp, s3.rd, s3.wr, s3.frame⟩, (u3.other _ (by decide)).trans c2.ebp⟩
  refine c3.wp_st hg (d := 4 * 21) (by decide) fun t4 c4 m4 => WP.block_nil ?_
  have sp4 : t4.gpr .esp = s.gpr .esp := by rw [c4.st.sp, hc.st.sp]
  have f4 : Frame [⟨(P.lay h.D).fr 80, 8⟩] s.mem t4.mem := by
    rw [m4.mem, u3.mem, m2.mem, u1.mem]
    exact (frame_hi h (d := 80) (by decide) _).trans (frame_hi h (d := 84) (by decide) _)
  refine ⟨⟨R1.hi h G hr c4 sp4 f4, hx⟩, ?_, ?_⟩
  · rw [m4.mem, u3.mem, Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega), m2.mem, u1.mem,
      Mem.readW_writeW_self32, u1.gpr]
    rfl
  · rw [m4.mem, u3.mem, show (4 * 21 : Nat) = 84 from rfl, Mem.readW_writeW_self32, u3.gpr]
    rfl

theorem extras_taint : TaintOk [.esp] (.block (copyArg 24 20 ++ copyArg 25 21)) := ⟨_, by taint_decide⟩

theorem extras_vp :
    VP (fun σ s => R1 h G P σ s ∧ XP h.D P pre L σ) (.block (copyArg 24 20 ++ copyArg 25 21)) (R1P h G P pre L) :=
  VP.taint [.esp] extras_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) fun _ _ hs => extras_wp h G hs.1 hs.2

/-! ## The call -/

theorem callWords {σ s : State} (hs : (P.lay h.D).St σ s) (hx : XP h.D P pre L σ) :
    Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L = Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L := by
  have fit : (pre.setWidth 64).toNat + 8 * L ≤ 2 ^ 32 := by
    have := hx.ok.fits (preR pre L) (List.mem_append_left _ (by simp))
    simp only at this; omega
  have sep : ∀ r ∈ (P.layP h.D pre L).W, (⟨pre.setWidth 64, 8 * L⟩ : Region).Disjoint r := by
    rw [show 8 * L = L * 8 from Nat.mul_comm _ _]
    exact lay_ro_apart hx.ok (R := preR pre L) (by simp)
  rw [Proof.Rsa.wordsAt_frame ((stP h hs hx).callEntry_frame (by show (4 : Nat) ≤ 3448; decide)) (by omega) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact sep _ (by simp [Lay.W])),
    Proof.Rsa.wordsAt_frame hs.frame (by omega) sep]

/-- The call's arguments, with `pre`. -/
theorem R1P.privArgsP {σ s : State} (hr : R1P h G P pre L σ s) :
    PrivArgsP s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv
      (P.scr + BitVec.ofNat 32 oRsa) pre P.K P.el P.pl P.ql (P.scl - 1024) L := by
  obtain ⟨⟨⟨hc, hk, -, pa⟩, hx⟩, s80, s84⟩ := hr
  have hi := hk.1
  have okP := hx.ok
  have hfit := okP.fit
  simp only [Lay.A, EP.argv, List.length_append, List.length_cons, List.length_nil, frameBytes] at hfit
  have hsp : s.gpr .esp = P.B := hc.st.sp
  have key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.callEntry.mem (P.n.setWidth 64) P.K)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.p.setWidth 64) P.pl)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.q.setWidth 64) P.ql) =
      some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L) := by
    have c4 : (4 : Nat) ≤ (P.lay h.D).C := by show (4 : Nat) ≤ 3448; decide
    rw [hc.st.callEntry_ro (R := P.N) c4 (by simp), hc.st.callEntry_ro (R := P.PP) c4 (by simp),
      hc.st.callEntry_ro (R := P.QQ) c4 (by simp), callWords h hc.st hx]
    have k := hx.key
    rw [← hi.nB] at k
    exact k
  refine ⟨pa, fun i hi' => ?_, by rw [hsp]; omega, hx.lenEq, key⟩
  have ha : addr (s.gpr .esp) (4 * i) = (P.lay h.D).fr (4 * i) := by
    rw [hsp]; exact hi.ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega)
  rcases (by omega : i < 20 ∨ i = 20 ∨ i = 21) with hlt | rfl | rfl
  · rw [pa.args i hlt]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
        i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> rfl
  · rw [ha]; exact s80
  · rw [ha]; exact s84

/-- `privNameP`: `vg_rsa_private_checked_precomputed` over `c`. -/
def privNameP (c : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ c.suffix

/-- `out` and the result: the call of `vg_rsa_private_checked_precomputed`. -/
theorem call_vpP (hG : Proof.Mgf1.Valid G) (c : CrtImpl) (w : CrtPImpl) :
    VP (R1P h G P pre L) (.call (privNameP c) (privCodeP c w))
      (fun σ s => Fin h G P σ s ∧ XP h.D P pre L σ) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verifiedP c w
  have hst := Proof.Rsa.X86.PrivChecked.code_stackP c w
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w)
    (privRdP P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv pre P.K P.el P.pl P.ql L)
    (privWrP P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have pa := R1P.privArgsP h G hr
    obtain ⟨⟨⟨hc, hk, -, -⟩, hx⟩, -, -⟩ := hr
    have hi := hk.1
    have okP := hx.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have fit := okP.fit
    simp only [Lay.A, EP.argv, List.length_append, List.length_cons, List.length_nil, frameBytes] at fit
    have oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp okP.wrw
    have args0 : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP h.D pre L).fr 0, 88⟩ := by simp
    have hsp := hc.st.sp
    rw [show (P.lay h.D).B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    have b88 : 0 + 88 ≤ (P.layP h.D pre L).F + 16 := by show 0 + 88 ≤ frameBytes + 16; decide
    refine priv_preP pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      have hr' : r = inpR P ∨ r ∈ (P.layP h.D pre L).ro := by
        simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | h3 | rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inr (by simp)
        · exact .inr (by simp)
        · exact .inl h3
        all_goals exact .inr (by simp)
      simp only [privWrP, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rcases hr' with rfl | hr'
      · exact oS.sub_right sI
      · exact okP.rw_ro (w := P.OUT) (by simp) hr'
      · exact dIS.symm
      · exact (okP.rw_ro (w := P.SCR) (by simp) hr').sub_left sS'
      · rw [args0]; exact (okP.stk_fr (R := P.SCR) (.inr (by simp)) b88).sub_right sI
      · rw [args0]; exact okP.stk_fr (.inl hr') b88
    · simp only [privWrP, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨oS.sub_right sS', ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact (okP.stk_fr (R := P.OUT) (.inr (by simp)) b88).symm
      · rw [args0]; exact ((okP.stk_fr (R := P.SCR) (.inr (by simp)) b88).symm).sub_left sS'
    · intro r hr
      rw [hsp, ← show (P.layP h.D pre L).B = P.B from rfl, okP.low_eq]
      have hr' : r = scrR P ∨ r = ⟨(s.gpr .esp).setWidth 64, 88⟩ ∨ r = inpR P ∨ r ∈ (P.layP h.D pre L).ro ∨
          r ∈ (P.layP h.D pre L).rw := by
        simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | h2 | h3 | rfl | rfl | h6 | rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inr (.inr (.inr (.inr (by simp))))
        · exact .inl h2
        · exact .inr (.inl h3)
        · exact .inr (.inr (.inr (.inl (by simp))))
        · exact .inr (.inr (.inr (.inl (by simp))))
        · exact .inr (.inr (.inl h6))
        all_goals exact .inr (.inr (.inr (.inl (by simp))))
      rcases hr' with rfl | rfl | rfl | hr' | hr'
      · exact (okP.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
      · have : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP h.D pre L).fr 0, 88⟩ := by simp
        rw [hsp, this]; exact (Lay.fr_low (by omega_arith) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact (okP.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
      · exact okP.low_buf (.inl hr')
      · exact okP.low_buf (.inr hr')
    · intro r hr
      have hg := hi.geo
      simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact okP.fits P.OUT (by simp)
      · show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 88 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      · exact okP.fits _ (by simp)
      · exact okP.fits _ (by simp)
      · show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
      all_goals exact okP.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨⟨⟨hc, hk, -, -⟩, hx⟩, -, -⟩ := hr
    have hi := hk.1
    have hs := stP h hc.st hx
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have hro : ∀ R ∈ (P.layP h.D pre L).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have hrw : ∀ R ∈ (P.layP h.D pre L).rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRw hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    have hA : Covers [⟨P.B.setWidth 64, 88⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 88) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWrP P.B P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      (hrw P.OUT (by simp)).cons ((show Covers [scrR P] s.wr by
        rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((show Covers [inpR P] (s.rd ++ s.wr) by
      rw [inpR, e1]; exact (inS (by unfold oEm; omega_arith)).right).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons ((hro (preR pre L) (by simp)).cons Covers.nil))))))))
  · rw [hr.1.1.1.st.sp]
    have : 3448 ≤ P.B.toNat := hr.1.1.2.1.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega_arith
  · have p₁ := R1P.privArgsP h G h₁
    have p₂ := R1P.privArgsP h G h₂
    have k₁ := p₁.key
    have k₂ := p₂.key
    have c4 : (4 : Nat) ≤ (P.lay h.D).C := by show (4 : Nat) ≤ 3448; decide
    have n₁ : Spec.Rsa.bytesAt s₁.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
      (h₁.1.1.1.st.callEntry_ro (R := P.N) c4 (by simp)).trans h₁.1.1.2.1.1.nB
    have n₂ : Spec.Rsa.bytesAt s₂.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
      (h₂.1.1.1.st.callEntry_ro (R := P.N) c4 (by simp)).trans h₂.1.1.2.1.1.nB
    rw [n₁] at k₁
    rw [n₂] at k₂
    have w₁ := preModulus k₁
    have w₂ := preModulus k₂
    rw [← w₂] at w₁
    have hl : P.nB.length = P.K := by rw [← h₁.1.1.2.1.1.nB, Proof.RsaPkcs1Sig.bytesAt_len]
    rw [hl] at w₁
    refine priv_pubP p₁ p₂ (by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]) ?_ ?_ ?_ ?_ (Option.some.inj w₁) _ _
    · rw [nB_at h h₁.1.1.2.1.1 h₁.1.1.1.st, nB_at h h₂.1.1.2.1.1 h₂.1.1.1.st]
    · rw [eB_at h h₁.1.1.2.1.1 h₁.1.1.1.st, eB_at h h₂.1.1.2.1.1 h₂.1.1.1.st]
    · rw [h₁.1.1.1.st.sp, h₁.1.1.2.1.1.ok.low_eq]
      exact h₁.1.1.2.1.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.1.1.st.sp, h₁.1.1.2.1.1.ok.low_eq]
      exact h₁.1.1.2.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have pa := R1P.privArgsP h G hr
    obtain ⟨⟨⟨hc, hk, he, -⟩, hx⟩, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    have low : Region.Sub (below (s.gpr .esp) (stackUse (privCodeP c w) + 4)) (P.lay h.D).LOW := by
      rw [hsp, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega_arith) ok.BC
    have st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨(P.lay h.D).FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.lay h.D).fr 0, 88⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨(P.lay h.D).LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨⟨hi, st⟩, ?_⟩, hx⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_postP pa po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ (P.lay h.D).ro) => hs.callEntry_ro (by show 4 ≤ 3448; decide) hR
    have em : Spec.Rsa.bytesAt s.callEntry.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
        (List.range P.K).map (emF h G P σ) := by
      rw [RsaPkcs1Sig.bytesAt_frame (hs.callEntry_frame (by show 4 ≤ 3448; decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (ok.low_buf (R := P.SCR) (.inr (by simp))).symm.sub_left sI)
        (by omega_arith)]
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, em,
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h G hG hi hk.2.1]
    exact this

/-! ## The tail and the body -/

variable {dn : String} {f : MdFns} {fG : Fns}

/-- The checks, then zeros or the encoding and the call of
`vg_rsa_private_checked_precomputed`, keeping `XP`. -/
theorem tail_vpP (P : EP) (pre : BitVec 32) (L : Nat)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash)
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (c : CrtImpl) (w : CrtPImpl) :
    VP (fun σ s => Sy (S h P) σ s ∧ XP h.D P pre L σ)
      (signTail f h.H fG (privNameP c) (privCodeP c w) privArgsP)
      (fun σ s => Fin h g.G P σ s ∧ XP h.D P pre L σ) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.1⟩
  show VP _ (.seq (.block (signChk ++ params h.H)) (.ite .ne signFail (.seq (signEncT f h.H fG)
    (.seq (.block (privArgs ++ (copyArg 24 20 ++ copyArg 25 21))) (.call (privNameP c) (privCodeP c w)))))) _
  exact ((VP.syms (chk_vp h P)).keep (XP h.D P pre L)).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.1.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.1.2.2.2.2.2, h₂.1.1.2.2.2.2.2])
    (((fail_vp h g.G P).keep (XP h.D P pre L)).mono (fun σ s ⟨⟨⟨h1, _⟩, x⟩, e⟩ => ⟨⟨h1, e⟩, x⟩) fun _ _ h => h)
    ((((enc_vp h P hP hTH fneH g hT fne).keep (XP h.D P pre L)).mono
      (fun σ s ⟨⟨⟨h1, sy⟩, x⟩, e⟩ => ⟨⟨e0_of h h1 e, sy⟩, x⟩) fun _ _ h => ⟨h.1.1, h.2⟩).seq
      ((((pa_vp h g.G P).keep (XP h.D P pre L)).block_append (extras_vp h g.G)).seq
        (call_vpP h g.G g.valid c w))))

/-- The body, for the hash function `h` of index `ix` and MGF1's `g`. -/
theorem body_vpP (P : EP) (pre : BitVec 32) (L : Nat) {ix : Nat} (hix₀ : ix ∈ idxs)
    (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash)
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (c : CrtImpl) (w : CrtPImpl) :
    VP (fun σ s => Sy (S h P) σ s ∧ XP h.D P pre L σ) (signBodyT f fG (privNameP c) (privCodeP c w) privArgsP)
      (fun σ s => Fin h g.G P σ s ∧ XP h.D P pre L σ) := by
  have hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VP _ (.seq (.block (idxLoad 22))
    (byLen (fun i => signTail f (ofIdx i) fG (privNameP c) (privCodeP c w) privArgsP) idxs)) _
  refine (((idx_vp h P fun σ hσ => (hTH σ hσ).2).keep (XP h.D P pre L)).mono (fun _ _ h => h)
    fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩).seq
    (byLen_vp (F := fun σ s => (Sy (S h P) σ s ∧ XP h.D P pre L σ) ∧ s.gpr .edx = BitVec.ofNat 32 ix)
      (D := ix) hlt (fun _ _ hs => hs.2)
      (fun σ s t ⟨⟨⟨⟨hi, hs⟩, sy⟩, x⟩, dx⟩ fu sy' => ⟨⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, x⟩, by rw [fu.gpr]; exact dx⟩)
      ?_ hix₀ cmpIdxs_taint)
  rw [tail_eq h hs privArgsP]
  exact (tail_vpP h P pre L (fun σ hσ => (hTH σ hσ).1) fneH g hT fne c w).mono (fun _ _ hs => hs.1)
    fun _ _ h => h

theorem tail_noSpP {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (c : CrtImpl) (w : CrtPImpl) :
    NoSp (signTail f h.H fG (privNameP c) (privCodeP c w) privArgsP) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig16
  have p3 := sp.cpSalt
  have p4 := sp.lenArgs19
  have p5 := sp.putH
  have p6 := sp.mgfArgs
  have hct := ctHashT_noSp h hi hc hd (j := 22) (NoSp.of_all (by decide +kernel))
  have hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 23) (NoSp.of_all (by decide +kernel))
  have hp := Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w
  simp only [signTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [signEncT, yDig, signFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSpP {f : MdFns} {fG : Fns} (hf : FnsSp f fG)
    (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i) (c : CrtImpl) (w : CrtPImpl) :
    NoSp (signBodyT f fG (privNameP c) (privCodeP c w) privArgsP) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs privArgsP]
  exact tail_noSpP h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf c w

/-! ## The contract -/

/-- The precomputed contract, with the hash function's table one of `tsH`
and MGF1's one of `ts`, and `vg_rsa_pss_sign`'s stack. -/
abbrev specP (tsH ts : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "signP_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

/-- The code, calling `vg_rsa_private_checked_precomputed` over `c` and `w`,
with the hash function any of the tables of `vs` and MGF1's any of `gs`. -/
abbrev signCodeP (vs : List MVar) (gs : List TVar) (c : CrtImpl) (w : CrtPImpl) : Prog isa :=
  sign (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) (privNameP c) (privCodeP c w) privArgsP

/-- The contract, with those tables. -/
abbrev sspecP (vs : List MVar) (gs : List TVar) : Contract isa :=
  specP (Proof.MdHashTable.X86.tables vs) (Proof.HashTable.X86.tables gs)

end VG.Proof.RsaPss.X86.Sg
