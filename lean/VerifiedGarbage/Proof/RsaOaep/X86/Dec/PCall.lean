module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Verified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCallP
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Impl.RsaOaep.X86
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# RSAES-OAEP decryption on x86, given `pre`: the call and the body

`vg_rsa_oaep_decrypt_precomputed`'s entry has `vg_rsa_oaep_decrypt`'s layout
with `pre` and `pre_len` after its arguments and `pre` read (`EP.layP`), and
`pre` holds the key's precomputed values (`XP`): a state
`vg_rsa_oaep_decrypt`'s body may start from (`Lay.Ok.prefix`), whose proofs
carry `XP` along (`VP.keep`). After `privArgs`, the arguments 25 and 26 to
the call's 20 and 21 (`extras_vp`), the call of
`vg_rsa_private_checked_precomputed` (`call_vpP`), whose result is
`vg_rsa_private_checked`'s, then `vg_rsa_oaep_decrypt`'s decoding
(`body_vpP`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st atS addi copyArg)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)

/-- `pre`. -/
abbrev preR (pre : BitVec 32) (L : Nat) : Region := ⟨pre.setWidth 64, L * 8⟩

/-- The layout of `vg_rsa_oaep_decrypt_precomputed`'s entry. -/
abbrev EP.layP (P : EP) (pre : BitVec 32) (L : Nat) : Lay :=
  { P.lay with argv := P.argv ++ [pre, BitVec.ofNat 32 L], ro := P.ro ++ [preR pre L] }

/-- What the entry adds to `vg_rsa_oaep_decrypt`'s: its layout, and `pre` the key's values. -/
structure XP (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) : Prop where
  ok : (P.layP pre L).Ok σ
  lenEq : L = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  key : Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) = some (Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L)

/-- The wider layout gives `vg_rsa_oaep_decrypt`'s. -/
theorem okBase {P : EP} {pre : BitVec 32} {L : Nat} {σ : State} (hk : (P.layP pre L).Ok σ) : P.lay.Ok σ :=
  Lay.Ok.prefix (L := P.lay) [pre, BitVec.ofNat 32 L] [preR pre L] hk

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

/-- A state of `vg_rsa_oaep_decrypt`'s body is one of the wider layout's. -/
theorem stP {σ s : State} (hs : P.lay.St σ s) (hx : XP P pre L σ) : (P.layP pre L).St σ s :=
  ⟨hx.ok, hs.sp, hs.rd, hs.wr, hs.frame⟩

/-! ## The arguments 20 and 21 -/

/-- Words written at the frame's bytes 80 to 87 keep the call's twenty arguments. -/
theorem R1.hi {σ s t : State} (hr : R1 P σ s) (hc : Ctx P.lay P.scr σ t)
    (hsp : t.gpr .esp = s.gpr .esp) (hf : Frame [⟨P.lay.fr 80, 8⟩] s.mem t.mem) : R1 P σ t := by
  obtain ⟨hc0, hi, pa⟩ := hr
  have ok := hi.ok
  have hfit := ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at hfit
  have spB : s.gpr .esp = P.B := hc0.st.sp
  refine ⟨hc, hi, { pa with args := fun i hi' => ?_, sp := ?_, fit := ?_ }⟩
  · rw [hsp, ← pa.args i hi']
    have ha : addr (s.gpr .esp) (4 * i) = P.lay.fr (4 * i) := by
      rw [spB]; exact ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega_using [hi'])
    rw [ha]
    refine hf.readW (r := ⟨P.lay.fr (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (.inl (by omega_using [hi'])) (by omega_using [hi']) (by omega_using [])
  · rw [hsp]; exact pa.sp
  · rw [hsp]; exact pa.fit

/-- Before the call of `vg_rsa_private_checked_precomputed`. -/
abbrev R1P (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  (R1 P σ s ∧ XP P pre L σ) ∧ s.mem.readW (P.lay.fr 80) 32 = pre ∧
    s.mem.readW (P.lay.fr 84) 32 = BitVec.ofNat 32 L

theorem frame_hi {m : Mem} {d : Nat} (hd : 80 ≤ d ∧ d + 4 ≤ 88) (v : BitVec 32) :
    Frame [⟨P.lay.fr 80, 8⟩] m (m.writeW (P.lay.fr d) v) := by
  refine (slot_frame P.lay m d v).sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have e : P.lay.fr d = P.lay.fr 80 + BitVec.ofNat 64 (d - 80) := by
    simp only [Lay.fr]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 80 + (d - 80) = d by omega_using [hd]]
  rw [slotR, e]
  exact Offset.sub_base _ (by omega_using [hd])

theorem extras_wp {σ s : State} (hr : R1 P σ s) (hx : XP P pre L σ) :
    WP isa (.block (copyArg 25 20 ++ copyArg 26 21)) s (R1P P pre L σ) := by
  have hc := hr.1
  have hg := hr.2.1.geo
  have ok := hr.2.1.ok
  simp only [copyArg, ld, st, List.cons_append, List.nil_append]
  refine (stP hc.st hx).wp_arg (j := 25) (by simp) (by decide) fun t1 s1 u1 => ?_
  have c1 : Ctx P.lay P.scr σ t1 := ⟨⟨ok, s1.sp, s1.rd, s1.wr, s1.frame⟩, (u1.other _ (by decide)).trans hc.ebp⟩
  refine c1.wp_st hg (d := 4 * 20) (by decide) fun t2 c2 m2 => ?_
  refine (stP c2.st hx).wp_arg (j := 26) (by simp) (by decide) fun t3 s3 u3 => ?_
  have c3 : Ctx P.lay P.scr σ t3 := ⟨⟨ok, s3.sp, s3.rd, s3.wr, s3.frame⟩, (u3.other _ (by decide)).trans c2.ebp⟩
  refine c3.wp_st hg (d := 4 * 21) (by decide) fun t4 c4 m4 => WP.block_nil ?_
  have sp4 : t4.gpr .esp = s.gpr .esp := by rw [c4.st.sp, hc.st.sp]
  have f4 : Frame [⟨P.lay.fr 80, 8⟩] s.mem t4.mem := by
    rw [m4.mem, u3.mem, m2.mem, u1.mem]
    exact (frame_hi (d := 80) (by decide) _).trans (frame_hi (d := 84) (by decide) _)
  refine ⟨⟨R1.hi hr c4 sp4 f4, hx⟩, ?_, ?_⟩
  · rw [m4.mem, u3.mem, Lay.readW_fr_other _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), m2.mem, u1.mem,
      Mem.readW_writeW_self32, u1.gpr]
    rfl
  · rw [m4.mem, u3.mem, show (4 * 21 : Nat) = 84 from rfl, Mem.readW_writeW_self32, u3.gpr]
    rfl

theorem extras_taint : TaintOk [.esp] (.block (copyArg 25 20 ++ copyArg 26 21)) := ⟨_, by taint_decide⟩

theorem extras_vp :
    VP (fun σ s => R1 P σ s ∧ XP P pre L σ) (.block (copyArg 25 20 ++ copyArg 26 21)) (R1P P pre L) :=
  VP.taint [.esp] extras_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.1.1.st.sp, h₂.1.1.st.sp]) fun _ _ hs => extras_wp hs.1 hs.2

/-! ## The call -/

theorem callWords {σ s : State} (hs : P.lay.St σ s) (hx : XP P pre L σ) :
    Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L = Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L := by
  have fit : (pre.setWidth 64).toNat + 8 * L ≤ 2 ^ 32 := by
    have := hx.ok.fits (preR pre L) (List.mem_append_left _ (by simp))
    simp only at this; omega_using [this]
  have sep : ∀ r ∈ (P.layP pre L).W, (⟨pre.setWidth 64, 8 * L⟩ : Region).Disjoint r := by
    rw [show 8 * L = L * 8 from Nat.mul_comm _ _]
    exact lay_ro_apart hx.ok (R := preR pre L) (by simp)
  rw [Proof.Rsa.wordsAt_frame ((stP hs hx).callEntry_frame (by show (4 : Nat) ≤ 3448; decide)) (by omega_using [fit]) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact sep _ (by simp [Lay.W])),
    Proof.Rsa.wordsAt_frame hs.frame (by omega_using [fit]) sep]

/-- The call's arguments, with `pre`. -/
theorem R1P.privArgsP {σ s : State} (hr : R1P P pre L σ s) :
    PrivArgsP s (P.scr + BitVec.ofNat 32 oEm) P.n P.e P.ct P.p P.q P.dp P.dq P.qinv
      (P.scr + BitVec.ofNat 32 oRsa) pre P.K P.el P.pl P.ql (P.scl - 1024) L := by
  obtain ⟨⟨⟨hc, hi, pa⟩, hx⟩, s80, s84⟩ := hr
  have okP := hx.ok
  have hfit := okP.fit
  simp only [Lay.A, EP.argv, List.length_append, List.length_cons, List.length_nil, frameBytes] at hfit
  have hsp : s.gpr .esp = P.B := hc.st.sp
  have key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.callEntry.mem (P.n.setWidth 64) P.K)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.p.setWidth 64) P.pl)
      (Spec.Rsa.bytesAt s.callEntry.mem (P.q.setWidth 64) P.ql) =
      some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L) := by
    have c4 : (4 : Nat) ≤ P.lay.C := by show (4 : Nat) ≤ 3448; decide
    rw [hc.st.callEntry_ro (R := P.N) c4 (by simp), hc.st.callEntry_ro (R := P.PP) c4 (by simp),
      hc.st.callEntry_ro (R := P.QQ) c4 (by simp), callWords hc.st hx]
    have k := hx.key
    rw [← hi.nB] at k
    exact k
  refine ⟨pa, fun i hi' => ?_, by rw [hsp]; omega_using [hfit], hx.lenEq, key⟩
  have ha : addr (s.gpr .esp) (4 * i) = P.lay.fr (4 * i) := by
    rw [hsp]; exact hi.ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega_using [hi'])
  rcases (by omega_using [hi'] : i < 20 ∨ i = 20 ∨ i = 21) with hlt | rfl | rfl
  · rw [pa.args i hlt]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
        i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 by omega_using [hlt]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> rfl
  · rw [ha]; exact s80
  · rw [ha]; exact s84

/-- `privNameP`: `vg_rsa_private_checked_precomputed` over `c`. -/
def privNameP (c : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ c.suffix

/-- `EM` and the result: the call of `vg_rsa_private_checked_precomputed`. -/
theorem call_vpP (c : CrtImpl) (w : CrtPImpl) :
    VP (R1P P pre L) (.call (privNameP c) (privCodeP c w)) (fun σ s => R2 P σ s ∧ XP P pre L σ) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verifiedP c w
  have hst := Proof.Rsa.X86.PrivChecked.code_stackP c w
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w)
    (privRdP P.n P.e P.ct P.p P.q P.dp P.dq P.qinv pre P.K P.el P.pl P.ql L)
    (privWrP P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
    (fun σ s hr => ?_) (fun σ s hr => ?_)
    (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have pa := R1P.privArgsP hr
    obtain ⟨⟨⟨hc, hi, -⟩, hx⟩, -, -⟩ := hr
    have okP := hx.ok
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have fit := okP.fit
    simp only [Lay.A, EP.argv, List.length_append, List.length_cons, List.length_nil, frameBytes] at fit
    have args0 : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP pre L).fr 0, 88⟩ := by simp
    have hsp := hc.st.sp
    rw [show P.lay.B = P.B from rfl] at hsp
    rw [← hsp] at args0
    rw [← hsp]
    have b88 : 0 + 88 ≤ (P.layP pre L).F + 16 := by show 0 + 88 ≤ frameBytes + 16; decide
    have ro : ∀ R ∈ (P.layP pre L).ro, ∀ {w : Region}, Region.Sub w P.SCR → w.Disjoint R := fun R hR w hw =>
      (okP.rw_ro (w := P.SCR) (r := R) (by simp) hR).sub_left hw
    refine priv_preP pa ?_ ?_ ?_ ?_
    · intro w hw r hr
      have hr' : r ∈ (P.layP pre L).ro := by
        simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simp only [privWrP, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ro r hr' sI
      · exact ro r hr' sS'
      · rw [args0]; exact okP.stk_fr (.inl hr') b88
    · simp only [privWrP, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨dIS, ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact ((okP.stk_fr (R := P.SCR) (.inr (by simp)) b88).symm).sub_left sI
      · rw [args0]; exact ((okP.stk_fr (R := P.SCR) (.inr (by simp)) b88).symm).sub_left sS'
    · intro r hr
      rw [hsp, ← show (P.layP pre L).B = P.B from rfl, okP.low_eq]
      simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with h1 | h2 | h3 | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h1]; exact (okP.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
      · rw [h2]; exact (okP.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
      · have : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP pre L).fr 0, 88⟩ := by simp
        rw [h3, hsp, this]; exact (Lay.fr_low (by omega_arith) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact okP.low_buf (.inl (by simp))
    · intro r hr
      have hg := hi.geo
      simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with h1 | h2 | h3 | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h1]
        show ((P.scr + BitVec.ofNat 32 oEm).setWidth 64).toNat + P.K ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oEm).isLt; omega_arith),
          hg.scr_lt (by decide)]
        unfold oEm; omega_arith
      · rw [h2]
        show ((P.scr + BitVec.ofNat 32 oRsa).setWidth 64).toNat + (P.scl - 1024) * 8 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (P.scr + BitVec.ofNat 32 oRsa).isLt; omega_arith),
          hg.scr_lt (Nat.le_refl _)]
        unfold oRsa; omega_arith
      · rw [h3, hsp]
        show (P.B.setWidth 64).toNat + 88 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_arith)]
        omega_arith
      all_goals exact okP.fits _ (by simp)
  · -- What the callee is given is ours.
    obtain ⟨⟨⟨hc, hi, -⟩, hx⟩, -, -⟩ := hr
    have hs := stP hc.st hx
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have hro : ∀ R ∈ (P.layP pre L).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.inRo hR
    have inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨P.scr.setWidth 64 + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, hs.inRw (by simp), Offset.contains_base _ hon (by omega_arith)⟩
    have hA : Covers [⟨P.B.setWidth 64, 88⟩] s.wr := by
      have := hs.inFr (d := 0) (n := 88) (by simp only [frameBytes]; omega_arith)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWrP P.B (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))
        s.wr :=
      (show Covers [emR P] s.wr by rw [emR, e1]; exact inS (by unfold oEm; omega_arith)).cons
        ((show Covers [scrR P] s.wr by rw [scrR, e2]; exact inS (by unfold oRsa; omega_arith)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    exact (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.CT (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons ((hro (preR pre L) (by simp)).cons Covers.nil))))))))
  · rw [hr.1.1.1.st.sp]
    have : 3448 ≤ P.B.toNat := hr.1.1.2.1.ok.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    show _ ≤ P.B.toNat
    omega_arith
  · have p₁ := R1P.privArgsP h₁
    have p₂ := R1P.privArgsP h₂
    have k₁ := p₁.key
    have k₂ := p₂.key
    have c4 : (4 : Nat) ≤ P.lay.C := by show (4 : Nat) ≤ 3448; decide
    have n₁ : Spec.Rsa.bytesAt s₁.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
      (h₁.1.1.1.st.callEntry_ro (R := P.N) c4 (by simp)).trans h₁.1.1.2.1.nB
    have n₂ : Spec.Rsa.bytesAt s₂.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
      (h₂.1.1.1.st.callEntry_ro (R := P.N) c4 (by simp)).trans h₂.1.1.2.1.nB
    rw [n₁] at k₁
    rw [n₂] at k₂
    have w₁ := preModulus k₁
    have w₂ := preModulus k₂
    rw [← w₂] at w₁
    have hl : P.nB.length = P.K := by rw [← h₁.1.1.2.1.nB, Proof.RsaPkcs1Sig.bytesAt_len]
    rw [hl] at w₁
    refine priv_pubP p₁ p₂ (by rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]) ?_ ?_ ?_ ?_ (Option.some.inj w₁) _ _
    · rw [nB_at h₁.1.1.2.1 h₁.1.1.1.st, nB_at h₂.1.1.2.1 h₂.1.1.1.st]
    · rw [eB_at h₁.1.1.2.1 h₁.1.1.1.st, eB_at h₂.1.1.2.1 h₂.1.1.1.st]
    · rw [h₁.1.1.1.st.sp, h₁.1.1.2.1.ok.low_eq]
      exact h₁.1.1.2.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.1.1.st.sp, h₁.1.1.2.1.ok.low_eq]
      exact h₁.1.1.2.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have pa := R1P.privArgsP hr
    obtain ⟨⟨⟨hc, hi, -⟩, hx⟩, -, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    have hsp := hs.sp
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo hi
    have low : Region.Sub (below (s.gpr .esp) (stackUse (privCodeP c w) + 4)) P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega_arith) ok.BC
    have hc' : Ctx P.lay P.scr σ s' := hc.write fr (fun r hr => by
      simp only [privWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨P.lay.fr 0, 88⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨P.lay.LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
      (cs .ebp (by simp [calleeSaved]))
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_postP pa po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ P.lay.ro) => hs.callEntry_ro (by show 4 ≤ 3448; decide) hR
    rw [ro (R := P.N) (by simp), hi.nB, ro (R := P.E) (by simp), hi.eB, ro (R := P.CT) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    obtain ⟨r0, hb, hl⟩ := em_of this
    refine ⟨⟨hc', hi, fun i hi' => ?_, r0, hl⟩, hx⟩
    have e := hb i hi'
    rw [e1] at e
    refine Eq.trans ?_ e
    simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The body -/

variable (h : OHash)

theorem decStart_append : decStart ++ privArgsP = (decStart ++ privArgs) ++ (copyArg 25 20 ++ copyArg 26 21) := by
  simp only [privArgsP, List.append_assoc]

/-- The body, keeping `XP` until the call. -/
theorem body_vpP (P : EP) (pre : BitVec 32) (L : Nat) (g : OHash) {f : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : CrtImpl) (w : CrtPImpl) :
    VP (Sy (fun σ s => S P σ s ∧ XP P pre L σ)) (decBody f (privNameP c) (privCodeP c w) privArgsP)
      (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (decStart ++ privArgsP)) (.seq (.call (privNameP c) (privCodeP c w))
    (.seq (.block (lenLoad 23)) (byLen (fun d => decTail (ofLen d) f) lens)))) _
  rw [decStart_append]
  refine VP.cont3 (VP.syms ((((pa_vp P).keep (XP P pre L)).block_append extras_vp).seq
      (((call_vpP c w).mono (fun _ _ x => x) fun _ _ x => x.1).seq (len_vp h P hTL)))) (byLen_vp (D := h.H.D)
    (by have := h.D_le; omega_using [this]) (fun _ _ hs => hs.1.2)
    (fun σ s t ⟨⟨⟨hc, hi, he, hr0, hk⟩, dx⟩, sy⟩ fu sy' =>
      ⟨⟨⟨hc.fupd fu, hi, by rw [fu.mem]; exact he, by rw [fu.gpr]; exact hr0, hk⟩, by rw [fu.gpr]; exact dx⟩,
        sy'.trans sy⟩) ?_ h.lens cmpLens_taint)
  show VP _ (decTail (ofLen h.H.D) f) _
  rw [decTail_D (G := ofLen h.H.D) (G' := h.H) rfl f]
  show VP _ (.seq (.block (decChk h.H)) (.ite .b decFail (decMain h.H f))) _
  exact VP.seq ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨r2, _⟩, sy⟩ => ⟨r2, sy⟩) fun _ _ x => x) (VP.ite
    (fun σ s hs => ⟨decide (P.K < 2 * h.H.D + 2), by simp only [eval, hs.1.2.2.2.2.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT hTL fne))

theorem body_noSpP {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2)
    (hf : ∀ q ∈ f.fin, NoSp q.2) (c : CrtImpl) (w : CrtPImpl) :
    NoSp (decBody f (privNameP c) (privCodeP c w) privArgsP) := by
  have hc := Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w
  have hb := byLen_noSp (b := fun d => decTail (ofLen d) f) (ds := lens) fun d hd => tail_noSp _ (lens_certs hd) hi hu hf
  simp only [decBody, Impl.RsaPss.X86.seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_call
    | exact hc | exact hb
    | exact NoSp.of_all (by decide +kernel))

/-! ## The contract -/

/-- The precomputed contract, with both hash functions each one of the
tables `ts`, and `vg_rsa_oaep_decrypt`'s stack. -/
abbrev specP (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "decP_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

end VG.Proof.RsaOaep.X86.Dec
