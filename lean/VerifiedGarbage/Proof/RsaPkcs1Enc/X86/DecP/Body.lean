module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCallP
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Verified
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecBody
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# RSAES-PKCS1-v1_5 decryption on x86, given `pre`: the call and the body

## Code proven on narrower permissions

At every stage of a `VP` (`VP.narrow`); the callee's lemmas are
`PrivCallP.lean`'s.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-! ## Narrowing a `VP` -/

/-- A `VP` proven from the states narrowed to `r` and `w` (each run's, from its entry `σ`) holds
of the states themselves, whose permissions cover those. -/
theorem VP.narrow {F G : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (r w : State → List Region) :
    VP (fun σ s => F (σ.withRegions (r σ) (w σ)) (s.withRegions (r σ) (w σ)) ∧
        Covers (r σ ++ w σ) (s.rd ++ s.wr) ∧ Covers (w σ) s.wr) c
      (fun σ s => G (σ.withRegions (r σ) (w σ)) (s.withRegions (r σ) (w σ))) := by
  have run : ∀ σ s, F (σ.withRegions (r σ) (w σ)) (s.withRegions (r σ) (w σ)) →
      Covers (r σ ++ w σ) (s.rd ++ s.wr) → Covers (w σ) s.wr →
      ∃ t n, Exec isa c (s.withRegions (r σ) (w σ)) t n ∧
        Exec isa c s t (n.withRegions s.rd s.wr) ∧
        G (σ.withRegions (r σ) (w σ)) ((n.withRegions s.rd s.wr).withRegions (r σ) (w σ)) := by
    intro σ s hF hc hw
    obtain ⟨t, n, he, hg⟩ := h.wp _ _ hF
    obtain ⟨he', e⟩ := regionModel.inline (s := s) he hc hw
    refine ⟨t, n, he, he', ?_⟩
    change G _ (State.withRegions (State.withRegions n s.rd s.wr) (r σ) (w σ))
    rw [show State.withRegions (State.withRegions n s.rd s.wr) (r σ) (w σ) = n from e]
    exact hg
  refine ⟨fun σ s ⟨hF, hc, hw⟩ => ?_, ?_⟩
  · obtain ⟨t, n, -, he', hg⟩ := run σ s hF hc hw
    exact ⟨t, _, he', hg⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨F₁, c₁, w₁⟩, ⟨F₂, c₂, w₂⟩⟩ e₁ e₂
    obtain ⟨u₁, n₁, en₁, x₁, g₁⟩ := run σ₁ s₁ F₁ c₁ w₁
    obtain ⟨u₂, n₂, en₂, x₂, g₂⟩ := run σ₂ s₂ F₂ c₂ w₂
    obtain ⟨rfl, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨rfl, rfl⟩ := Exec.det e₂ x₂
    exact ⟨(h.ct _ _ _ _ _ _ ⟨_, _, F₁, F₂⟩ en₁ en₂).1, σ₁, σ₂, g₁, g₂⟩

end VG.Proof.RsaPkcs1Sig.X86

/-!
## RSAES-PKCS1-v1_5 decryption on x86, given `pre`: the body

`vg_rsa_pkcs1_decrypt_precomputed`'s entry has `vg_rsa_pkcs1_decrypt`'s
buffers, `pre` (read) and two more arguments (`EP.layP`, `SP`). The body
copies the call's twenty-two arguments (`privArgsP_vp`), calls
`vg_rsa_private_checked_precomputed` (`call_vpP`), and from there on is
`vg_rsa_pkcs1_decrypt`'s, proven on the states narrowed to its
permissions (`rest_vp`, `VP.narrow`, `bodyP_vp`).
-/


namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)

/-- `pre`. -/
abbrev preR (pre : BitVec 32) (L : Nat) : Region := ⟨pre.setWidth 64, L * 8⟩

namespace EP

variable (P : EP) (pre : BitVec 32) (L : Nat)

/-- The arguments of `vg_rsa_pkcs1_decrypt_precomputed`, in order. -/
abbrev argvP : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.ml, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.d,
    BitVec.ofNat 32 P.dl, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q, BitVec.ofNat 32 P.ql,
    P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl, P.scr,
    BitVec.ofNat 32 P.sl, pre, BitVec.ofNat 32 L]

abbrev roP : List Region := [P.N, P.E, P.D, P.INP, P.PP, P.QQ, P.DP, P.DQ, P.QI, preR pre L]

abbrev layP : Lay where
  B := P.B
  F := frameBytes
  argv := P.argvP pre L
  ro := P.roP pre L
  rw := P.rw
  C := 3448

/-- The permissions `vg_rsa_pkcs1_decrypt`'s proofs are about. -/
abbrev wrB : List Region := P.lay.FR :: P.lay.SAVE :: (P.rw ++ [P.lay.ARGS])

end EP

/-- A state with `vg_rsa_pkcs1_decrypt`'s permissions. -/
abbrev narrowS (P : EP) (s : State) : State := s.withRegions P.ro P.wrB

variable {P : EP} {pre : BitVec 32} {L : Nat}

/-- The state the body starts from. -/
structure InP (P : EP) (pre : BitVec 32) (L : Nat) (σ : State) : Prop where
  ok : (P.layP pre L).Ok σ
  base : In P (narrowS P σ)
  lenEq : L = Spec.Rsa.privatePrecomputedWords P.K P.pl P.ql
  key : Spec.Rsa.privatePrecompute P.nB (pB P σ) (qB P σ) = some (Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L)

/-- A state of the body, up to the call. -/
abbrev SP (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := InP P pre L σ ∧ (P.layP pre L).St σ s

/-- The call's arguments. -/
abbrev outvP (P : EP) (pre : BitVec 32) (L : Nat) : List (BitVec 32) :=
  privArgvP P.out P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.scr pre P.K P.el P.pl P.ql P.sl L

/-- The first `k` of them in the frame. -/
def SlotsP (P : EP) (pre : BitVec 32) (L : Nat) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW ((P.layP pre L).fr (4 * i)) 32 = (outvP P pre L).getD i 0

/-- Before the call. -/
def R1P (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop := SP P pre L σ s ∧ SlotsP P pre L s.mem 22

/-- After the call. -/
def R2W (P : EP) (pre : BitVec 32) (L : Nat) (σ s : State) : Prop :=
  SP P pre L σ s ∧ Priv P σ s.mem (s.gpr .eax)

/-- A buffer only read misses what the body writes. -/
theorem lay_ro_apart {Ly : Lay} {σ : State} (h : Ly.Ok σ) {R : Region} (hR : R ∈ Ly.ro) :
    ∀ r ∈ Ly.W, R.Disjoint r := by
  intro r hr
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.stk R (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (h.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.stk R (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem SP.nB {σ s : State} (hs : SP P pre L σ s) : Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.base.nB

theorem SP.eB {σ s : State} (hs : SP P pre L σ s) : Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.base.eB

/-! ## The call's arguments -/

theorem copySlotP {σ s : State} {i j : Nat} (h : SP P pre L σ s) (hs : SlotsP P pre L s.mem i) (hi : i < 22)
    (hj : j < 25) (hv : (P.argvP pre L).getD j 0 = (outvP P pre L).getD i 0) {is : List Instr}
    {Q : State → Prop} (kk : ∀ t, SP P pre L σ t → SlotsP P pre L t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  refine h.2.wp_arg (j := j) (by simp only [EP.argvP, List.length_cons, List.length_nil]; omega)
    (by decide) fun t1 s1 u1 => ?_
  refine s1.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega)
    fun t2 s2 m2 => kk t2 ⟨h.1, s2⟩ ?_
  intro k hk
  rw [m2.mem]
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, u1.gpr, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega), u1.mem]
    exact hs k hki

theorem privArgsP_eq : privArgsP = copyArg 0 0 ++ copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++ copyArg 9 6 ++ copyArg 4 7 ++ copyArg 11 8 ++ copyArg 12 9 ++ copyArg 13 10 ++ copyArg 14 11 ++ copyArg 15 12 ++ copyArg 16 13 ++ copyArg 17 14 ++ copyArg 18 15 ++ copyArg 19 16 ++ copyArg 20 17 ++ copyArg 21 18 ++ copyArg 22 19 ++ copyArg 23 20 ++ copyArg 24 21 := by decide

theorem privArgsP_wp {σ s : State} (h : SP P pre L σ s) : WP isa (.block privArgsP) s (R1P P pre L σ) := by
  rw [privArgsP_eq]
  simp only [List.append_assoc]
  have h0 := h
  have z0 : SlotsP P pre L s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlotP h0 z0 (by decide) (j := 0) (by decide) rfl fun t1 h1 z1 => ?_
  refine copySlotP h1 z1 (by decide) (j := 4) (by decide) rfl fun t2 h2 z2 => ?_
  refine copySlotP h2 z2 (by decide) (j := 3) (by decide) rfl fun t3 h3 z3 => ?_
  refine copySlotP h3 z3 (by decide) (j := 4) (by decide) rfl fun t4 h4 z4 => ?_
  refine copySlotP h4 z4 (by decide) (j := 5) (by decide) rfl fun t5 h5 z5 => ?_
  refine copySlotP h5 z5 (by decide) (j := 6) (by decide) rfl fun t6 h6 z6 => ?_
  refine copySlotP h6 z6 (by decide) (j := 9) (by decide) rfl fun t7 h7 z7 => ?_
  refine copySlotP h7 z7 (by decide) (j := 4) (by decide) rfl fun t8 h8 z8 => ?_
  refine copySlotP h8 z8 (by decide) (j := 11) (by decide) rfl fun t9 h9 z9 => ?_
  refine copySlotP h9 z9 (by decide) (j := 12) (by decide) rfl fun t10 h10 z10 => ?_
  refine copySlotP h10 z10 (by decide) (j := 13) (by decide) rfl fun t11 h11 z11 => ?_
  refine copySlotP h11 z11 (by decide) (j := 14) (by decide) rfl fun t12 h12 z12 => ?_
  refine copySlotP h12 z12 (by decide) (j := 15) (by decide) rfl fun t13 h13 z13 => ?_
  refine copySlotP h13 z13 (by decide) (j := 16) (by decide) rfl fun t14 h14 z14 => ?_
  refine copySlotP h14 z14 (by decide) (j := 17) (by decide) rfl fun t15 h15 z15 => ?_
  refine copySlotP h15 z15 (by decide) (j := 18) (by decide) rfl fun t16 h16 z16 => ?_
  refine copySlotP h16 z16 (by decide) (j := 19) (by decide) rfl fun t17 h17 z17 => ?_
  refine copySlotP h17 z17 (by decide) (j := 20) (by decide) rfl fun t18 h18 z18 => ?_
  refine copySlotP h18 z18 (by decide) (j := 21) (by decide) rfl fun t19 h19 z19 => ?_
  refine copySlotP h19 z19 (by decide) (j := 22) (by decide) rfl fun t20 h20 z20 => ?_
  refine copySlotP h20 z20 (by decide) (j := 23) (by decide) rfl fun t21 h21 z21 => ?_
  refine copySlotP h21 z21 (by decide) (j := 24) (by decide) rfl fun t22 h22 z22 => ?_
  exact WP.block_nil ⟨h22, z22⟩

theorem privArgsP_taint : TaintOk [.esp] (.block privArgsP) := ⟨_, by taint_decide⟩

theorem privArgsP_vp : VP (SP P pre L) (.block privArgsP) (R1P P pre L) :=
  VP.taint [.esp] privArgsP_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.2.sp, h₂.2.sp]) fun _ _ h => privArgsP_wp h

/-! ## The call -/

theorem InP.fit {σ : State} (h : InP P pre L σ) : P.B.toNat + 224 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, EP.argvP, List.length_cons, List.length_nil, frameBytes] at this
  omega

theorem InP.BC {σ : State} (h : InP P pre L σ) : 3448 ≤ P.B.toNat := h.ok.BC

theorem SP.callN {σ s : State} (hs : SP P pre L σ s) :
    Spec.Rsa.bytesAt s.callEntry.mem (P.n.setWidth 64) P.K = P.nB :=
  (hs.2.callEntry_ro (R := P.N) (by show (4 : Nat) ≤ 3448; decide) (by simp)).trans hs.1.base.nB

theorem SP.callWords {σ s : State} (hs : SP P pre L σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L = Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L := by
  have fit : (pre.setWidth 64).toNat + 8 * L ≤ 2 ^ 32 := by
    have := hs.1.ok.fits (preR pre L) (List.mem_append_left _ (by simp))
    simp only at this; omega
  have sep : ∀ r ∈ (P.layP pre L).W, (⟨pre.setWidth 64, 8 * L⟩ : Region).Disjoint r := by
    rw [show 8 * L = L * 8 from Nat.mul_comm _ _]
    exact lay_ro_apart hs.1.ok (R := preR pre L) (by simp)
  rw [Proof.Rsa.wordsAt_frame (hs.2.callEntry_frame (by show (4 : Nat) ≤ 3448; decide)) (by omega) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact sep _ (by simp [Lay.W])),
    Proof.Rsa.wordsAt_frame hs.2.frame (by omega) sep]

theorem R1P.privArgsP {σ s : State} (h : R1P P pre L σ s) :
    PrivArgsP s P.out P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.scr pre P.K P.el P.pl P.ql P.sl L := by
  obtain ⟨hs, sl⟩ := h
  have ok := hs.1.ok
  have fit := hs.1.fit
  have bc := hs.1.BC
  have hsp : s.gpr .esp = P.B := hs.2.sp
  have base := hs.1.base
  have argsP : ∀ i < 22, s.mem.readW (addr (s.gpr .esp) (4 * i)) 32 = (outvP P pre L).getD i 0 := by
    intro i hi
    have hd : 4 * i < (P.layP pre L).F + 20 + (P.layP pre L).A := by
      simp only [Lay.A, EP.argvP, List.length_cons, List.length_nil, frameBytes]; omega
    rw [hsp, ok.addrB hd]
    exact sl i hi
  have key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K)
      (Spec.Rsa.bytesAt σ.mem (P.p.setWidth 64) P.pl) (Spec.Rsa.bytesAt σ.mem (P.q.setWidth 64) P.ql) =
      some (Spec.Rsa.wordsAt σ.mem (pre.setWidth 64) L) := by
    have k := hs.1.key
    rw [← base.nB] at k
    exact k
  have c4 : (4 : Nat) ≤ (P.layP pre L).C := by show (4 : Nat) ≤ 3448; decide
  rw [← hs.2.callEntry_ro (R := P.N) c4 (by simp), ← hs.2.callEntry_ro (R := P.PP) c4 (by simp),
    ← hs.2.callEntry_ro (R := P.QQ) c4 (by simp), ← hs.callWords] at key
  refine ⟨⟨fun i hi => ?_, ?_, ?_, base.kv, base.el1, base.elK, base.pl1, base.plK, base.ql1, base.qlK, base.slK,
    base.sl32⟩, argsP, ?_, hs.1.lenEq, key⟩
  · rw [argsP i (by omega)]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [hsp]; exact bc
  · rw [hsp]; omega
  · rw [hsp]; omega

/-- `privNameP`: `vg_rsa_private_checked_precomputed` over `c`. -/
def privNameP (c : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ c.suffix

theorem call_vpP (c : CrtImpl) (w : CrtPImpl) :
    VP (R1P P pre L) (.call (privNameP c) (privCodeP c w)) (R2W P pre L) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verifiedP c w
  have hst := Proof.Rsa.X86.PrivChecked.code_stackP c w
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w)
    (privRdP P.n P.e P.inp P.p P.q P.dp P.dq P.qinv pre P.K P.el P.pl P.ql L)
    (privWrP P.B P.out P.scr P.K P.sl) (fun σ s h => ?_) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.2.sp, h₂.1.2.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' h rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have hs := h.1
    have ok := hs.1.ok
    have hp := h.privArgsP
    have fit := hs.1.fit
    have args0 : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP pre L).fr 0, 88⟩ := by simp
    have hsp : s.gpr .esp = P.B := hs.2.sp
    rw [← hsp] at args0
    rw [← hsp]
    refine priv_preP hp ?_ ?_ ?_ ?_
    · intro w hw r hr
      have hr' : r ∈ (P.layP pre L).ro := by
        simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simp only [privWrP, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) hr'
      · exact ok.rw_ro (w := P.SCR) (by simp) hr'
      · rw [args0]; exact ok.stk_fr (.inl hr') (by simp only [frameBytes]; omega)
    · simp only [privWrP, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at ww
      refine ⟨⟨ww.1.2, ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [frameBytes]; omega)).symm
      · rw [args0]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [frameBytes]; omega)).symm
    · intro r hr
      rw [hsp, ← show (P.layP pre L).B = P.B from rfl, ok.low_eq]
      simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [args0]; exact (Lay.fr_low (by omega) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      simp only [privWrP, privRdP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 88 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega)]
        omega
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    have hs := h.1
    have hro : ∀ R ∈ (P.layP pre L).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    have hrw : ∀ R ∈ (P.layP pre L).rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    have hA : Covers [⟨P.B.setWidth 64, 88⟩] s.wr := by
      have := hs.2.inFr (d := 0) (n := 88) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWrP P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons ((hro (preR pre L) (by simp)).cons Covers.nil))))))))
  · rw [show s.gpr .esp = P.B from h.1.2.sp]
    have := h.1.1.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    omega
  · have k₁ := h₁.privArgsP.key
    have k₂ := h₂.privArgsP.key
    rw [h₁.1.callN] at k₁
    rw [h₂.1.callN] at k₂
    have w₁ := preModulus k₁
    have w₂ := preModulus k₂
    rw [← w₂] at w₁
    have hl : P.nB.length = P.K := by rw [← h₁.1.1.base.nB, Proof.RsaPkcs1Sig.bytesAt_len]
    rw [hl] at w₁
    refine priv_pubP (h₁.privArgsP) (h₂.privArgsP) (by rw [h₁.1.2.sp, h₂.1.2.sp]) ?_ ?_ ?_ ?_
      (Option.some.inj w₁) _ _
    · rw [h₁.1.nB, h₂.1.nB]
    · rw [h₁.1.eB, h₂.1.eB]
    · rw [h₁.1.2.sp, h₁.1.1.ok.low_eq]
      exact h₁.1.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.2.sp, h₁.1.1.ok.low_eq]
      exact h₁.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have hh := h
    obtain ⟨hs, -⟩ := h
    have ok := hs.1.ok
    have hsp : s.gpr .esp = P.B := hs.2.sp
    have low : Region.Sub (below (s.gpr .esp) (stackUse (privCodeP c w) + 4))
        (P.layP pre L).LOW := by
      rw [hsp, ← show (P.layP pre L).B = P.B from rfl, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega) ok.BC
    have st : (P.layP pre L).St σ s' := hs.2.write fr (fun r hr => by
      simp only [privWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨(P.layP pre L).FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 88⟩ : Region) = ⟨(P.layP pre L).fr 0, 88⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨(P.layP pre L).LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hs.1, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_postP hh.privArgsP po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ (P.layP pre L).ro) => hs.2.callEntry_ro (by show 4 ≤ 3448; decide) hR
    rw [ro (R := P.N) (by simp), show Spec.Rsa.bytesAt σ.mem P.N.base P.N.len = P.nB from hs.1.base.nB,
      ro (R := P.E) (by simp), show Spec.Rsa.bytesAt σ.mem P.E.base P.E.len = P.eB from hs.1.base.eB,
      ro (R := P.INP) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    exact this

/-! ## The rest, on the narrowed states -/

/-- After the call, `vg_rsa_pkcs1_decrypt`'s state, narrowed. -/
theorem R2W.narrow {σ s : State} (h : R2W P pre L σ s) :
    R2 P (narrowS P σ) (narrowS P s) ∧ Covers (P.ro ++ P.wrB) (s.rd ++ s.wr) ∧ Covers P.wrB s.wr := by
  obtain ⟨⟨hin, st⟩, out⟩ := h
  have ok := hin.ok
  have mW : ∀ r ∈ (P.layP pre L).FR :: (P.layP pre L).SAVE :: (P.layP pre L).rw, r ∈ s.wr := fun r hr => by
    rw [st.wr]; exact ok.wr r hr
  obtain ⟨k, hk, hA⟩ := ok.argsW
  have mA : (⟨(P.layP pre L).fr ((P.layP pre L).F + 20), k⟩ : Region) ∈ s.wr := by rw [st.wr]; exact hA
  have wB : Covers P.wrB s.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [EP.wrB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, mW _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, mW _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨P.OUT, mW _ (by simp), 0, by simp, by simp⟩
    · exact ⟨P.ML, mW _ (by simp), 0, by simp, by simp⟩
    · exact ⟨P.SCR, mW _ (by simp), 0, by simp, by simp⟩
    · exact ⟨_, mA, 0, by simp, Nat.le_trans (by simp [Lay.A, EP.argvP]) hk⟩
  refine ⟨⟨⟨hin.base, ⟨hin.base.ok, st.sp, rfl, rfl, st.frame⟩⟩, out⟩,
    Covers.append_left ?_ wB.right, wB⟩
  exact Covers.left (Covers.of_mem fun r hr => by
    rw [st.rd]
    apply ok.rd
    simp only [EP.ro, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

/-- `vg_rsa_pkcs1_decrypt`'s body after the call. -/
abbrev restCode (v : Backend) : Prog isa :=
  .seq (.block (saveR ++ dZero)) (.seq zeroLoop
    (.seq (.block dCopy) (.seq Impl.Bignum.X86.copyBytes (.seq (hashD v.F) (.seq (kdkMac v.F) (.seq (clLoop v.F)
    (.seq (amLoop v.F) (.seq alPart selPart))))))))

theorem rest_vp (v : Backend) : VP (R2 P) (restCode v) (Fin P) :=
  dZero_vp.seq (zero_vp.seq (dCopy_vp.seq (copy_vp.seq ((hashD_vp v).seq
    ((kdkMac_vp v).seq ((clLoop_vp v).seq ((amLoop_vp v).seq (alPart_vp.seq selPart_vp))))))))

/-- The body: the result, of the states narrowed (`Fin`). -/
theorem bodyP_vp (v : Backend) (c : CrtImpl) (w : CrtPImpl) :
    VP (SP P pre L) (body v.F (privNameP c) (privCodeP c w) privArgsP)
      (fun σ s => Fin P (narrowS P σ) (narrowS P s)) :=
  privArgsP_vp.seq ((call_vpP c w).seq (((rest_vp (P := P) v).narrow (fun _ => P.ro) (fun _ => P.wrB)).mono
    (fun _ _ h => h.narrow) fun _ _ h => h))

theorem bodyP_noSp (v : Backend) (c : CrtImpl) (w : CrtPImpl) :
    NoSp (body v.F (privNameP c) (privCodeP c w) privArgsP) := by
  have h := body_noSp v c
  unfold body at h ⊢
  exact noSp_seq (.of_all (by decide +kernel))
    (noSp_seq (noSp_call (Proof.Rsa.X86.PrivChecked.privateCodeP_noSp c w)) (fun i hi => h i (by
      simp only [instrs, List.mem_append] at hi ⊢; exact .inr (.inr hi))))

end VG.Proof.RsaPkcs1Enc.X86.Dec
