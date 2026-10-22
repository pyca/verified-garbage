module

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecBase

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the private-key operation

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPriv.lean`): the call's twenty
arguments, one word of the frame at a time (`Slots`, `copySlot`,
`privArgs_wp`), and the call of `vg_rsa_private_checked` (`call_vp`,
correct and constant time: its arguments and the public key it reads are
the same in two runs), which writes `EM` or zeros to `out` and returns its
result (`Priv`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  privArgv P.out P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.scr P.K P.el P.pl P.ql P.sl

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- The ciphertext and the private key. -/
abbrev cB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.inp.setWidth 64) P.K
abbrev dB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.d.setWidth 64) P.dl
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.p.setWidth 64) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.q.setWidth 64) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dp.setWidth 64) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.dq.setWidth 64) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.qinv.setWidth 64) P.pl

/-- The private-key operation's result. -/
abbrev privO (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked P.nB P.eB (cB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)

/-- What the call writes to `out` and returns. -/
def Priv (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (P.out.setWidth 64) P.K r (privO P σ)

/-- Before the call. -/
def R1 (P : EP) (σ s : State) : Prop := S P σ s ∧ Slots P s.mem 20

/-- After the call. -/
def R2 (P : EP) (σ s : State) : Prop := S P σ s ∧ Priv P σ s.mem (s.gpr .eax)

theorem S.nB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.n.setWidth 64) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {σ s : State} {i j : Nat} (h : S P σ s) (hs : Slots P s.mem i) (hi : i < 20)
    (hj : j < 23) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, S P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q := by
  refine h.2.wp_arg (j := j) (by simp only [EP.argv, List.length_cons, List.length_nil]; omega) (by decide)
    fun t1 s1 u1 => ?_
  refine s1.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega)
    fun t2 s2 m2 => kk t2 ⟨h.1, s2⟩ ?_
  intro k hk
  rw [m2.mem]
  rcases (by omega : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, u1.gpr, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega) (by omega) (by omega), u1.mem]
    exact hs k hki

theorem privArgs_eq : privArgs = copyArg 0 0 ++ copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++ copyArg 9 6 ++ copyArg 4 7 ++ copyArg 11 8 ++ copyArg 12 9 ++ copyArg 13 10 ++ copyArg 14 11 ++ copyArg 15 12 ++ copyArg 16 13 ++ copyArg 17 14 ++ copyArg 18 15 ++ copyArg 19 16 ++ copyArg 20 17 ++ copyArg 21 18 ++ copyArg 22 19 := by decide

theorem privArgs_wp {σ s : State} (h : S P σ s) : WP isa (.block privArgs) s (R1 P σ) := by
  rw [privArgs_eq]
  simp only [List.append_assoc]
  have h0 := h
  have z0 : Slots P s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h0 z0 (by decide) (j := 0) (by decide) rfl fun t1 h1 z1 => ?_
  refine copySlot h1 z1 (by decide) (j := 4) (by decide) rfl fun t2 h2 z2 => ?_
  refine copySlot h2 z2 (by decide) (j := 3) (by decide) rfl fun t3 h3 z3 => ?_
  refine copySlot h3 z3 (by decide) (j := 4) (by decide) rfl fun t4 h4 z4 => ?_
  refine copySlot h4 z4 (by decide) (j := 5) (by decide) rfl fun t5 h5 z5 => ?_
  refine copySlot h5 z5 (by decide) (j := 6) (by decide) rfl fun t6 h6 z6 => ?_
  refine copySlot h6 z6 (by decide) (j := 9) (by decide) rfl fun t7 h7 z7 => ?_
  refine copySlot h7 z7 (by decide) (j := 4) (by decide) rfl fun t8 h8 z8 => ?_
  refine copySlot h8 z8 (by decide) (j := 11) (by decide) rfl fun t9 h9 z9 => ?_
  refine copySlot h9 z9 (by decide) (j := 12) (by decide) rfl fun t10 h10 z10 => ?_
  refine copySlot h10 z10 (by decide) (j := 13) (by decide) rfl fun t11 h11 z11 => ?_
  refine copySlot h11 z11 (by decide) (j := 14) (by decide) rfl fun t12 h12 z12 => ?_
  refine copySlot h12 z12 (by decide) (j := 15) (by decide) rfl fun t13 h13 z13 => ?_
  refine copySlot h13 z13 (by decide) (j := 16) (by decide) rfl fun t14 h14 z14 => ?_
  refine copySlot h14 z14 (by decide) (j := 17) (by decide) rfl fun t15 h15 z15 => ?_
  refine copySlot h15 z15 (by decide) (j := 18) (by decide) rfl fun t16 h16 z16 => ?_
  refine copySlot h16 z16 (by decide) (j := 19) (by decide) rfl fun t17 h17 z17 => ?_
  refine copySlot h17 z17 (by decide) (j := 20) (by decide) rfl fun t18 h18 z18 => ?_
  refine copySlot h18 z18 (by decide) (j := 21) (by decide) rfl fun t19 h19 z19 => ?_
  refine copySlot h19 z19 (by decide) (j := 22) (by decide) rfl fun t20 h20 z20 => ?_
  exact WP.block_nil ⟨h20, z20⟩

theorem S.sp {σ s : State} (hs : S P σ s) : s.gpr .esp = P.B := hs.2.sp

theorem In.fit {σ : State} (h : In P σ) : P.B.toNat + 216 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at this
  omega

theorem In.BC {σ : State} (h : In P σ) : 3392 ≤ P.B.toNat := h.ok.BC

theorem R1.privArgs {σ s : State} (h : R1 P σ s) :
    PrivArgs s P.out P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.scr P.K P.el P.pl P.ql P.sl := by
  obtain ⟨hs, sl⟩ := h
  have ok := hs.1.ok
  have fit := hs.1.fit
  have bc := hs.1.BC
  have hsp := hs.sp
  refine ⟨fun i hi => ?_, ?_, ?_, hs.1.kv, hs.1.el1, hs.1.elK, hs.1.pl1, hs.1.plK, hs.1.ql1, hs.1.qlK, hs.1.slK,
    hs.1.sl32⟩
  · have hd : 4 * i < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega
    rw [hsp, ok.addrB hd]
    exact sl i hi
  · rw [hsp]; exact bc
  · rw [hsp]; omega

/-- The name of `vg_rsa_private_checked` over `v`. -/
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix

theorem call_vp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (R2 P) := by
  have hv := Proof.Rsa.X86.PrivChecked.code_verified v
  have hst := Proof.Rsa.X86.PrivChecked.code_stack v
  refine VP.call hv.1 hv.2.1 (Proof.Rsa.X86.PrivChecked.privateCode_noSp v)
    (privRd P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.B P.out P.scr P.K P.sl) (fun σ s h => ?_) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.2.sp, h₂.1.2.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' h rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have hs := h.1
    have ok := hs.1.ok
    have hp := h.privArgs
    have fit := hs.1.fit
    have args0 : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
    have aSub : Region.Sub ⟨P.B.setWidth 64, 80⟩ P.lay.FR := by
      rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
    have hsp := hs.sp
    rw [← hsp] at aSub args0
    rw [← hsp]
    refine priv_pre hp ?_ ?_ ?_ ?_
    · intro w hw r hr
      have hr' : r ∈ P.lay.ro := by
        simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) hr'
      · exact ok.rw_ro (w := P.SCR) (by simp) hr'
      · rw [args0]; exact ok.stk_fr (.inl hr') (by simp only [frameBytes]; omega)
    · simp only [privWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at ww
      refine ⟨⟨ww.1.2, ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [frameBytes]; omega)).symm
      · rw [args0]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [frameBytes]; omega)).symm
    · intro r hr
      rw [hsp, ← show P.lay.B = P.B from rfl, ok.low_eq]
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [args0]; exact (Lay.fr_low (by omega) (by show (3392 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega)]
        omega
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    have hs := h.1
    have ok := hs.1.ok
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    have hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.2.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega)
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    have wr : Covers (privWr P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [h.1.sp]
    have := h.1.1.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    omega
  · refine priv_pub (h₁.privArgs) (h₂.privArgs) (by rw [h₁.1.sp, h₂.1.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [h₁.1.nB, h₂.1.nB]
    · rw [h₁.1.eB, h₂.1.eB]
    · rw [h₁.1.sp, ← show P.lay.B = P.B from rfl, h₁.1.1.ok.low_eq]
      exact h₁.1.1.ok.low_buf (R := P.N) (.inl (by simp))
    · rw [h₁.1.sp, ← show P.lay.B = P.B from rfl, h₁.1.1.ok.low_eq]
      exact h₁.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have hh := h
    obtain ⟨hs, -⟩ := h
    have ok := hs.1.ok
    have hsp := hs.sp
    have low : Region.Sub (below (s.gpr .esp) (stackUse (Proof.Rsa.X86.PrivChecked.privCode v) + 4))
        P.lay.LOW := by
      rw [hsp, ← show P.lay.B = P.B from rfl, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega) ok.BC
    have st : P.lay.St σ s' := hs.2.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega)
      · exact ⟨P.lay.LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hs.1, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post hh.privArgs po
    rw [m₂, g₂ .eax (by decide)] at this
    have ro := fun {R : Region} (hR : R ∈ P.lay.ro) => hs.2.callEntry_ro (by show 4 ≤ 3392; decide) hR
    rw [ro (R := P.N) (by simp), hs.1.nB, ro (R := P.E) (by simp), hs.1.eB, ro (R := P.INP) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86.Dec
