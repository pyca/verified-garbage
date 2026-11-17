module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select

/-! ### `RsaPkcs1Enc.X86.DecSel`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecValid`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecScan`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecAl`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecIrprf`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecPrf`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecKdk`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecHash`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecCalls`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecD`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.DecPriv`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the private-key operation

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPrf.lean`): the call's twenty
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
  refine h.2.wp_arg (j := j) (by simp only [EP.argv, List.length_cons, List.length_nil]; omega_using [hj]) (by decide)
    fun t1 s1 u1 => ?_
  refine s1.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega_using [hi])
    fun t2 s2 m2 => kk t2 ⟨h.1, s2⟩ ?_
  intro k hk
  rw [m2.mem]
  rcases (by omega_using [hk] : k = i ∨ k < i) with rfl | hki
  · rw [Mem.readW_writeW_self32, u1.gpr, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_using [hki]) (by omega_using [hi, hk]) (by omega_using [hi]), u1.mem]
    exact hs k hki

theorem privArgs_eq : privArgs = copyArg 0 0 ++ copyArg 4 1 ++ copyArg 3 2 ++ copyArg 4 3 ++ copyArg 5 4 ++ copyArg 6 5 ++ copyArg 9 6 ++ copyArg 4 7 ++ copyArg 11 8 ++ copyArg 12 9 ++ copyArg 13 10 ++ copyArg 14 11 ++ copyArg 15 12 ++ copyArg 16 13 ++ copyArg 17 14 ++ copyArg 18 15 ++ copyArg 19 16 ++ copyArg 20 17 ++ copyArg 21 18 ++ copyArg 22 19 := by decide

theorem privArgs_wp {σ s : State} (h : S P σ s) : WP isa (.block privArgs) s (R1 P σ) := by
  rw [privArgs_eq]
  simp only [List.append_assoc]
  have h0 := h
  obtain z0 : Slots P s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
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
  omega_using [this]

theorem In.BC {σ : State} (h : In P σ) : 3448 ≤ P.B.toNat := h.ok.BC

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
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes]; omega_using [hi]
    rw [hsp, ok.addrB hd]
    exact sl i hi
  · rw [hsp]; exact bc
  · rw [hsp]; omega_using [fit]

/-- The name of `vg_rsa_private_checked` over `v`. -/
def privName (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix

theorem call_vp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (R1 P) (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (R2 P) := by
  obtain hv := Proof.Rsa.X86.PrivChecked.code_verified v
  obtain hst := Proof.Rsa.X86.PrivChecked.code_stack v
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
    obtain args0 : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
    obtain aSub : Region.Sub ⟨P.B.setWidth 64, 80⟩ P.lay.FR := by
      rw [args0]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_using [])
    have hsp := hs.sp
    rw [← hsp] at aSub args0
    rw [← hsp]
    refine priv_pre hp ?_ ?_ ?_ ?_
    · intro w hw r hr
      obtain hr' : r ∈ P.lay.ro := by
        simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) hr'
      · exact ok.rw_ro (w := P.SCR) (by simp) hr'
      · rw [args0]; exact ok.stk_fr (.inl hr') (by simp only [frameBytes]; omega_using [])
    · simp only [privWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at ww
      refine ⟨⟨ww.1.2, ?_⟩, ?_, fun _ h => h.elim⟩
      · rw [args0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [frameBytes]; omega_using [])).symm
      · rw [args0]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [frameBytes]; omega_using [])).symm
    · intro r hr
      rw [hsp, ← show P.lay.B = P.B from rfl, ok.low_eq]
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [args0]; exact (Lay.fr_low (by omega_using []) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).symm
      all_goals exact ok.low_buf (.inl (by simp))
    · intro r hr
      simp only [privWr, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [hsp]
        show (P.B.setWidth 64).toNat + 80 ≤ 2 ^ 32
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := P.B.isLt; omega_using [])]
        omega_using [fit]
      all_goals exact ok.fits _ (by simp)
  · -- What the callee is given is ours.
    have hs := h.1
    have ok := hs.1.ok
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    obtain hA : Covers [⟨P.B.setWidth 64, 80⟩] s.wr := by
      have := hs.2.inFr (d := 0) (n := 80) (by simp only [frameBytes]; omega_using [])
      simp only [Lay.fr, BitVec.add_zero] at this
      exact Covers.one this
    obtain wr : Covers (privWr P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    refine ⟨Covers.append_left ?_ wr.right, wr⟩
    refine (hro P.N (by simp)).cons ((hro P.E (by simp)).cons ((hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons
      ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons ((hro P.DQ (by simp)).cons
      ((hro P.QI (by simp)).cons Covers.nil)))))))
  · rw [h.1.sp]
    have := h.1.1.BC
    simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
    omega_using [hst, this]
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
    obtain low : Region.Sub (below (s.gpr .esp) (stackUse (Proof.Rsa.X86.PrivChecked.privCode v) + 4))
        P.lay.LOW := by
      rw [hsp, ← show P.lay.B = P.B from rfl, ← ok.low_eq]
      simp only [Proof.Rsa.X86.PrivChecked.stackBytes] at hst
      exact below_sub (by simp only; omega_using [hst]) ok.BC
    obtain st : P.lay.St σ s' := hs.2.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        have : (⟨P.B.setWidth 64, 80⟩ : Region) = ⟨P.lay.fr 0, 80⟩ := by simp
        rw [this]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_using [])
      · exact ⟨P.lay.LOW, by simp, low⟩) rd wr (cs .esp (by simp [calleeSaved]))
    refine ⟨⟨hs.1, st⟩, ?_⟩
    obtain ⟨s₂, m₂, g₂, po⟩ := po
    have := priv_post hh.privArgs po
    rw [m₂, g₂ .eax (by decide)] at this
    obtain ro := fun {R : Region} (hR : R ∈ P.lay.ro) => hs.2.callEntry_ro (by show 4 ≤ 3448; decide) hR
    rw [ro (R := P.N) (by simp), hs.1.nB, ro (R := P.E) (by simp), hs.1.eB, ro (R := P.INP) (by simp),
      ro (R := P.PP) (by simp), ro (R := P.QQ) (by simp), ro (R := P.DP) (by simp), ro (R := P.DQ) (by simp),
      ro (R := P.QI) (by simp)] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: `D = I2OSP(d, k)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPrf.lean`): from here on the call's
result stays in `out` and in its slot (`Base`), as long as memory changes
only in `scratch`, the frame's other words and the stack below
(`Base.frame`). `D`, `k` bytes in `scratch`: zeros (`dZero_vp`,
`zero_vp`), then `d` copied to its end (`dCopy_vp`, `copy_vp`): `d` after
`k - d_len` zeros (`Dfull`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86 VG.WriteBytes
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_addS wp_subS)

variable {P : EP}

/-- The call's result, in `out` and in its slot. -/
def Base (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ rc, Priv P σ s.mem rc ∧ s.mem.readW (P.lay.fr oR) 32 = rc

/-- What the frame's slots and the stack below may change. -/
def Safe (P : EP) (r : Region) : Prop := P.OUT.Disjoint r ∧ Region.Disjoint ⟨P.lay.fr oR, 4⟩ r

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.writtenOutcome m a K r o) :
    Spec.Rsa.writtenOutcome m' a K r o := by
  cases o with
  | ok y => exact ⟨h.1, hb.trans h.2⟩
  | invalid => exact ⟨h.1, hb.trans h.2⟩
  | fault => exact ⟨h.1, hb.trans h.2⟩

theorem Base.frame {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Safe P r) : Base P σ t := by
  obtain ⟨hS, rc, pr, sl⟩ := h
  have hK := hS.1.k1024
  refine ⟨⟨hS.1, st⟩, rc, writtenOutcome_congr (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hs r hr).1)
    (by omega_using [hK])) pr, ?_⟩
  rw [hf.readW (r := ⟨P.lay.fr oR, 4⟩) (Region.contains_self _ _) (fun r hr => (hs r hr).2) (by decide)]
  exact sl

/-! ## Safe regions -/

namespace In

variable {σ : State} (h : In P σ)
include h

theorem safe_sc {o n : Nat} (hn : o + n ≤ 8448) : Safe P (sc P o n) :=
  ⟨(h.sc_out hn).symm, h.fr_sc (by simp only [oR, frameBytes]; omega_using []) hn⟩

theorem safe_low : Safe P P.lay.LOW :=
  ⟨(h.ok.low_buf (R := P.OUT) (.inr (by simp))).symm, Lay.fr_low (by simp only [oR]; omega_using [])
    (by show (3448 : Nat) ≤ 2 ^ 32; decide)⟩

theorem safe_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d) :
    Safe P ⟨P.lay.fr d, n⟩ :=
  ⟨(h.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + n ≤ frameBytes + 16; omega_using [hd])).symm,
    Lay.fr_sep (by omega_using [ho]) (by simp only [oR]; omega_using []) (by simp only [frameBytes] at hd; omega_using [hd])⟩

end In

/-! ## The stages -/

/-- `D = I2OSP(d, k)`: `d` after zeros. -/
abbrev Dfull (P : EP) (σ : State) : List Byte := List.replicate (P.K - P.dl) 0 ++ dB P σ

/-- Before the zeros of `D`. -/
def D1 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sD ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

/-- `D` zeros. -/
def D2 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = List.replicate P.K 0

/-- Before the copy of `d`. -/
def D3 (P : EP) (σ s : State) : Prop :=
  D2 P σ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl)) ∧ s.gpr .esi = P.d ∧
    s.gpr .ecx = BitVec.ofNat 32 P.dl

/-- `D` built. -/
def D4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = Dfull P σ

theorem dZero_wp {σ s : State} (h : R2 P σ s) : WP isa (.block (saveR ++ dZero)) s (D1 P σ) := by
  obtain ⟨hs, pr⟩ := h
  have hK := hs.1.k1024
  simp only [saveR, dZero, scr, movI, List.cons_append, List.nil_append]
  refine hs.2.wp_strFr (d := oR) (by simp only [oR, frameBytes]; omega_using []) fun t1 s1 m1 => ?_
  refine s1.wp_arg (j := 21) (r := .esi) (by simp) (by decide) fun t2 s2 u2 => ?_
  refine wp_addi fun t3 u3 => ?_
  obtain s3 := s2.upd u3 (by decide)
  refine s3.wp_arg (j := 4) (r := .ecx) (by simp) (by decide) fun t4 s4 u4 => ?_
  refine wp_movi fun t5 u5 => WP.block_nil ?_
  obtain s4' := s4.upd u5 (by decide)
  obtain mm : t5.mem = s.mem.writeW (P.lay.fr oR) (s.gpr .eax) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, m1.mem]
  refine ⟨⟨⟨hs.1, s4'⟩, s.gpr .eax, ?_, ?_⟩, ?_, ?_, u5.gpr⟩
  · rw [Priv, mm]
    refine writtenOutcome_congr (Proof.RsaPkcs1Sig.bytesAt_frame
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => ?_)
      (by omega_using [hK])) pr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oR, frameBytes]; omega_using [])).symm
  · rw [mm, Mem.readW_writeW_self32]
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr]; rfl

theorem zero_wp {σ s : State} (h : D1 P σ s) : WP isa zeroLoop s (D2 P σ) := by
  obtain ⟨hb, esi, ecx, eax⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  obtain hsD : (P.scr + BitVec.ofNat 32 sD).setWidth 64 = P.scr.setWidth 64 + BitVec.ofNat 64 sD :=
    hs.1.scrA (by decide)
  have fit := hs.1.scr_fit
  have sl8 := hs.1.sl8
  refine WP.mono (zero_ok (p := P.scr + BitVec.ofNat 32 sD) (n := P.K) (by have := hs.1.k64; omega_using [this]) (by omega_using [hK])
    (by rw [hs.1.scr_toNat (by decide)]; simp only [sD]; omega_using [hK, fit, sl8]) esi ecx eax
    (by rw [hsD]; exact St.sc_w hs (by simp only [sD]; omega_using [hK]))) fun t ht => ?_
  obtain fr : Frame [sc P sD P.K] s.mem t.mem := by
    rw [ht.mem, hsD]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD) (List.replicate P.K 0)
    simpa using this
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.SCR, by simp, hs.1.sc_sub (by simp only [sD]; omega_using [hK])⟩) ht.rd ht.wr
    (ht.other _ (by decide) (by decide))
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega_using [hK])
  · rw [ht.mem, hsD]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD)
      (List.replicate P.K 0) (by simp; omega_using [hK])
    simpa using this

theorem dCopy_wp {σ s : State} (h : D2 P σ s) : WP isa (.block dCopy) s (D3 P σ) := by
  have hs := h.1.1
  have hdl := hs.1.dlK
  have hK := hs.1.k1024
  simp only [dCopy, scr, List.cons_append, List.nil_append]
  refine hs.2.wp_arg (j := 21) (r := .ebx) (by simp) (by decide) fun t1 s1 u1 => ?_
  refine wp_addi fun t2 u2 => ?_
  obtain s2 := s1.upd u2 (by decide)
  refine wp_addS (s2.readArg (j := 4) (by simp)) fun t3 u3 _ => ?_
  obtain s3 := s2.upd u3 (by decide)
  refine wp_subS (s3.readArg (j := 8) (by simp)) fun t4 u4 _ => ?_
  obtain s4 := s3.upd u4 (by decide)
  refine s4.wp_arg (j := 7) (r := .esi) (by simp) (by decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 8) (r := .ecx) (by simp) (by decide) fun t6 s6 u6 => WP.block_nil ?_
  obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨⟨⟨hs.1, s6⟩, ?_⟩, by rw [mm]; exact h.2⟩, ?_, ?_, ?_⟩
  · obtain ⟨rc, pr, sl⟩ := h.1.2
    exact ⟨rc, by rw [Priv, mm]; exact pr, by rw [mm]; exact sl⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr]
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    rw [show BitVec.ofNat 32 P.K = BitVec.ofNat 32 (P.K - P.dl) + BitVec.ofNat 32 P.dl by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hdl], ← BitVec.add_assoc, BitVec.add_sub_cancel,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem copy_wp {σ s : State} (h : D3 P σ s) : WP isa Impl.Bignum.X86.copyBytes s (D4 P σ) := by
  obtain ⟨⟨hb, hz⟩, ebx, esi, ecx⟩ := h
  have hs := hb.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have hdl := hs.1.dlK
  have hfd := ok.fits P.D (by simp)
  have fit := hs.1.scr_fit
  have sl8 := hs.1.sl8
  simp only [BitVec.toNat_setWidth] at hfd
  rw [Nat.mod_eq_of_lt (by have := P.d.isLt; omega_using [])] at hfd
  have hdst : (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))).setWidth 64 =
      P.scr.setWidth 64 + BitVec.ofNat 64 (sD + (P.K - P.dl)) := hs.1.scrA (by simp only [sD]; omega_using [hK])
  have ctx := Proof.Bignum.X86.copyCtx_of_regions s P.d (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))) (n := P.dl)
    (by omega_using [hK, hdl]) hfd (by rw [hs.1.scr_toNat (by simp only [sD]; omega_using [hK])]; simp only [sD]; omega_using [hK, hdl, fit, sl8])
    ⟨P.D, hs.2.inRo (by simp), Region.contains_self _ _⟩
    (by simp only [Proof.Bignum.X86.byteAddr]; rw [hdst]; exact St.sc_w hs (by simp only [sD]; omega_using [hK, hdl]))
    (by simp only [Proof.Bignum.X86.byteAddr]; rw [hdst]
        exact (hs.1.sc_ro (by simp only [sD]; omega_using [hK, hdl]) (R := P.D) (by simp)).symm)
  refine WP.mono (Proof.Bignum.X86.copyBytes_ok s ctx (by have := hs.1.dl1; omega_using [this]) esi ebx ecx) fun t ht => ?_
  have fr := ht.frame (by rw [hs.1.scr_toNat (by simp only [sD]; omega_using [hK])]; simp only [sD]; omega_using [hK, hdl, fit, sl8])
  simp only [Proof.Bignum.X86.byteAddr] at fr
  rw [hdst] at fr
  have hsub : Region.Sub (sc P (sD + (P.K - P.dl)) P.dl) P.SCR := hs.1.sc_sub (by simp only [sD]; omega_using [hK, hdl])
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hsub⟩) ht.rest.2.1 ht.rest.2.2
    (ht.rest.1 .esp (by decide))
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega_using [hK, hdl])
  · have hl : (Dfull P σ).length = P.K := by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega_using [hdl]
    show Spec.Rsa.bytesAt t.mem (P.scr.setWidth 64 + BitVec.ofNat 64 sD) P.K = Dfull P σ
    have e := Proof.RsaPkcs1Sig.bytesAt_eq (m := t.mem) (p := P.scr.setWidth 64 + BitVec.ofNat 64 sD)
      (xs := Dfull P σ) fun i hi => ?_
    · rw [hl] at e; exact e
    rw [hl] at hi
    have scrN := hs.1.scr_toNat (o := sD + i) (by simp only [sD]; omega_using [hK, hi])
    rw [Offset.add_ofNat_add_ofNat]
    have bA : ∀ j < P.dl, Proof.Bignum.X86.byteAddr (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl)) + BitVec.ofNat 32 j) =
        P.scr.setWidth 64 + BitVec.ofNat 64 (sD + (P.K - P.dl) + j) := by
      intro j hj
      simp only [Proof.Bignum.X86.byteAddr]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sD]; omega_using [hK, hdl, hj])]
    rcases (by omega_using [] : i < P.K - P.dl ∨ P.K - P.dl ≤ i) with hi' | hi'
    · -- One of the zeros.
      have o := ht.outside (P.scr.setWidth 64 + BitVec.ofNat 64 (sD + i)) fun j hj he => by
        rw [bA j hj] at he
        exact Offset.add_ofNat_ne _ (by simp only [sD]; omega_using [scrN]) (by simp only [sD]; omega_using [hK, hdl, hj]) (by omega_using [hi']) he
      have z := congrArg (fun l => l.getD i 0) hz
      simp only at z
      rw [Proof.RsaPkcs1Sig.bytesAt_getD (by omega_using [hi]), Offset.add_ofNat_add_ofNat] at z
      rw [o, z, Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp; omega_using [hi'])]
      simp [List.getD_eq_getElem?_getD, hi', show i < P.K by omega_using [hi]]
    · -- A byte of `d`.
      obtain ⟨j, rfl⟩ : ∃ j, i = P.K - P.dl + j := ⟨i - (P.K - P.dl), by omega_using [hi']⟩
      have hj : j < P.dl := by omega_using [hi]
      have c := ht.copied j hj
      rw [bA j hj] at c
      rw [show sD + (P.K - P.dl + j) = sD + (P.K - P.dl) + j by omega_using [], c,
        Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp), List.length_replicate, Nat.add_sub_cancel_left,
        Proof.RsaPkcs1Sig.bytesAt_getD hj]
      have ro := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.D) (by simp))
      simp only at ro
      rw [Proof.RsaPkcs1Sig.bytesAt_getD hj, Proof.RsaPkcs1Sig.bytesAt_getD hj] at ro
      simp only [Proof.Bignum.X86.byteAddr]
      rw [show (P.d + BitVec.ofNat 32 j).setWidth 64 = P.d.setWidth 64 + BitVec.ofNat 64 j from addr_eq (by omega_using [hfd, hi])]
      exact ro

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end

/-! ### `RsaPkcs1Sig.X86.HashVp`, which only this module used -/

section

/-!
# The x86 RSA padding functions: their calls of SHA-256 and HMAC-SHA-256

SHA-256's streaming `init`, `update` and `finalize` and HMAC-SHA-256's
`init` and `finalize`, made with one backend `v` (`Backend.F`), each called
in a frame of its arguments (`Proof/Pbkdf2/Stream/X86/Hash.lean`,
`Proof/Pbkdf2/Whole/X86/Calls.lean`), as a stage `VP` of a function: from
states whose arguments each stage fixes, with the same `esp` in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs UpdArgs FinArgs After init_frame upd_frame fin_frame init_rel
  upd_rel fin_rel upd6 fin5)
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs hi_frame hf_frame hi_rel hf_rel hi5 hf6 sha256OKF)

/-- SHA-256's streaming functions with the backend `v`, verified. -/
abbrev hk (v : Backend) : Proof.Pbkdf2.Stream.X86.HashOK v.F.H := (sha256OKF v).hH

variable {F G : State → State → Prop} (v : Backend) {sp : BitVec 32}

namespace VP

/-- SHA-256's `init` of the state at `st` (in `edi`). -/
theorem shaInit {st : BitVec 32} (hA : ∀ σ s, F σ s → InitArgs (H := v.F.H) s .edi st ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩] s' →
      Spec.Sha256.Repr s'.mem (st.setWidth 64) [] → G σ s') :
    VP F (.frame (.push [.edi]) (.call v.F.H.initN v.F.H.initC) (.pop .eax 1)) G :=
  of_ct (fun _ _ => init_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => init_frame (hk v) (hA σ s h).1 (hG σ s h)

/-- SHA-256's `update` of the state at `st` (in `edi`), at the count `c`
(in `esi`), with `len` bytes at `d` and the working space at `sc`. -/
theorem shaUpd {st d sc c : BitVec 32} {len : Nat}
    (hA : ∀ σ s, F σ s → UpdArgs (hk v) s .esi .edi st d sc c len ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩, ⟨sc.setWidth 64, 160⟩] s' →
      (∀ m, Spec.Sha256.Repr s.mem (st.setWidth 64) m → (0 : BitVec 32) ++ c = BitVec.ofNat 64 m.length →
        Spec.Sha256.Repr s'.mem (st.setWidth 64) (m ++ Spec.Sha256.bytesAt s.mem (d.setWidth 64) len)) → G σ s') :
    VP F (.frame (.push (upd6 .esi .edi)) (.call v.F.H.updN v.F.H.updC) (.pop .eax 6)) G :=
  of_ct (fun _ _ => upd_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => upd_frame (hk v) (hA σ s h).1 (hG σ s h)

/-- SHA-256's `finalize` of the state at `st` (in `edi`), at the count
`hi ++ lo`, to `o`, with the working space at `sc`. -/
theorem shaFin {st o sc lo hi : BitVec 32}
    (hA : ∀ σ s, F σ s → FinArgs (hk v) s .edi st o sc lo hi ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s', After s [⟨st.setWidth 64, 96⟩, ⟨o.setWidth 64, 32⟩, ⟨sc.setWidth 64, 160⟩] s' →
      (∀ m, Spec.Sha256.Repr s.mem (st.setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt s'.mem (o.setWidth 64) 32 = Spec.Sha256.hash m) → G σ s') :
    VP F (.frame (.push (fin5 .edi)) (.call v.F.H.finN v.F.H.finC) (.pop .eax 5)) G :=
  of_ct (fun _ _ => fin_rel (hk v) (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => fin_frame (hk v) (hA σ s h).1 fun s' ha hp => hG σ s h s' ha fun m hr hl hc => by
      have := hp m hr hl hc
      rwa [List.take_of_length_le (by simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range]; exact Nat.le_refl _)] at this

/-- HMAC's `init` of the states at `inn` and `ou` with `kl` bytes of key at
`k`, and the working space at `sc`. -/
theorem macInit {inn ou k sc : BitVec 32} {kl : Nat}
    (hA : ∀ σ s, F σ s → HiArgs (hk v).SH 104 s inn ou k sc kl ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s',
      Proof.Pbkdf2.Whole.X86.After s [⟨inn.setWidth 64, 96⟩, ⟨ou.setWidth 64, 96⟩, ⟨sc.setWidth 64, 832⟩] s' →
      Spec.Sha256.Repr s'.mem (inn.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt s.mem (k.setWidth 64) kl)) Spec.Hmac.ipad) →
      Spec.Sha256.Repr s'.mem (ou.setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Sha256.bytesAt s.mem (k.setWidth 64) kl)) Spec.Hmac.opad) → G σ s') :
    VP F (.frame (.push hi5) (.call v.F.hiN v.F.hiC) (.pop .eax 5)) G :=
  of_ct (fun _ _ => hi_rel (sha256OKF v).hi (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => hi_frame (sha256OKF v).hi (sha256OKF v).hiSp (sha256OKF v).hiSU (hA σ s h).1 (hG σ s h)

/-- HMAC's `finalize` of the states at `inn` and `ou`, at the count
`hi ++ lo`, to `o`, with the working space at `sc`. -/
theorem macFin {inn ou lo hi o sc : BitVec 32}
    (hA : ∀ σ s, F σ s → HfArgs (hk v).SH 104 s inn ou lo hi o sc ∧ s.gpr .esp = sp)
    (hG : ∀ σ s, F σ s → ∀ s',
      Proof.Pbkdf2.Whole.X86.After s [⟨inn.setWidth 64, 96⟩, ⟨o.setWidth 64, 32⟩, ⟨sc.setWidth 64, 832⟩] s' →
      (∀ k0 text, k0.length = 64 → k0.length + text.length < 2 ^ 64 →
        Spec.Sha256.Repr s.mem (inn.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text) →
        hi ++ lo = BitVec.ofNat 64 (64 + text.length) →
        Spec.Sha256.Repr s.mem (ou.setWidth 64) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) →
        Spec.Sha256.bytesAt s'.mem (o.setWidth 64) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text) → G σ s') :
    VP F (.frame (.push hf6) (.call v.F.hfN v.F.hfC) (.pop .eax 6)) G :=
  of_ct (fun _ _ => hf_rel (sha256OKF v).hf (sp := sp) fun _ _ h =>
      ⟨(hA _ _ h.1).1, (hA _ _ h.2).1, (hA _ _ h.1).2, (hA _ _ h.2).2⟩)
    fun σ s h => hf_frame (S := (hk v).SH) (Wf := 104) Hmac.Generic.Common.sha256_repr (by show 96 ≤ 2 ^ 64; decide) (sha256OKF v).hf (sha256OKF v).hfSp
      (sha256OKF v).hfSU (hA σ s h).1 (hG σ s h)

end VP

end VG.Proof.RsaPkcs1Sig.X86

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: the calls of SHA-256 and HMAC

The parts of `scratch` the calls use, by their pointers (`sr P o n`): apart
from each other, the stack below the frame and the buffers we only read.
A call changes memory only there, which keeps the private-key operation's
result (`Base.call`). And the arguments of each call (`initA`, `updA`,
`finA`, `hiA`, `hfA`), with the states at `scratch + sSt` (and the outer
state at `scratch + sOuter`) and the working space at `scratch + sW`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs UpdArgs FinArgs)
open VG.Proof.Pbkdf2.Whole.X86 (HiArgs HfArgs)

variable {P : EP}

/-- The `n` bytes at `scratch + o`, by the pointer the code computes. -/
abbrev sr (P : EP) (o n : Nat) : Region := ⟨(P.scr + BitVec.ofNat 32 o).setWidth 64, n⟩

namespace In

variable {σ : State} (h : In P σ)
include h

theorem sr_eq {o n : Nat} (ho : o < 8448) : sr P o n = sc P o n := by
  simp only [sr, sc]; rw [h.scrA ho]

theorem sr_fit {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) :
    (P.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [h.scr_toNat ho]; have := h.scr_fit; have := h.sl8; omega_arith

theorem sr_sep {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (ho : o < 8448) (ho' : o' < 8448)
    (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) : (sr P o n).Disjoint (sr P o' n') := by
  rw [h.sr_eq ho, h.sr_eq ho']; exact sc_sep hs h₁ h₂

theorem sr_sub {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) : Region.Sub (sr P o n) P.SCR := by
  rw [h.sr_eq ho]; exact h.sc_sub hn

theorem low_of {k : Nat} (hk : k ≤ 3448) : Region.Sub (below P.B k) P.lay.LOW := by
  rw [← h.ok.low_eq]; exact below_sub hk h.ok.BC

theorem below_sr {k o n : Nat} (hk : k ≤ 3448) (ho : o < 8448) (hn : o + n ≤ 8448) :
    (below P.B k).Disjoint (sr P o n) := by
  rw [h.sr_eq ho]; exact (h.low_sc hn).sub_left (h.low_of hk)

theorem below_ro {k : Nat} (hk : k ≤ 3448) {R : Region} (hR : R ∈ P.ro) : (below P.B k).Disjoint R :=
  (h.ok.low_buf (.inl hR)).sub_left (h.low_of hk)

theorem sr_ro {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) {R : Region} (hR : R ∈ P.ro) :
    (sr P o n).Disjoint R := by
  rw [h.sr_eq ho]; exact h.sc_ro hn hR

theorem sr_safe {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) : Safe P (sr P o n) := by
  rw [h.sr_eq ho]; exact h.safe_sc hn

theorem below_safe {k : Nat} (hk : k ≤ 3448) : Safe P (below P.B k) :=
  ⟨h.safe_low.1.sub_right (h.low_of hk), h.safe_low.2.sub_right (h.low_of hk)⟩

theorem sp_toNat : 3448 ≤ P.B.toNat := h.ok.BC

end In

theorem St.cov_sr {σ s : State} (hs : S P σ s) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) :
    Covers [sr P o n] s.wr := by
  rw [hs.1.sr_eq ho]; exact Covers.one (St.sc_w hs hn)

theorem St.cov_ro {σ s : State} (hs : S P σ s) {R : Region} (hR : R ∈ P.ro) : Covers [R] (s.rd ++ s.wr) :=
  Covers.one (a := R.base) (n := R.len) ⟨R, hs.2.inRo hR, Region.contains_self _ _⟩

/-- A call writes only parts of `scratch` and the stack below the frame. -/
theorem Base.call {σ s t : State} (h : Base P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hws : ∀ r ∈ ws, ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) : Base P σ t := by
  have hs := h.1
  rw [hs.2.sp] at hf
  obtain hsub : ∀ r ∈ ws ++ [below P.B k], ∃ R ∈ P.lay.W, Region.Sub r R := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr
      exact ⟨P.SCR, by simp, hs.1.sr_sub ho hn⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.lay.LOW, by simp, hs.1.low_of hk⟩
  refine h.frame (hs.2.write hf hsub rd wr sp) hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr; exact hs.1.sr_safe ho hn
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.below_safe hk

/-- Bytes of `scratch` the call does not write. -/
theorem keep_sr {σ s t : State} (hs : S P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448)
    (hd : ∀ r ∈ ws, (sr P o n).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sr P o n).base n = Spec.Rsa.bytesAt s.mem (sr P o n).base n := by
  rw [hs.2.sp] at hf
  refine Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.below_sr hk ho hn).symm

/-- A SHA-256 state kept while memory changes elsewhere. -/
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) {msg : List Byte} (h : Spec.Sha256.Repr m p msg) :
    Spec.Sha256.Repr m' p msg :=
  Proof.Hmac.Generic.Common.sha256_repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, 96⟩) hd (by show (96 : Nat) ≤ 2 ^ 64; decide) hi) h

/-- A SHA-256 state in `scratch` through a call that does not write it. -/
theorem repr_keep_sr {σ s t : State} (hs : S P σ s) {ws : List Region} {k : Nat} (hk : k ≤ 3448)
    (hf : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem) {o : Nat} (ho : o + 96 ≤ 8448)
    (hd : ∀ r ∈ ws, (sr P o 96).Disjoint r) {msg : List Byte}
    (h : Spec.Sha256.Repr s.mem (sr P o 96).base msg) : Spec.Sha256.Repr t.mem (sr P o 96).base msg := by
  rw [hs.2.sp] at hf
  refine repr_keep hf (fun r hr => ?_) h
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.below_sr hk (by omega_using [ho]) ho).symm

/-! ## What a call leaves -/

/-- After a call that writes the regions `ws` and the `k` bytes below `esp`. -/
structure Called (s t : State) (ws : List Region) (k : Nat) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.gpr .esp = s.gpr .esp
  frame : Frame (ws ++ [below (s.gpr .esp) k]) s.mem t.mem

theorem Called.ofStream {s t : State} {ws : List Region} (a : Proof.Pbkdf2.Stream.X86.After s ws t) :
    Called s t ws 48 := ⟨a.rd, a.wr, a.esp, a.frame⟩

theorem Called.ofWhole {s t : State} {ws : List Region} (a : Proof.Pbkdf2.Whole.X86.After s ws t) :
    Called s t ws 76 := ⟨a.rd, a.wr, a.esp, a.frame⟩

/-- The regions a call writes, in `scratch`. -/
def InScr (P : EP) (ws : List Region) : Prop := ∀ r ∈ ws, ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n

theorem Called.base {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (h : Base P σ s)
    (hk : k ≤ 3448) (hws : InScr P ws) : Base P σ t :=
  h.call hk hws c.rd c.wr c.sp c.frame

theorem Called.st {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) (hws : InScr P ws) : S P σ t := by
  have hf := c.frame
  rw [hs.2.sp] at hf
  refine ⟨hs.1, hs.2.write hf (fun r hr => ?_) c.rd c.wr c.sp⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨o, n, ho, hn, rfl⟩ := hws r hr
    exact ⟨P.SCR, by simp, hs.1.sr_sub ho hn⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.lay.LOW, by simp, hs.1.low_of hk⟩

theorem Called.keep {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) (hd : ∀ r ∈ ws, (sr P o n).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sr P o n).base n = Spec.Rsa.bytesAt s.mem (sr P o n).base n :=
  keep_sr hs hk c.frame ho hn hd

theorem Called.repr {σ s t : State} {ws : List Region} {k : Nat} (c : Called s t ws k) (hs : S P σ s)
    (hk : k ≤ 3448) {o : Nat} (ho : o + 96 ≤ 8448) (hd : ∀ r ∈ ws, (sr P o 96).Disjoint r) {msg : List Byte}
    (h : Spec.Sha256.Repr s.mem (sr P o 96).base msg) : Spec.Sha256.Repr t.mem (sr P o 96).base msg :=
  repr_keep_sr hs hk c.frame ho hd h

/-! ## The arguments of the calls -/

section Args

variable {σ s : State} (hs : S P σ s) (v : Backend)
include hs

theorem stk48 : Proof.Pbkdf2.Stream.X86.stk s = below P.B 48 := by
  show below (s.gpr .esp) 48 = _; rw [hs.2.sp]

theorem stk76 : Proof.Pbkdf2.Whole.X86.stk s = below P.B 76 := by
  show below (s.gpr .esp) 76 = _; rw [hs.2.sp]

/-- SHA-256's `init` of the state at `scratch + sSt`. -/
theorem initA (he : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) :
    InitArgs (H := v.F.H) s .edi (P.scr + BitVec.ofNat 32 sSt) :=
  { hst := he, hr := by decide
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cw := St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide)
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide) }

/-- SHA-256's `update` of the state at `scratch + sSt`, at the count `c`,
with `len` bytes at `d`. -/
theorem updA {d c : BitVec 32} {len : Nat} (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt)
    (esi : s.gpr .esi = c) (eax : s.gpr .eax = 0) (ecx : s.gpr .ecx = BitVec.ofNat 32 len)
    (edx : s.gpr .edx = d) (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) (hlen : len < 2 ^ 32)
    (cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr))
    (d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sSt 96))
    (d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sW 160))
    (b_d : (below P.B 48).Disjoint ⟨d.setWidth 64, len⟩) (nd : d.toNat + len ≤ 2 ^ 32) :
    UpdArgs (hk v) s .esi .edi (P.scr + BitVec.ofNat 32 sSt) d (P.scr + BitVec.ofNat 32 sW) c len :=
  { hst := edi, hlo := esi, eax := eax, ecx := ecx, edx := edx, ebp := ebp, hr := by decide, hl := by decide
    hlen := hlen
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cd := cd
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (St.cov_sr hs (o := sW) (n := 160) (by decide) (by decide))
    st_sc := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 160) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    d_st := d_st, d_sc := d_sc
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_d := by rw [stk48 hs]; exact b_d
    b_sc := by rw [stk48 hs]; exact hs.1.below_sr (o := sW) (n := 160) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    nd := nd
    nsc := hs.1.sr_fit (o := sW) (n := 160) (by decide) (by decide) }

/-- SHA-256's `finalize` of the state at `scratch + sSt` to `scratch + t`. -/
theorem finA {t : Nat} {lo hi : BitVec 32} (ht₁ : 192 ≤ t) (ht₂ : t + 32 ≤ 2576)
    (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) (eax : s.gpr .eax = lo) (ecx : s.gpr .ecx = hi)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 t) (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    FinArgs (hk v) s .edi (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 t)
      (P.scr + BitVec.ofNat 32 sW) lo hi :=
  { hst := edi, eax := eax, ecx := ecx, edx := edx, ebp := ebp, hr := by decide
    sp48 := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := t) (n := 32) (by omega_using [ht₂]) (by omega_using [ht₂]))
        (St.cov_sr hs (o := sW) (n := 160) (by decide) (by decide)))
    st_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := t) (n' := 32) (by simp only [sSt]; omega_using [ht₁]) (by decide)
      (by omega_using [ht₂]) (by decide) (by omega_using [ht₂])
    st_sc := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 160) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_sc := hs.1.sr_sep (o := t) (n := 32) (o' := sW) (n' := 160) (by simp only [sW]; omega_using [ht₂]) (by omega_using [ht₂])
      (by decide) (by omega_using [ht₂]) (by decide)
    b_st := by rw [stk48 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk48 hs]; exact hs.1.below_sr (o := t) (n := 32) (by decide) (by omega_using [ht₂]) (by omega_using [ht₂])
    b_sc := by rw [stk48 hs]; exact hs.1.below_sr (o := sW) (n := 160) (by decide) (by decide) (by decide)
    nst := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := t) (n := 32) (by omega_using [ht₂]) (by omega_using [ht₂])
    nsc := hs.1.sr_fit (o := sW) (n := 160) (by decide) (by decide) }

/-- HMAC's `init` of the states at `scratch + sSt` and `scratch + sOuter`
with the `kl` bytes of key at `scratch + o`. -/
theorem hiA {o kl : Nat} (ho₁ : 192 ≤ o) (ho₂ : o + kl ≤ 2576) (hkl : kl ≤ 64)
    (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 sSt) (esi : s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 o) (ecx : s.gpr .ecx = BitVec.ofNat 32 kl)
    (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    HiArgs (hk v).SH 104 s (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 sOuter)
      (P.scr + BitVec.ofNat 32 o) (P.scr + BitVec.ofNat 32 sW) kl :=
  { edi := edi, esi := esi, edx := edx, ecx := ecx, ebp := ebp
    klB := hkl
    kl32 := by omega_using [ho₂]
    sp := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cr := Covers.right (St.cov_sr hs (o := o) (n := kl) (by omega_using [ho₂]) (by omega_using [ho₂]))
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := sOuter) (n := 96) (by decide) (by decide))
        (St.cov_sr hs (o := sW) (n := 104 * 8) (by decide) (by decide)))
    i_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := sOuter) (n' := 96) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    i_k := hs.1.sr_sep (o := sSt) (n := 96) (o' := o) (n' := kl) (by simp only [sSt]; omega_using [ho₁]) (by decide)
      (by omega_using [ho₂]) (by decide) (by omega_using [ho₂])
    i_s := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_k := hs.1.sr_sep (o := sOuter) (n := 96) (o' := o) (n' := kl) (by simp only [sOuter]; omega_using [ho₁]) (by decide)
      (by omega_using [ho₂]) (by decide) (by omega_using [ho₂])
    o_s := hs.1.sr_sep (o := sOuter) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    k_s := hs.1.sr_sep (o := o) (n := kl) (o' := sW) (n' := 104 * 8) (by simp only [sW]; omega_using [ho₂]) (by omega_using [ho₂])
      (by decide) (by omega_using [ho₂]) (by decide)
    b_i := by rw [stk76 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk76 hs]; exact hs.1.below_sr (o := sOuter) (n := 96) (by decide) (by decide) (by decide)
    b_k := by rw [stk76 hs]; exact hs.1.below_sr (o := o) (n := kl) (by decide) (by omega_using [ho₂]) (by omega_using [ho₂])
    b_s := by rw [stk76 hs]; exact hs.1.below_sr (o := sW) (n := 104 * 8) (by decide) (by decide) (by decide)
    ni := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := sOuter) (n := 96) (by decide) (by decide)
    nk := hs.1.sr_fit (o := o) (n := kl) (by omega_using [ho₂]) (by omega_using [ho₂])
    nsc := hs.1.sr_fit (o := sW) (n := 104 * 8) (by decide) (by decide) }

/-- HMAC's `finalize` of the states at `scratch + sSt` and
`scratch + sOuter`, at the count `hi ++ lo`, to `scratch + t`. -/
theorem hfA {t : Nat} {lo hi : BitVec 32} (ht₁ : 192 ≤ t) (ht₂ : t + 32 ≤ 2576)
    (edx : s.gpr .edx = P.scr + BitVec.ofNat 32 sSt) (esi : s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter)
    (eax : s.gpr .eax = lo) (ecx : s.gpr .ecx = hi) (edi : s.gpr .edi = P.scr + BitVec.ofNat 32 t)
    (ebp : s.gpr .ebp = P.scr + BitVec.ofNat 32 sW) :
    HfArgs (hk v).SH 104 s (P.scr + BitVec.ofNat 32 sSt) (P.scr + BitVec.ofNat 32 sOuter) lo hi
      (P.scr + BitVec.ofNat 32 t) (P.scr + BitVec.ofNat 32 sW) :=
  { edx := edx, esi := esi, eax := eax, ecx := ecx, edi := edi, ebp := ebp
    sp := by rw [hs.2.sp]; exact Nat.le_trans (by decide) hs.1.sp_toNat
    cr := Covers.right (St.cov_sr hs (o := sOuter) (n := 96) (by decide) (by decide))
    cw := Covers.cons (St.cov_sr hs (o := sSt) (n := 96) (by decide) (by decide))
      (Covers.cons (St.cov_sr hs (o := t) (n := 32) (by omega_using [ht₂]) (by omega_using [ht₂]))
        (St.cov_sr hs (o := sW) (n := 104 * 8) (by decide) (by decide)))
    i_u := hs.1.sr_sep (o := sSt) (n := 96) (o' := sOuter) (n' := 96) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    i_o := hs.1.sr_sep (o := sSt) (n := 96) (o' := t) (n' := 32) (by simp only [sSt]; omega_using [ht₁]) (by decide)
      (by omega_using [ht₂]) (by decide) (by omega_using [ht₂])
    i_s := hs.1.sr_sep (o := sSt) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    u_o := hs.1.sr_sep (o := sOuter) (n := 96) (o' := t) (n' := 32) (by simp only [sOuter]; omega_using [ht₁]) (by decide)
      (by omega_using [ht₂]) (by decide) (by omega_using [ht₂])
    u_s := hs.1.sr_sep (o := sOuter) (n := 96) (o' := sW) (n' := 104 * 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    o_s := hs.1.sr_sep (o := t) (n := 32) (o' := sW) (n' := 104 * 8) (by simp only [sW]; omega_using [ht₂]) (by omega_using [ht₂])
      (by decide) (by omega_using [ht₂]) (by decide)
    b_i := by rw [stk76 hs]; exact hs.1.below_sr (o := sSt) (n := 96) (by decide) (by decide) (by decide)
    b_u := by rw [stk76 hs]; exact hs.1.below_sr (o := sOuter) (n := 96) (by decide) (by decide) (by decide)
    b_o := by rw [stk76 hs]; exact hs.1.below_sr (o := t) (n := 32) (by decide) (by omega_using [ht₂]) (by omega_using [ht₂])
    b_s := by rw [stk76 hs]; exact hs.1.below_sr (o := sW) (n := 104 * 8) (by decide) (by decide) (by decide)
    ni := hs.1.sr_fit (o := sSt) (n := 96) (by decide) (by decide)
    nu := hs.1.sr_fit (o := sOuter) (n := 96) (by decide) (by decide)
    no := hs.1.sr_fit (o := t) (n := 32) (by omega_using [ht₂]) (by omega_using [ht₂])
    nsc := hs.1.sr_fit (o := sW) (n := 104 * 8) (by decide) (by decide) }

end Args

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: `DH = SHA256(D)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecHash.lean`): SHA-256's `init`,
`update` with `D` and `finalize` to `scratch + sDH`, each after the block of
its arguments (`hashD_vp`): `DH`, the SHA-256 digest of `D` (`H6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)

variable {P : EP}

/-! ## The blocks of arguments -/

/-- `d ← scratch + o`. -/
theorem St.scrW {σ s : State} (hs : S P σ s) {d : Reg} (hd : d ≠ .esp) (o : Nat) {is : List Instr}
    {Q : State → Prop} (k : ∀ t, S P σ t → Upd s t d (P.scr + BitVec.ofNat 32 o) → WP isa (.block is) t Q) :
    WP isa (.block (scr d o ++ is)) s Q := by
  simp only [scr, List.cons_append, List.nil_append]
  refine hs.2.wp_arg (j := 21) (r := d) (by simp) hd fun t1 s1 u1 => ?_
  refine wp_addi fun t2 u2 => k t2 ⟨hs.1, s1.upd u2 hd⟩ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u2.gpr, u1.gpr]; rfl
  · rw [u2.other r hr, u1.other r hr]
  · rw [u2.mem, u1.mem]
  · rw [u2.rd, u1.rd]
  · rw [u2.wr, u1.wr]
  · rw [u2.syms, u1.syms]

/-- `d ← v`. -/
theorem St.movi {σ s : State} (hs : S P σ s) {d : Reg} (hd : d ≠ .esp) (v : Nat) {is : List Instr}
    {Q : State → Prop} (k : ∀ t, S P σ t → Upd s t d (BitVec.ofNat 32 v) → WP isa (.block is) t Q) :
    WP isa (.block (movI d v :: is)) s Q :=
  VG.X86.Wp.wp_movi fun t u => k t ⟨hs.1, hs.2.upd u hd⟩ u

/-- `d ← argument j`. -/
theorem St.argv {σ s : State} (hs : S P σ s) {j : Nat} (hj : j < 23) {d : Reg} (hd : d ≠ .esp)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → Upd s t d (P.argv.getD j 0) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (arg j) :: is)) s Q :=
  hs.2.wp_arg (j := j) (r := d) (by simpa using hj) hd fun t st u => k t ⟨hs.1, st⟩ u

/-- The private-key operation's result, through changes of registers. -/
theorem Base.regs {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : Base P σ t := by
  obtain ⟨hs, rc, pr, sl⟩ := h
  exact ⟨⟨hs.1, st⟩, rc, by rw [Priv, hm]; exact pr, by rw [hm]; exact sl⟩

/-! ## The stages -/

/-- Before `init`. -/
def H1 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt

/-- After `init`. -/
def H2 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ Spec.Sha256.Repr s.mem (sr P sSt 96).base []

/-- Before `update`. -/
def H3 (P : EP) (σ s : State) : Prop :=
  H2 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sD ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `update`. -/
def H4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Sha256.Repr s.mem (sr P sSt 96).base (Dfull P σ)

/-- Before `finalize`. -/
def H5 (P : EP) (σ s : State) : Prop :=
  H4 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .eax = BitVec.ofNat 32 P.K ∧ s.gpr .ecx = 0 ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sDH ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- `DH`. -/
def H6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sr P sDH 32).base 32 = Spec.Sha256.hash (Dfull P σ)

theorem D4.bytes_sr {σ s : State} (h : D4 P σ s) :
    Spec.Rsa.bytesAt s.mem (sr P sD P.K).base P.K = Dfull P σ := by
  rw [h.1.1.1.sr_eq (by decide)]; exact h.2

theorem shaInitArgs_vp : VP (D4 P) (.block shaInitArgs) (H1 P) :=
  VP.taint [.esp] shaInitArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.2.sp, h₂.1.1.2.sp])
    fun σ s h => by
      rw [shaInitArgs, ← List.append_nil (scr _ _)]
      exact St.scrW h.1.1 (by decide) sSt fun t st u => WP.block_nil
        ⟨⟨h.1.regs st.2 u.mem, by rw [u.mem]; exact h.2⟩, u.gpr⟩

theorem shaInit_vp (v : Backend) : VP (H1 P) (callInit v.F) (H2 P) :=
  VP.shaInit v (sp := P.B) (fun σ s h => ⟨initA h.1.1.1 v h.2, h.1.1.1.2.sp⟩) fun σ s h s' a hr => by
    have hs := h.1.1.1
    have hK := hs.1.k1024
    obtain hws : ∀ r ∈ [sr P sSt 96], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n := fun r hr => by
      simp only [List.mem_singleton] at hr; exact ⟨sSt, 96, by decide, by decide, hr⟩
    refine ⟨⟨h.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩, hr⟩
    rw [← h.1.bytes_sr, ← hs.1.sr_eq (by decide)]
    refine keep_sr hs (by decide) a.frame (by decide) (by simp only [sD]; omega_using [hK]) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.sr_sep (by simp only [sD, sSt]; omega_using []) (by decide) (by decide) (by simp only [sD]; omega_using [hK])
      (by decide)

theorem shaUpdArgs_vp : VP (H2 P) (.block shaUpdArgs) (H3 P) :=
  VP.taint [.esp] shaUpdArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp])
    fun σ s h => by
      have hs := h.1.1.1
      simp only [shaUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
      refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
      refine St.movi s1 (d := .esi) (by decide) 0 fun t2 s2 u2 => ?_
      refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
      refine St.scrW s3 (d := .edx) (by decide) sD fun t4 s4 u4 => ?_
      refine St.argv s4 (j := 4) (by decide) (d := .ecx) (by decide) fun t5 s5 u5 => ?_
      rw [← List.append_nil (scr _ _)]
      refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
      obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      refine ⟨⟨⟨h.1.1.regs s6.2 mm, by rw [mm]; exact h.1.2⟩, by rw [mm]; exact h.2⟩, ?_⟩
      simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
        u2.gpr, u2.other, u1.gpr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem shaUpd_vp (v : Backend) : VP (H3 P) (callUpd v.F) (H4 P) :=
  VP.shaUpd v (sp := P.B) (c := 0) (len := P.K) (d := P.scr + BitVec.ofNat 32 sD)
    (fun σ s h => by
      have hs := h.1.1.1.1
      have hK := hs.1.k1024
      obtain ⟨_, edi, esi, eax, edx, ecx, ebp⟩ := h
      exact ⟨updA hs v edi esi eax ecx edx ebp (by omega_using [hK])
        (Covers.right (St.cov_sr hs (o := sD) (n := P.K) (by decide) (by simp only [sD]; omega_using [hK])))
        (hs.1.sr_sep (by simp only [sD, sSt]; omega_using []) (by decide) (by decide) (by simp only [sD]; omega_using [hK])
          (by decide))
        (hs.1.sr_sep (by simp only [sD, sW]; omega_using [hK]) (by decide) (by decide) (by simp only [sD]; omega_using [hK])
          (by decide))
        (hs.1.below_sr (by decide) (by decide) (by simp only [sD]; omega_using [hK]))
        (hs.1.sr_fit (by decide) (by simp only [sD]; omega_using [hK])), hs.2.sp⟩)
    fun σ s h s' a hp => by
      have hs := h.1.1.1.1
      obtain hws : ∀ r ∈ [sr P sSt 96, sr P sW 160], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n :=
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨sSt, 96, by decide, by decide, rfl⟩
          · exact ⟨sW, 160, by decide, by decide, rfl⟩
      refine ⟨h.1.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩
      have := hp [] h.1.2 rfl
      rwa [List.nil_append, show Spec.Sha256.bytesAt s.mem ((P.scr + BitVec.ofNat 32 sD).setWidth 64) P.K =
        Dfull P σ from h.1.1.bytes_sr] at this

theorem shaFinArgs_vp : VP (H4 P) (.block shaFinArgs) (H5 P) :=
  VP.taint [.esp] shaFinArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.2.sp, h₂.1.1.2.sp])
    fun σ s h => by
      have hs := h.1.1
      simp only [shaFinArgs, List.append_assoc, List.cons_append, List.nil_append]
      refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
      refine St.argv s1 (j := 4) (by decide) (d := .eax) (by decide) fun t2 s2 u2 => ?_
      refine St.movi s2 (d := .ecx) (by decide) 0 fun t3 s3 u3 => ?_
      refine St.scrW s3 (d := .edx) (by decide) sDH fun t4 s4 u4 => ?_
      rw [← List.append_nil (scr _ _)]
      refine St.scrW s4 (d := .ebp) (by decide) sW fun t5 s5 u5 => WP.block_nil ?_
      obtain mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      refine ⟨⟨h.1.regs s5.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
      simp (disch := decide) only [u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
        u1.gpr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem shaFin_vp (v : Backend) : VP (H5 P) (callFin v.F) (H6 P) :=
  VP.shaFin v (sp := P.B) (lo := BitVec.ofNat 32 P.K) (hi := 0)
    (fun σ s h => by
      have hs := h.1.1.1
      obtain ⟨_, edi, eax, ecx, edx, ebp⟩ := h
      exact ⟨finA hs v (t := sDH) (by decide) (by decide) edi eax ecx edx ebp, hs.2.sp⟩)
    fun σ s h s' a hp => by
      have hs := h.1.1.1
      have hK := hs.1.k1024
      obtain hws : ∀ r ∈ [sr P sSt 96, sr P sDH 32, sr P sW 160], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧
          r = sr P o n := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨sSt, 96, by decide, by decide, rfl⟩
        · exact ⟨sDH, 32, by decide, by decide, rfl⟩
        · exact ⟨sW, 160, by decide, by decide, rfl⟩
      refine ⟨h.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩
      obtain hl : (Dfull P σ).length = P.K := by
        simp [Proof.RsaPkcs1Sig.bytesAt_len]; have := hs.1.dlK; omega_using [this]
      exact hp _ h.1.2 (by omega_using [hK, hl])
        (by rw [hl]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by omega_using [hK]))

theorem hashD_vp (v : Backend) : VP (D4 P) (hashD v.F) (H6 P) :=
  shaInitArgs_vp.seq ((shaInit_vp v).seq (shaUpdArgs_vp.seq ((shaUpd_vp v).seq
    (shaFinArgs_vp.seq (shaFin_vp v)))))

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: `KDK = HMAC(DH, C)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecKdk.lean`): HMAC-SHA-256's `init`
with a 32-byte key in `scratch` (`macInit_vp`), SHA-256's `update` of its
inner state (`macUpd_vp`) and HMAC's `finalize` to `scratch`
(`macFin_vp`), as IRPRF uses them too; and with them the key derivation
key of the draft's step 3.1 (`kdk_vp`, `kdkV`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)

variable {P : EP}

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega_using [h]
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega_using [h]

theorem hash_length (x : List Byte) : (Spec.Sha256.hash x).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

/-- `K₀` for the key `k`. -/
abbrev k0Of (k : List Byte) : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 k

/-- HMAC's states after `init` with the key `k`, and the inner one after
`text`. -/
def Macd (m : Mem) (P : EP) (k text : List Byte) : Prop :=
  Spec.Sha256.Repr m (sr P sSt 96).base (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.ipad ++ text) ∧
    Spec.Sha256.Repr m (sr P sOuter 96).base (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.opad)

/-! ## The calls -/

/-- What HMAC's `init` writes. -/
abbrev hiWs (P : EP) : List Region := [sr P sSt 96, sr P sOuter 96, sr P sW (104 * 8)]
/-- What SHA-256's `update` writes. -/
abbrev updWs (P : EP) : List Region := [sr P sSt 96, sr P sW 160]
/-- What HMAC's `finalize` to `scratch + o` writes. -/
abbrev hfWs (P : EP) (o : Nat) : List Region := [sr P sSt 96, sr P o 32, sr P sW (104 * 8)]

theorem hiWs_scr : InScr P (hiWs P) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨sOuter, 96, by decide, by decide, rfl⟩
  · exact ⟨sW, 104 * 8, by decide, by decide, rfl⟩

theorem updWs_scr : InScr P (updWs P) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨sW, 160, by decide, by decide, rfl⟩

theorem hfWs_scr {o : Nat} (ho : o + 32 ≤ 2576) : InScr P (hfWs P o) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨o, 32, by omega_using [ho], by omega_using [ho], rfl⟩
  · exact ⟨sW, 104 * 8, by decide, by decide, rfl⟩

/-- HMAC's `init` with the 32 bytes of key at `scratch + key`. -/
theorem macInit_vp (v : Backend) {key : Nat} (hk₁ : 192 ≤ key) (hk₂ : key + 32 ≤ 2576) {F G : State → State → Prop}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 key ∧
      s.gpr .ecx = BitVec.ofNat 32 32 ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW)
    (hG : ∀ σ s t, F σ s → Called s t (hiWs P) 76 →
      Macd t.mem P (Spec.Rsa.bytesAt s.mem (sr P key 32).base 32) [] → G σ t) :
    VP F (callHi v.F) G :=
  VP.macInit v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, d, e⟩ := hF σ s h
      exact ⟨hiA hs v hk₁ hk₂ (by decide) a b c d e, hs.2.sp⟩)
    fun σ s h t a hi ho => hG σ s t h (Called.ofWhole a) ⟨by rw [List.append_nil]; exact hi, ho⟩

/-- What `update` needs of the data, `len` bytes at `d`. -/
structure DataOk (P : EP) (s : State) (d : BitVec 32) (len : Nat) : Prop where
  hlen : len < 2 ^ 32
  cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr)
  d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sSt 96)
  d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sW 160)
  b_d : (below P.B 48).Disjoint ⟨d.setWidth 64, len⟩
  nd : d.toNat + len ≤ 2 ^ 32

/-- SHA-256's `update` of HMAC's inner state, after `init`, with the `len`
bytes at `d`. -/
theorem macUpd_vp (v : Backend) {d : BitVec 32} {len : Nat} {F G : State → State → Prop}
    {key : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = BitVec.ofNat 32 len ∧ s.gpr .edx = d ∧
      s.gpr .ebp = P.scr + BitVec.ofNat 32 sW ∧ Macd s.mem P (key σ s) [] ∧ (key σ s).length ≤ 64 ∧
      DataOk P s d len)
    (hG : ∀ σ s t, F σ s → Called s t (updWs P) 48 →
      Macd t.mem P (key σ s) (Spec.Rsa.bytesAt s.mem (d.setWidth 64) len) → G σ t) :
    VP F (callUpd v.F) G :=
  VP.shaUpd v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, e, f, g, -, -, dk⟩ := hF σ s h
      exact ⟨updA hs v a b c e f g dk.hlen dk.cd dk.d_st dk.d_sc dk.b_d dk.nd, hs.2.sp⟩)
    fun σ s h t a hp => by
      obtain ⟨hs, -, -, -, -, -, -, md, hk, -⟩ := hF σ s h
      obtain c := Called.ofStream a
      refine hG σ s t h c ⟨?_, c.repr hs (by decide) (o := sOuter) (by decide) (fun r hr => ?_) md.2⟩
      · have := hp _ (by have := md.1; rwa [List.append_nil] at this)
          (by rw [Proof.Hmac.Common.xorPad_length, blockKey_length hk]
              exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by decide))
        exact this
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.1.sr_sep (by decide) (by decide) (by decide) (by decide) (by decide)
        · exact hs.1.sr_sep (by decide) (by decide) (by decide) (by decide) (by decide)

/-- HMAC's `finalize` to the 32 bytes at `scratch + o`, after `tl` bytes of text. -/
theorem macFin_vp (v : Backend) {o tl : Nat} (ho₁ : 192 ≤ o) (ho₂ : o + 32 ≤ 2576)
    {F G : State → State → Prop} {key text : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ s.gpr .eax = BitVec.ofNat 32 (64 + tl) ∧ s.gpr .ecx = 0 ∧
      s.gpr .edi = P.scr + BitVec.ofNat 32 o ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW ∧
      Macd s.mem P (key σ s) (text σ s) ∧ (key σ s).length ≤ 64 ∧ (text σ s).length = tl ∧ 64 + tl < 2 ^ 32)
    (hG : ∀ σ s t, F σ s → Called s t (hfWs P o) 76 →
      Spec.Rsa.bytesAt t.mem (sr P o 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 (key σ s) (text σ s) →
      G σ t) :
    VP F (callHf v.F) G :=
  VP.macFin v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, e, f, g, -⟩ := hF σ s h
      exact ⟨hfA hs v ho₁ ho₂ a b c e f g, hs.2.sp⟩)
    fun σ s h t a hp => by
      obtain ⟨hs, -, -, -, -, -, -, md, hk, ht, htl⟩ := hF σ s h
      refine hG σ s t h (Called.ofWhole a) ?_
      exact hp _ _ (blockKey_length hk) (by rw [blockKey_length hk, ht]; omega_using [htl]) md.1
        (by rw [ht]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat htl) md.2

/-! ## The blocks of arguments -/

theorem macInitArgs_wp {σ s : State} (hs : S P σ s) (key : Nat) {Q : State → Prop}
    (k : ∀ t, S P σ t → t.mem = s.mem → t.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      t.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ t.gpr .edx = P.scr + BitVec.ofNat 32 key ∧
      t.gpr .ecx = BitVec.ofNat 32 32 ∧ t.gpr .ebp = P.scr + BitVec.ofNat 32 sW → Q t) :
    WP isa (.block (macInitArgs key)) s Q := by
  simp only [macInitArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
  refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
  refine St.scrW s2 (d := .edx) (by decide) key fun t3 s3 u3 => ?_
  refine St.movi s3 (d := .ecx) (by decide) 32 fun t4 s4 u4 => ?_
  rw [← List.append_nil (scr _ _)]
  refine St.scrW s4 (d := .ebp) (by decide) sW fun t5 s5 u5 => WP.block_nil (k t5 s5 ?_ ?_)
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · simp (disch := decide) only [u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
      u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

/-! ## `KDK` -/

/-- The key derivation key. -/
abbrev kdkV (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.kdk P.K (dB P σ) (cB P σ)

/-- `DH`. -/
abbrev dhV (P : EP) (σ : State) : List Byte := Spec.Sha256.hash (Dfull P σ)

/-- Before `init`. -/
def K1 (P : EP) (σ s : State) : Prop :=
  H6 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sDH ∧ s.gpr .ecx = BitVec.ofNat 32 32 ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `init`. -/
def K2 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) []

/-- Before `update`. -/
def K3 (P : EP) (σ s : State) : Prop :=
  K2 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .edx = P.inp ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `update`. -/
def K4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) (cB P σ)

/-- Before `finalize`. -/
def K5 (P : EP) (σ s : State) : Prop :=
  K4 P σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .eax = BitVec.ofNat 32 (64 + P.K) ∧ s.gpr .ecx = 0 ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sKDK ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- `KDK`. -/
def K6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sr P sKDK 32).base 32 = kdkV P σ

theorem sp_agree {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp], s₁.gpr r = s₂.gpr r := fun _ _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).2.sp, (hF _ _ h₂).2.sp]

theorem kdkInitArgs_vp : VP (H6 P) (.block (macInitArgs sDH)) (K1 P) :=
  VP.taint [.esp] macInitDH_taint (sp_agree fun _ _ h => h.1.1) fun σ s h =>
    macInitArgs_wp h.1.1 sDH fun t st hm r =>
      ⟨⟨h.1.regs st.2 hm, by rw [hm]; exact h.2⟩, r⟩

theorem kdkInit_vp (v : Backend) : VP (K1 P) (callHi v.F) (K2 P) :=
  macInit_vp v (key := sDH) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1, h.2⟩) fun σ s t h c md => by
    obtain ⟨⟨hb, dh⟩, -⟩ := h
    exact ⟨c.base hb (by decide) hiWs_scr, by rw [dh] at md; exact md⟩

theorem kdkUpdArgs_vp : VP (K2 P) (.block kdkUpdArgs) (K3 P) :=
  VP.taint [.esp] kdkUpdArgs_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    simp only [kdkUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.movi s1 (d := .esi) (by decide) 64 fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.argv s3 (j := 9) (by decide) (d := .edx) (by decide) fun t4 s4 u4 => ?_
    refine St.argv s4 (j := 4) (by decide) (d := .ecx) (by decide) fun t5 s5 u5 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
    obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨h.1.regs s6.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
      u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem dataINP {σ s : State} (hs : S P σ s) : DataOk P s P.inp P.K :=
  { hlen := by have := hs.1.k1024; omega_using [this]
    cd := St.cov_ro hs (R := P.INP) (by simp)
    d_st := (hs.1.sr_ro (by decide) (by decide) (R := P.INP) (by simp)).symm
    d_sc := (hs.1.sr_ro (by decide) (by decide) (R := P.INP) (by simp)).symm
    b_d := hs.1.below_ro (by decide) (R := P.INP) (by simp)
    nd := by
      have := hs.1.ok.fits P.INP (by simp)
      simp only [BitVec.toNat_setWidth] at this
      rwa [Nat.mod_eq_of_lt (by have := P.inp.isLt; omega_using [])] at this }

theorem kdkUpd_vp (v : Backend) : VP (K3 P) (callUpd v.F) (K4 P) :=
  macUpd_vp v (key := fun σ _ => dhV P σ) (fun _ _ h => by
      obtain ⟨⟨hb, md⟩, a, b, c, e, f, g⟩ := h
      exact ⟨hb.1, a, b, c, e, f, g, md, by rw [hash_length]; decide, dataINP hb.1⟩)
    fun σ s t h c md => by
      obtain ⟨⟨hb, -⟩, -⟩ := h
      have hs := hb.1
      refine ⟨c.base hb (by decide) updWs_scr, ?_⟩
      rw [show Spec.Rsa.bytesAt s.mem (P.inp.setWidth 64) P.K = cB P σ from hs.2.ro (R := P.INP) (by simp)]
        at md
      exact md

theorem kdkFinArgs_vp : VP (K4 P) (.block kdkFinArgs) (K5 P) :=
  VP.taint [.esp] kdkFinArgs_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    have hK := hs.1.k1024
    simp only [kdkFinArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edx) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
    refine St.argv s2 (j := 4) (by decide) (d := .eax) (by decide) fun t3 s3 u3 => ?_
    refine wp_addi fun t4 u4 => ?_
    obtain s4 : S P σ t4 := ⟨hs.1, s3.2.upd u4 (by decide)⟩
    refine St.movi s4 (d := .ecx) (by decide) 0 fun t5 s5 u5 => ?_
    refine St.scrW s5 (d := .edi) (by decide) sKDK fun t6 s6 u6 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s6 (d := .ebp) (by decide) sW fun t7 s7 u7 => WP.block_nil ?_
    obtain mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨h.1.regs s7.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u7.gpr, u7.other, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other,
      u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | skip
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    apply BitVec.eq_of_toNat_eq
    have e64 : (64 : BitVec 32).toNat = 64 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e64]
    omega_using []

theorem kdkV_eq (P : EP) {σ : State} (h : In P σ) :
    kdkV P σ = Spec.Hmac.hmac Spec.Hmac.sha256 (dhV P σ) (cB P σ) := by
  simp only [kdkV, Spec.RsaPkcs1Enc.kdk, dhV, Dfull]
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [Proof.RsaPkcs1Sig.bytesAt_len]; exact h.dlK),
    Proof.RsaPkcs1Sig.bytesAt_len]

theorem kdkFin_vp (v : Backend) : VP (K5 P) (callHf v.F) (K6 P) :=
  macFin_vp v (o := sKDK) (tl := P.K) (key := fun σ _ => dhV P σ) (text := fun σ _ => cB P σ) (by decide)
    (by decide)
    (fun _ _ h => by
      obtain ⟨⟨hb, md⟩, a, b, c, e, f, g⟩ := h
      exact ⟨hb.1, a, b, c, e, f, g, md, by rw [hash_length]; decide, Proof.RsaPkcs1Sig.bytesAt_len _ _ _,
        by have := hb.1.1.k1024; omega_using [this]⟩)
    fun σ s t h c hk => by
      obtain ⟨⟨hb, -⟩, -⟩ := h
      exact ⟨c.base hb (by decide) (hfWs_scr (by decide)), by rw [hk, kdkV_eq P hb.1.1]⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end

/-! ### `RsaPkcs1Enc.X86.DecMsg`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the message of an IRPRF block

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecMsg.lean`):
`I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)` (`msgV`), written byte by byte
in order to `scratch + sMsg` (at `ebx`; `MW`, `msgBytes_wp`): the two bytes
of `i` (in `ecx`), the label's (`putLabel`), and the bit length's (`clLen`
for 256 bytes, `amLen` for `k`, in `edx`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The message's place. -/
abbrev msgA (P : EP) : Addr := (sc P sMsg 16).base

/-- The message of block `i`, for the label `lab` and `length` bytes. -/
def msgV (i : Nat) (lab : List Byte) (L : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ lab ++ Spec.Rsa.i2osp (8 * L) 2

theorem msgV_length (i : Nat) (lab : List Byte) (L : Nat) : (msgV i lab L).length = lab.length + 4 := by
  simp [msgV, VG.Proof.RsaPkcs1Enc.i2osp_length]; omega_arith

/-- The message's first `n` bytes written, memory changed only in its 16
bytes, and the registers but `eax` kept. -/
structure MW (P : EP) (σ s₀ : State) (xs : List Byte) (n : Nat) (t : State) : Prop where
  st : S P σ t
  frame : Frame [sc P sMsg 16] s₀.mem t.mem
  regs : ∀ r, r ≠ .eax → t.gpr r = s₀.gpr r
  bytes : ∀ j < n, t.mem (msgA P + BitVec.ofNat 64 j) = xs.getD j 0

section
variable {σ s₀ t : State} {xs : List Byte} {n : Nat}

theorem MW.start (hs : S P σ s₀) : MW P σ s₀ xs 0 s₀ :=
  ⟨hs, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MW.upd (h : MW P σ s₀ xs n t) {t' : State} {v : BitVec 32} (u : Upd t t' .eax v) : MW P σ s₀ xs n t' :=
  ⟨⟨h.st.1, h.st.2.upd u (by decide)⟩, by rw [u.mem]; exact h.frame,
    fun r hr => by rw [u.other r hr]; exact h.regs r hr, fun j hj => by rw [u.mem]; exact h.bytes j hj⟩

/-- `mov byte [ebx + n], r` of byte `n`. -/
theorem MW.st8 (h : MW P σ s₀ xs n t) (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {r : Reg8} (hb : (t.gpr r.reg).setWidth 8 = xs.getD n 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → t'.gpr = t.gpr → WP isa (.block is) t' Q) :
    WP isa (.block (.store8 (Impl.RsaPkcs1Sig.X86.at_ .ebx n) r :: is)) t Q := by
  have hs := h.st
  obtain ha : t.ea (Impl.RsaPkcs1Sig.X86.at_ .ebx n) = msgA P + BitVec.ofNat 64 n := by
    show t.ea ⟨.ebx, n⟩ = _
    rw [ea_at, h.regs _ (by decide), hbx, hs.1.addrSc (by simp only [sMsg]; omega_arith)]
    exact (Offset.add_ofNat_add_ofNat _ _ _).symm
  obtain hc : (sc P sMsg 16).Contains (msgA P + BitVec.ofNat 64 n) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine wp_store8 ha (by rw [Offset.add_ofNat_add_ofNat]; exact St.sc_w hs (by simp only [sMsg]; omega_arith))
    fun t' u => k t' ⟨⟨hs.1, ?_⟩, ?_, fun r hr => by rw [u.gpr]; exact h.regs r hr, ?_⟩ u.gpr
  · refine hs.2.write (rs := [sc P sMsg 16]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hs.1.sc_sub (by decide)⟩) u.rd u.wr
      (by rw [u.gpr])
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ hc
  · intro j hj
    rw [u.mem, WriteBytes.writeW8_apply]
    by_cases e : j = n
    · subst e; simp [hb]
    · simp only [Offset.add_ofNat_ne (msgA P) (by omega_arith) (by omega_arith) e, ↓reduceIte]
      exact h.bytes j (by omega_arith)

theorem setWidth_ofNat8 (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `putByte n v`: the byte `v` at index `n`. -/
theorem MW.putByte (h : MW P σ s₀ xs n t) (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {v : Nat} (hb : xs.getD n 0 = BitVec.ofNat 8 v) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → WP isa (.block is) t' Q) :
    WP isa (.block (putByte n v ++ is)) t Q :=
  wp_movi fun t1 u1 => (h.upd u1).st8 hbx hn (r := .al) (by rw [show Reg8.al.reg = .eax from rfl, u1.gpr,
    setWidth_ofNat8, hb]) fun t2 h2 _ => k t2 h2

/-- `putLabel vs n`: the bytes `vs` from index `n`. -/
theorem MW.putLabel (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) :
    ∀ (vs : List Nat) {n : Nat} {t : State}, MW P σ s₀ xs n t → n + vs.length ≤ 16 →
      (∀ j < vs.length, xs.getD (n + j) 0 = BitVec.ofNat 8 (vs.getD j 0)) →
      ∀ {is : List Instr} {Q : State → Prop}, (∀ t', MW P σ s₀ xs (n + vs.length) t' → WP isa (.block is) t' Q) →
      WP isa (.block (Impl.RsaPkcs1Enc.X86.Decrypt.putLabel vs n ++ is)) t Q
  | [], n, t, h, _, _, _, _, k => by simpa [Impl.RsaPkcs1Enc.X86.Decrypt.putLabel] using k t h
  | v :: vs, n, t, h, hn, hb, _, _, k => by
    simp only [Impl.RsaPkcs1Enc.X86.Decrypt.putLabel, List.append_assoc]
    refine h.putByte hbx (by simp at hn; omega_arith) (by simpa using hb 0 (by simp)) fun t1 h1 => ?_
    refine MW.putLabel hbx vs h1 (by simp at hn; omega_arith)
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega_arith, hb (j + 1) (by simp; omega_arith)]; rfl)
      fun t2 h2 => k t2 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)

end

/-! ## The whole message -/

theorem i2osp_two_lt {i : Nat} (hi : i < 256) : Spec.Rsa.i2osp i 2 = [0, BitVec.ofNat 8 i] := by
  rw [VG.Proof.RsaPkcs1Enc.i2osp_two, Nat.div_eq_of_lt hi]; rfl

/-- The message: its bytes, from the label's bytes `vs` and the code `len`
of the bit length's two bytes. -/
theorem msgBytes_wp {σ s : State} {vs : List Nat} {len : List Instr} {L i : Nat} (hs : S P σ s)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hcx : s.gpr .ecx = BitVec.ofNat 32 i) (hi : i < 256)
    (hvs : vs.length + 4 ≤ 16)
    (hlen : ∀ {t : State}, MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
      ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q) :
    WP isa (.block (msgBytes vs len)) s fun t =>
      S P σ t ∧ Frame [sc P sMsg 16] s.mem t.mem ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Spec.Rsa.bytesAt t.mem (sc P sMsg (vs.length + 4)).base (vs.length + 4) =
        msgV i (vs.map (BitVec.ofNat 8)) L := by
  obtain hm : (msgV i (vs.map (BitVec.ofNat 8)) L).length = vs.length + 4 := by rw [msgV_length]; simp
  unfold msgBytes
  refine (MW.start (xs := msgV i (vs.map (BitVec.ofNat 8)) L) hs).putByte hbx (by decide) (v := 0)
    (by simp only [msgV, i2osp_two_lt hi]; rfl) fun t1 h1 => ?_
  refine h1.st8 hbx (by decide) (r := .cl) (by
      rw [show Reg8.cl.reg = .ecx from rfl, h1.regs _ (by decide), hcx, setWidth_ofNat8]
      simp [msgV, i2osp_two_lt hi])
    fun t2 h2 _ => ?_
  refine MW.putLabel hbx vs h2 (by omega_arith) (fun j hj => ?_) fun t3 h3 => ?_
  · simp only [msgV, i2osp_two_lt hi, List.cons_append, List.nil_append]
    rw [show 0 + 1 + 1 + j = j + 2 by omega_arith, List.getD_cons_succ, List.getD_cons_succ,
      Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp; omega_arith)]
    simp [List.getD_eq_getElem?_getD, hj]
  · refine hlen (by simpa [Nat.add_comm] using h3) fun t4 h4 => ⟨h4.st, h4.frame, h4.regs, ?_⟩
    rw [← hm]
    exact Proof.RsaPkcs1Sig.bytesAt_eq fun j hj => by rw [hm] at hj; exact h4.bytes j hj

/-- The bit length 2048 (`clLen`), after a label of 6 bytes. -/
theorem clLen_wp {σ s t : State} {lab : List Byte} {i : Nat} (hl : lab.length = 6)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (h : MW P σ s (msgV i lab 256) 8 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab 256) 10 t' → Q t') : WP isa (.block clLen) t Q := by
  obtain e8 : (msgV i lab 256).getD 8 0 = BitVec.ofNat 8 0x08 := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  obtain e9 : (msgV i lab 256).getD 9 0 = BitVec.ofNat 8 0x00 := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have := h.putByte hbx (by decide) (v := 0x08) e8 (is := putByte 9 0) fun t1 h1 =>
    h1.putByte hbx (by decide) (v := 0) e9 (is := []) fun t2 h2 => WP.block_nil (k t2 h2)
  simpa [clLen] using this

theorem shr5 {K : Nat} (hK : K ≤ 1024) : (BitVec.ofNat 32 K >>> 5).setWidth 8 = BitVec.ofNat 8 (8 * K / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem times8 (K : Nat) :
    ((BitVec.ofNat 32 K + BitVec.ofNat 32 K + (BitVec.ofNat 32 K + BitVec.ofNat 32 K)) +
      (BitVec.ofNat 32 K + BitVec.ofNat 32 K + (BitVec.ofNat 32 K + BitVec.ofNat 32 K))).setWidth 8 =
      BitVec.ofNat 8 (8 * K) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- The bit length `8 k` (`amLen`), after a label of 7 bytes, from `k` in `edx`. -/
theorem amLen_wp {σ s t : State} {lab : List Byte} {i K : Nat} (hl : lab.length = 7) (hK : K ≤ 1024)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hdx : s.gpr .edx = BitVec.ofNat 32 K)
    (h : MW P σ s (msgV i lab K) 9 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab K) 11 t' → Q t') : WP isa (.block amLen) t Q := by
  obtain dx : t.gpr .edx = BitVec.ofNat 32 K := by rw [h.regs _ (by decide), hdx]
  obtain e9 : (msgV i lab K).getD 9 0 = BitVec.ofNat 8 (8 * K / 256) := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  obtain e10 : (msgV i lab K).getD 10 0 = BitVec.ofNat 8 (8 * K) := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  simp only [amLen]
  refine wp_mov fun t1 u1 => ?_
  refine wp_shr (n := 5) (by decide) fun t2 u2 _ => ?_
  refine ((h.upd u1).upd u2).st8 hbx (by decide) (r := .al)
    (by rw [show Reg8.al.reg = .eax from rfl, u2.gpr, u1.gpr, dx, shr5 hK, e9]) fun t3 h3 g3 => ?_
  obtain dx' : t3.gpr .edx = BitVec.ofNat 32 K := by rw [g3, u2.other _ (by decide), u1.other _ (by decide), dx]
  refine wp_mov fun t4 u4 => ?_
  refine wp_add fun t5 u5 _ => ?_
  refine wp_add fun t6 u6 _ => ?_
  refine wp_add fun t7 u7 _ => ?_
  refine ((((h3.upd u4).upd u5).upd u6).upd u7).st8 hbx (by decide) (r := .al)
    (by rw [show Reg8.al.reg = .eax from rfl, u7.gpr, u6.gpr, u5.gpr, u4.gpr, dx', times8, e10])
    fun t8 h8 _ => WP.block_nil (k t8 h8)

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: an IRPRF loop

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPrf.lean`,
`Proof/RsaPkcs1Enc/Arm/DecVerified.lean`): a loop (`Prf`) writes block `i`
of IRPRF, `HMAC(KDK, msgV i label L)`, to `scratch + dst + 32 i`
(`prfBody_vp`), keeping `KDK` and `xn` bytes of `scratch` at `xo`; the
whole loop (`loop_vp`) writes its `nb` blocks (`CI`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_addS wp_cmpS)
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

/-- An IRPRF loop: the label's bytes `vs`, the code `len` of the bit length,
the output's length `L`, its place `dst` in `scratch`, its number `nb` of
blocks, and the `xn` bytes `xv` at `scratch + xo` it keeps. -/
structure Prf (P : EP) where
  vs : List Nat
  len : List Instr
  L : Nat
  dst : Nat
  nb : Nat
  xo : Nat
  xn : Nat
  xv : State → List Byte
  vs_len : vs.length + 4 ≤ 16
  nb1 : 1 ≤ nb
  nb_le : nb ≤ 256
  dst_lo : 272 ≤ dst
  dst_hi : dst + 32 * nb ≤ 2576
  x_lo : 208 ≤ xo
  x_hi : xo + xn ≤ 2576
  x_sep : xo + xn ≤ dst ∨ dst + 32 * nb ≤ xo
  lenOk : ∀ {σ s t : State} {i : Nat}, S P σ s → s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg →
    s.gpr .edx = BitVec.ofNat 32 P.K → MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
    ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q

namespace Prf

variable (R : Prf P)

/-- The label. -/
abbrev lab : List Byte := R.vs.map (BitVec.ofNat 8)

/-- The length of a block's message. -/
abbrev tl : Nat := R.vs.length + 4

end Prf

/-- Before block `i`. -/
structure CI (P : EP) (R : Prf P) (i : Nat) (σ s : State) : Prop where
  hi : i ≤ R.nb
  base : Base P σ s
  kdk : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ
  x : Spec.Rsa.bytesAt s.mem (sc P R.xo R.xn).base R.xn = R.xv σ
  sNB : s.mem.readW (P.lay.fr oNB) 32 = BitVec.ofNat 32 R.nb
  blk : Spec.Rsa.bytesAt s.mem (sc P R.dst (32 * i)).base (32 * i) =
    (List.range i).flatMap (prfBlock (kdkV P σ) R.lab R.L)

/-- What the loop's writes stay apart from. -/
structure Keep (P : EP) (R : Prf P) (i : Nat) (r : Region) : Prop where
  safe : Safe P r
  kdk : (sc P sKDK 32).Disjoint r
  x : (sc P R.xo R.xn).Disjoint r
  blk : (sc P R.dst (32 * i)).Disjoint r
  nb : Region.Disjoint ⟨P.lay.fr oNB, 4⟩ r

section
variable {R : Prf P} {i : Nat} {σ s t : State}

theorem CI.keep (h : CI P R i σ s) (st : P.lay.St σ t) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hk : ∀ r ∈ rs, Keep P R i r) : CI P R i σ t where
  hi := h.hi
  base := h.base.frame st hf fun r hr => (hk r hr).safe
  kdk := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).kdk) (by decide)).trans h.kdk
  x := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).x)
    (by have := R.x_hi; omega_using [this])).trans h.x
  sNB := by
    rw [hf.readW (r := ⟨P.lay.fr oNB, 4⟩) (Region.contains_self _ _) (fun r hr => (hk r hr).nb) (by decide)]
    exact h.sNB
  blk := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).blk)
    (by have := R.dst_hi; have := h.hi; omega_arith)).trans h.blk

theorem CI.of_mem (h : CI P R i σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : CI P R i σ t :=
  h.keep st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

theorem CI.S (h : CI P R i σ s) : S P σ s := h.base.1

/-- A slot of the frame kept. -/
theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

namespace In
variable (h : In P σ)
include h

theorem keep_sr {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) (hk : o + n ≤ sKDK ∨ sKDK + 32 ≤ o)
    (hx : o + n ≤ R.xo ∨ R.xo + R.xn ≤ o) (hb : o + n ≤ R.dst ∨ R.dst + 32 * i ≤ o) (hi : i ≤ R.nb) :
    Keep P R i (sr P o n) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (sr P o n) := by
  rw [h.sr_eq ho]
  exact ⟨{ safe := h.safe_sc hn
           kdk := sc_sep (by simp only [sKDK] at hk ⊢; omega_using [hk]) (by decide) hn
           x := sc_sep (by omega_using [hx]) (by have := R.x_hi; omega_using [this]) hn
           blk := sc_sep (by omega_using [hb]) (by have := R.dst_hi; omega_using [hi, this]) hn
           nb := h.fr_sc (by simp only [oNB, frameBytes]; decide) hn },
    h.fr_sc (by simp only [oI, frameBytes]; decide) hn⟩

theorem keep_below {k : Nat} (hk : k ≤ 3448) (hi : i ≤ R.nb) :
    Keep P R i (below P.B k) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (below P.B k) := by
  obtain hl := h.low_of hk
  exact ⟨{ safe := h.below_safe hk
           kdk := (h.low_sc (by decide)).symm.sub_right hl
           x := (h.low_sc (by have := R.x_hi; omega_using [this])).symm.sub_right hl
           blk := (h.low_sc (by have := R.dst_hi; omega_using [hi, this])).symm.sub_right hl
           nb := (Lay.fr_low (by simp only [oNB]; decide) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).sub_right hl },
    (Lay.fr_low (by simp only [oI]; decide) (by show (3448 : Nat) ≤ 2 ^ 32; decide)).sub_right hl⟩

theorem keep_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d)
    (hnb : d + n ≤ oNB ∨ oNB + 4 ≤ d) (hi : i ≤ R.nb) : Keep P R i ⟨P.lay.fr d, n⟩ where
  safe := h.safe_fr hd ho
  kdk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_using [hd]) (by decide)).symm
  x := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_using [hd]) (by have := R.x_hi; omega_using [this])).symm
  blk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega_using [hd]) (by have := R.dst_hi; omega_using [hi, this])).symm
  nb := Lay.fr_sep (by simp only [oNB] at hnb ⊢; omega_using [hnb]) (by decide) (by simp only [frameBytes] at hd; omega_using [hd])

end In

/-- Through a call. -/
theorem CI.call (h : CI P R i σ s) {ws : List Region} {k : Nat} (c : Called s t ws k) (hk : k ≤ 3448)
    (hws : InScr P ws) (hkp : ∀ r ∈ ws, Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) :
    CI P R i σ t ∧ t.mem.readW (P.lay.fr oI) 32 = s.mem.readW (P.lay.fr oI) 32 := by
  have hs := h.S
  have hf := c.frame
  rw [hs.2.sp] at hf
  obtain kp : ∀ r ∈ ws ++ [below P.B k], Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hkp r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.keep_below hk h.hi
  exact ⟨h.keep (c.st hs hk hws).2 hf fun r hr => (kp r hr).1, slot_keep hf fun r hr => (kp r hr).2⟩

end

/-! ## The stages of block `i` -/

section
variable (P : EP) (R : Prf P) (i : Nat) (σ s : State)

/-- Block `i` begins: its counter in its slot. -/
def B0 : Prop := CI P R i σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The message's place, `i` and `k`. -/
def B1 : Prop :=
  B0 P R i σ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg ∧ s.gpr .ecx = BitVec.ofNat 32 i ∧
    s.gpr .edx = BitVec.ofNat 32 P.K

/-- The message written. -/
def B2 : Prop := B0 P R i σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L

/-- Before HMAC's `init`. -/
def B3 : Prop :=
  B2 P R i σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sKDK ∧ s.gpr .ecx = BitVec.ofNat 32 32 ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After it. -/
def B4 : Prop := B2 P R i σ s ∧ Macd s.mem P (kdkV P σ) []

/-- Before `update`. -/
def B5 : Prop :=
  B4 P R i σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 R.tl ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sMsg ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After it. -/
def B6 : Prop := B0 P R i σ s ∧ Macd s.mem P (kdkV P σ) (msgV i R.lab R.L)

/-- Before `finalize`. -/
def B7 : Prop :=
  B6 P R i σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .eax = BitVec.ofNat 32 (64 + R.tl) ∧ s.gpr .ecx = 0 ∧
    s.gpr .edi = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- Block `i` written. -/
def B8 : Prop := CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

end

/-- Before block `nb - m`, `m` blocks left. -/
def LI (P : EP) (R : Prf P) (m : Nat) (σ s : State) : Prop := m ≤ R.nb ∧ B0 P R (R.nb - m) σ s

/-! ## The pieces -/

section
variable {R : Prf P} {i : Nat}

theorem hmac_len (k t : List Byte) : (Spec.Hmac.hmac Spec.Hmac.sha256 k t).length = 32 := by
  simp only [Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, Spec.Hmac.sha256]; exact hash_length _

theorem kdkV_length {σ : State} : (kdkV P σ).length = 32 := hmac_len _ _

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, Offset.add_add]

theorem sub_beq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      replace this : (2 ^ 32 - b + a) % 2 ^ 32 = 0 := this
      omega_using [ha, hb, h, this]
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

theorem msgPtr_vp : VP (B0 P R i) (.block msgPtr) (B1 P R i) :=
  VP.taint [.esp] msgPtr_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    simp only [msgPtr, List.cons_append, List.nil_append, scr]
    refine St.argv hs (j := 21) (by decide) (d := .ebx) (by decide) fun t1 s1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    obtain s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine s2.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .ecx) (by decide)
      fun t3 st3 u3 => ?_
    refine St.argv ⟨hs.1, st3⟩ (j := 4) (by decide) (d := .edx) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    obtain m2 : t2.mem = s.mem := by rw [u2.mem, u1.mem]
    obtain mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, m2]
    refine ⟨⟨h.1.of_mem s4.2 mm, by rw [mm]; exact h.2⟩, ?_, ?_, u4.gpr⟩
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr]; rfl
    · rw [u4.other _ (by decide), u3.gpr, m2, h.2]

theorem msg_vp (cert : TaintOk [.ebx] (.block (msgBytes R.vs R.len))) (hi : i < 256) :
    VP (B1 P R i) (.block (msgBytes R.vs R.len)) (B2 P R i) :=
  VP.taint [.ebx] cert (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun σ s h => by
    obtain ⟨⟨hc, sI⟩, bx, cx, dx⟩ := h
    have hs := hc.S
    refine WP.mono (msgBytes_wp (L := R.L) hs bx cx hi R.vs_len (R.lenOk hs bx dx)) fun t ⟨st, fr, _, hb⟩ => ?_
    obtain hk : ∀ r ∈ [sc P sMsg 16], Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [← hs.1.sr_eq (by decide)]
      exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sMsg]; omega_using [this]))
        (.inl (by have := R.dst_lo; simp only [sMsg]; omega_using [this])) hc.hi
    exact ⟨⟨hc.keep st.2 fr fun r hr => (hk r hr).1, by rw [slot_keep fr fun r hr => (hk r hr).2]; exact sI⟩, hb⟩

theorem initArgs_vp : VP (B2 P R i) (.block (macInitArgs sKDK)) (B3 P R i) :=
  VP.taint [.esp] macInitKDK_taint (sp_agree fun _ _ h => h.1.1.S) fun σ s h =>
    macInitArgs_wp h.1.1.S sKDK fun t st hm r =>
      ⟨⟨⟨h.1.1.of_mem st.2 hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2⟩, r⟩

/-- The message, through a call that writes elsewhere. -/
theorem msg_keep {σ s t : State} {ws : List Region} {k : Nat} (h : B2 P R i σ s) (c : Called s t ws k)
    (hk : k ≤ 3448) (hd : ∀ r ∈ ws, (sr P sMsg R.tl).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L := by
  have hs := h.1.1.S
  have := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  rw [← hs.1.sr_eq (by decide), c.keep hs hk (by decide) (by simp only [sMsg]; omega_using [this, htl]) hd, hs.1.sr_eq (by decide)]
  exact h.2

theorem init_vp (v : Backend) : VP (B3 P R i) (callHi v.F) (B4 P R i) :=
  macInit_vp v (key := sKDK) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1.S, h.2⟩) fun σ s t h c md => by
    obtain ⟨hb, -⟩ := h
    have hs := hb.1.1.S
    have hi := hb.1.1.hi
    have := R.vs_len
    have htl : R.tl = R.vs.length + 4 := rfl
    obtain ci := hb.1.1.call c (by decide) hiWs_scr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega_using [this]))
          (.inl (by have := R.dst_lo; simp only [sSt]; omega_using [this])) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sOuter]; omega_using [this]))
          (.inl (by have := R.dst_lo; simp only [sOuter]; omega_using [this])) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega_using [this]))
          (.inr (by have := R.dst_hi; simp only [sW]; omega_using [hi, this])) hi
    refine ⟨⟨⟨ci.1, by rw [ci.2]; exact hb.1.2⟩, msg_keep hb c (by decide) fun r hr => ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hs.1.sr_sep (by simp only [sMsg, sSt, sOuter, sW]; omega_arith) (by decide) (by decide)
          (by simp only [sMsg]; omega_using [this, htl]) (by decide)
    · rw [show Spec.Rsa.bytesAt s.mem (sr P sKDK 32).base 32 = kdkV P σ by
        rw [hs.1.sr_eq (by decide)]; exact hb.1.1.kdk] at md
      exact md

theorem updArgs_vp (cert : TaintOk [.esp] (.block (prfUpdArgs R.tl))) :
    VP (B4 P R i) (.block (prfUpdArgs R.tl)) (B5 P R i) :=
  VP.taint [.esp] cert (sp_agree fun _ _ h => h.1.1.1.S) fun σ s h => by
    have hs := h.1.1.1.S
    simp only [prfUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.movi s1 (d := .esi) (by decide) 64 fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.scrW s3 (d := .edx) (by decide) sMsg fun t4 s4 u4 => ?_
    refine St.movi s4 (d := .ecx) (by decide) R.tl fun t5 s5 u5 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
    obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨⟨h.1.1.1.of_mem s6.2 mm, by rw [mm]; exact h.1.1.2⟩, by rw [mm]; exact h.1.2⟩,
      by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
      u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem upd_vp (v : Backend) : VP (B5 P R i) (callUpd v.F) (B6 P R i) := by
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  refine macUpd_vp (P := P) v (d := P.scr + BitVec.ofNat 32 sMsg) (len := R.tl) (key := fun σ _ => kdkV P σ)
    (fun _ _ h => ?_) fun σ s t h c md => ?_
  · obtain ⟨⟨hb, md⟩, a, b, e, f, g, k⟩ := h
    have hs := hb.1.1.S
    exact ⟨hs, a, b, e, f, g, k, md, by rw [kdkV_length]; decide,
      { hlen := by omega_using [hl, htl]
        cd := Covers.right (St.cov_sr hs (by decide) (by simp only [sMsg]; omega_using [hl, htl]))
        d_st := hs.1.sr_sep (by simp only [sMsg, sSt]; omega_using []) (by decide) (by decide)
          (by simp only [sMsg]; omega_using [hl, htl]) (by decide)
        d_sc := hs.1.sr_sep (by simp only [sMsg, sW]; omega_using [hl, htl]) (by decide) (by decide)
          (by simp only [sMsg]; omega_using [hl, htl]) (by decide)
        b_d := hs.1.below_sr (by decide) (by decide) (by simp only [sMsg]; omega_using [hl, htl])
        nd := hs.1.sr_fit (by decide) (by simp only [sMsg]; omega_using [hl, htl]) }⟩
  · obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1.1.S
    have hi := hb.1.1.hi
    obtain ci := hb.1.1.call c (by decide) updWs_scr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega_using [this]))
          (.inl (by have := R.dst_lo; simp only [sSt]; omega_using [this])) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega_using [this]))
          (.inr (by have := R.dst_hi; simp only [sW]; omega_using [hi, this])) hi
    refine ⟨⟨ci.1, by rw [ci.2]; exact hb.1.2⟩, ?_⟩
    obtain e : Spec.Rsa.bytesAt s.mem ((P.scr + BitVec.ofNat 32 sMsg).setWidth 64) R.tl = msgV i R.lab R.L := by
      rw [show (P.scr + BitVec.ofNat 32 sMsg).setWidth 64 = (sc P sMsg R.tl).base from hs.1.scrA (by decide)]
      exact hb.2
    rw [e] at md
    exact md

theorem add_self_ofNat (n : Nat) : BitVec.ofNat 32 n + BitVec.ofNat 32 n = BitVec.ofNat 32 (2 * n) := by
  rw [BitVec.ofNat_add_ofNat, Nat.two_mul]

theorem finArgs_vp (cert : TaintOk [.esp] (.block (prfFinArgs R.tl R.dst))) :
    VP (B6 P R i) (.block (prfFinArgs R.tl R.dst)) (B7 P R i) :=
  VP.taint [.esp] cert (sp_agree fun _ _ h => h.1.1.S) fun σ s h => by
    have hs := h.1.1.S
    have hi := h.1.1.hi
    have := R.nb_le
    have := R.dst_hi
    simp only [prfFinArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edx) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) (64 + R.tl) fun t3 s3 u3 => ?_
    refine St.movi s3 (d := .ecx) (by decide) 0 fun t4 s4 u4 => ?_
    refine s4.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .edi) (by decide)
      fun t5 st5 u5 => ?_
    refine wp_add fun t6 u6 _ => ?_
    refine wp_add fun t7 u7 _ => ?_
    refine wp_add fun t8 u8 _ => ?_
    refine wp_add fun t9 u9 _ => ?_
    refine wp_add fun t10 u10 _ => ?_
    obtain s10 : S P σ t10 := ⟨hs.1, ((((st5.upd u6 (by decide)).upd u7 (by decide)).upd u8 (by decide)).upd u9
      (by decide)).upd u10 (by decide)⟩
    refine wp_addS (s10.2.readArg (j := 21) (by simp)) fun t11 u11 _ => ?_
    refine wp_addi fun t12 u12 => ?_
    obtain s12 : S P σ t12 := ⟨hs.1, (s10.2.upd u11 (by decide)).upd u12 (by decide)⟩
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s12 (d := .ebp) (by decide) sW fun t13 s13 u13 => WP.block_nil ?_
    obtain mm : t13.mem = s.mem := by
      rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
        u1.mem]
    obtain m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨h.1.1.of_mem s13.2 mm, by rw [mm]; exact h.1.2⟩, by rw [mm]; exact h.2⟩, ?_⟩
    obtain di : t13.gpr .edi = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) := by
      rw [u13.other _ (by decide), u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, m4, h.1.2]
      simp only [add_self_ofNat, EP.argv, List.getD_cons_succ, List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using []
    refine ⟨?_, ?_, ?_, ?_, di, ?_⟩
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.other, u2.other, u1.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.other, u2.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.gpr]; rfl
    · exact u13.gpr

theorem fin_vp (v : Backend) (hi : i < R.nb) : VP (B7 P R i) (callHf v.F) (B8 P R i) := by
  have hd := R.dst_hi
  have hd' := R.dst_lo
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  refine macFin_vp (P := P) v (o := R.dst + 32 * i) (tl := R.tl) (key := fun σ _ => kdkV P σ)
    (text := fun _ _ => msgV i R.lab R.L) (by omega_using [hd']) (by omega_using [hi, hd])
    (fun _ _ h => ?_) fun σ s t h c hk => ?_
  · obtain ⟨⟨hb, md⟩, a, b, e, f, g, k⟩ := h
    exact ⟨hb.1.S, a, b, e, f, g, k, md, by rw [kdkV_length]; decide, by rw [msgV_length]; simp, by omega_using [hl, htl]⟩
  · obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1.S
    have hx := R.x_sep
    obtain ci := hb.1.call c (by decide) (hfWs_scr (by omega_using [hi, hd])) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega_using [this]))
          (.inl (by simp only [sSt]; omega_using [hd'])) hb.1.hi
      · exact hs.1.keep_sr (by omega_using [hi, hd]) (by omega_using [hi, hd]) (.inr (by simp only [sKDK]; omega_using [hd']))
          (by rcases hx with hx | hx
              · exact .inr (by omega_using [hx])
              · exact .inl (by omega_using [hi, hx])) (.inr (by omega_using [])) hb.1.hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega_using [this]))
          (.inr (by simp only [sW]; omega_using [hi, hd])) hb.1.hi
    have c' := ci.1
    refine ⟨⟨by omega_using [hi], c'.base, c'.kdk, c'.x, c'.sNB, ?_⟩, by rw [ci.2]; exact hb.2⟩
    rw [show 32 * (i + 1) = 32 * i + 32 by omega_using [], bytesAt_add, c'.blk, Offset.add_add, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]
    refine congrArg _ ?_
    rw [hs.1.sr_eq (by omega_using [hi, hd])] at hk
    exact hk

/-- The counter incremented, and whether there is another block, `n` left after this one. -/
theorem incr_vp {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B8 P R i) (.block incr) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) :=
  VP.taint [.esp] incr_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    obtain ⟨hc, sI⟩ := h
    have hs := hc.S
    have hnb := R.nb_le
    simp only [incr]
    refine hs.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t1 st1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    obtain st2 := st1.upd u2 (by decide)
    refine st2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t3 st3 m3 => ?_
    refine wp_cmpS (st3.readSlot (d := oNB) (by show oNB + 4 ≤ frameBytes; decide)) fun t4 u4 hz => WP.block_nil ?_
    obtain st4 : P.lay.St σ t4 := st3.fupd u4
    obtain ax : t2.gpr .eax = BitVec.ofNat 32 (i + 1) := by
      rw [u2.gpr, u1.gpr, sI]; exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 i
    obtain mm : t4.mem = s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 (i + 1)) := by
      rw [u4.mem, m3.mem, ax, u2.mem, u1.mem]
    obtain fr : Frame [⟨P.lay.fr oI, 4⟩] s.mem t4.mem := by
      rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain hc' := hc.keep st4 fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.1.keep_fr (by decide) (by simp only [oR, oI]; decide) (by simp only [oNB, oI]; decide) hc.hi
    obtain nb : t3.mem.readW (P.lay.fr oNB) 32 = BitVec.ofNat 32 R.nb := by
      rw [← u4.mem]; exact hc'.sNB
    rw [m3.gpr, ax, nb, sub_beq_zero (by omega_using [hn, hnb]) (by omega_using [hnb])] at hz
    obtain e : (!decide (i + 1 = R.nb)) = decide (0 < n) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [decide_eq_true (by omega_using [hn, h0] : i + 1 = R.nb), decide_eq_false (by omega_using [h0] : ¬ 0 < n)]; rfl
      · rw [decide_eq_false (by omega_using [hn, h0] : ¬ i + 1 = R.nb), decide_eq_true h0]; rfl
    refine ⟨by show eval .ne t4 = _; simp only [eval, hz]; rw [← e]; rfl, fun h0 => ?_, fun h0 => ?_⟩
    · rw [show R.nb = i + 1 by omega_using [hn, h0]]; exact hc'
    · refine ⟨by omega_using [hn], ?_⟩
      rw [show R.nb - n = i + 1 by omega_using [hn]]
      exact ⟨hc', by rw [mm, Mem.readW_writeW_self32]⟩

/-- The certificates of the taint analysis a loop needs. -/
structure Certs (R : Prf P) : Prop where
  msg : TaintOk [.ebx] (.block (msgBytes R.vs R.len))
  upd : TaintOk [.esp] (.block (prfUpdArgs R.tl))
  fin : TaintOk [.esp] (.block (prfFinArgs R.tl R.dst))

theorem prfBody_vp (v : Backend) (ce : Certs R) {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B0 P R i) (prfBody v.F R.vs R.len R.dst) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) := by
  have hnb := R.nb_le
  exact (msgPtr_vp.block_append (msg_vp ce.msg (by omega_using [hn, hnb]))).seq (initArgs_vp.seq ((init_vp v).seq
    ((updArgs_vp ce.upd).seq ((upd_vp v).seq ((finArgs_vp ce.fin).seq ((fin_vp v (by omega_using [hn])).seq
      (incr_vp hn)))))))

/-- A piece no state reaches. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  VP.of_ct (fun _ _ _ _ _ _ _ _ hh => absurd hh.1 (h _ _)) fun σ s hs => absurd hs (h σ s)

/-- The loop, from block 0. -/
theorem loop_vp (v : Backend) (ce : Certs R) :
    VP (B0 P R 0) (.loop (prfBody v.F R.vs R.len R.dst) .ne) (CI P R R.nb) := by
  have h1 := R.nb1
  refine (VP.loop (I := LI P R) (fun n => ?_) (R.nb - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  · by_cases hn : n + 1 ≤ R.nb
    · exact (prfBody_vp (i := R.nb - (n + 1)) v ce (by omega_using [hn])).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact VP.of_false fun _ _ h => hn h.1
  · refine ⟨by omega_using [h1], ?_⟩
    rw [show R.nb - (R.nb - 1 + 1) = 0 by omega_using []]; exact h

end

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: `CL` and `AM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecIrprf.lean`): the two IRPRF loops
(`Prf`): `CL = IRPRF(KDK, "length", 256)` at `scratch + sCL`
(`clLoop_vp`), keeping `KDK`, and `AM = IRPRF(KDK, "message", k)` at
`scratch + sAM` (`amLoop_vp`), keeping `CL` (`IR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = lengthLabel.map (BitVec.ofNat 8) := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = messageLabel.map (BitVec.ofNat 8) := by decide

/-- `CL`. -/
abbrev clV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "length") 256

/-- `AM`. -/
abbrev amV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "message") P.K

/-- The loop of `CL`, keeping `KDK`. -/
def RCL (P : EP) : Prf P where
  vs := lengthLabel
  len := clLen
  L := 256
  dst := sCL
  nb := 8
  xo := sKDK
  xn := 32
  xv := kdkV P
  vs_len := by decide
  nb1 := by decide
  nb_le := by decide
  dst_lo := by decide
  dst_hi := by decide
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ bx _ h _ k => clLen_wp rfl bx h k

/-- `CL`'s blocks. -/
abbrev clBlocks (P : EP) (σ : State) : List Byte :=
  (List.range 8).flatMap (prfBlock (kdkV P σ) (lengthLabel.map (BitVec.ofNat 8)) 256)

/-- The loop of `AM`, keeping `CL`, for `64 ≤ k ≤ 1024`. -/
def RAM (P : EP) (hK : 64 ≤ P.K ∧ P.K ≤ 1024) : Prf P where
  vs := messageLabel
  len := amLen
  L := P.K
  dst := sAM
  nb := (P.K + 31) / 32
  xo := sCL
  xn := 256
  xv := clBlocks P
  vs_len := by decide
  nb1 := by omega_using [hK]
  nb_le := by omega_using [hK]
  dst_lo := by decide
  dst_hi := by simp only [sAM]; omega_using [hK]
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ bx dx h _ k => amLen_wp rfl hK.2 bx dx h k

theorem certsCL : Certs (RCL P) := ⟨msgCL_taint, prfUpdCL_taint, prfFinCL_taint⟩

theorem certsAM {hK : 64 ≤ P.K ∧ P.K ≤ 1024} : Certs (RAM P hK) := ⟨msgAM_taint, prfUpdAM_taint, prfFinAM_taint⟩

/-- `mov eax, 0; mov [oI], eax`, then the number of blocks `nb` (from `is`)
to its slot: the counter's and the number's slots written. -/
theorem slots_frame {s t : State} {nb : Nat}
    (h : t.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB) (BitVec.ofNat 32 nb)) :
    Frame [⟨P.lay.fr oI, 4⟩, ⟨P.lay.fr oNB, 4⟩] s.mem t.mem := by
  rw [h]
  exact ((Frame.refl _ _).writeW List.mem_cons_self (BitVec.ofNat 32 0) (Region.contains_self _ _)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) (BitVec.ofNat 32 nb) (Region.contains_self _ _)

/-- The loop starts: what it keeps, and the slots. -/
theorem b0_start {R : Prf P} {σ s t : State} (hb : Base P σ s) (st : P.lay.St σ t)
    (hk : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ)
    (hx : Spec.Rsa.bytesAt s.mem (sc P R.xo R.xn).base R.xn = R.xv σ)
    (h : t.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB) (BitVec.ofNat 32 R.nb)) :
    B0 P R 0 σ t := by
  have hs := hb.1
  obtain fr := slots_frame h
  obtain sd : ∀ r ∈ [(⟨P.lay.fr oI, 4⟩ : Region), ⟨P.lay.fr oNB, 4⟩],
      Safe P r ∧ (sc P sKDK 32).Disjoint r ∧ (sc P R.xo R.xn).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oI]; decide),
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by have := R.x_hi; omega_using [this])).symm⟩
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oNB]; decide),
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by have := R.x_hi; omega_using [this])).symm⟩
  refine ⟨⟨Nat.zero_le _, hb.frame st fr fun r hr => (sd r hr).1,
    (Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => (sd r hr).2.1) (by decide)).trans hk,
    (Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => (sd r hr).2.2) (by have := R.x_hi; omega_using [this])).trans hx,
    ?_, by simp [Spec.Rsa.bytesAt]⟩, ?_⟩
  · rw [h, Mem.readW_writeW_self32]
  · rw [h, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem clInit_vp : VP (K6 P) (.block clInit) (B0 P (RCL P) 0) :=
  VP.taint [.esp] clInit_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    obtain ⟨hb, kd⟩ := h
    have hs := hb.1
    simp only [clInit]
    refine St.movi hs (d := .eax) (by decide) 0 fun t1 s1 u1 => ?_
    refine s1.2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t2 st2 m2 => ?_
    refine St.movi ⟨hs.1, st2⟩ (d := .eax) (by decide) 8 fun t3 s3 u3 => ?_
    refine s3.2.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) fun t4 st4 m4 => WP.block_nil ?_
    obtain kd' : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ := by
      rw [← hs.1.sr_eq (by decide)]; exact kd
    exact b0_start (R := RCL P) hb st4 kd' kd' (by rw [m4.mem, u3.gpr, u3.mem, m2.mem, u1.gpr, u1.mem]; rfl)

theorem nb_val {K : Nat} (hK : K ≤ 1024) :
    (BitVec.ofNat 32 K + BitVec.ofNat 32 31) >>> 5 = BitVec.ofNat 32 ((K + 31) / 32) := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hK]

theorem amInit_vp (hK : 64 ≤ P.K ∧ P.K ≤ 1024) : VP (CI P (RCL P) 8) (.block amInit) (B0 P (RAM P hK) 0) :=
  VP.taint [.esp] amInit_taint (sp_agree fun _ _ h => h.S) fun σ s h => by
    have hs := h.S
    simp only [amInit]
    refine St.movi hs (d := .eax) (by decide) 0 fun t1 s1 u1 => ?_
    refine s1.2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t2 st2 m2 => ?_
    refine St.argv ⟨hs.1, st2⟩ (j := 4) (by decide) (d := .eax) (by decide) fun t3 s3 u3 => ?_
    refine wp_addi fun t4 u4 => ?_
    refine wp_shr (n := 5) (by decide) fun t5 u5 _ => ?_
    obtain st5 := (s3.2.upd u4 (by decide)).upd u5 (by decide)
    refine st5.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) fun t6 st6 m6 => WP.block_nil ?_
    obtain ax : t5.gpr .eax = BitVec.ofNat 32 ((P.K + 31) / 32) := by
      rw [u5.gpr, u4.gpr, u3.gpr]; exact nb_val hK.2
    refine b0_start (R := RAM P hK) h.base st6 h.kdk h.blk ?_
    rw [m6.mem, ax, u5.mem, u4.mem, u3.mem, m2.mem, u1.gpr, u1.mem]; rfl

/-! ## The loops -/

/-- `CL` and `AM` in `scratch`. -/
def IR (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sCL 256).base 256 = clV P σ ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ

theorem flatMap_blocks_length (kd lab : List Byte) (L : Nat) :
    ∀ n, ((List.range n).flatMap (prfBlock kd lab L)).length = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_blocks_length kd lab L n,
      List.flatMap_singleton, prfBlock, hmac_len]
    omega_using []

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem clV_eq (P : EP) (σ : State) : clV P σ = clBlocks P σ := by
  rw [clV, Proof.RsaPkcs1Enc.irprf_eq, ascii_length]
  exact List.take_of_length_le (by rw [flatMap_blocks_length])

theorem ir_of {σ s : State} {hK : 64 ≤ P.K ∧ P.K ≤ 1024} (h : CI P (RAM P hK) ((P.K + 31) / 32) σ s) :
    IR P σ s := by
  refine ⟨h.base, by rw [clV_eq]; exact h.x, ?_⟩
  have hb := h.blk
  simp only [RAM] at hb
  rw [amV, Proof.RsaPkcs1Enc.irprf_eq, ascii_message, ← hb, ← bytesAt_take _ _ (by omega_using [])]

theorem clLoop_vp (v : Backend) : VP (K6 P) (clLoop v.F) (CI P (RCL P) 8) :=
  clInit_vp.seq (loop_vp (R := RCL P) v certsCL)

theorem amLoop_vp (v : Backend) : VP (CI P (RCL P) 8) (amLoop v.F) (IR P) := by
  by_cases hK : 64 ≤ P.K ∧ P.K ≤ 1024
  · exact (amInit_vp hK).seq ((loop_vp (R := RAM P hK) v certsAM).mono (fun _ _ h => h) fun _ _ h => ir_of h)
  · exact VP.of_false fun _ _ h => hK ⟨h.S.1.k64, h.S.1.k1024⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: the alternative length

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecAl.lean`): the mask of the
candidates, `2^bitLength(k - 11) - 1`, by doublings (`maskLoop_vp`), and
`AL`, the last candidate not above `k - 11`, a fold over the 128 candidates
of `CL` (`alLoop_vp`), to its slot (`alPart_vp`, `AL`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_subS)
open VG.Proof.Pbkdf2.Stream.X86 (wp_xori)
open VG.Proof.RsaPkcs1Enc (bitMask altStep)
open VG.Spec.RsaPkcs1Enc (bitLength)

variable {P : EP}

/-! ## Memory kept -/

theorem IR.of_mem {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : IR P σ t :=
  ⟨h.1.regs st hm, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem IR.keep_fr {σ s t : State} (h : IR P σ s) (st : P.lay.St σ t) {d : Nat} {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) (hd : d + 4 ≤ frameBytes) (ho : d + 4 ≤ oR ∨ oR + 4 ≤ d) :
    IR P σ t := by
  have hs := h.1.1
  have hK := hs.1.k1024
  obtain fr : Frame [⟨P.lay.fr d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  obtain hd' : d + 4 ≤ frameBytes + 16 := by omega_using [hd]
  refine ⟨h.1.frame st fr fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr hd ho
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hs.1.fr_sc hd' (by decide)).symm) (by decide)]
    exact h.2.1
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.1.fr_sc hd' (by simp only [sAM]; omega_using [hK])).symm) (by omega_using [hK])]
    exact h.2.2

/-! ## The mask -/

/-- The mask `2^j - 1` (`eax`), and `k - 11` (`ecx`). -/
def MI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .eax = BitVec.ofNat 32 (2 ^ j - 1) ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - 11)

/-- The mask. -/
def MK (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .eax = BitVec.ofNat 32 (bitMask (P.K - 11)) ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - 11)

theorem maskInit_vp : VP (IR P) (.block maskInit) (MI P 0) :=
  VP.taint [.esp] maskInit_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    have hK := hs.1.k64
    simp only [maskInit]
    refine St.argv hs (j := 4) (by decide) (d := .ecx) (by decide) fun t1 s1 u1 => ?_
    refine wp_subi fun t2 u2 _ _ => ?_
    obtain s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => WP.block_nil ?_
    refine ⟨h.of_mem s3.2 (by rw [u3.mem, u2.mem, u1.mem]), u3.gpr, ?_⟩
    rw [u3.other _ (by decide), u2.gpr, u1.gpr]
    exact Offset.ofNat_sub_ofNat (d := 11) (by omega_using [hK])

/-- The loop's stage, `m` doublings left. -/
def MLI (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ bitLength (P.K - 11) ∧ MI P (bitLength (P.K - 11) - m) σ s

theorem bitLength_le {x : Nat} (hx : x ≠ 0) (hx' : x < 2 ^ 30) : 2 ^ bitLength x - 1 < 2 ^ 31 := by
  have := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  simp only [bitMask] at this
  omega_using [hx', this]

theorem maskBody_vp (n : Nat) : VP (MLI P (n + 1)) (.block maskBody) fun σ s =>
    isa.eval .b s = some (decide (0 < n)) ∧ (n = 0 → MK P σ s) ∧ (0 < n → MLI P n σ s) := by
  refine VP.taint [.eax, .ecx] maskBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  obtain ⟨hn, hir, ax, cx⟩ := h
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  obtain hx : P.K - 11 ≠ 0 := by omega_using [hK]
  generalize hB : bitLength (P.K - 11) = B at hn ax
  obtain hj : B - (n + 1) < bitLength (P.K - 11) := by omega_using [hB, hn]
  obtain hlt := VG.Proof.RsaPkcs1Enc.bitMask_lt hx hj
  obtain hst := VG.Proof.RsaPkcs1Enc.bitMask_step (by omega_using [hK] : 1 ≤ P.K - 11) hlt
  obtain hp : 2 ^ (B - (n + 1) + 1) - 1 ≤ 2 ^ B - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega_using [hn])) _
  obtain hB31 : 2 ^ B - 1 < 2 ^ 31 := by rw [← hB]; exact bitLength_le hx (by omega_using [hK'])
  simp only [maskBody]
  refine wp_add fun t1 u1 _ => ?_
  refine wp_addi fun t2 u2 => ?_
  refine wp_cmp fun t3 u3 hc _ => WP.block_nil ?_
  obtain ax2 : t2.gpr .eax = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by
    rw [u2.gpr, u1.gpr, ax, ← hst.1]
    apply BitVec.eq_of_toNat_eq
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e1]
    omega_using []
  obtain cx2 : t2.gpr .ecx = BitVec.ofNat 32 (P.K - 11) := by
    rw [u2.other _ (by decide), u1.other _ (by decide), cx]
  obtain st : P.lay.St σ t3 := ((hs.2.upd u1 (by decide)).upd u2 (by decide)).fupd u3
  obtain ir := hir.of_mem st (by rw [u3.mem, u2.mem, u1.mem])
  obtain e : (2 ^ (B - (n + 1) + 1) - 1 < P.K - 11) = (0 < n) := by
    apply propext; constructor
    · intro h; by_contra h0
      have := VG.Proof.RsaPkcs1Enc.bitMask_ge hx
      rw [hB] at this
      rw [show B - (n + 1) + 1 = B by omega_using [hn, h0]] at h
      omega_using [cx, hK, hK', hx, hB, hn, ax, hj, hlt, hst, hp, hB31, ax2, cx2, h, h0, this]
    · intro h0
      exact VG.Proof.RsaPkcs1Enc.bitMask_lt hx (by omega_using [hB, hn, h0])
  rw [ax2, cx2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hK', hlt]),
    Nat.mod_eq_of_lt (by omega_using [hK'])] at hc
  obtain ax3 : t3.gpr .eax = BitVec.ofNat 32 (2 ^ (B - (n + 1) + 1) - 1) := by rw [u3.gpr, ax2]
  obtain cx3 : t3.gpr .ecx = BitVec.ofNat 32 (P.K - 11) := by rw [u3.gpr, cx2]
  refine ⟨by show eval .b t3 = _; simp only [eval, hc, e], fun h0 => ⟨ir, ?_, cx3⟩,
    fun h0 => ⟨by omega_using [hB, hn], ir, ?_, cx3⟩⟩
  · rw [ax3, show B - (n + 1) + 1 = B by omega_using [hn, h0], ← hB]; rfl
  · rw [ax3, show B - (n + 1) + 1 = B - n by omega_using [hn], hB]

theorem maskLoop_vp : VP (MI P 0) maskLoop (MK P) := by
  refine (VP.loop (I := MLI P) maskBody_vp (bitLength (P.K - 11) - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.1.1.k64
  have : 1 ≤ bitLength (P.K - 11) := by
    simp only [bitLength, show P.K - 11 ≠ 0 by omega_using [hK], ↓reduceIte]; omega_using []
  refine ⟨by omega_using [this], ?_⟩
  rw [show bitLength (P.K - 11) - (bitLength (P.K - 11) - 1 + 1) = 0 by omega_using []]; exact h

/-! ## The candidates -/

theorem altStep_and (K : Nat) (CL : List Byte) (al i : Nat) :
    altStep K CL al i =
      (let c := (256 * (CL.getD (2 * i) 0).toNat + (CL.getD (2 * i + 1) 0).toNat) &&& bitMask (K - 11);
        if c ≤ K - 11 then c else al) := by
  simp only [altStep, VG.Proof.RsaPkcs1Enc.cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod]

theorem byte_rotate (b : BitVec 8) : (b.setWidth 32).rotateRight 24 = b.setWidth 32 <<< 8 := by
  obtain hz : b.setWidth 32 >>> 24 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    change b.toNat % 2 ^ 32 / 2 ^ 24 = 0
    omega_using []
  rw [BitVec.rotateRight_def, hz]
  exact BitVec.zero_or

theorem cand_bv (b0 b1 : Byte) :
    (b0.setWidth 32).rotateRight 24 ||| b1.setWidth 32 = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
  have h0 := b0.isLt
  have h1 := b1.isLt
  rw [byte_rotate]
  obtain hz : (b0.setWidth 32 <<< 8) &&& b1.setWidth 32 = 0 := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
    by_cases h : i < 8
    · simp [h]
    · simp only [h, decide_false, Bool.not_false, Bool.true_and]
      rw [BitVec.getLsbD_of_ge b1 i (by omega_using [h])]; simp
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

theorem sel_bv (a c : BitVec 32) (p : Bool) :
    a ^^^ ((c ^^^ a) &&& ((if p then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32)) = if p then a else c := by
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_xor,
      BitVec.and_allOnes, BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [↓reduceIte]
    rw [BitVec.xor_self, BitVec.and_zero, BitVec.xor_zero]

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
  by_cases h : n = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 n ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
      exact h this
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- The fold of the first `j` candidates. -/
abbrev alFold (P : EP) (σ : State) (j : Nat) : Nat := (List.range j).foldl (altStep P.K (clV P σ)) 0

/-- Before candidate `j`. -/
def ALI (P : EP) (j : Nat) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 (sCL + 2 * j) ∧
    s.gpr .edi = BitVec.ofNat 32 (bitMask (P.K - 11)) ∧ s.gpr .ebp = BitVec.ofNat 32 (P.K - 11) ∧
    s.gpr .ebx = BitVec.ofNat 32 (alFold P σ j) ∧ s.gpr .ecx = BitVec.ofNat 32 (128 - j)

/-- `AL` in `ebx`. -/
def ALQ (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.gpr .ebx = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

/-- `AL` in its slot. -/
def AL (P : EP) (σ s : State) : Prop :=
  IR P σ s ∧ s.mem.readW (P.lay.fr oAL) 32 = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength P.K (clV P σ))

theorem alInit_vp : VP (MK P) (.block alInit) (ALI P 0) :=
  VP.taint [.esp] alInit_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    obtain ⟨hir, ax, cx⟩ := h
    have hs := hir.1.1
    simp only [alInit]
    refine St.scrW hs (d := .esi) (by decide) sCL fun t1 s1 u1 => ?_
    refine wp_mov fun t2 u2 => ?_
    refine wp_mov fun t3 u3 => ?_
    obtain s3 : S P σ t3 := ⟨hs.1, (s1.2.upd u2 (by decide)).upd u3 (by decide)⟩
    refine St.movi s3 (d := .ebx) (by decide) 0 fun t4 s4 u4 => ?_
    refine St.movi s4 (d := .ecx) (by decide) 128 fun t5 s5 u5 => WP.block_nil ?_
    refine ⟨hir.of_mem s5.2 (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]), ?_, ?_, ?_, ?_, ?_⟩
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
      rfl
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
        u1.other _ (by decide), ax]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), cx]
    · rw [u5.other _ (by decide), u4.gpr]; rfl
    · rw [u5.gpr]

/-- `m` candidates left. -/
def ALM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ 128 ∧ ALI P (128 - m) σ s

/-- Byte `i` of `CL`. -/
theorem cl_byte {σ s : State} (h : IR P σ s) {i : Nat} (hi : i < 256) :
    s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + i)) = (clV P σ).getD i 0 := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_getD hi, Offset.add_add]

theorem alBody_vp (n : Nat) : VP (ALM P (n + 1)) (.block alBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → ALQ P σ s) ∧ (0 < n → ALM P n σ s) := by
  refine VP.taint [.esi, .ecx] alBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2]
  obtain ⟨hn, hir, si, di, bp, bx, cx⟩ := h
  generalize hj : 128 - (n + 1) = j at si bx cx
  obtain hjn : j + n + 1 = 128 := by omega_using [hn, hj]
  have hs := hir.1.1
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  obtain hx : P.K - 11 ≠ 0 := by omega_using [hK]
  obtain hm := VG.Proof.RsaPkcs1Enc.bitMask_le hx
  obtain ha : ∀ d < 2, s.ea ⟨.esi, d⟩ = P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + d)) := by
    intro d hd
    rw [ea_at, si, hs.1.addrSc (by simp only [sCL]; omega_using [hj, hd]), Nat.add_assoc]
  obtain e0 := cl_byte hir (i := 2 * j + 0) (by omega_using [hj])
  obtain e1 := cl_byte hir (i := 2 * j + 1) (by omega_using [hj])
  simp only [alBody]
  refine wp_movzx8 (ha 0 (by decide)) (St.sc_r hs (by simp only [sCL]; omega_using [hj])) fun t1 u1 => ?_
  refine wp_ror (n := 24) (by decide) fun t2 u2 => ?_
  refine wp_movzx8 (a := P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + 1)))
    (by rw [ea_at, u2.other _ (by decide), u1.other _ (by decide), ← ea_at]; exact ha 1 (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sCL]; omega_using [hj])) fun t3 u3 => ?_
  refine wp_or fun t4 u4 => ?_
  refine wp_and fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => ?_
  refine wp_subS (readSrc_reg _ _) fun t7 u7 c7 => ?_
  refine wp_sbb_self c7 fun t8 u8 => ?_
  refine wp_xori fun t9 u9 => ?_
  refine wp_xor fun t10 u10 => ?_
  refine wp_and fun t11 u11 => ?_
  refine wp_xor fun t12 u12 => ?_
  refine wp_addi fun t13 u13 => ?_
  refine wp_subi fun t14 u14 _ hz => WP.block_nil ?_
  obtain mm : t14.mem = s.mem := by
    rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
      u2.mem, u1.mem]
  obtain st : P.lay.St σ t14 := hs.2.regs (by rw [u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd,
      u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]) mm
  generalize hb0 : (clV P σ).getD (2 * j) 0 = b0 at e0
  generalize hb1 : (clV P σ).getD (2 * j + 1) 0 = b1 at e1
  generalize hc : (256 * b0.toNat + b1.toNat) &&& bitMask (P.K - 11) = c
  obtain hcm : c ≤ bitMask (P.K - 11) := hc ▸ Nat.and_le_right
  obtain c4 : t4.gpr .eax = BitVec.ofNat 32 (256 * b0.toNat + b1.toNat) := by
    rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.gpr, u3.gpr, u2.mem, u1.mem, e1]
    rw [show s.mem (P.scr.setWidth 64 + BitVec.ofNat 64 (sCL + (2 * j + 0))) = b0 from e0]
    exact cand_bv _ _
  obtain c5 : t5.gpr .eax = BitVec.ofNat 32 c := by
    rw [u5.gpr, c4, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), di, ← hc, BitVec.ofNat_and]
  obtain dp6 : t6.gpr .edx = BitVec.ofNat 32 (P.K - 11) := by
    rw [u6.gpr]; simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other]; exact bp
  rw [dp6, u6.other _ (by decide), c5, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hK']),
    Nat.mod_eq_of_lt (by omega_using [hK', hm, hcm])] at c7
  obtain bx11 : t11.gpr .ebx = BitVec.ofNat 32 (alFold P σ j) := by
    simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other,
      u4.other, u3.other, u2.other, u1.other]; exact bx
  obtain cnd : decide ((t6.gpr .edx).toNat < (t6.gpr .eax).toNat) = decide (P.K - 11 < c) := by
    rw [dp6, u6.other _ (by decide), c5, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hK']),
      Nat.mod_eq_of_lt (by omega_using [hK', hm, hcm])]
  obtain ax9 : t10.gpr .eax = BitVec.ofNat 32 c ^^^ BitVec.ofNat 32 (alFold P σ j) := by
    rw [u10.gpr]
    simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other]
    rw [c5]
    simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [bx]
  obtain dx10 : t10.gpr .edx = (if decide (P.K - 11 < c) then BitVec.allOnes 32 else 0) ^^^ BitVec.allOnes 32 := by
    rw [u10.other _ (by decide), u9.gpr, u8.gpr, cnd]
  obtain c12 : t12.gpr .ebx = if decide (P.K - 11 < c) then BitVec.ofNat 32 (alFold P σ j) else BitVec.ofNat 32 c := by
    rw [u12.gpr, u11.gpr, ax9, dx10, bx11]
    exact sel_bv _ _ _
  obtain fold : alFold P σ (j + 1) = if P.K - 11 < c then alFold P σ j else c := by
    rw [alFold, VG.Proof.RsaPkcs1Enc.foldl_range_succ, altStep_and]
    simp only [hb0, hb1, hc]
    by_cases h : P.K - 11 < c
    · simp [h, show ¬ c ≤ P.K - 11 by omega_using [h]]
    · simp [h, show c ≤ P.K - 11 by omega_using [h]]
  obtain bxt : t14.gpr .ebx = BitVec.ofNat 32 (alFold P σ (j + 1)) := by
    rw [u14.other _ (by decide), u13.other _ (by decide), c12, fold]
    by_cases h : P.K - 11 < c <;> simp [h]
  obtain cx13 : t13.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
      u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [cx, show 128 - j = n + 1 by omega_using [hn, hj]]
  obtain cxt : t14.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u14.gpr, cx13]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_using [])
  obtain ir := hir.of_mem st mm
  refine ⟨?_, fun h0 => ⟨ir, ?_⟩, fun h0 => ⟨by omega_using [hn], ir, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show eval .ne t14 = _
    rw [cx13, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega_using []), ofNat_beq_zero (by omega_using [hn])] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_using [h0]
  · rw [bxt, show j + 1 = 128 by omega_using [hj, h0]]; rfl
  · rw [u14.other _ (by decide), u13.gpr]
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [si, BitVec.add_assoc, show 128 - n = j + 1 by omega_using [hn, hj]]
    refine congrArg (P.scr + ·) ?_
    apply BitVec.eq_of_toNat_eq
    have e2 : (2 : BitVec 32).toNat = 2 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e2]
    omega_using []
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]; exact di
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]; exact bp
  · rw [bxt, show 128 - n = j + 1 by omega_using [hn, hj]]
  · rw [cxt, show 128 - (128 - n) = n by omega_using [hn]]

theorem alLoop_vp : VP (ALI P 0) alLoop (ALQ P) :=
  (VP.loop (I := ALM P) alBody_vp 127).mono (fun _ _ h => ⟨by decide, h⟩) fun _ _ h => h

theorem alSave_vp : VP (ALQ P) (.block alSave) (AL P) :=
  VP.taint [.esp] alSave_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    obtain ⟨hir, bx⟩ := h
    have hs := hir.1.1
    refine hs.2.wp_strFr (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) fun t1 st1 m1 => WP.block_nil ?_
    exact ⟨hir.keep_fr st1 m1.mem (by decide) (by simp only [oR, oAL]; decide),
      by rw [m1.mem, Mem.readW_writeW_self32, bx]⟩

theorem alPart_vp : VP (IR P) alPart (AL P) :=
  maskInit_vp.seq (maskLoop_vp.seq (alInit_vp.seq (alLoop_vp.seq alSave_vp)))

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: the scan of `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecScan.lean`): what `out` holds after
the private-key operation (`emOf`: `EM`, or zeros for an error) and the
call's result (`rcOf`). The scan of `EM` from index 2 for its first zero
(`scanLoop_vp`): whether there is one, as a mask (`mk`), and where
(`Proof.RsaPkcs1Enc.firstZero`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Pbkdf2.Stream.X86 (wp_xori)
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {P : EP}

/-! ## `out` and the result after the call -/

/-- `out` after the call: `EM`, or zeros. -/
def emOf (P : EP) (σ : State) : List Byte :=
  match privO P σ with
  | .ok y => y
  | _ => List.replicate P.K 0

/-- The call's result. -/
def rcOf (P : EP) (σ : State) : BitVec 32 :=
  match privO P σ with
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

theorem Priv.em {σ : State} {m : Mem} {rc : BitVec 32} (h : Priv P σ m rc) :
    Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = emOf P σ ∧ rc = rcOf P σ := by
  unfold Priv at h
  unfold emOf rcOf
  generalize privO P σ = o at h ⊢
  cases o <;> exact ⟨h.2, h.1⟩

theorem rcOf_cases (P : EP) (σ : State) : rcOf P σ = 1 ∨ rcOf P σ = 0 ∨ rcOf P σ = 2 := by
  unfold rcOf; split <;> simp

/-- `out`, the result in its slot, and `AL` in its slot. -/
def SB (P : EP) (σ s : State) : Prop :=
  AL P σ s ∧ Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = emOf P σ ∧
    s.mem.readW (P.lay.fr oR) 32 = rcOf P σ

theorem AL.sb {σ s : State} (h : AL P σ s) : SB P σ s := by
  obtain ⟨rc, pr, sl⟩ := h.1.1.2
  obtain e := Priv.em pr
  exact ⟨h, e.1, by rw [sl, e.2]⟩

theorem emOf_length {σ s : State} (h : SB P σ s) : (emOf P σ).length = P.K := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_len]

theorem SB.of_mem {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : SB P σ t :=
  ⟨⟨h.1.1.of_mem st hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem SB.S {σ s : State} (h : SB P σ s) : S P σ s := h.1.1.1.1

/-! ## Addresses in `out` -/

namespace In
variable {σ : State} (h : In P σ)
include h

theorem out_fit : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := h.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at this

theorem outA {i d : Nat} (hi : i + d < P.K) : addr (P.out + BitVec.ofNat 32 i) d = P.out.setWidth 64 + BitVec.ofNat 64 (i + d) := by
  have := h.out_fit
  rw [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact addr_eq (by omega_using [hi, this])

end In

theorem St.out_w {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions s.wr (P.out.setWidth 64 + BitVec.ofNat 64 i) n :=
  ⟨P.OUT, hs.2.inRw (by simp), Offset.contains_base _ hn (by have := hs.1.k1024; omega_using [hn, this])⟩

theorem St.out_r {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions (s.rd ++ s.wr) (P.out.setWidth 64 + BitVec.ofNat 64 i) n :=
  let ⟨r, hr, hc⟩ := St.out_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Byte `i` of `out`. -/
theorem SB.byte {σ s : State} (h : SB P σ s) {i : Nat} (hi : i < P.K) :
    s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) = (emOf P σ).getD i 1 := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_getD hi]

/-! ## Masks -/

/-- A condition as a mask: all ones or zero. -/
def mk (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0#32

theorem sbb_mk (c : Bool) : (if c = true then BitVec.allOnes 32 else 0) = mk c := rfl

/-- `b - 1` borrows exactly when the byte `b` is zero. -/
theorem zcf (b : Byte) : decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = decide (b = 0) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
  by_cases h : b = 0
  · subst h; rfl
  · have : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [decide_eq_false h, decide_eq_false (by omega_using [this])]

/-! ## The scan -/

/-- The first zero of `EM` before index `i`. -/
abbrev fz (P : EP) (σ : State) (i : Nat) : Option Nat := firstZero (emOf P σ) i

/-- `j` bytes scanned, from index 2. -/
def SCI (P : EP) (j : Nat) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .esi = P.out + BitVec.ofNat 32 (2 + j) ∧ s.gpr .edx = BitVec.ofNat 32 (2 + j) ∧
    s.gpr .ecx = BitVec.ofNat 32 (P.K - 2 - j) ∧ s.gpr .ebx = mk (fz P σ (2 + j)).isSome ∧
    s.gpr .edi = BitVec.ofNat 32 ((fz P σ (2 + j)).getD 0)

theorem scanInit_vp : VP (AL P) (.block scanInit) (SCI P 0) :=
  VP.taint [.esp] scanInit_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    have hb := h.sb
    have hs := hb.S
    have hK := hs.1.k64
    simp only [scanInit]
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    obtain s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine St.argv s2 (j := 4) (by decide) (d := .ecx) (by decide) fun t3 s3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => ?_
    obtain s4 : S P σ t4 := ⟨hs.1, s3.2.upd u4 (by decide)⟩
    refine St.movi s4 (d := .edx) (by decide) 2 fun t5 s5 u5 => ?_
    refine St.movi s5 (d := .ebx) (by decide) 0 fun t6 s6 u6 => ?_
    refine St.movi s6 (d := .edi) (by decide) 0 fun t7 s7 u7 => WP.block_nil ?_
    obtain mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨hb.of_mem s7.2 mm, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr]; rfl
    · simp (disch := decide) only [u7.other, u6.other, u5.gpr]
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.gpr]
      exact Offset.ofNat_sub_ofNat (d := 2) (by omega_using [hK])
    · simp (disch := decide) only [u7.other, u6.gpr]; rfl
    · rw [u7.gpr]; rfl

/-- `m` bytes left. -/
def SCM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K - 2 ∧ SCI P (P.K - 2 - m) σ s

/-- The scan done. -/
def SCQ (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .ebx = mk (fz P σ P.K).isSome ∧ s.gpr .edi = BitVec.ofNat 32 ((fz P σ P.K).getD 0)

/-- One step of the scan, at index `i`. -/
theorem scan_step (EM : List Byte) {i : Nat} (hi : 2 ≤ i) :
    (BitVec.ofNat 32 ((firstZero EM i).getD 0) |||
      ((mk (firstZero EM i).isSome ^^^ BitVec.allOnes 32) &&& mk (decide (EM.getD i 1 = 0)) &&& BitVec.ofNat 32 i) =
        BitVec.ofNat 32 ((firstZero EM (i + 1)).getD 0)) ∧
    (mk (firstZero EM i).isSome ||| mk (decide (EM.getD i 1 = 0)) = mk (firstZero EM (i + 1)).isSome) := by
  rw [firstZero]
  cases hf : firstZero EM i with
  | some k =>
    simp only [Option.isSome_some, Option.getD_some, mk, ↓reduceIte, BitVec.xor_self, BitVec.zero_and,
      BitVec.or_zero, BitVec.allOnes_or, and_self]
  | none =>
    simp only [Option.isSome_none, Option.getD_none, mk, Bool.false_eq_true, ↓reduceIte, BitVec.zero_xor,
      BitVec.allOnes_and, BitVec.zero_or]
    by_cases e : EM.getD i 1 = 0
    · simp only [e, decide_true, ↓reduceIte, hi, and_self, Option.getD_some, Option.isSome_some,
        BitVec.allOnes_and]
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, and_false, Option.getD_none,
        Option.isSome_none, BitVec.zero_and]
      constructor <;> first | trivial | rfl

theorem scanBody_vp (n : Nat) : VP (SCM P (n + 1)) (.block scanBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SCQ P σ s) ∧ (0 < n → SCM P n σ s) := by
  refine VP.taint [.esi, .ecx] scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  obtain ⟨hn, hb, si, dx, cx, bx, di⟩ := h
  generalize hj : P.K - 2 - (n + 1) = j at si dx cx bx di
  have hs := hb.S
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  obtain hjK : 2 + j < P.K := by omega_using [hn, hj]
  simp only [scanBody]
  refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 (2 + j))
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA (d := 0) (by omega_using [hn, hj])]; rfl) (St.out_r hs (by omega_using [hn, hj])) fun t1 u1 => ?_
  refine wp_subi fun t2 u2 c2 _ => ?_
  refine wp_sbb_self c2 fun t3 u3 => ?_
  refine wp_mov fun t4 u4 => ?_
  refine wp_xori fun t5 u5 => ?_
  refine wp_and fun t6 u6 => ?_
  refine wp_and fun t7 u7 => ?_
  refine wp_or fun t8 u8 => ?_
  refine wp_or fun t9 u9 => ?_
  refine wp_addi fun t10 u10 => ?_
  refine wp_addi fun t11 u11 => ?_
  refine wp_subi fun t12 u12 _ hz => WP.block_nil ?_
  obtain mm : t12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain st : P.lay.St σ t12 := hs.2.regs (by rw [u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd,
      u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]) mm
  obtain z3 : t3.gpr .eax = mk (decide ((emOf P σ).getD (2 + j) 1 = 0)) := by
    rw [u3.gpr, sbb_mk, u1.gpr, hb.byte hjK, zcf]
  obtain step := scan_step (emOf P σ) (i := 2 + j) (by omega_using [])
  obtain bp7 : t7.gpr .ebp = (mk (fz P σ (2 + j)).isSome ^^^ BitVec.allOnes 32) &&&
      mk (decide ((emOf P σ).getD (2 + j) 1 = 0)) &&& BitVec.ofNat 32 (2 + j) := by
    rw [u7.gpr, u6.gpr, u5.gpr, u4.gpr]
    simp (disch := decide) only [u6.other, u5.other, u4.other]
    rw [z3]
    simp (disch := decide) only [u3.other, u2.other, u1.other]
    rw [bx, dx]
  obtain dit : t12.gpr .edi = BitVec.ofNat 32 ((fz P σ (2 + j + 1)).getD 0) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other]
    rw [u8.gpr, bp7, u7.other _ (by decide)]
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [di]; exact step.1
  obtain bxt : t12.gpr .ebx = mk (fz P σ (2 + j + 1)).isSome := by
    simp (disch := decide) only [u12.other, u11.other, u10.other]
    rw [u9.gpr]
    simp (disch := decide) only [u8.other, u7.other, u6.other, u5.other, u4.other]
    rw [z3]
    simp (disch := decide) only [u3.other, u2.other, u1.other]
    rw [bx]; exact step.2
  obtain dxt : t12.gpr .edx = BitVec.ofNat 32 (2 + j + 1) := by
    simp (disch := decide) only [u12.other, u11.other, u10.gpr, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [dx]; exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 _
  obtain sit : t12.gpr .esi = P.out + BitVec.ofNat 32 (2 + j + 1) := by
    simp (disch := decide) only [u12.other, u11.gpr, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [si, BitVec.add_assoc]; exact congrArg (P.out + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  obtain cx11 : t11.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [cx, show P.K - 2 - j = n + 1 by omega_using [hn, hj]]
  obtain cxt : t12.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u12.gpr, cx11]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_using [])
  obtain sb := hb.of_mem st mm
  refine ⟨?_, fun h0 => ⟨sb, ?_, ?_⟩, fun h0 => ⟨by omega_using [hn], sb, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show eval .ne t12 = _
    rw [cx11, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega_using []), ofNat_beq_zero (by omega_using [hn, hK'])] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_using [h0]
  · rw [bxt, show 2 + j + 1 = P.K by omega_using [hn, hj, h0]]
  · rw [dit, show 2 + j + 1 = P.K by omega_using [hn, hj, h0]]
  · rw [sit, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_using [hn, hj]]
  · rw [dxt, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_using [hn, hj]]
  · rw [cxt, show P.K - 2 - (P.K - 2 - n) = n by omega_using [hn]]
  · rw [bxt, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_using [hn, hj]]
  · rw [dit, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega_using [hn, hj]]

theorem scanLoop_vp : VP (SCI P 0) scanLoop (SCQ P) := by
  refine (VP.loop (I := SCM P) scanBody_vp (P.K - 2 - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.S.1.k64
  exact ⟨by omega_using [hK], by rw [show P.K - 2 - (P.K - 2 - 1 + 1) = 0 by omega_using []]; exact h⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: the validity and the length

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecValid.lean`): the validity of the
padding as the scan finds it (`vEM`), as a mask in its slot, the selected
length (`lselOf`), the mask of a successful private-key operation in its
slot, and the length masked with it (`validRest_vp`), written as a 64-bit
word to `*msg_len` (`mlRest_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_storeS)
open VG.Proof.RsaPkcs1Enc (firstZero vEM vOf lselOf)

variable {P : EP}

/-! ## Masks -/

theorem mk_and (a b : Bool) : mk a &&& mk b = mk (a && b) := by cases a <;> cases b <;> decide

theorem mk_not (b : Bool) : mk b ^^^ BitVec.allOnes 32 = mk (!b) := by cases b <;> decide

theorem sel2 (x y : BitVec 32) (b : Bool) : ((x ^^^ y) &&& mk b) ^^^ y = if b then x else y := by
  cases b
  · simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero, BitVec.zero_xor]
  · simp only [mk, ↓reduceIte, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem mask_and (v : Nat) (b : Bool) :
    BitVec.ofNat 32 v &&& mk b = BitVec.ofNat 32 (if b then v else 0) := by
  cases b
  · simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero]
  · exact BitVec.and_allOnes

/-- `b ^ 2` is zero exactly when the byte `b` is 2. -/
theorem xcf (b : Byte) : decide ((b.setWidth 32 ^^^ 2).toNat < (1 : BitVec 32).toNat) = decide (b = 2) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1]
  by_cases h : b = 2
  · subst h; decide
  · have : b.setWidth 32 ^^^ 2 ≠ 0 := by
      intro e
      obtain e1 := congrArg (· ^^^ (2 : BitVec 32)) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at e1
      obtain e2 := congrArg (BitVec.setWidth 8) e1
      simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] at e2
      exact h (e2.trans (by decide))
    have : (b.setWidth 32 ^^^ 2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [decide_eq_false h, decide_eq_false (by omega_using [this])]

theorem sepcf {sep : Nat} (h : sep < 2 ^ 32) :
    decide ((BitVec.ofNat 32 sep).toNat < (10 : BitVec 32).toNat) = decide (sep < 10) := by
  have e : (10 : BitVec 32).toNat = 10 := rfl
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem okcf (P : EP) (σ : State) :
    mk (decide ((rcOf P σ ^^^ 1).toNat < (1 : BitVec 32).toNat)) = mk (decide (rcOf P σ = 1)) := by
  rcases rcOf_cases P σ with e | e | e <;> rw [e] <;> decide

theorem vOf_bits (b0 b1 : Byte) (f : Bool) (sep : Nat) :
    (((decide (b0 = 0) && decide (b1 = 2)) && f) && !decide (sep < 10)) = vOf b0 b1 f sep := by
  by_cases c : sep < 10
  · simp [vOf, c, show ¬ 10 ≤ sep by omega_using [c]]
  · simp [vOf, c, show 10 ≤ sep by omega_using [c], Bool.and_assoc]

/-! ## The validity -/

/-- The selection's inputs: `AL`, the validity, the separator and the
selected length. -/
abbrev alV (P : EP) (σ : State) : Nat := Spec.RsaPkcs1Enc.altLength P.K (clV P σ)
abbrev vB (P : EP) (σ : State) : Bool := vEM (emOf P σ) P.K
abbrev sepV (P : EP) (σ : State) : Nat := (fz P σ P.K).getD 0
abbrev lselV (P : EP) (σ : State) : Nat := lselOf (vB P σ) (sepV P σ) (alV P σ) P.K
abbrev okB (P : EP) (σ : State) : Bool := decide (rcOf P σ = 1)

theorem alV_le (P : EP) (σ : State) : alV P σ ≤ P.K - 11 := VG.Proof.RsaPkcs1Enc.altLength_le _ _

theorem sep_lt (P : EP) (σ : State) : sepV P σ < P.K ∨ sepV P σ = 0 := by
  simp only [sepV, fz]
  cases hf : firstZero (emOf P σ) P.K with
  | none => exact .inr rfl
  | some i => exact .inl (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1

theorem sep_ok {σ : State} (h : vB P σ = true) : 10 ≤ sepV P σ ∧ sepV P σ < P.K := by
  have h' := h
  simp only [vB, vEM, vOf, decide_eq_true_eq] at h'
  obtain ⟨-, -, hs, h10⟩ := h'
  refine ⟨h10, ?_⟩
  simp only [sepV, fz]
  cases hf : firstZero (emOf P σ) P.K with
  | none => rw [hf] at hs; cases hs
  | some i => exact (VG.Proof.RsaPkcs1Enc.firstZero_some hf).2.1

theorem lsel_le (P : EP) (σ : State) (hK : 11 ≤ P.K) : lselV P σ ≤ P.K := by
  have := alV_le P σ
  simp only [lselV, lselOf]; split <;> omega_arith

/-- `out`, `AL` and the result kept by a store to another slot of the frame. -/
theorem SB.keep_fr {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) {d : Nat} {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) (hd : d + 4 ≤ frameBytes) (ho : d + 4 ≤ oR ∨ oR + 4 ≤ d)
    (hal : d + 4 ≤ oAL ∨ oAL + 4 ≤ d) : SB P σ t := by
  have hs := h.S
  have hK := hs.1.k1024
  obtain ⟨⟨ir, al⟩, out, rc⟩ := h
  obtain fr : Frame [⟨P.lay.fr d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine ⟨⟨ir.keep_fr st hm hd ho, ?_⟩, ?_, ?_⟩
  · rw [hm, Lay.readW_fr_other _ _ _ hal.symm (by decide) (by simp only [frameBytes] at hd; omega_using [hd])]; exact al
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_using [hd])).symm) (by omega_using [hK])]
    exact out
  · rw [hm, Lay.readW_fr_other _ _ _ ho.symm (by decide) (by simp only [frameBytes] at hd; omega_using [hd])]; exact rc

/-- After the load of `out`'s pointer. -/
def V0 (P : EP) (σ s : State) : Prop := SCQ P σ s ∧ s.gpr .esi = P.out

/-- After `validBlock`: the masks in their slots, `k - len` and `len & OK`. -/
def VB (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) ∧
    s.gpr .edx = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0)

theorem validHead_vp : VP (SCQ P) (.block (validBlock.take 1)) (V0 P) :=
  VP.taint [.esp] validHead_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => WP.block_nil ?_
    obtain ⟨hb, bx, di⟩ := h
    exact ⟨⟨hb.of_mem s1.2 u1.mem, by rw [u1.other _ (by decide), bx], by rw [u1.other _ (by decide), di]⟩,
      u1.gpr⟩

theorem In.outA0 {σ : State} (h : In P σ) {d : Nat} (hd : d < P.K) :
    addr P.out d = P.out.setWidth 64 + BitVec.ofNat 64 d := by
  have := h.out_fit
  exact addr_eq (by omega_using [hd, this])

theorem validRest_vp : VP (V0 P) (.block (validBlock.drop 1)) (VB P) :=
  VP.taint [.esp, .esi] validRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.S.2.sp, h₂.1.1.S.2.sp]
      · rw [h₁.2, h₂.2]) fun σ s h => by
    obtain ⟨⟨hb, bx, di⟩, si⟩ := h
    have hs := hb.S
    have hK := hs.1.k64
    have hK' := hs.1.k1024
    obtain hsep : sepV P σ < 2 ^ 32 := by have := sep_lt P σ; omega_using [hK', this]
    simp only [validBlock, List.drop_succ_cons, List.drop_zero]
    refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 0)
      (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA0 (by omega_using [hK])]) (St.out_r hs (by omega_using [hK])) fun t1 u1 => ?_
    refine wp_subi fun t2 u2 c2 _ => ?_
    refine wp_sbb_self c2 fun t3 u3 => ?_
    refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 1)
      (by show t3.ea ⟨.esi, 1⟩ = _
          rw [ea_at, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), si,
            hs.1.outA0 (by omega_using [hK])])
      (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact St.out_r hs (by omega_using [hK])) fun t4 u4 => ?_
    refine wp_xorI fun t5 u5 => ?_
    refine wp_subi fun t6 u6 c6 _ => ?_
    refine wp_sbb_self c6 fun t7 u7 => ?_
    refine wp_and fun t8 u8 => ?_
    refine wp_and fun t9 u9 => ?_
    refine wp_mov fun t10 u10 => ?_
    refine wp_subi fun t11 u11 c11 _ => ?_
    refine wp_sbb_self c11 fun t12 u12 => ?_
    refine wp_xorI fun t13 u13 => ?_
    refine wp_and fun t14 u14 => ?_
    obtain st14 : P.lay.St σ t14 := (((((((((((((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).upd
      u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide)).upd u8 (by decide)).upd u9
      (by decide)).upd u10 (by decide)).upd u11 (by decide)).upd u12 (by decide)).upd u13 (by decide)).upd u14
      (by decide)
    refine st14.wp_strFr (d := oV) (by show oV + 4 ≤ frameBytes; decide) fun t15 st15 m15 => ?_
    refine St.argv ⟨hs.1, st15⟩ (j := 4) (by decide) (d := .edx) (by decide) fun t16 s16 u16 => ?_
    refine wp_sub fun t17 u17 _ => ?_
    refine wp_subi fun t18 u18 _ _ => ?_
    obtain st18 := (s16.2.upd u17 (by decide)).upd u18 (by decide)
    refine st18.wp_slot (d := oAL) (by show oAL + 4 ≤ frameBytes; decide) (r := .ecx) (by decide)
      fun t19 st19 u19 => ?_
    refine wp_xor fun t20 u20 => ?_
    refine wp_and fun t21 u21 => ?_
    refine wp_xor fun t22 u22 => ?_
    obtain st22 := ((st19.upd u20 (by decide)).upd u21 (by decide)).upd u22 (by decide)
    refine st22.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t23 st23 u23 => ?_
    refine wp_xorI fun t24 u24 => ?_
    refine wp_subi fun t25 u25 c25 _ => ?_
    refine wp_sbb_self c25 fun t26 u26 => ?_
    obtain st26 := ((st23.upd u24 (by decide)).upd u25 (by decide)).upd u26 (by decide)
    refine st26.wp_strFr (d := oOK) (by show oOK + 4 ≤ frameBytes; decide) fun t27 st27 m27 => ?_
    refine St.argv ⟨hs.1, st27⟩ (j := 4) (by decide) (d := .ebx) (by decide) fun t28 s28 u28 => ?_
    refine wp_sub fun t29 u29 _ => ?_
    refine wp_and fun t30 u30 => WP.block_nil ?_
    obtain st30 := (s28.2.upd u29 (by decide)).upd u30 (by decide)
    -- The values.
    obtain m14 : t14.mem = s.mem := by
      rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
        u2.mem, u1.mem]
    obtain a3 : t3.gpr .eax = mk (decide ((emOf P σ).getD 0 1 = 0)) := by
      rw [u3.gpr, sbb_mk, u1.gpr, hb.byte (i := 0) (by omega_using [hK]), zcf]
    obtain d7 : t7.gpr .edx = mk (decide ((emOf P σ).getD 1 1 = 2)) := by
      rw [u7.gpr, sbb_mk, u5.gpr, u4.gpr, u3.mem, u2.mem, u1.mem, hb.byte (by omega_using [hK]), xcf]
    obtain a9 : t9.gpr .eax = mk ((decide ((emOf P σ).getD 0 1 = 0) && decide ((emOf P σ).getD 1 1 = 2)) &&
        (fz P σ P.K).isSome) := by
      rw [u9.gpr, u8.gpr, d7]
      simp (disch := decide) only [u8.other, u7.other, u6.other, u5.other, u4.other]
      rw [a3]
      simp (disch := decide) only [u3.other, u2.other, u1.other]
      rw [bx, mk_and, mk_and]
    obtain d13 : t13.gpr .edx = mk (!decide (sepV P σ < 10)) := by
      rw [u13.gpr, u12.gpr, sbb_mk, u10.gpr]
      simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other,
        u2.other, u1.other]
      rw [di, sepcf hsep, mk_not]
    obtain a14 : t14.gpr .eax = mk (vB P σ) := by
      rw [u14.gpr, d13, u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
        u10.other _ (by decide), a9, mk_and, vOf_bits]
    obtain mm15 : t15.mem = s.mem.writeW (P.lay.fr oV) (mk (vB P σ)) := by rw [m15.mem, m14, a14]
    obtain d18 : t18.gpr .edx = BitVec.ofNat 32 P.K - BitVec.ofNat 32 (sepV P σ) - 1 := by
      rw [u18.gpr, u17.gpr, u16.gpr, u16.other _ (by decide), m15.gpr]
      simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
        u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
      rw [di]; rfl
    obtain m18 : t18.mem = t15.mem := by rw [u18.mem, u17.mem, u16.mem]
    obtain c19 : t19.gpr .ecx = BitVec.ofNat 32 (alV P σ) := by
      rw [u19.gpr, m18, mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.1.2
    obtain a21 : t20.gpr .eax = mk (vB P σ) := by
      rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide),
        u17.other _ (by decide), u16.other _ (by decide), m15.gpr, a14]
    obtain d22 : t22.gpr .edx = BitVec.ofNat 32 (lselV P σ) := by
      rw [u22.gpr, u21.gpr, a21, u20.gpr, u21.other _ (by decide), u20.other _ (by decide), c19,
        u19.other _ (by decide), d18, sel2]
      simp only [lselV, lselOf]
      cases hv : vB P σ
      · rfl
      · have := sep_ok hv
        simp only [↓reduceIte]
        rw [Offset.ofNat_sub_ofNat (by omega_using [this])]
        exact Offset.ofNat_sub_ofNat (d := 1) (by omega_using [this])
    obtain m22 : t22.mem = t15.mem := by rw [u22.mem, u21.mem, u20.mem, u19.mem, m18]
    obtain r23 : t23.gpr .eax = rcOf P σ := by
      rw [u23.gpr, m22, mm15, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide)]; exact hb.2.2
    obtain a26 : t26.gpr .eax = mk (okB P σ) := by
      rw [u26.gpr, sbb_mk, u24.gpr, r23]; exact okcf P σ
    obtain m26 : t26.mem = t15.mem := by rw [u26.mem, u25.mem, u24.mem, u23.mem, m22]
    obtain mm27 : t27.mem = t15.mem.writeW (P.lay.fr oOK) (mk (okB P σ)) := by rw [m27.mem, m26, a26]
    obtain d28 : t28.gpr .edx = BitVec.ofNat 32 (lselV P σ) := by
      rw [u28.other _ (by decide), m27.gpr, u26.other _ (by decide), u25.other _ (by decide),
        u24.other _ (by decide), u23.other _ (by decide), d22]
    obtain hl := lsel_le P σ (by omega_using [hK])
    obtain b30 : t30.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) := by
      rw [u30.other _ (by decide), u29.gpr, u28.gpr, d28]
      exact Offset.ofNat_sub_ofNat hl
    obtain d30 : t30.gpr .edx = BitVec.ofNat 32 (if okB P σ then lselV P σ else 0) := by
      rw [u30.gpr, u29.other _ (by decide), d28, u29.other _ (by decide), u28.other _ (by decide), m27.gpr, a26,
        mask_and]
    obtain m30 : t30.mem = t27.mem := by rw [u30.mem, u29.mem, u28.mem]
    obtain sb15 := (hb.of_mem st14 m14).keep_fr st15 (m15.mem) (by decide) (by simp only [oR, oV]; decide)
      (by simp only [oAL, oV]; decide)
    obtain sb27 := (sb15.of_mem st26 m26).keep_fr st27 (by rw [m27.mem]) (by decide)
      (by simp only [oR, oOK]; decide) (by simp only [oAL, oOK]; decide)
    refine ⟨sb27.of_mem st30 m30, ?_, ?_, b30, d30⟩
    · rw [m30, mm27, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), mm15,
        Mem.readW_writeW_self32]
    · rw [m30, mm27, Mem.readW_writeW_self32]

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: `*msg_len` and the output

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecValid.lean`,
`Proof/RsaPkcs1Enc/Arm/DecSel.lean`): the masked length written as a 64-bit
word to `*msg_len` (`mlRest_vp`); byte `i` of `out` (`obV`): `EM[i]` or
`AM[i]` as the validity selects, if `i ≥ k - len` and the private-key
operation succeeded, and zero otherwise (`selLoop_vp`); then the result
returned (`finR_vp`), which is what the shared contract states (`res_of`,
`Res`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_storeS wp_subS)
open VG.Proof.RsaPkcs1Enc (outByte)

variable {P : EP}

/-! ## `*msg_len` -/

/-- A 64-bit word written as two 32-bit halves, the high one zero. -/
theorem readW_pair (m : Mem) (a : Addr) {L : Nat} (hL : L < 2 ^ 32) :
    ((m.writeW a (BitVec.ofNat 32 L)).writeW (a + BitVec.ofNat 64 4) (BitVec.ofNat 32 0)).readW a 64 =
      BitVec.ofNat 64 L := by
  show (Mem.read _ a 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := BitVec.ofNat 64 L) fun i hi => ?_]
  · exact BitVec.setWidth_eq _
  by_cases h4 : i < 4
  · have e1 : ¬ (a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4)).toNat < 32 / 8 := by
      rw [show a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 i - BitVec.ofNat 64 4 by
        rw [Offset.add_sub_add_left]]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [h4]
    simp only [Mem.writeW]
    rw [Mem.write_apply e1]
    simp only [Mem.write, Mem.sub_ofNat_toNat a (by omega_using [hi] : i < 2 ^ 64), show i < 32 / 8 by omega_using [h4], ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ (8 * (32 / 8)) from hL),
      Nat.mod_eq_of_lt (show L < 2 ^ (8 * 8) from Nat.lt_of_lt_of_le hL (by decide))]
    rw [show 8 * (32 / 8) = 32 from rfl, Nat.mod_eq_of_lt hL]
  · have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) := by
      rw [Offset.add_add, show 4 + (i - 4) = i by omega_using [h4]]
    simp only [Mem.writeW, Mem.write]
    rw [e, Mem.sub_ofNat_toNat _ (by omega_using [hi] : i - 4 < 2 ^ 64)]
    simp only [show i - 4 < 32 / 8 by omega_using [hi], ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : 2 ^ 32 ≤ 2 ^ (8 * i) := Nat.pow_le_pow_right (by decide) (by omega_using [h4])
    rw [Nat.div_eq_of_lt (by omega_using [hL, this] : L % 2 ^ 64 < 2 ^ (8 * i))]
    simp

theorem In.ml_fit {σ : State} (h : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.ML (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.ml.isLt; omega_using [])] at this

theorem In.out_ml {σ : State} (h : In P σ) : P.OUT.Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

theorem SB.keep_ml {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hf : Frame [P.ML] s.mem t.mem) :
    SB P σ t := by
  have hs := h.S
  have hK := hs.1.k1024
  obtain fr : ∀ d, d + 4 ≤ frameBytes → Region.Disjoint ⟨P.lay.fr d, 4⟩ P.ML := fun d hd =>
    hs.1.ok.stk_fr (R := P.ML) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_using [hd])
  obtain one : ∀ {R : Region}, R.Disjoint P.ML → ∀ r ∈ [P.ML], R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain ⟨⟨⟨hb, cl, am⟩, al⟩, out, rc⟩ := h
  refine ⟨⟨⟨hb.frame st hf fun r hr => ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hs.1.out_ml, fr oR (by decide)⟩
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one (hs.1.sc_ml (by decide))) (by decide)]; exact cl
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one (hs.1.sc_ml (by simp only [sAM]; omega_using [hK]))) (by omega_using [hK])]
    exact am
  · rw [slot_keep hf (one (fr oAL (by decide)))]; exact al
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one hs.1.out_ml) (by omega_using [hK])]; exact out
  · rw [slot_keep hf (one (fr oR (by decide)))]; exact rc

/-- What the output needs: `out`, `AM`, the result and the masks in their slots, and `k - len`. -/
def VK (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ)

/-- After the load of `msg_len`. -/
def VM (P : EP) (σ s : State) : Prop := VB P σ s ∧ s.gpr .esi = P.ml

/-- `*msg_len` written. -/
def VW (P : EP) (σ s : State) : Prop :=
  VK P σ s ∧ Spec.Rsa.wordsAt s.mem (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]

theorem mlHead_vp : VP (VB P) (.block (mlStore.take 1)) (VM P) :=
  VP.taint [.esp] mlHead_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    refine St.argv hs (j := 2) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => WP.block_nil ?_
    obtain ⟨hb, v, ok, bx, dx⟩ := h
    exact ⟨⟨hb.of_mem s1.2 u1.mem, by rw [u1.mem]; exact v, by rw [u1.mem]; exact ok,
      by rw [u1.other _ (by decide), bx], by rw [u1.other _ (by decide), dx]⟩, u1.gpr⟩

theorem mlRest_vp : VP (VM P) (.block (mlStore.drop 1)) (VW P) :=
  VP.taint [.esi] mlRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s h => by
    obtain ⟨⟨hb, v, ok, bx, dx⟩, si⟩ := h
    have hs := hb.S
    have hK := hs.1.k1024
    have fit := hs.1.ml_fit
    obtain win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
      ⟨P.ML, hs.2.inRw (by simp), Offset.contains_base _ hd (by omega_using [hd])⟩
    simp only [mlStore, List.drop_succ_cons, List.drop_zero]
    refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
      (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si]; exact addr_eq (by omega_using [])) (win 0 (by decide)) fun t1 m1 => ?_
    refine wp_movi fun t2 u2 => ?_
    refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
      (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, u2.other _ (by decide), m1.gpr, si]; exact addr_eq (by omega_using [fit]))
      (by rw [u2.wr, m1.wr]; exact win 4 (by decide)) fun t3 m3 => WP.block_nil ?_
    obtain mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (s.gpr .edx)).writeW
        (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
      rw [m3.mem, u2.gpr, u2.mem, m1.mem]
    obtain fr : Frame [P.ML] s.mem t3.mem := by
      rw [mm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s.gpr .edx)
        (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    obtain st : P.lay.St σ t3 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
      (by rw [m3.rd, u2.rd, m1.rd]) (by rw [m3.wr, u2.wr, m1.wr])
      (by rw [m3.gpr, u2.other _ (by decide), m1.gpr])
    obtain frd : ∀ d, d + 4 ≤ frameBytes → ∀ r ∈ [P.ML], Region.Disjoint ⟨P.lay.fr d, 4⟩ r := fun d hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.1.ok.stk_fr (R := P.ML) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_using [hd])
    refine ⟨⟨hb.keep_ml st fr, by rw [slot_keep fr (frd oV (by decide))]; exact v,
      by rw [slot_keep fr (frd oOK (by decide))]; exact ok, by rw [m3.gpr, u2.other _ (by decide), m1.gpr, bx]⟩, ?_⟩
    obtain hl : (if okB P σ then lselV P σ else 0) < 2 ^ 32 := by
      have := lsel_le P σ (by have := hs.1.k64; omega_using [this]); split <;> omega_arith
    show [t3.mem.readW (P.ml.setWidth 64 + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [mm, dx, show 8 * 0 = 0 from rfl]
    exact congrArg (· :: []) (by rw [BitVec.add_zero]; exact readW_pair _ _ hl)

/-! ## The output -/

/-- Byte `i` of the output. -/
abbrev obV (P : EP) (σ : State) (i : Nat) : Byte :=
  outByte (vB P σ) (okB P σ) (P.K - lselV P σ) i ((emOf P σ).getD i 1) ((amV P σ).getD i 0)

/-- `j` bytes of `out` written. -/
def SL (P : EP) (j : Nat) (σ s : State) : Prop :=
  S P σ s ∧
    (∀ i < P.K, s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) = if i < j then obV P σ i else (emOf P σ).getD i 1) ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ ∧ s.mem.readW (P.lay.fr oR) 32 = rcOf P σ ∧
    Spec.Rsa.wordsAt s.mem (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)] ∧
    s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .esi = P.out + BitVec.ofNat 32 j ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 (sAM + j) ∧
    s.gpr .edx = BitVec.ofNat 32 j ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - j) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) ∧ (emOf P σ).length = P.K

theorem selInit_vp : VP (VW P) (.block selInit) (SL P 0) :=
  VP.taint [.esp] selInit_taint (sp_agree fun _ _ h => h.1.1.S) fun σ s h => by
    obtain ⟨⟨hb, v, ok, bx⟩, ml⟩ := h
    have hs := hb.S
    simp only [selInit, List.cons_append, List.append_assoc]
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .edi) (by decide) sAM fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .edx) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.argv s3 (j := 4) (by decide) (d := .ecx) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    obtain mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨s4, fun i hi => ?_, by rw [mm]; exact hb.1.1.2.2, by rw [mm]; exact hb.2.2, by rw [mm]; exact ml,
      by rw [mm]; exact v, by rw [mm]; exact ok, ?_, ?_, ?_, ?_, ?_, emOf_length hb⟩
    · rw [mm, hb.byte hi]; simp
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
      exact (BitVec.add_zero _).symm
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
    · rw [u4.other _ (by decide), u3.gpr]
    · rw [u4.gpr]; rfl
    · simp (disch := decide) only [u4.other, u3.other, u2.other, u1.other]; exact bx

theorem selByte (e a : Byte) (v c : Bool) :
    ((if v then e.setWidth 32 else a.setWidth 32) &&& mk c).setWidth 8 = if c then (if v then e else a) else 0 := by
  obtain h8 : ∀ b : Byte, (b.setWidth 32).setWidth 8 = b := fun b => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  cases c <;> cases v <;> simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero, BitVec.and_allOnes, h8]
    <;> rfl

theorem outByte_eq (v ok : Bool) (kl i : Nat) (e a : Byte) :
    outByte v ok kl i e a = if (!decide (i < kl) && ok) then (if v then e else a) else 0 := by
  simp only [outByte]
  by_cases h : i < kl <;> cases ok <;> simp [h] <;> omega_using [h]

/-- `m` bytes left. -/
def SLM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K ∧ SL P (P.K - m) σ s

theorem selBody_vp (n : Nat) : VP (SLM P (n + 1)) (.block selBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SL P P.K σ s) ∧ (0 < n → SLM P n σ s) := by
  refine VP.taint [.esp, .esi, .edi, .ecx] selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.1.2.sp, h₂.2.1.2.sp]
    · rw [h₁.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.2.2.1]
  obtain ⟨hn, hs, ob, am, rc, ml, sv, sok, si, di, dx, cx, bx, hEM⟩ := h
  generalize hj : P.K - (n + 1) = j at ob si di dx cx
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  obtain hjK : j < P.K := by omega_using [hn, hj]
  obtain hl := lsel_le P σ (by omega_using [hK])
  simp only [selBody]
  refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 j)
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA (d := 0) (by omega_using [hn, hj])]; rfl)
    (St.out_r hs (by omega_using [hn, hj])) fun t1 u1 => ?_
  refine wp_movzx8 (a := P.scr.setWidth 64 + BitVec.ofNat 64 (sAM + j))
    (by show t1.ea ⟨.edi, 0⟩ = _
        rw [ea_at, u1.other _ (by decide), di, hs.1.addrSc (by simp only [sAM]; omega_using [hj, hK'])]; rfl)
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sAM]; omega_using [hj, hK'])) fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => ?_
  obtain st3 := ((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)
  refine wp_andS (st3.readSlot (d := oV) (by show oV + 4 ≤ frameBytes; decide)) fun t4 u4 => ?_
  refine wp_xor fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => ?_
  refine wp_subS (readSrc_reg _ _) fun t7 u7 c7 => ?_
  refine wp_sbb_self c7 fun t8 u8 => ?_
  refine wp_xorI fun t9 u9 => ?_
  obtain st9 := ((((((st3.upd u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide)).upd u8
    (by decide)).upd u9 (by decide))
  refine wp_andS (st9.readSlot (d := oOK) (by show oOK + 4 ≤ frameBytes; decide)) fun t10 u10 => ?_
  refine wp_and fun t11 u11 => ?_
  obtain m11 : t11.mem = s.mem := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine wp_store8 (a := P.out.setWidth 64 + BitVec.ofNat 64 j)
    (by show t11.ea ⟨.esi, 0⟩ = _
        rw [ea_at]
        simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other,
          u4.other, u3.other, u2.other, u1.other]
        rw [si, hs.1.outA (d := 0) (by omega_using [hn, hj])]; rfl)
    (by rw [u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
        exact St.out_w hs (by omega_using [hn, hj])) fun t12 m12 => ?_
  refine wp_addi fun t13 u13 => ?_
  refine wp_addi fun t14 u14 => ?_
  refine wp_addi fun t15 u15 => ?_
  refine wp_subi fun t16 u16 _ hz => WP.block_nil ?_
  -- The values.
  obtain e1 : t1.gpr .eax = ((emOf P σ).getD j 1).setWidth 32 := by
    rw [u1.gpr, ob j hjK]; simp only [Nat.lt_irrefl, ↓reduceIte]
  obtain a2 : t2.gpr .ebp = ((amV P σ).getD j 0).setWidth 32 := by
    rw [u2.gpr, u1.mem, ← am, Proof.RsaPkcs1Sig.bytesAt_getD hjK, Offset.add_add]
  obtain v5 : t5.gpr .eax = if vB P σ then ((emOf P σ).getD j 1).setWidth 32 else ((amV P σ).getD j 0).setWidth 32 := by
    rw [u5.gpr, u4.gpr, u3.gpr, u4.other _ (by decide), u3.other _ (by decide), a2, u2.other _ (by decide), e1,
      u3.mem, u2.mem, u1.mem, sv, sel2]
  obtain kl7 : decide ((t6.gpr .ebp).toNat < (t6.gpr .ebx).toNat) = decide (j < P.K - lselV P σ) := by
    rw [u6.gpr]
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [dx, bx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hK']), Nat.mod_eq_of_lt (by omega_using [hK'])]
  obtain m9 : t9.mem = s.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain bp10 : t10.gpr .ebp = mk (!decide (j < P.K - lselV P σ) && okB P σ) := by
    rw [u10.gpr, u9.gpr, u8.gpr, sbb_mk, kl7, mk_not, m9, sok, mk_and]
  obtain bv : ((t11.gpr .eax).setWidth 8) = obV P σ j := by
    rw [u11.gpr, bp10, u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide),
      u7.other _ (by decide), u6.other _ (by decide), v5, selByte]
    exact (outByte_eq _ _ _ _ _ _).symm
  obtain mm : t16.mem = s.mem.writeW (P.out.setWidth 64 + BitVec.ofNat 64 j) (obV P σ j) := by
    rw [u16.mem, u15.mem, u14.mem, u13.mem, m12.mem, m11, show Reg8.al.reg = .eax from rfl, bv]
  obtain W1 : Region.Sub ⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩ P.OUT := Offset.sub_base _ (by omega_using [hn, hj])
  obtain fr : Frame [⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩] s.mem t16.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) (obV P σ j) (Region.contains_self _ _)
  obtain st : P.lay.St σ t16 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, W1⟩)
    (by rw [u16.rd, u15.rd, u14.rd, u13.rd, m12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd,
      u3.rd, u2.rd, u1.rd])
    (by rw [u16.wr, u15.wr, u14.wr, u13.wr, m12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr,
      u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u16.other, u15.other, u14.other, u13.other, m12.gpr, u11.other, u10.other,
      u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other])
  obtain one : ∀ {R : Region}, R.Disjoint P.OUT → ∀ r ∈ [(⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩ : Region)],
      R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right W1
  obtain frO : ∀ d, d + 4 ≤ frameBytes → Region.Disjoint ⟨P.lay.fr d, 4⟩ P.OUT := fun d hd =>
    hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega_using [hd])
  obtain gg : ∀ r, r ≠ .eax → r ≠ .ebp → t12.gpr r = s.gpr r := fun r h1 h2 => by
    rw [m12.gpr]
    simp (disch := first | exact h1 | exact h2 | exact Ne.symm h1 | exact Ne.symm h2) only [u11.other,
      u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
  obtain sit : t16.gpr .esi = P.out + BitVec.ofNat 32 (j + 1) := by
    rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.gpr,
      gg _ (by decide) (by decide), si, BitVec.add_assoc]
    exact congrArg (P.out + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  obtain dit : t16.gpr .edi = P.scr + BitVec.ofNat 32 (sAM + (j + 1)) := by
    rw [u16.other _ (by decide), u15.other _ (by decide), u14.gpr, u13.other _ (by decide),
      gg _ (by decide) (by decide), di, BitVec.add_assoc, ← Nat.add_assoc]
    exact congrArg (P.scr + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  obtain dxt : t16.gpr .edx = BitVec.ofNat 32 (j + 1) := by
    rw [u16.other _ (by decide), u15.gpr, u14.other _ (by decide), u13.other _ (by decide),
      gg _ (by decide) (by decide), dx]
    exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 _
  obtain cx15 : t15.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
      gg _ (by decide) (by decide), cx, show P.K - j = n + 1 by omega_using [hn, hj]]
  obtain cxt : t16.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u16.gpr, cx15]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_using [])
  obtain obt : ∀ i < P.K, t16.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) =
      if i < j + 1 then obV P σ i else (emOf P σ).getD i 1 := by
    intro i hi
    rw [mm, WriteBytes.writeW8_apply]
    by_cases e : i = j
    · subst e; simp
    · simp only [Offset.add_ofNat_ne (P.out.setWidth 64) (by omega_using [hK', hi]) (by omega_using [hj, hK']) e, ↓reduceIte]
      rw [ob i hi]
      simp only [show (i < j + 1) = (i < j) by apply propext; omega_using [e]]
  obtain sl : SL P (j + 1) σ t16 :=
    ⟨⟨hs.1, st⟩, obt,
      (Proof.RsaPkcs1Sig.bytesAt_frame fr (one (hs.1.sc_out (by simp only [sAM]; omega_using [hK']))) (by omega_using [hK'])).trans am,
      by rw [slot_keep fr (one (frO oR (by decide)))]; exact rc,
      (Proof.RsaPkcs1Sig.wordsAt_frame' fr (one hs.1.out_ml.symm) (by decide)).trans ml,
      by rw [slot_keep fr (one (frO oV (by decide)))]; exact sv,
      by rw [slot_keep fr (one (frO oOK (by decide)))]; exact sok,
      sit, dit, dxt, by rw [cxt, show P.K - (j + 1) = n by omega_using [hn, hj]],
      by rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
        gg _ (by decide) (by decide), bx], hEM⟩
  refine ⟨?_, fun h0 => ?_, fun h0 => ⟨by omega_using [hn], by rw [show P.K - n = j + 1 by omega_using [hn, hj]]; exact sl⟩⟩
  · show eval .ne t16 = _
    rw [cx15, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega_using []), ofNat_beq_zero (by omega_using [hn, hK'])] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega_using [h0]
  · rw [show P.K = j + 1 by omega_using [hn, hj, h0]]; exact sl

theorem selLoop_vp : VP (SL P 0) selLoop (SL P P.K) := by
  refine (VP.loop (I := SLM P) selBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.k64
  exact ⟨by omega_using [hK], by rw [show P.K - (P.K - 1 + 1) = 0 by omega_using []]; exact h⟩

/-! ## The result -/

/-- What the shared contract states of the result `r` and the memory `m`. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg m (P.out.setWidth 64) (P.ml.setWidth 64) P.K r
    (Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ))

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem amV_length (P : EP) (σ : State) : (amV P σ).length = P.K := by
  rw [amV, VG.Proof.RsaPkcs1Enc.irprf_eq, List.length_take, flatMap_blocks_length]
  omega_using []

theorem res_of {σ : State} {m : Mem} (hin : In P σ) (hEM : (emOf P σ).length = P.K)
    (hout : ∀ i < P.K, m (P.out.setWidth 64 + BitVec.ofNat 64 i) = obV P σ i)
    (hml : Spec.Rsa.wordsAt m (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]) :
    Res P σ m (rcOf P σ) := by
  have hK := hin.k64
  obtain hn : P.nB.length = P.K := by rw [← hin.nB, Proof.RsaPkcs1Sig.bytesAt_len]
  obtain hC : (cB P σ).length = P.K := Proof.RsaPkcs1Sig.bytesAt_len _ _ _
  obtain hb : Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = (List.range P.K).map (obV P σ) :=
    List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  unfold Res Spec.RsaPkcs1Enc.decrypt
  rw [hn]
  cases ho : privO P σ with
  | ok EM =>
    obtain e1 : emOf P σ = EM := by simp only [emOf, ho]
    obtain r1 : rcOf P σ = 1 := by simp only [rcOf, ho]
    obtain ok1 : okB P σ = true := by simp only [okB, r1]; rfl
    obtain hEM' : EM.length = P.K := e1 ▸ hEM
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by omega_using [hK]) ho]
    obtain ⟨hl, hm⟩ := VG.Proof.RsaPkcs1Enc.sel_eq (EM := EM) (AM := amV P σ) (al := alV P σ) hEM'
      (amV_length P σ) (by omega_using [hK]) (alV_le P σ)
    obtain hM : Spec.RsaPkcs1Enc.implicitDecode (dB P σ) (cB P σ) EM =
        (if Spec.RsaPkcs1Enc.valid EM then Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength EM) EM
          else Spec.RsaPkcs1Enc.lastN (alV P σ) (amV P σ)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEM']
    rw [hM]
    refine ⟨r1, ?_, ?_⟩
    · rw [hb, ← hm]
      refine List.map_congr_left fun i _ => ?_
      simp only [obV, vB, lselV, sepV, fz, e1, ok1]
    · rw [hml, ok1, ← hl]
      simp only [lselV, vB, sepV, fz, e1, ↓reduceIte]
  | invalid =>
    obtain r0 : rcOf P σ = 0 := by simp only [rcOf, ho]
    obtain ok0 : okB P σ = false := by simp only [okB, r0]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_invalid (C := cB P σ)
      (rsadp := fun C => Spec.Rsa.privateChecked P.nB P.eB C (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)) ho]
    refine ⟨r0, ?_, by rw [hml, ok0]; rfl⟩
    obtain z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i, List.map_const', List.length_range]
  | fault =>
    obtain r2 : rcOf P σ = 2 := by simp only [rcOf, ho]
    obtain ok0 : okB P σ = false := by simp only [okB, r2]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by omega_using [hK]) ho]
    refine ⟨r2, ?_, by rw [hml, ok0]; rfl⟩
    obtain z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i, List.map_const', List.length_range]

theorem finR_vp : VP (SL P P.K) (.block fin) (Fin P) :=
  VP.taint [.esp] fin_taint (sp_agree fun _ _ h => h.1) fun σ s h => by
    obtain ⟨hs, ob, -, rc, ml, -, -, -, -, -, -, -, hEM⟩ := h
    refine hs.2.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t1 st1 u1 => WP.block_nil ⟨⟨hs.1, st1⟩, ?_⟩
    rw [u1.gpr, rc, u1.mem]
    exact res_of hs.1 hEM (fun i hi => by rw [ob i hi]; simp [hi]) ml

end VG.Proof.RsaPkcs1Enc.X86.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86: the body

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecVerified.lean`): the pieces in order,
each correct and constant time (`body_vp`), from the state the body starts
from to the result (`Fin`); and no instruction of the body or of the
functions it calls writes `esp` (`body_noSp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Pbkdf2.Whole.X86 (sha256OKF)

variable {P : EP}

/-! ## The private-key operation and `D` -/

theorem privArgs_vp : VP (S P) (.block privArgs) (R1 P) :=
  VP.taint [.esp] privArgs_taint (sp_agree fun _ _ h => h) fun _ _ h => privArgs_wp h

theorem dZero_vp : VP (R2 P) (.block (saveR ++ dZero)) (D1 P) :=
  VP.taint [.esp] dZero_taint (sp_agree fun _ _ h => h.1) fun _ _ h => dZero_wp h

theorem zero_vp : VP (D1 P) zeroLoop (D2 P) :=
  VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => zero_wp h

theorem dCopy_vp : VP (D2 P) (.block dCopy) (D3 P) :=
  VP.taint [.esp] dCopy_taint (sp_agree fun _ _ h => h.1.1) fun _ _ h => dCopy_wp h

theorem copy_vp : VP (D3 P) Impl.Bignum.X86.copyBytes (D4 P) :=
  VP.taint [.esi, .ebx, .ecx] copyBytes_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) fun _ _ h => copy_wp h

/-! ## `KDK` -/

theorem kdkMac_vp (v : Backend) : VP (H6 P) (kdkMac v.F) (K6 P) :=
  kdkInitArgs_vp.seq ((kdkInit_vp v).seq (kdkUpdArgs_vp.seq ((kdkUpd_vp v).seq (kdkFinArgs_vp.seq
    (kdkFin_vp v)))))

/-! ## The padding and the output -/

theorem validBlock_vp : VP (SCQ P) (.block validBlock) (VB P) := by
  have := validHead_vp.block_append (validRest_vp (P := P))
  rwa [List.take_append_drop] at this

theorem mlStore_vp : VP (VB P) (.block mlStore) (VW P) := by
  have := mlHead_vp.block_append (mlRest_vp (P := P))
  rwa [List.take_append_drop] at this

theorem selPart_vp : VP (AL P) selPart (Fin P) :=
  scanInit_vp.seq (scanLoop_vp.seq (validBlock_vp.seq (mlStore_vp.seq (selInit_vp.seq (selLoop_vp.seq
    finR_vp)))))

/-! ## The body -/

theorem body_vp (v : Backend) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (S P) (body v.F (privName c) (Proof.Rsa.X86.PrivChecked.privCode c)) (Fin P) :=
  privArgs_vp.seq ((call_vp c).seq (dZero_vp.seq (zero_vp.seq (dCopy_vp.seq (copy_vp.seq ((hashD_vp v).seq
    ((kdkMac_vp v).seq ((clLoop_vp v).seq ((amLoop_vp v).seq (alPart_vp.seq selPart_vp))))))))))

theorem prfBody_noSp (v : Backend) {label : List Nat} {len : List Instr} {dst : Nat}
    (hm : NoSp (.block (msgPtr ++ msgBytes label len) : Prog isa))
    (hu : NoSp (.block (prfUpdArgs (label.length + 4)) : Prog isa))
    (hf : NoSp (.block (prfFinArgs (label.length + 4) dst) : Prog isa)) :
    NoSp (prfBody v.F label len dst) :=
  noSp_seq hm (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (sha256OKF v).hiSp)
    (noSp_seq hu (noSp_seq (noSp_pushCall (hk v).updSp) (noSp_seq hf (noSp_seq (noSp_pushCall (sha256OKF v).hfSp)
      (.of_all (by decide +kernel))))))))

theorem body_noSp (v : Backend) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (body v.F (privName c) (Proof.Rsa.X86.PrivChecked.privCode c)) := by
  refine noSp_seq (.of_all (by decide +kernel))
    (noSp_seq (noSp_call (Proof.Rsa.X86.PrivChecked.privateCode_noSp c)) ?_)
  refine noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel)) ?_)
  refine noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel)) ?_)
  refine noSp_seq ?_ (noSp_seq ?_ (noSp_seq ?_ (noSp_seq ?_
    (noSp_seq (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).initSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).updSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_pushCall (hk v).finSp)))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (sha256OKF v).hiSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_pushCall (hk v).updSp)
      (noSp_seq (.of_all (by decide +kernel)) (noSp_pushCall (sha256OKF v).hfSp)))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_loop (prfBody_noSp v (.of_all (by decide +kernel))
      (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))
  · exact noSp_seq (.of_all (by decide +kernel)) (noSp_loop (prfBody_noSp v (.of_all (by decide +kernel))
      (.of_all (by decide +kernel)) (.of_all (by decide +kernel))))

end VG.Proof.RsaPkcs1Enc.X86.Dec
