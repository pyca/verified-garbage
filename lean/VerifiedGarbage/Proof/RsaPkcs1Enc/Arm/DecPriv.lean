module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecBase
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.Rsa.Arm.PrivPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the private-key operation

The call's sixteen stack arguments, one word of the frame at a time
(`Slots`, `copySlot`, `privArgs_wp`), and the call of
`vg_rsa_private_checked` (`call_vp`, correct and constant time: its
arguments and the public key it reads are the same in two runs), which
writes `EM` or zeros to `out` and returns its result (`Priv`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.inp, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q,
    BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl,
    P.scr, BitVec.ofNat 32 P.sl] ++ if P.pc then [P.pre, BitVec.ofNat 32 P.prl] else []

/-- Their number. -/
abbrev ncall (P : EP) : Nat := if P.pc then 18 else 16

/-- The first `k` of them in the frame. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- The ciphertext and the private key. -/
abbrev cB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.inp) P.K
abbrev dB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.d) P.dl
abbrev pB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.p) P.pl
abbrev qB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.q) P.ql
abbrev dpB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dp) P.pl
abbrev dqB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dq) P.ql
abbrev qiB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.qinv) P.pl

/-- The private-key operation's result. -/
abbrev privO (P : EP) (σ : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked P.nB P.eB (cB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)

/-- What the call writes to `out` and returns. -/
def Priv (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.writtenOutcome m (State.addr P.out) P.K r (privO P σ)

/-- Before the call. -/
def R1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Slots P s.mem (ncall P) ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.n ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K

/-- After the call. -/
def R2 (P : EP) (σ s : State) : Prop := S P σ s ∧ Priv P σ s.mem (s.gpr .r0)

theorem S.nB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB :=
  (hs.2.ro (R := P.N) (by simp)).trans hs.1.nB

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem arg_lt {j : Nat} (hj : j < 25) : Impl.RsaPkcs1Sig.Arm.argOff frameBytes j < 4096 := by
  unfold Impl.RsaPkcs1Sig.Arm.argOff
  split <;> simp only [frameBytes] <;> omega_using [hj]

/-- `str r0, [r12, #4k]` of the stack argument `k`. -/
theorem strSlot {σ s : State} {k : Nat} (h : S P σ s) (hs : Slots P s.mem k) (hk : k < 18)
    (h12 : s.gpr .r12 = P.B) (hv : s.gpr .r0 = (outv P).getD k 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, S P σ t → Slots P t.mem (k + 1) → t.gpr = s.gpr → WP isa (.block is) t Q) :
    WP isa (.block (.str .r0 .r12 (4 * k) :: is)) s Q := by
  refine h.2.wp_strFr (d := 4 * k) (by show 4 * k + 4 ≤ frameBytes; simp only [frameBytes]; omega_using [hk]) (by omega_using [hk]) h12
    fun t st m => kk t ⟨h.1, st⟩ ?_ m.gpr
  intro i hi
  rw [m.mem]
  rcases (by omega_using [hi] : i = k ∨ i < k) with rfl | hik
  · rw [Mem.readW_writeW_self32, hv]
  · rw [Lay.readW_fr_other _ _ _ (by omega_using [hik]) (by omega_using [hk, hi]) (by omega_using [hk])]
    exact hs i hik

/-- Argument `j` to the call's stack argument `k`. -/
theorem argv23 (P : EP) : 23 ≤ P.argv.length := by
  simp only [EP.argv, List.length_append, List.length_cons, List.length_nil]; omega_using []

theorem copySlot {σ s : State} {k j : Nat} (h : S P σ s) (hs : Slots P s.mem k) (hk : k < 18)
    (h12 : s.gpr .r12 = P.B) (hj : j < 25) (hjl : j < P.argv.length) (hv : P.argv.getD j 0 = (outv P).getD k 0)
    {is : List Instr}
    {Q : State → Prop} (kk : ∀ t, S P σ t → Slots P t.mem (k + 1) → t.gpr .r12 = P.B → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j k ++ is)) s Q :=
  h.2.wp_arg (j := j) hjl (arg_lt hj)
    fun t1 s1 u1 => strSlot ⟨h.1, s1⟩ (by rw [u1.mem]; exact hs)
      hk (by rw [u1.other _ (by decide), h12]) (by rw [u1.gpr, hv])
      fun t st sl g => kk t st sl (by rw [g, u1.other _ (by decide), h12])

theorem privStack_wp {σ s : State} (h : S P σ s) :
    WP isa (.block privStack) s fun t => S P σ t ∧ Slots P t.mem 16 ∧ t.gpr .r12 = P.B := by
  simp only [privStack, List.append_assoc, List.cons_append, List.nil_append]
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  have h0 : S P σ t0 := ⟨h.1, h.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem⟩
  have r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, h.2.sp, BitVec.add_zero]
  have z : Slots P t0.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h0 z (by decide) r12 (j := 5) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t1 h1 z1 r1 => ?_
  refine copySlot h1 z1 (by decide) r1 (j := 6) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t2 h2 z2 r2 => ?_
  refine copySlot h2 z2 (by decide) r2 (j := 9) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t3 h3 z3 r3 => ?_
  refine copySlot h3 z3 (by decide) r3 (j := 4) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t4 h4 z4 r4 => ?_
  refine copySlot h4 z4 (by decide) r4 (j := 11) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t5 h5 z5 r5 => ?_
  refine copySlot h5 z5 (by decide) r5 (j := 12) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t6 h6 z6 r6 => ?_
  refine copySlot h6 z6 (by decide) r6 (j := 13) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t7 h7 z7 r7 => ?_
  refine copySlot h7 z7 (by decide) r7 (j := 14) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t8 h8 z8 r8 => ?_
  refine copySlot h8 z8 (by decide) r8 (j := 15) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t9 h9 z9 r9 => ?_
  refine copySlot h9 z9 (by decide) r9 (j := 16) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t10 h10 z10 r10 => ?_
  refine copySlot h10 z10 (by decide) r10 (j := 17) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t11 h11 z11 r11 => ?_
  refine copySlot h11 z11 (by decide) r11 (j := 18) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t12 h12 z12 r12 => ?_
  refine copySlot h12 z12 (by decide) r12 (j := 19) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t13 h13 z13 r13 => ?_
  refine copySlot h13 z13 (by decide) r13 (j := 20) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t14 h14 z14 r14 => ?_
  refine copySlot h14 z14 (by decide) r14 (j := 21) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t15 h15 z15 r15 => ?_
  refine copySlot h15 z15 (by decide) r15 (j := 22) (by decide) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) rfl fun t16 h16 z16 r16 => ?_
  exact WP.block_nil ⟨h16, z16, r16⟩

theorem privPre_wp {σ s : State} (h : S P σ s) (z : Slots P s.mem 16) (r12 : s.gpr .r12 = P.B) :
    WP isa (.block (privPre P.pc)) s fun t => S P σ t ∧ Slots P t.mem (ncall P) := by
  unfold privPre ncall
  cases hpc : P.pc
  · exact WP.block_nil ⟨h, z⟩
  · have len : P.argv.length = 25 := by simp [EP.argv, hpc]
    rw [← List.append_nil (copyArg 24 17)]
    refine copySlot h z (by decide) r12 (j := 23) (by decide) (by omega_using [len]) (by simp [EP.argv, outv, hpc])
      fun t1 h1 z1 r1 => ?_
    refine copySlot h1 z1 (by decide) r1 (j := 24) (by decide) (by omega_using [len]) (by simp [EP.argv, outv, hpc])
      fun t2 h2 z2 _ => WP.block_nil ⟨h2, z2⟩

theorem privRegs_wp {σ s : State} (h : S P σ s) (z : Slots P s.mem (ncall P)) :
    WP isa (.block privRegs) s (R1 P σ) := by
  have s16 := h.2
  refine s16.wp_arg (j := 0) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) (by dsimp only; decide) fun t17 s17 u17 => ?_
  refine s17.wp_arg (j := 4) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) (by dsimp only; decide) fun t18 s18 u18 => ?_
  refine s18.wp_arg (j := 3) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) (by dsimp only; decide) fun t19 s19 u19 => ?_
  refine s19.wp_arg (j := 4) (Nat.lt_of_lt_of_le (by decide) (argv23 P)) (by dsimp only; decide)
    fun t20 s20 u20 => WP.block_nil ?_
  have mm : t20.mem = s.mem := by rw [u20.mem, u19.mem, u18.mem, u17.mem]
  refine ⟨⟨h.1, s20⟩, by rw [mm]; exact z, ?_, ?_, ?_, ?_⟩
  · rw [u20.other _ (by decide), u19.other _ (by decide), u18.other _ (by decide), u17.gpr]; rfl
  · rw [u20.other _ (by decide), u19.other _ (by decide), u18.gpr]; rfl
  · rw [u20.other _ (by decide), u19.gpr]; rfl
  · rw [u20.gpr]; rfl

theorem privArgs_wp {σ s : State} (h : S P σ s) : WP isa (.block (privArgs P.pc)) s (R1 P σ) := by
  rw [privArgs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (privStack_wp h) fun t ⟨ht, z, r12⟩ => ?_
  exact WP.mono (privPre_wp ht z r12) fun u ⟨hu, zu⟩ => privRegs_wp hu zu

theorem R1.privArgs {σ s : State} (h : R1 P σ s) :
    PrivArgs s P.out P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.scr P.K P.el P.pl P.ql P.sl := by
  obtain ⟨hs, oa, r0, r1, r2, r3⟩ := h
  have a : ∀ i < 16, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i (by unfold ncall; split <;> omega_using [hi])]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (P.lt_lay (by simp only [frameBytes]; omega_using [hi]))]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
    a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), h1.kv, h1.el1,
    h1.elK, h1.pl1, h1.plK, h1.ql1, h1.qlK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_using [this]⟩

theorem call_pre {σ s : State} (h : R1 P σ s) :
    (Proof.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd P.B P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.K P.el
        P.pl P.ql) (privWr P.out P.scr P.K P.sl)) := by
  have hs := h.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have dOS : P.OUT.Disjoint P.SCR := by
    have := ok.wrw
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at this
    exact this.1.2
  refine priv_pre h.privArgs hs.2.sp hB (by simp only [frameBytes] at fit; omega_using [fit]) ?_ dOS ?_ ?_
  · intro w hw r hr
    have hw' : w ∈ P.lay.rw := by
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp
    simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · rw [q0]; exact (ok.stk_fr (d := 0) (n := 64) (.inr hw') (by simp only [frameBytes]; omega_using [])).symm
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact ok.low_buf (R := P.SCR) (.inr (by simp))
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact ok.low_buf (R := P.INP) (.inl (by simp))
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)

theorem call_vp (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1 P) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (R2 P) := by
  refine VP.callF (Proof.Rsa.Arm.code_verified v) (privCode_stack v)
    (privRd P.B P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.out P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1
    have ok := hs.1.ok
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (privWr P.out P.scr P.K P.sl) s.wr := (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine (hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons (Covers.cons ?_ Covers.nil))))))
    rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 64 ≤ frameBytes; decide))).right
  · rw [h.1.2.sp]; exact h.1.1.ok.B56
  · exact priv_pub h₁.privArgs h₂.privArgs (by rw [h₁.1.2.sp, h₂.1.2.sp]) (by rw [h₁.1.nB, h₂.1.nB])
      (by rw [h₁.1.eB, h₂.1.eB]) _ _
  · have hh := h
    obtain ⟨hs, -, -⟩ := h
    have ok := hs.1.ok
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hs.1, st⟩, ?_⟩
    have := priv_post hh.privArgs po
    rw [hs.nB, hs.eB, hs.2.ro (R := P.INP) (by simp), hs.2.ro (R := P.PP) (by simp), hs.2.ro (R := P.QQ) (by simp),
      hs.2.ro (R := P.DP) (by simp), hs.2.ro (R := P.DQ) (by simp), hs.2.ro (R := P.QI) (by simp)] at this
    exact this

/-! ## `vg_rsa_private_checked_precomputed` -/

theorem R1.preArgs {σ s : State} (hpc : P.pc = true) (h : R1 P σ s) :
    stackArg s 16 = P.pre ∧ stackArg s 17 = BitVec.ofNat 32 P.prl := by
  obtain ⟨hs, oa, -⟩ := h
  have a : ∀ i < 18, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i (by unfold ncall; rw [hpc]; exact hi)]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (P.lt_lay (by simp only [frameBytes]; omega_using [hi]))]
  refine ⟨(a 16 (by decide)).trans ?_, (a 17 (by decide)).trans ?_⟩ <;> simp [outv, hpc]

theorem In.prl32 {σ : State} (hpc : P.pc = true) (h : In P σ) : P.prl < 2 ^ 32 := by
  have := h.ok.fits P.PRE (List.mem_append_left _ (by simp [EP.ro, hpc]))
  simp only [Proof.X25519.Arm.addr_toNat] at this
  omega_using [this]

theorem call_preP {σ s : State} (hpc : P.pc = true) (h : R1 P σ s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRdP P.B P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.pre
        P.K P.el P.pl P.ql P.prl) (privWr P.out P.scr P.K P.sl)) := by
  have hs := h.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  have preRo : P.PRE ∈ P.lay.ro := by simp [EP.ro, hpc]
  have hA : P.lay.A = 84 := by simp [hpc]
  rw [hA] at fit
  have dOS : P.OUT.Disjoint P.SCR := by
    have := ok.wrw
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at this
    exact this.1.2
  obtain ⟨a16, a17⟩ := h.preArgs hpc
  refine priv_preP h.privArgs a16 a17 (hs.1.prl32 hpc) hs.2.sp hB (by simp only [frameBytes] at fit; omega_using [fit]) ?_
    dOS ?_ ?_ (hs.1.prl hpc) ?_
  · intro w hw r hr
    have hw' : w ∈ P.lay.rw := by
      simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp
    simp only [privRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' (by simp)
    · exact ok.rw_ro hw' preRo
    · rw [q0]; exact (ok.stk_fr (d := 0) (n := 72) (.inr hw') (by simp only [frameBytes]; omega_using [])).symm
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = P.lay.LOW := rfl
    rw [low]
    simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact ok.low_buf (R := P.SCR) (.inr (by simp))
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact ok.low_buf (R := P.INP) (.inl (by simp))
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · exact ok.low_buf (R := P.PRE) (.inl preRo)
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (List.mem_append_left _ preRo)
  · have rn := hs.2.ro (R := P.N) (by simp)
    have rp := hs.2.ro (R := P.PP) (by simp)
    have rq := hs.2.ro (R := P.QQ) (by simp)
    have rw := hs.2.ro_words (R := P.PRE) preRo (n := P.prl) rfl
    dsimp only at rn rp rq rw
    rw [rn, rp, rq, rw]
    exact hs.1.pre hpc

theorem leak_st {σ s : State} (hpc : P.pc = true) (hs : S P σ s) :
    Spec.Rsa.privatePrecomputedLeak s.mem (State.addr P.pre) P.K = P.preL := by
  have preRo : P.PRE ∈ P.lay.ro := by simp [EP.ro, hpc]
  have le : Spec.Rsa.precomputedWords P.K ≤ P.prl := by
    rw [hs.1.prl hpc, Spec.Rsa.privatePrecomputedWords]; omega_using []
  have rw := hs.2.ro_words (R := P.PRE) preRo (n := P.prl) rfl
  dsimp only at rw
  rw [← hs.1.preL hpc]
  unfold Spec.Rsa.privatePrecomputedLeak
  rw [Proof.Rsa.Arm.wordsAt_take le, Proof.Rsa.Arm.wordsAt_take (m := σ.mem) le, rw]

theorem call_vpP (v : Proof.Rsa.Arm.CrtImpl) (hpc : P.pc = true) :
    VP (R1 P) (.call (Proof.Rsa.Arm.privNameP v) (Proof.Rsa.Arm.privCodeP v)) (R2 P) := by
  refine VP.callC (fun s h => Proof.Rsa.Arm.private_contract_correctP v s h) (Proof.Rsa.Arm.private_contract_ctP v)
    (privCodeP_stack v)
    (privRdP P.B P.n P.e P.inp P.p P.q P.dp P.dq P.qinv P.pre P.K P.el P.pl P.ql P.prl)
    (privWr P.out P.scr P.K P.sl) (fun _ _ h => call_preP hpc h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1
    have ok := hs.1.ok
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    have wr : Covers (privWr P.out P.scr P.K P.sl) s.wr := (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine (hro P.INP (by simp)).cons ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons ((hro P.PRE (by simp [EP.ro, hpc])).cons
        (Covers.cons ?_ Covers.nil)))))))
    rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 72 ≤ frameBytes; decide))).right
  · rw [h.1.2.sp]; exact h.1.1.ok.B56
  · obtain ⟨p16, p17⟩ := h₁.preArgs hpc
    obtain ⟨q16, q17⟩ := h₂.preArgs hpc
    exact priv_pubP h₁.privArgs h₂.privArgs (by rw [h₁.1.2.sp, h₂.1.2.sp]) p16 q16 p17 q17
      (by rw [h₁.1.nB, h₂.1.nB]) (by rw [h₁.1.eB, h₂.1.eB])
      (by rw [leak_st hpc h₁.1, leak_st hpc h₂.1]) _ _
  · have hh := h
    obtain ⟨hs, -, -⟩ := h
    have ok := hs.1.ok
    have low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    have st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hs.1, st⟩, ?_⟩
    have := priv_postP hh.privArgs po
    rw [hs.nB, hs.eB, hs.2.ro (R := P.INP) (by simp), hs.2.ro (R := P.PP) (by simp), hs.2.ro (R := P.QQ) (by simp),
      hs.2.ro (R := P.DP) (by simp), hs.2.ro (R := P.DQ) (by simp), hs.2.ro (R := P.QI) (by simp)] at this
    exact this

/-- The checked private operation the code calls: with `pc`,
`vg_rsa_private_checked_precomputed`. -/
def privN (pc : Bool) (v : Proof.Rsa.Arm.CrtImpl) : String :=
  if pc then Proof.Rsa.Arm.privNameP v else Proof.Rsa.Arm.privName v
def privC (pc : Bool) (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  if pc then Proof.Rsa.Arm.privCodeP v else Proof.Rsa.Arm.privCode v

theorem call_vpG (v : Proof.Rsa.Arm.CrtImpl) : VP (R1 P) (.call (privN P.pc v) (privC P.pc v)) (R2 P) := by
  cases hpc : P.pc
  · exact call_vp v
  · exact call_vpP v hpc

end VG.Proof.RsaPkcs1Enc.Arm.Dec
