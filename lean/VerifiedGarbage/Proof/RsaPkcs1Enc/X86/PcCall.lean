module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcPieces
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the call

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcCall.lean`): the call's ten
arguments at the frame's base (`Slots`, `callArgs_wp`), and the call of
`vg_rsa_public_precomputed_checked` (`call_vp`, correct and constant time:
its arguments and the public data it reads are the same in two runs), which
writes `EM^e mod n` or zeros to `out` (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  pubArgv P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.rl P.el P.sl

/-- The first `k` of them in place. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def G7 (P : EP) (σ s : State) : Prop := G6 P σ s ∧ Slots P s.mem 10

/-- What the call writes and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r (Spec.Rsa.publicOpChecked nB P.eB (enc P σ))

/-- After the call. -/
def G8 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ CR P σ s.mem (s.gpr .eax)

theorem G6.upd {σ s t : State} (h : G6 P σ s) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) :
    G6 P σ t :=
  ⟨⟨h.1.1, h.1.2.upd u hd⟩, by rw [Zs, u.mem]; exact h.2.1, h.2.2.of_mem u.mem⟩

/-- `mov [esp + 4 i], eax`: the call's argument `i`. -/
theorem slotStore {σ s : State} {i : Nat} (h : G6 P σ s) (hs : Slots P s.mem i) (hi : i < 10)
    (hv : s.gpr .eax = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, G6 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (.store (Impl.RsaPkcs1Sig.X86.stk (4 * i)) .eax :: is)) s Q := by
  have hK := h.1.1.k1024
  refine h.1.2.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega_arith)
    fun t s2 m2 => kk t ⟨⟨h.1.1, s2⟩, ?_, ?_⟩ ?_
  · rw [Zs, m2.mem, Lay.readW_fr_other _ _ _ (by simp only [oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by omega_arith)]
    exact h.2.1
  · refine EMok.frame h.2.2 (rs := [⟨P.lay.fr (4 * i), 4⟩]) ?_ fun k hk r hr => ?_
    · rw [m2.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith) (by omega_arith)
  · intro k hk
    rw [m2.mem]
    rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
    · rw [Mem.readW_writeW_self32, hv]
    · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {σ s : State} {i j : Nat} (h : G6 P σ s) (hs : Slots P s.mem i) (hi : i < 10)
    (hj : j < 14) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, G6 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q :=
  h.1.2.wp_arg (j := j) (by simp only [EP.argv, List.length_cons, List.length_nil]; omega_arith) (by decide)
    fun t1 _ u1 => slotStore (h.upd u1 (by decide)) (fun k hk => by rw [u1.mem]; exact hs k hk) hi
      (by rw [u1.gpr, hv]) kk

theorem callArgs_wp {σ s : State} (h : G6 P σ s) : WP isa (.block callArgs) s (G7 P σ) := by
  simp only [callArgs, List.append_assoc, List.cons_append, List.nil_append]
  have z0 : Slots P s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h z0 (by decide) (j := 0) (by decide) rfl fun t1 h1 z1 => ?_
  refine copySlot h1 z1 (by decide) (j := 3) (by decide) rfl fun t2 h2 z2 => ?_
  refine copySlot h2 z2 (by decide) (j := 12) (by decide) rfl fun t3 h3 z3 => ?_
  refine copySlot h3 z3 (by decide) (j := 13) (by decide) rfl fun t4 h4 z4 => ?_
  refine copySlot h4 z4 (by decide) (j := 4) (by decide) rfl fun t5 h5 z5 => ?_
  refine copySlot h5 z5 (by decide) (j := 5) (by decide) rfl fun t6 h6 z6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  have h8 := (h6.upd u7 (by decide)).upd u8 (by decide)
  refine slotStore (i := 6) h8 (fun k hk => by rw [u8.mem, u7.mem]; exact z6 k hk) (by decide)
    (by rw [u8.gpr, u7.gpr, h6.1.2.sp]; rfl) fun t9 h9 z9 => ?_
  refine copySlot h9 z9 (by decide) (j := 3) (by decide) rfl fun t10 h10 z10 => ?_
  refine copySlot h10 z10 (by decide) (j := 10) (by decide) rfl fun t11 h11 z11 => ?_
  refine copySlot h11 z11 (by decide) (j := 11) (by decide) rfl fun t12 h12 z12 => ?_
  exact WP.block_nil ⟨h12, z12⟩

theorem In.fit {σ : State} (h : In P σ) : P.B.toNat + frameBytes + 76 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil] at this
  omega_arith

theorem In.BC {σ : State} (h : In P σ) : 100 ≤ P.B.toNat := h.ok.BC

/-- `EM`, as the call reads it. -/
theorem In.emA {σ : State} (h : In P σ) : (P.B + BitVec.ofNat 32 oEM).setWidth 64 = P.lay.fr oEM :=
  h.ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, oEM, frameBytes]; omega_arith)

/-- The call's arguments, at the frame's base. -/
theorem argsA (P : EP) : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨P.lay.fr 0, 40⟩ := by
  simp

theorem G7.pubArgs {σ s : State} (h : G7 P σ s) :
    PubArgs s P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.rl P.el P.sl := by
  obtain ⟨⟨hs, -, -⟩, sl⟩ := h
  have fit := hs.1.fit
  refine ⟨fun i hi => ?_, ?_, ?_, hs.1.kv, hs.1.rlK, hs.1.el1, hs.1.elK, hs.1.slK, hs.1.sl32⟩
  · have hd : 4 * i < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit ⊢; omega_arith
    rw [hs.2.sp, hs.1.ok.addrB hd]
    exact sl i hi
  · rw [show s.gpr .esp = P.B from hs.2.sp]; exact hs.1.BC
  · rw [show s.gpr .esp = P.B from hs.2.sp]; simp only [frameBytes] at fit; omega_arith

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

/-- `pre`'s words, in a state of the body. -/
theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hs.1.ok
  have hR : P.PRE ∈ P.lay.ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.2.frame (fun r hr => ?_) (by omega_arith)).trans hs.1.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.OUT (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `pre`'s words, in a callee's entry state. -/
theorem S.callPw {σ s : State} (hs : S P σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hs.1.ok
  have hR : P.PRE ∈ P.lay.ro := by simp
  have hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.2.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
    (by omega_arith)).trans hs.pw
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem EMok.bytes {σ s : State} (h : EMok P σ s P.K) (hK : P.pl + P.ml + 3 = P.K) :
    Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = enc P σ := by
  have hl := enc_length P σ
  rw [show P.K = (enc P σ).length by omega_arith]
  exact Proof.RsaPkcs1Sig.bytesAt_eq fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]; exact h i (by omega_arith)

theorem call_vp (c : Ver.PublicImpl) : VP (G7 P) (.call c.name c.code) (G8 P) := by
  refine VP.call c.verified.1 c.verified.2.1 c.noSp
    (pubRd P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.rl P.el) (pubWr P.B P.out P.scr P.K P.sl)
    (fun σ s h => ?_) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' h rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have fit := hs.1.fit
    have hsp : s.gpr .esp = P.B := hs.2.sp
    have em := hs.1.emA
    have ar := argsA P
    have := pub_pre h.pubArgs ?_ ?_ ?_ ?_
    · rw [hsp] at this; exact this
    all_goals rw [hsp]
    · intro w hw r hr
      simp only [pubWr, pubRd, List.mem_cons, List.not_mem_nil, or_false] at hw hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.PRE) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.E) (by simp)
      · rw [em]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.PRE) (by simp)
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.E) (by simp)
      · rw [em]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm
      · rw [ar]; exact ok.stk_fr (R := P.PRE) (.inl (by simp)) (by simp only [frameBytes]; omega_arith)
      · rw [ar]; exact ok.stk_fr (R := P.E) (.inl (by simp)) (by simp only [frameBytes]; omega_arith)
      · rw [ar, em]; exact Lay.fr_sep (by simp only [oEM]; omega_arith) (by omega_arith) (by simp only [oEM]; omega_arith)
    · simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq] at ww
      refine ⟨⟨ww.1, ?_⟩, ?_⟩
      · rw [ar]; exact (ok.stk_fr (R := P.OUT) (d := 0) (n := 40) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega_arith)).symm
      · rw [ar]; exact ⟨(ok.stk_fr (R := P.SCR) (d := 0) (n := 40) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega_arith)).symm, fun _ h => h.elim⟩
    · intro r hr
      rw [show below P.B 100 = P.lay.LOW from ok.low_eq]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [ar]; exact (Lay.fr_low (by omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact ok.low_buf (R := P.PRE) (.inl (by simp))
      · exact ok.low_buf (R := P.E) (.inl (by simp))
      · rw [em]; exact (Lay.fr_low (by simp only [oEM]; omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm
    · intro r hr
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      have hfr : ∀ d, d ≤ frameBytes → (P.lay.fr d).toNat = P.B.toNat + d := fun d hd =>
        Lay.fr_toNat (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil] at fit ⊢; omega_arith)
          (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil]; omega_arith)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [ar]; show (P.lay.fr 0).toNat + 40 ≤ _; rw [hfr 0 (by decide)]; simp only [frameBytes] at fit; omega_arith
      · exact ok.fits P.PRE (by simp)
      · exact ok.fits P.E (by simp)
      · rw [em]; show (P.lay.fr oEM).toNat + P.K ≤ _
        rw [hfr oEM (by decide)]; simp only [oEM, frameBytes] at fit ⊢; omega_arith
  · -- What the callee is given is ours.
    have hs := h.1.1
    have hK := hs.1.k1024
    have em := hs.1.emA
    have ar := argsA P
    have hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    have hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    have hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      rw [ar]; exact Covers.one (hs.2.inFr (by simp only [frameBytes]; omega_arith))
    have hE : Covers [⟨(P.B + BitVec.ofNat 32 oEM).setWidth 64, P.K⟩] (s.rd ++ s.wr) := by
      rw [em]; exact Covers.one (hs.2.inFrR (by simp only [oEM, frameBytes]; omega_arith))
    have wr : Covers (pubWr P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    exact ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons (hE.cons Covers.nil)))
      wr.right, wr⟩
  · rw [show s.gpr .esp = P.B from h.1.1.2.sp]
    have := h.1.1.1.BC
    have := c.stack
    omega_arith
  · refine pub_pub h₁.pubArgs h₂.pubArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [h₁.1.1.pw, h₂.1.1.pw]
    · rw [h₁.1.1.eB, h₂.1.1.eB]
    · rw [h₁.1.1.2.sp, show below P.lay.B 100 = P.lay.LOW from h₁.1.1.1.ok.low_eq]
      exact h₁.1.1.1.ok.low_buf (R := P.PRE) (.inl (by simp))
    · rw [h₁.1.1.2.sp, show below P.lay.B 100 = P.lay.LOW from h₁.1.1.1.ok.low_eq]
      exact h₁.1.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have hh := h
    obtain ⟨⟨hs, zs, emk⟩, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have hpl := hs.1.em_len
    have hsp := hs.2.sp
    have ar := argsA P
    have low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 100; omega_arith) ok.BC
    have hw : ∀ r ∈ pubWr P.B P.out P.scr P.K P.sl ++ [below (s.gpr .esp) (stackUse c.code + 4)],
        ∃ R ∈ P.lay.W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        rw [ar]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨P.lay.LOW, by simp, low⟩
    have st : P.lay.St σ s' := hs.2.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    have apart : ∀ {d n : Nat}, 40 ≤ d → d + n ≤ frameBytes →
        ∀ r ∈ pubWr P.B P.out P.scr P.K P.sl ++ [below (s.gpr .esp) (stackUse c.code + 4)],
        Region.Disjoint ⟨P.lay.fr d, n⟩ r := fun h0 hd r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 16; omega_arith)
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 16; omega_arith)
      · rw [ar]; exact Lay.fr_sep (by omega_arith) (by simp only [frameBytes] at hd; omega_arith) (by decide)
      · exact (Lay.fr_low (by simp only [frameBytes] at hd; omega_arith)
          (by show (100 : Nat) ≤ 2 ^ 32; decide)).sub_right low
    refine ⟨⟨hs.1, st⟩, ?_, fun nB hn hp => ?_⟩
    · rw [Zs, fr.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _)
        (apart (by simp only [oZ]; omega_arith) (by simp only [oZ, frameBytes]; omega_arith)) (by decide)]
      exact zs
    · obtain ⟨s₂, m₂, g₂, po⟩ := po
      have := pub_post hh.pubArgs po nB hn (by rw [hs.callPw]; exact hp)
      rw [m₂, g₂ .eax (by decide)] at this
      have eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
        (hs.2.callEntry_ro (by show 4 ≤ 100; decide) (R := P.E) (by simp)).trans hs.1.eB
      have eM : Spec.Rsa.bytesAt s.callEntry.mem ((P.B + BitVec.ofNat 32 oEM).setWidth 64) P.K = enc P σ := by
        rw [hs.1.emA]
        refine (Proof.RsaPkcs1Sig.bytesAt_frame (hs.2.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
          (by omega_arith)).trans (emk.bytes hpl)
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.fr_low (by simp only [oEM]; omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)
      rw [eE, eM] at this
      exact this

end VG.Proof.RsaPkcs1Enc.X86.Pc
