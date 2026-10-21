module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Rows
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Base
public import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EkInline16

/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`, constant time

Two runs whose pointers and `ρ` agree leak the same (`kemKeyGenH16_ct`):
every piece but the matrix's fragments and the branches on their results
leaks only the pointers (taint checks from them, `KgH16T`, and the
callees' contracts); the fragments sample from the seeds of `ρ`
(`sampleHAtM16_tr`), and the branches test `r15`, which only `ρ` decides.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of the fragment absorbing `m` blocks inlined, from the same seeds and pointers. -/
theorem sampleHAtM16_tr {m : Nat} {b : Prog isa} (hb : BatchHMOk16 m b) {oa oz : Nat} :
    RelCT isa (fun x y => SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (Encaps.sampleHAt b (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (regionModel.relCT_inline (Pre := (sampleHMKW true m).pre)
      (Pub := (sampleHMKW true m).pub) (fun s hs => let ⟨t, s', e, _, p⟩ := hb.ok s hs; ⟨t, s', e, p⟩) hb.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, shPreM16 m hx hv1 k1, shPreM16 m hy hv2 k2, ?_,
    by show Covers _ (x1.rd ++ x1.wr); rw [k1.2.1, k1.2.2]; exact hx.c,
    by show Covers _ x1.wr; rw [k1.2.2]; exact hx.w,
    by show Covers _ (y1.rd ++ y1.wr); rw [k2.2.1, k2.2.2]; exact hy.c,
    by show Covers _ y1.wr; rw [k2.2.2]; exact hy.w⟩
  show sample4K.pub (x1.withRegions _ _) (y1.withRegions _ _)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1,
    hv2.2.2, hm1, hm2, e4, hs1, hs2, e3]
  simp only [pa, e1, and_self]

/-- Two runs of the fragment computing outputs of `PRF₂` inlined, from the same seeds and pointers. -/
theorem sampleHAtP16_tr {b : Prog isa} (hb : BatchPOk16 b) {oa oz : Nat} :
    RelCT isa (fun x y => SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (Encaps.sampleHAt b (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (regionModel.relCT_inline (Pre := samplePKW.pre)
      (Pub := samplePKW.pub) (fun s hs => let ⟨t, s', e, _, p⟩ := hb.ok s hs; ⟨t, s', e, p⟩) hb.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, shPre16 hx hv1 k1, shPre16 hy hv2 k2, ?_,
    by show Covers _ (x1.rd ++ x1.wr); rw [k1.2.1, k1.2.2]; exact hx.c,
    by show Covers _ x1.wr; rw [k1.2.2]; exact hx.w,
    by show Covers _ (y1.rd ++ y1.wr); rw [k2.2.1, k2.2.2]; exact hy.c,
    by show Covers _ y1.wr; rw [k2.2.2]; exact hy.w⟩
  show sample4K.pub (x1.withRegions _ _) (y1.withRegions _ _)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1,
    hv2.2.2, hm1, hm2, e4, hs1, hs2, e3]
  simp only [pa, e1, and_self]

namespace KeyGenH

open KeyGen KeyGen16 VG.Impl.MlKem.X86_64.Top16 VG.Impl.MlKem.X86_64.KeyGenH16

variable (K : Kem16)

/-- The taint checks of the pieces that leak only the pointers. -/
structure KgH16T : Prop where
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (.block (Encaps16.hzero K)) h).isSome = true
  cT : ∀ i < 3, (hm i).1 ≠ 0 → ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1)) h).isSome = true
  sT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (sc 0) (sc (Encaps16.oHS K)) 200) h).isSome = true
  pT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (sc (K.oW + Sample4.oPS)) (sc (oG + 32)) 32) h).isSome = true

variable {K}

section
variable (W : KgH16Wf K)
include W

/-- A piece whose taint check from the pointers passes. -/
theorem trK {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true) :
    RelCT isa (LRel kgR (kgW K.L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r13] (fun _ _ h =>
    fa4 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2)) ht

/-! ## Before the rows -/

theorem prfs_tr (v : Sample4Impl) :
    RelCT isa (R K.L fun σ s => KA K.L σ s ∧ s.gpr .r15 = 1) (v.callee.prfs 2 4 (K.oPR + 256) (K.oW / 32))
      (R K.L (KN K 2)) := by
  have Wb := W.toKgWfB
  have hc := W.pr
  simp only [Bool.and_eq_true] at hc
  exact relInv (fun σ s hp hs => prfs_ok W hp v hs.1 hs.2)
    (rel2_of (v.prfs_tr (kgB_bases K.L) (by omega) hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
      kc_lrel Wb p₁ p₂ pub h₁.1.kc h₂.1.kc)

theorem se_tr (v : Sample4Impl) :
    RelCT isa (R K.L (KN K 2)) (seqR (cbdN K v.callee.arith) 2 4) (R K.L (KN K 6)) := by
  have Wb := W.toKgWfB
  exact seqR_tr (R := fun k => R K.L (KN K k)) 4 2 fun N hN hN' =>
    relInv (fun σ s hp hs => se_ok W hp v.arith (by omega) hN hs)
      (rel2_of (cbd2_16At_trL v.arith rbx_na (by
          have h := W.se N (by omega); simp only [Bool.and_eq_true] at h; exact h.1))
        fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel Wb p₁ p₂ pub h₁.kc h₂.kc)

theorem hzG_tr (T : KgH16T K) : RelCT isa (R K.L (KG K · 0 false)) (.block (Encaps16.hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trK W t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W.toKgWfB p₁ p₂ pub h₁.kc h₂.kc

theorem cbdP_tr (v : Sample4Impl) {N : Nat} (hN : N < 2) :
    RelCT isa (R K.L (KG K · N true)) (cbdP K v.callee.arith N) fun _ _ => True :=
  rel2_of (cbd2_16At_trL v.arith rbx_na (by
      have h := W.cP N hN; simp only [Bool.and_eq_true] at h; exact h.1))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W.toKgWfB p₁ p₂ pub h₁.kc h₂.kc

theorem nttG_tr (hK : KgRowsOk K.L) : RelCT isa (R K.L (KG K · 2 true)) (nttAt K) fun _ _ => True := by
  have Wb := W.toKgWfB
  have k3 := W.k3
  have hc := W.nt
  simp only [Bool.and_eq_true] at hc
  have hkn : knChk (kgB K.L) (kgW K.L) K.L.k (.r13, 0) (sc oSH) (sc oEH) (sc K.oR) (sc oZK) = true := by
    rw [k3]; exact hc.1
  have red : ∀ {σ s}, KG K σ 2 true s → VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k) := fun h N hN => by
    rw [sc_w16]
    rcases (by omega : N < 2 ∨ 2 ≤ N) with h2 | h2
    exacts [(h.se0 N h2).1, (h.se N (by rw [k3] at hN; omega) h2).1]
  exact rel2_of (kgNttAt_trL hK rbx_na rbx_na rbx_na rbx_na hkn) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel Wb p₁ p₂ pub h₁.kc h₂.kc, red h₁, red h₂⟩

end

/-- After the noise, for the seed `ρ` of `Â`. -/
abbrev KNρ (K : Kem16) (ρ : List Byte) (x : State) : Prop :=
  ∃ σ, (keyGenK K.L).pre σ ∧ KN K 6 σ x ∧ rhoK K.L σ = ρ

section
variable (W : KgH16Wf K) (T : KgH16T K)
include W T

theorem frag0_tr (v : Sample4Impl) {p : Prog isa} (hpb : v.callee.batchP16 = some p) :
    RelCT isa (R K.L (KN K 6)) (frag0 K p) fun _ _ => True := by
  have Wb := W.toKgWfB
  have k3 := W.k3
  have hsd := W.sd0
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := W.sm0
  simp only [Bool.and_eq_true] at hsm
  have c4 := hsm.1
  have hB := v.batchP16 p hpb
  have hc0 := W.c0
  simp only [Bool.and_eq_true] at hc0
  obtain ⟨_, hr0⟩ := keepAll_spec hc0.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel kgR (kgW K.L) x y ∧ KNρ K ρ x ∧ KNρ K ρ y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag0
    have hok : ∀ x, KNρ K ρ x →
        WP isa (copy (sc (K.oW + Sample4.oPS)) (sc (oG + 32)) 32) x
          fun x' => PPostB x x' [(psP K, 32)] ∧ SeedsIs ρ K.L.k 0 0 x' := by
      rintro x ⟨σ, hp, h, e⟩
      have L₀ := h.kc.lay Wb hp
      exact WP.mono (copy_okL L₀ (dst := psP K) (src := sigP) (n := 32) (by decide) hc0.1) fun x' ⟨hP, _⟩ =>
        ⟨hP.b, ⟨by rw [L₀.keepBytes hP.b (hr0 (sc oSB, 32) (by simp)), h.sb, e],
          fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    obtain ⟨_, tP⟩ := T.pT
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trK W tP) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(psP K, 32)] ∧ SeedsIs ρ K.L.k 0 0 x')
      (Q := RQ kgR (kgW K.L) ρ K.L.k 0 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (kgB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    have st : ∀ J < 4, RelCT isa (RQ kgR (kgW K.L) ρ K.L.k 0 J)
        (seedAt J ((0 + J) / 3) ((0 + J) % 3)) (RQ kgR (kgW K.L) ρ K.L.k 0 (J + 1)) := fun J hJ => by
      have := seed_tr (kgB_bases K.L) (ρ := ρ) (n := K.L.k) (e₀ := 0) (K := J) (by omega) hJ
        (by rw [k3]; omega) (by rw [k3]; omega) (hsd J hJ).1
      rwa [show (0 + J) / K.L.k = (0 + J) / 3 by rw [k3], show (0 + J) % K.L.k = (0 + J) % 3 by rw [k3]] at this
    refine RelCT.seq (st 0 (by decide)) (RelCT.seq (st 1 (by decide)) (RelCT.seq (st 2 (by decide))
      (RelCT.seq (st 3 (by decide)) ?_)))
    rw [Top16.aP, Nat.mul_zero, Nat.add_zero]
    refine RelCT.mono (sampleHAtP16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq Wb.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨rhoK K.L σ₁, kc_lrel Wb p₁ p₂ pub h₁.kc h₂.kc, ⟨σ₁, p₁, h₁, rfl⟩, ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

end

/-! ## The rows -/

/-- Before the fragment of row `i`, for the seed `ρ` of `Â`. -/
abbrev KHρ (K : Kem16) (ρ : List Byte) (i : Nat) (x : State) : Prop :=
  ∃ σ, (keyGenK K.L).pre σ ∧ KH K σ i (3 * i) x ∧ rhoK K.L σ = ρ

section
variable (W : KgH16Wf K) (T : KgH16T K)
include W T

theorem frag_tr (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {i : Nat} (hi : i < 3) :
    RelCT isa (R K.L fun σ s => KH K σ i (3 * i) s) (frag K b i) fun _ _ => True := by
  have Wb := W.toKgWfB
  have k3 := W.k3
  obtain ⟨e2, e21, hbd, hm3⟩ := hm_spec i hi
  have hsd := W.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := W.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have c4 := hsm.1
  have hB := v.batchHM16 b hb _ hm3
  have hcp := W.cp i hi
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel kgR (kgW K.L) x y ∧ KHρ K ρ i x ∧ KHρ K ρ i y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, KHρ K ρ i x →
        WP isa (if (hm i).1 = 0 then .block [] else copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1))
          x fun x' => PPostB x x' [(hbP K, 136 * (hm i).1)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := by
      rintro x ⟨σ, hp, h, e⟩
      by_cases h0 : (hm i).1 = 0
      · rw [ite_eq_left h0]
        exact WP.block_nil ⟨(Post.refl x _).b, ⟨by rw [h.sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
      · rw [ite_eq_right h0]
        simp only [cpChk, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at hcp
        obtain ⟨_, hr⟩ := keepAll_spec hcp.2
        have L₀ := h.kc.lay Wb hp
        exact WP.mono (copy_okL L₀ (show Reg.r12 ≠ .rdi by decide) hcp.1) fun x' ⟨hP, _⟩ =>
          ⟨hP.b, ⟨by rw [L₀.keepBytes hP.b (hr (sc oSB, 32) (List.mem_append_left _ (by simp))), h.sb, e],
            fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    have htr : RelCT isa (LRel kgR (kgW K.L))
        (if (hm i).1 = 0 then .block [] else copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1))
        fun _ _ => True := by
      by_cases h0 : (hm i).1 = 0
      · rw [ite_eq_left h0]; exact RelCT.mono nil_tr (fun _ _ h => h) fun _ _ _ => trivial
      · rw [ite_eq_right h0]; obtain ⟨_, t⟩ := T.cT i hi h0; exact trK W t
    refine RelCT.seq (RelCT.postDep (RelCT.mono htr (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(hbP K, 136 * (hm i).1)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ kgR (kgW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (kgB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    have st : ∀ J < 4, RelCT isa (RQ kgR (kgW K.L) ρ K.L.k (3 * i) J)
        (seedAt J ((3 * i + J) / 3) ((3 * i + J) % 3)) (RQ kgR (kgW K.L) ρ K.L.k (3 * i) (J + 1)) := fun J hJ => by
      have := seed_tr (kgB_bases K.L) (ρ := ρ) (n := K.L.k) (e₀ := 3 * i) (K := J) (by omega) hJ
        (by rw [k3]; omega) (by rw [k3]; omega) (hsd J hJ).1
      rwa [show (3 * i + J) / K.L.k = (3 * i + J) / 3 by rw [k3],
        show (3 * i + J) % K.L.k = (3 * i + J) % 3 by rw [k3]] at this
    have s0 := st 0 (by decide)
    rw [show (3 * i + 0) / 3 = i by omega, show (3 * i + 0) % 3 = 0 by omega] at s0
    have s1 := st 1 (by decide)
    rw [show (3 * i + 1) / 3 = i by omega, show (3 * i + 1) % 3 = 1 by omega] at s1
    have s2 := st 2 (by decide)
    rw [show (3 * i + 2) / 3 = i by omega, show (3 * i + 2) % 3 = 2 by omega] at s2
    have s3 := st 3 (by decide)
    rw [show (3 * i + 3) / 3 = i + 1 by omega, show (3 * i + 3) % 3 = 0 by omega] at s3
    refine RelCT.seq s0 (RelCT.seq s1 (RelCT.seq s2 (RelCT.seq s3 ?_)))
    rw [Top16.aP, k3]
    refine RelCT.mono (sampleHAtM16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq Wb.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨rhoK K.L σ₁, kc_lrel Wb p₁ p₂ pub h₁.kc h₂.kc, ⟨σ₁, p₁, h₁, rfl⟩, ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

end

section
variable (W : KgH16Wf K)
include W

/-- What a call of row `i` needs reduced, once every `SampleNTT` so far succeeded. -/
theorem KH.redRow {σ s : State} {i : Nat} (hi : i < 3) (h : KH K σ i (3 * i + 3) s)
    (ho : allOk K.L.k (rhoK K.L σ) (3 * i + 3)) :
    VecReducedW 16 s.mem (pa s (aP K (3 * i))) K.L.k ∧ VecReduced s.mem (pa s (sc oSH)) K.L.k ∧
      Reduced s.mem (pa s (ehP i)) := by
  have k3 := W.k3
  refine ⟨fun j hj => ?_, fun j hj => ?_, (h.eh i hi (Nat.le_refl _)).1⟩
  · have := h.mat.mat (3 * i + j) (by rw [k3] at hj; omega) _ (aHat_part ho (e' := 3 * i + j) (by rw [k3] at hj; omega))
    rw [aP, sc_w16, show K.oA + 512 * (3 * i) + 512 * j = K.oA + 512 * (3 * i + j) by omega]
    exact this.1
  · rw [pa_off]; exact (h.sh j (by omega)).1

/-- The last 504 bytes of `ek` absorbed, `H(ek)` and the rest of the keys, from the pointers. -/
theorem tail_trL (T : KgH16T K) : RelCT isa (LRel kgR (kgW K.L)) (tail K) fun _ _ => True := by
  have Wb := W.toKgWfB
  have hek := W.ek
  have tC := W.tC
  simp only [Bool.and_eq_true] at tC
  obtain ⟨hrate, hk, hps, hsq, hna, _⟩ := hashChk_spec W.tH
  have hin : inB (kgB K.L) (.r13, 384 * K.L.k + K.L.ekLen) 32 = true := by
    simp only [ksqzChk, wrOk, rdOk, Bool.and_eq_true] at hsq; exact hsq.1.1.1.2.1.2
  obtain ⟨_, t₁⟩ := Wb.finT₁
  obtain ⟨_, t₂⟩ := Wb.finT₂
  obtain ⟨_, t₄⟩ := Wb.finT₄
  unfold tail
  rw [show K.L.ekLen - 136 * hDone = 504 by rw [hek]; rfl, show 136 * hDone = 680 from rfl]
  refine RelCT.seq (LRel.step (kgB_bases K.L) (trK W t₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 384 * K.L.k)) (src := sc oG) (n := 32) (by decide) Wb.f₁)
        fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kgB_bases K.L) (trK W t₂) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 384 * K.L.k)) (src := (.r12, 0)) (n := K.L.ekLen) (by decide) Wb.f₂)
        fun _ h => ⟨_, h.1⟩) ?_
  obtain ⟨_, tS⟩ := T.sT
  refine RelCT.seq (LRel.step (kgB_bases K.L) (trK W tS) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc 0) (src := hsP K) (n := 200) (show Reg.rbx ≠ .rdi by decide) tC.1)
        fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (absAll_tr (kgB_bases K.L) hrate hk [((.r12, 680), 504)] 0 hps (by decide)) ?_
  refine RelCT.seq (LRel.step (kgB_bases K.L) (RelCT.mono (kpad_tr (show 6 < 256 by decide))
      (fun x y h => ⟨KPadH.of h.1 hk hrate (pos := 504 % 136) (by decide), KPadH.of h.2.1 hk hrate (by decide),
        h.eq (kChk_in hk), h.2.2.2⟩) fun _ _ _ => trivial)
    fun x Lx => WP.mono (kpad_ok (show 6 < 256 by decide) (KPadH.of Lx hk hrate (pos := 504 % 136) (by decide)))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kgB_bases K.L) (RelCT.mono (ksqz_tr hna) (fun x y h =>
      ⟨KSqzH.of h.1 hsq hrate, KSqzH.of h.2.1 hsq hrate, h.eq (kChk_in hk), h.eq hin, h.2.2.2⟩) fun _ _ _ => trivial)
    fun x Lx => WP.mono (ksqz_ok hna (KSqzH.of Lx hsq hrate)) fun _ h => ⟨_, h.1⟩) ?_
  exact trK W t₄

end

section
variable (W : KgH16Wf K)
include W

/-- The relation of two runs on entry to row `i`, after the test of `r15`. -/
abbrev RowRel (K : Kem16) (i : Nat) (x y : State) : Prop :=
  ∃ x₀ y₀, R K.L (fun σ s => KH K σ i (3 * i + 3) s) x₀ y₀ ∧ PPost x₀ x [] ∧ PPost y₀ y [] ∧
    (x₀.gpr .r15).setWidth 32 ≠ 0

theorem rowRel_of {i : Nat} (hi : i < 3) {x y : State} (h : RowRel K i x y) :
    LRel kgR (kgW K.L) x y ∧
      (VecReducedW 16 x.mem (pa x (aP K (3 * i))) K.L.k ∧ VecReduced x.mem (pa x (sc oSH)) K.L.k ∧
        Reduced x.mem (pa x (ehP i))) ∧
      (VecReducedW 16 y.mem (pa y (aP K (3 * i))) K.L.k ∧ VecReduced y.mem (pa y (sc oSH)) K.L.k ∧
        Reduced y.mem (pa y (ehP i))) := by
  obtain ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ := h
  have hf := W.flg i hi
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hkc, hr⟩ := keepAll_spec hf.1
  have k₁ := h₁.keep W p₁ hx.b (hx.cs .r15 (by decide)) hkc hr fun _ => hf.2
  have k₂ := h₂.keep W p₂ hy.b (hy.cs .r15 (by decide)) hkc hr fun _ => hf.2
  have o₁ := r15_ok h₁.mat.r15 hne
  have o₂ : allOk K.L.k (rhoK K.L σ₂) (3 * i + 3) := by rw [← rho_pub pub]; exact o₁
  exact ⟨kc_lrel W.toKgWfB p₁ p₂ pub k₁.kc k₂.kc, k₁.redRow W hi o₁, k₂.redRow W hi o₂⟩

theorem rowL_tr (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) :
    RelCT isa (RowRel K i) (rowAt K i) (LRel kgR (kgW K.L)) := by
  have k3 := W.k3
  have hc := W.rw i hi
  simp only [rwChk, Bool.and_eq_true] at hc
  have hkr : krChk (kgB K.L) (kgW K.L) K.L.k (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) = true := by
    rw [k3]; exact hc.1
  have ep : rowAt K i = K.L.kgRowAt (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) := by rw [rowAt, k3]
  rw [ep]
  refine RelCT.postDep (RelCT.mono (kgRowAt_trL hK rbx_na rbx_na rbx_na rbx_na hkr)
      (fun x y h => rowRel_of W hi h) fun _ _ _ => trivial) (F := fun x x' => ∃ W, Post x x' W)
    (fun x y h => ?_) fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (rowRel_of W hi h).1.post (kgB_bases K.L) hx.b hy.b
  obtain ⟨L, ⟨a₁, s₁, e₁⟩, ⟨a₂, s₂, e₂⟩⟩ := rowRel_of W hi h
  exact ⟨WP.mono (kgRowAt_okL hK L.1 rbx_na rbx_na rbx_na rbx_na hkr a₁ s₁ e₁) fun _ h => ⟨_, h.1⟩,
    WP.mono (kgRowAt_okL hK L.2.1 rbx_na rbx_na rbx_na rbx_na hkr a₂ s₂ e₂) fun _ h => ⟨_, h.1⟩⟩

omit W in
theorem r15_eq {i : Nat} {x y : State} (h : R K.L (fun σ s => KH K σ i (3 * i + 3) s) x y) :
    (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32 := by
  obtain ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ := h
  rw [h₁.mat.r15, h₂.mat.r15, rho_pub pub]

theorem rowIf_tr (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) :
    RelCT isa (R K.L fun σ s => KH K σ i (3 * i + 3) s) (ifOk (rowAt K i)) fun _ _ => True :=
  ifOk_tr (fun _ _ h => r15_eq h) (RelCT.mono (rowL_tr W hK hi) (fun _ _ h => h) fun _ _ _ => trivial)
    fun _ _ _ => trivial

theorem lastIf_tr (hK : KgRowsOk K.L) (T : KgH16T K) :
    RelCT isa (R K.L fun σ s => KH K σ 2 9 s) (ifOk (.seq (rowAt K 2) (tail K))) fun _ _ => True :=
  ifOk_tr (fun _ _ h => r15_eq (i := 2) h) (RelCT.seq (rowL_tr W hK (i := 2) (by decide)) (tail_trL W T))
    fun _ _ _ => trivial

theorem rows_tr (hK : KgRowsOk K.L) (T : KgH16T K) (v : Sample4Impl) {b : Nat → Prog isa}
    (hb : v.callee.batchHM16 = some b) {p : Prog isa} (hpb : v.callee.batchP16 = some p) :
    RelCT isa (R K.L (KN K 6)) (KeyGenH16.rows K b p v.callee.arith) (R K.L (KEnd K.L)) := by
  unfold KeyGenH16.rows
  refine RelCT.seq (relInv (I' := fun σ s => KG K σ 0 false s)
    (fun σ s hp hs => frag0_ok W hp v hpb hs) (frag0_tr W T v hpb)) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KG K σ 0 true s) (fun σ s hp hs => hzG_ok W hp hs) (hzG_tr W T)) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KG K σ (0 + 1) true s)
    (fun σ s hp hs => cbdP_ok W hp v.arith (N := 0) (by decide) hs) (cbdP_tr W v (N := 0) (by decide))) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KG K σ (1 + 1) true s)
    (fun σ s hp hs => cbdP_ok W hp v.arith (N := 1) (by decide) hs) (cbdP_tr W v (N := 1) (by decide))) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KH K σ 0 (3 * 0 + 3) s)
    (fun σ s hp hs => nttG_ok W hp hK hs) (nttG_tr W hK)) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KH K σ (0 + 1) (3 * 0 + 3) s)
    (fun σ s hp hs => rowIf_ok W hp hK (i := 0) (by decide) hs) (rowIf_tr W hK (i := 0) (by decide))) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KH K σ 1 (3 * 1 + 3) s)
    (fun σ s hp hs => frag_ok W hp v hb (i := 1) (by decide) hs) (frag_tr W T v hb (i := 1) (by decide))) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KH K σ (1 + 1) (3 * 1 + 3) s)
    (fun σ s hp hs => rowIf_ok W hp hK (i := 1) (by decide) hs) (rowIf_tr W hK (i := 1) (by decide))) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KH K σ 2 9 s)
    (fun σ s hp hs => frag_ok W hp v hb (i := 2) (by decide) hs) (frag_tr W T v hb (i := 2) (by decide))) ?_
  exact relInv (I' := KEnd K.L) (fun σ s hp hs => last_ok W hp hK hs) (lastIf_tr W hK T)

end

end KeyGenH

open KeyGen KeyGenH in
theorem kemKeyGenH16_ct {K : Kem16} (hK : KgRowsOk K.L) (v : Sample4Impl) (W : KgH16Wf K) (T : KgH16T K)
    {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {p : Prog isa} (hpb : v.callee.batchP16 = some p) :
    ConstantTime isa (keyGenK K.L).pre (keyGenK K.L).pub (kemKeyGenH16 K v.callee b p) := by
  have Wb := W.toKgWfB
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemKeyGenH16
  refine RelCT.seq (relInv (I' := fun σ s => KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok Wb hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KA K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => gRho_ok Wb hp hs.1 hs.2) (gRho_tr Wb)) ?_
  refine RelCT.seq (prfs_tr W v) ?_
  refine RelCT.seq (se_tr W v) ?_
  refine RelCT.seq (rows_tr W hK T v hb hpb) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
