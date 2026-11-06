module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTFront
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets

/-!
# A candidate on x86-64: constant time

For runs that agree on the arguments, `e` and `candidateLeak`: the entry,
the zeros to `out` and the length check depend on the arguments alone, and
`kMainWith` on the schedule the leak fixes (`schedOf_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (Sched schedOf shapeOf)

/-- The public data of `vg_rsa_keygen_candidate`: the stages' and the stack
pointer. -/
structure CPub where
  f : FPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
structure CRel (p : CPub) (s : State) : Prop where
  pre : candPre s
  rsp : s.gpr .rsp = p.rsp
  B : arg s 3 = p.f.B
  Z : (arg s 4).toNat * 8 = p.f.Z
  w : (s.gpr .rsi).toNat = 8 * p.f.w
  op : s.gpr .rdi = p.f.op
  up : s.gpr .rdx = p.f.up
  eP : s.gpr .rcx = p.f.eP
  eB : Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = p.f.eB
  pP : s.gpr .r9 = p.f.pP
  pl : (arg s 0).toNat = p.f.pl
  rP : arg s 1 = p.f.rP
  rl : (arg s 2).toNat = p.f.rl
  wr : s.wr = p.f.wr
  sch : 8 * p.f.w ≤ p.f.rl → schedOf (8 * p.f.w) (Spec.Rsa.os2ip p.f.eB)
    (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
    (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) = p.f.sch

theorem candPre_wr {s : State} (h : candPre s) :
    s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨arg s 3, (arg s 4).toNat * 8⟩] := h.2.2.1

/-- The writable regions the precondition gives. -/
theorem kw_of {s : State} (h : candPre s) : KW (arg s 3) s.wr := by
  have c := kctx_of h
  have hZ := c.hZ
  have hk1 := c.k1
  simp only [candPre] at h
  obtain ⟨-, -, hwr, dOu, -, -, -, dOs, -, -, -, -, dUs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wS, -⟩ := h
  refine ⟨_, _, _, hwr, Nat.le_refl _, by omega, ?_, ?_⟩
  · rw [hwr]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl); exacts [dOu, dOs]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; exact dUs
  · rw [hwr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact Nat.le_of_lt (s.gpr .rsi).isLt
    · dsimp only; decide
    · dsimp only; omega

/-- After the zeros to `out` and the length check. -/
def C3 (p : CPub) (t : State) : Prop := ∃ s t₁, CRel p s ∧ EntryPost s t₁ (arg s 3) ∧ Front s t₁ t

theorem WP.and' {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

theorem kEntry_split : kEntry = ([.mov .r11 (.mem { base := .rsp, disp := 32 })] : List Instr) ++ kEntry.drop 1 := rfl

/-- What `kMainWith` needs, from a state past the length check with enough
octets. -/
theorem C3.k0 {p : CPub} {t : State} (h : C3 p t) (hlt : ¬ p.f.rl < 8 * p.f.w) : K0 p.f t := by
  obtain ⟨s, t₁, hs, he, hf⟩ := h
  have c := kctx_of hs.pre
  have hk1 := c.k1
  have hk2 := c.k2
  have hle : (s.gpr .rsi).toNat ≤ (arg s 2).toNat := by rw [hs.w, hs.rl]; omega
  have hm := mainCtx_of c he hf hs.w hle
  have hw := hs.w
  have hsch := hs.sch (by omega)
  rw [hs.eB, hs.B, hs.Z, hs.op, hs.up, hs.eP, hs.pP, hs.rP] at hm
  rw [hs.pP, hs.rP] at hsch
  refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, (hf.keep.2.2.trans he.keep.2.2).trans hs.wr,
    ⟨by have := hm.z; rwa [show 8 * p.f.w / 8 = p.f.w by omega] at this,
      by have := hm.zx; rwa [show 8 * p.f.w / 8 = p.f.w by omega] at this, by omega, by omega,
      by rw [← hs.rl]; exact (arg s 2).isLt, by omega, ?_, ?_, ?_⟩, _, _, hm, by rw [bytesAt_length, hs.pl],
    by rw [bytesAt_length, hs.rl], hsch⟩
  · rw [← hs.eB, bytesAt_length]; exact c.el1
  · rw [← hs.eB, bytesAt_length]; exact c.el8
  · rw [← hs.pl, ← hs.w]; exact c.pl

/-- The public data of a state. -/
def cpubOf (s : State) : CPub :=
  ⟨⟨arg s 3, (arg s 4).toNat * 8, (s.gpr .rsi).toNat / 8, s.wr, s.gpr .rdi, s.gpr .rdx, s.gpr .rcx,
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat, s.gpr .r9, (arg s 0).toNat, arg s 1, (arg s 2).toNat,
    schedOf (8 * ((s.gpr .rsi).toNat / 8)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
      (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat)⟩, s.gpr .rsp⟩

theorem crel_self {s : State} (h : candPre s) : CRel (cpubOf s) s := by
  have := (kctx_of h).k8
  exact ⟨h, rfl, rfl, rfl, by dsimp only [cpubOf]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Runs that agree on the arguments and the leak agree on the public data. -/
theorem crel_of {s₁ s₂ : State} (h₁ : candPre s₁) (h₂ : candPre s₂) (hp : candPub s₁ s₂) : CRel (cpubOf s₁) s₂ := by
  obtain ⟨hdi, hsi, hdx, hcx, hr8, hr9, hsp, ha, hl⟩ := hp
  have c := kctx_of h₁
  have hk8 := c.k8
  have hk1 := c.k1
  unfold candLeak at hl
  obtain ⟨he, hl'⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt_length, hr8])
  have heB := VG.Proof.RsaKeyGen.map_toNat_inj he
  refine ⟨h₂, hsp.symm, (ha 3 (by decide)).symm, by rw [← ha 4 (by decide)]; rfl, by dsimp only [cpubOf]; rw [← hsi]; omega,
    hdi.symm, hdx.symm, hcx.symm, heB.symm, hr9.symm, by rw [← ha 0 (by decide)]; rfl, (ha 1 (by decide)).symm,
    by rw [← ha 2 (by decide)]; rfl, ?_, fun hk => ?_⟩
  · rw [candPre_wr h₂, ← hdi, ← hsi, ← hdx, ← ha 3 (by decide), ← ha 4 (by decide), ← candPre_wr h₁]; rfl
  · dsimp only [cpubOf] at hk ⊢
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl'
    unfold Spec.RsaKeyGen.candidateOp at hl'
    rw [← heB, ← hsi] at hl'
    rw [show 8 * ((s₁.gpr .rsi).toNat / 8) = (s₁.gpr .rsi).toNat by omega] at hk ⊢
    refine (VG.Proof.RsaKeyGen.schedOf_eq (by omega) (by rw [bytesAt_length, bytesAt_length, ha 2 (by decide)])
      (by rw [bytesAt_length]; omega) hl').symm

end VG.Proof.RsaKeyGen.X86_64
