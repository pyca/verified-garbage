module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Sat
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
public import VerifiedGarbage.Proof.Mcdt.X86_64

/-!
# ML-DSA on x86-64: external message representatives with prepared keys

The entry wrappers set the kernel's public prepared-key flag to one. The
proofs frame the entire prepared key across the call's return-address write,
so the kernels use its cached polynomials. Correctness, permitted leakage,
ABI preservation and satisfiability establish the public external-`μ`
contracts for every arithmetic implementation.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign.Prepared

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep Rel2 relStart relInv)
open VG.Proof.MlDsa.Sign
open VG.Proof.MlDsa.X86_64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def signKP (p : Params) (D : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, preparedSecretKeyBytes p⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, p.sigLen⟩, ⟨s.gpr .r8, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, preparedSecretKeyBytes p⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, preparedSecretKeyBytes p⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, preparedSecretKeyBytes p⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdi, preparedSecretKeyBytes p⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + preparedSecretKeyBytes p ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + scrLen p ≤ 2 ^ 64 ∧
    D ≤ (s.gpr .rsp).toNat ∧ PreparedSecretKey p s.mem (s.gpr .rdi)
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .rdi) p.skLen) (bytesAt s.mem (s.gpr .rsi) 64)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rcx) p.sigLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    signLeak p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) 64)
        (bytesAt s₁.mem (s₁.gpr .rdx) 32) =
      signLeak p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) 64)
        (bytesAt s₂.mem (s₂.gpr .rdx) 32)

section
variable {p : Params} {σ s e : State} (hp : (signKP p 56).pre σ) (hs : Moved .r9 1 σ s)
  (he : Proof.Mcdt.X86_64.EntryOf s e)
include hp hs he

omit hp in
theorem ce_gpr {r : Reg} (h1 : r ≠ .rsp) (h2 : r ≠ .r9) (h3 : r ≠ .rax) (h4 : r ≠ .rbx) : e.gpr r = σ.gpr r := by
  rw [he.gpr r h1 h3 h4, hs.gpr r h2]

omit hp in
theorem ce_rsp : e.gpr .rsp = σ.gpr .rsp - 24 := by
  rw [he.rsp, hs.gpr .rsp (by decide)]

omit hp in
/-- The frame and the return address of the call are below `rsp`, apart from the buffers. -/
theorem ce_bytes {a : Addr} {len : Nat} (hd : (below (σ.gpr .rsp) 56).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt e.mem a len = bytesAt σ.mem a len := by
  have hf : Frame [below (σ.gpr .rsp) 24] σ.mem e.mem := by
    have := he.mem; rwa [hs.mem, hs.gpr .rsp (by decide)] at this
  refine VG.Proof.MlKem.bytesAt_frame hf (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega_using []) (by omega_using []))).symm

theorem kpreP : (signK p 32).pre (e.withRegions s.rd s.wr) := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp, hprep⟩ := hp'
  have h9 : (e.withRegions s.rd s.wr).gpr .r9 = 1 := by
    rw [State.withRegions_gpr, he.gpr _ (by decide) (by decide) (by decide), hs.r9]
  have hL : skL p (e.withRegions s.rd s.wr) = preparedSecretKeyBytes p := by
    simp only [skL, h9, show (1 : BitVec 64) ≠ 0 by decide, ite_false]
  rw [hs.rd, hs.wr] at hL
  have e1 := ce_gpr hs he (r := .rdi) (by decide) (by decide) (by decide) (by decide)
  have e2 := ce_gpr hs he (r := .rsi) (by decide) (by decide) (by decide) (by decide)
  have e3 := ce_gpr hs he (r := .rdx) (by decide) (by decide) (by decide) (by decide)
  have e4 := ce_gpr hs he (r := .rcx) (by decide) (by decide) (by decide) (by decide)
  have e5 := ce_gpr hs he (r := .r8) (by decide) (by decide) (by decide) (by decide)
  have er := ce_rsp hs he
  have hret : Region.Sub (retR (e.withRegions s.rd s.wr)) (below (σ.gpr .rsp) 56) := by
    rw [retR, State.withRegions_gpr, er]; exact Proof.Mcdt.X86_64.sub_at _ (a := 24) (by omega) (by omega)
  have hbel : Region.Sub (below ((e.withRegions s.rd s.wr).gpr .rsp) 32) (below (σ.gpr .rsp) 56) := by
    rw [State.withRegions_gpr, er]; exact Proof.Mcdt.X86_64.sub_below _ (a := 24) (by omega) (by omega)
  have hsp' : 32 ≤ ((e.withRegions s.rd s.wr).gpr .rsp).toNat := by
    rw [State.withRegions_gpr, er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt
    simp only [show (24 : BitVec 64).toNat = 24 from rfl]; omega_using [hsp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsp', ?_⟩
  all_goals simp only [hL, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    e1, e2, e3, e4, e5, hs.rd, hs.wr]
  · exact hrd
  · exact hwr
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · exact d5
  · exact d6
  · exact d7
  · exact k1.sub_left hret
  · exact k2.sub_left hret
  · exact k3.sub_left hret
  · exact k4.sub_left hret
  · exact k5.sub_left hret
  · exact k1.sub_left hbel
  · exact k2.sub_left hbel
  · exact k3.sub_left hbel
  · exact k4.sub_left hbel
  · exact k5.sub_left hbel
  · exact n1
  · exact n2
  · exact n3
  · exact n4
  · exact n5
  · intro _
    exact Message.prepared_congr (ce_bytes hs he k1 (by omega_using [n1])) hprep

theorem kpostP {s' s₂ : State} (hm : Frame [below (σ.gpr .rsp) 16] s₂.mem s'.mem) (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (signK p 32).post (e.withRegions s.rd s.wr) s₂) : (signKP p 56).post σ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, k4, _, n1, n2, n3, n4, _, _⟩ := hp'
  show Outcome _ _ _
  have h' : Outcome _ _ _ := h
  have hsig : bytesAt s₂.mem (σ.gpr .rcx) p.sigLen = bytesAt s'.mem (σ.gpr .rcx) p.sigLen :=
    (VG.Proof.MlKem.bytesAt_frame hm (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (k4.sub_left (below_sub (by omega_using []) (by omega_using []))).symm) (by omega_using [n4])).symm
  simp only [State.withRegions_gpr, State.withRegions_mem] at h'
  rw [ce_gpr hs he (r := .rdi) (by decide) (by decide) (by decide) (by decide), ce_gpr hs he (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr hs he (r := .rdx) (by decide) (by decide) (by decide) (by decide), ce_gpr hs he (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_bytes hs he (k1.sub_right (Region.sub_prefix (by simp only [preparedSecretKeyBytes]; omega_using []))) (by simp only [preparedSecretKeyBytes] at n1; omega_using [n1]), ce_bytes hs he k2 (by omega_using []), ce_bytes hs he k3 (by omega_using []), hsig, hax] at h'
  exact h'

end

theorem entryP_correct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) (σ : State)
    (hpre : (signKP p 56).pre σ) :
    ∃ t s', Exec isa (entry n c 1) σ t s' ∧ abiPreserved σ s' ∧ (signKP p 56).post σ s' := by
  have hp' := hpre
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, r4, r5, _, _, _, k4, k5, _, _, _, _, _, hsp, _⟩ := hp'
  have hdep := hK.depth
  have main : WP isa (entry n c 1) σ fun s' => abiPreserved σ s' ∧ (signKP p 56).post σ s' := by
    unfold entry
    refine WP.seq (WP.mono (flag_ok .r9 1 σ) fun s hs => ?_)
    have hs' : Moved .r9 1 σ s := hs
    have hsp1 : s.gpr .rsp = σ.gpr .rsp := hs'.gpr .rsp (by decide)
    refine Proof.Mcdt.X86_64.WP.mcdtCall hK.ok hK.nosp (by rw [hsp1]; omega) (rd := s.rd) (wr := s.wr)
      (fun e he => kpreP hpre hs' he) (Covers.refl _) (Covers.refl _) (fun r hr => ?_)
      fun s' _ _ hcs hf ⟨e, s₂, he, hm₂, hg₂, hq⟩ hmx => ⟨?_, ?_⟩
    · rw [hs'.wr, hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hsp1]
      rcases hr with rfl | rfl
      exacts [k4.sub_left (below_sub (by omega) (by omega)), k5.sub_left (below_sub (by omega) (by omega))]
    · refine entry_abi hsp (Nat.le_refl _) hs' (by decide) (fun r hr => ?_) (by omega) hcs hf hmx
      rw [hs'.wr, hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [r4, r5]
    · rw [hsp1] at hm₂
      exact kpostP hpre hs' he hm₂ (hg₂ _ (by decide) (by decide)) hq
  obtain ⟨t, s', he, ha, hq⟩ := main
  exact ⟨t, s', he, ha, hq⟩

theorem entryP_ct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) :
    ConstantTime isa (signKP p 56).pre (signKP p 56).pub (entry n c 1) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold entry
  refine RelCT.seq (relInv (I' := fun σ s => Moved .r9 1 σ s) (fun σ s _ (hs : s = σ) => by rw [hs]; exact flag_ok .r9 1 σ)
    (block_tr (rs := []) rfl fun _ _ _ r hr => absurd hr (List.not_mem_nil))) ?_
  refine Proof.Mcdt.X86_64.RelCT.mcdtCall hK.ok hK.ct hK.nosp fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, h₁, h₂⟩ => ?_
  have hdep := hK.depth
  have q₁ := p₁; have q₂ := p₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, _, _, n1, n2, n3, _, _, hsp₁, _⟩ := q₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, l1, l2, l3, _, _, m1, m2, m3, _, _, _, _⟩ := q₂
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hpub
  refine ⟨by rw [h₁.gpr .rsp (by decide), h₂.gpr .rsp (by decide), e6], by rw [h₁.gpr .rsp (by decide)]; omega,
    x.rd, x.wr, y.rd, y.wr, Covers.refl _, Covers.refl _, Covers.refl _, Covers.refl _,
    fun a b ha hb => ⟨kpreP p₁ h₁ ha, kpreP p₂ h₂ hb, ?_⟩⟩
  show _ = _ ∧ _
  simp only [State.withRegions_gpr, State.withRegions_mem]
  rw [ce_gpr h₁ ha (r := .rdi) (by decide) (by decide) (by decide) (by decide), ce_gpr h₁ ha (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .rdx) (by decide) (by decide) (by decide) (by decide), ce_gpr h₁ ha (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .r8) (by decide) (by decide) (by decide) (by decide), ce_rsp h₁ ha,
    ce_gpr h₂ hb (r := .rdi) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .rdx) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .r8) (by decide) (by decide) (by decide) (by decide), ce_rsp h₂ hb,
    ce_bytes h₁ ha (k1.sub_right (Region.sub_prefix (by simp only [preparedSecretKeyBytes]; omega_using []))) (by simp only [preparedSecretKeyBytes] at n1; omega_using [n1]), ce_bytes h₁ ha k2 (by omega_using []), ce_bytes h₁ ha k3 (by omega_using []),
    ce_bytes h₂ hb (l1.sub_right (Region.sub_prefix (by simp only [preparedSecretKeyBytes]; omega_using []))) (by simp only [preparedSecretKeyBytes] at m1; omega_using [m1]), ce_bytes h₂ hb l2 (by omega_using []), ce_bytes h₂ hb l3 (by omega_using []),
    ha.gpr _ (by decide) (by decide) (by decide), hb.gpr _ (by decide) (by decide) (by decide), h₁.r9, h₂.r9]
  exact ⟨e1, e2, e3, e4, e5, by rw [e6], e7, rfl⟩

theorem implies {p : Params} (hsat : ∃ s, (preparedSignContract p X86_64.abi 56).pre s) :
    (signKP p 56).Implies (preparedSignContract p X86_64.abi 56) where
  pre := by sig_implies_pre [preparedSignContract, preparedSignSig, signKP, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [preparedSignContract, preparedSignSig, signKP, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [preparedSignContract, preparedSignSig, signKP, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

def externalSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0xA000 | .rdx => 0xA100 | .rcx => 0xB000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := m
  rd := [⟨0x1000, preparedSecretKeyBytes p⟩, ⟨0xA000, 64⟩, ⟨0xA100, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem sat {P : Impl.MlDsa.X86_64.Verify.Prims} (C : Verify.PrimsOk P) {p : Params}
    (hp : p ∈ Verify.params) : ∃ s, (preparedSignContract p X86_64.abi 56).pre s := by
  have hsz : p.skLen < 0x10000 ∧ preparedSecretKeyBytes p < 0x7000 := by
    simp only [Verify.params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  obtain ⟨_, s', _, _, _, hk⟩ := Verify.Prepare.prepareSecret_correct C hp _
    (Message.runSat_pre hsz.1 (by omega_using [hsz]))
  refine ⟨externalSat p s'.mem, ?_⟩
  simp only [Verify.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedSignContract, preparedSignSig, X86_64.abi, X86_64.argRegs] <;> sig_and_intros
  all_goals first | exact hk | rfl | decide | exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86_64.Sign.Prepared

namespace VG.Proof.MlDsa.X86_64.Verify.Prepared

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep Rel2 relStart relInv)
open VG.Proof.MlDsa.X86_64.Sign (Moved flag_ok)
open VG.Proof.MlDsa.X86_64.Verify
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

structure VPreP (p : Params) (σ : State) : Prop where
  sp : 56 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩, ⟨σ.gpr .rsi, 64⟩, ⟨σ.gpr .rdx, p.sigLen⟩]
  wr : σ.wr = [⟨σ.gpr .rcx, scrLen p⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d2 : Region.Disjoint ⟨σ.gpr .rsi, 64⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d3 : Region.Disjoint ⟨σ.gpr .rdx, p.sigLen⟩ ⟨σ.gpr .rcx, scrLen p⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, 64⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, p.sigLen⟩
  r4 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rcx, scrLen p⟩
  k1 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩
  k2 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rsi, 64⟩
  k3 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rdx, p.sigLen⟩
  k4 : (below (σ.gpr .rsp) 56).Disjoint ⟨σ.gpr .rcx, scrLen p⟩
  n1 : (σ.gpr .rdi).toNat + preparedPublicKeyBytes p ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + 64 ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + p.sigLen ≤ 2 ^ 64
  n4 : (σ.gpr .rcx).toNat + scrLen p ≤ 2 ^ 64
  prep : PreparedPublicKey p σ.mem (σ.gpr .rdi)

/-- The contract of the entry of an encoded key. -/
def verifyKP (p : Params) : Contract isa where
  pre := VPreP p
  post := (verifyK p).post
  pub σ₁ σ₂ := σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧ σ₁.gpr .rdx = σ₂.gpr .rdx ∧
    σ₁.gpr .rcx = σ₂.gpr .rcx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp ∧ vPk p σ₁ = vPk p σ₂ ∧ vMu σ₁ = vMu σ₂ ∧
    vSig p σ₁ = vSig p σ₂

section
variable {p : Params} {σ s e : State} (hp : VPreP p σ) (hs : Moved .r8 1 σ s) (he : Proof.Mcdt.X86_64.EntryOf s e)
include hp hs he

omit hp in
theorem ce_gpr {r : Reg} (h1 : r ≠ .rsp) (h2 : r ≠ .r8) (h3 : r ≠ .rax) (h4 : r ≠ .rbx) : e.gpr r = σ.gpr r := by
  rw [he.gpr r h1 h3 h4, hs.gpr r h2]

omit hp in
theorem ce_rsp : e.gpr .rsp = σ.gpr .rsp - 24 := by
  rw [he.rsp, hs.gpr .rsp (by decide)]

omit hp in
theorem ce_bytes {a : Addr} {len : Nat} (hd : (below (σ.gpr .rsp) 56).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt e.mem a len = bytesAt σ.mem a len := by
  have hf : Frame [below (σ.gpr .rsp) 24] σ.mem e.mem := by
    have := he.mem; rwa [hs.mem, hs.gpr .rsp (by decide)] at this
  refine Proof.MlKem.bytesAt_frame hf (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega_using []) (by omega_using []))).symm

theorem kpreP : VPre p (e.withRegions s.rd s.wr) := by
  have h8 : (e.withRegions s.rd s.wr).gpr .r8 = 1 := by
    rw [State.withRegions_gpr, he.gpr _ (by decide) (by decide) (by decide), hs.r9]
  have hL : pkL p (e.withRegions s.rd s.wr) = preparedPublicKeyBytes p := by
    simp only [pkL, h8, show (1 : BitVec 64) ≠ 0 by decide, ite_false]
  rw [hs.rd, hs.wr] at hL
  have e1 := ce_gpr hs he (r := .rdi) (by decide) (by decide) (by decide) (by decide)
  have e2 := ce_gpr hs he (r := .rsi) (by decide) (by decide) (by decide) (by decide)
  have e3 := ce_gpr hs he (r := .rdx) (by decide) (by decide) (by decide) (by decide)
  have e4 := ce_gpr hs he (r := .rcx) (by decide) (by decide) (by decide) (by decide)
  have er := ce_rsp hs he
  have hsp := hp.sp
  have hret : Region.Sub ⟨(e.withRegions s.rd s.wr).gpr .rsp, 8⟩ (below (σ.gpr .rsp) 56) := by
    rw [State.withRegions_gpr, er]; exact Proof.Mcdt.X86_64.sub_at _ (a := 24) (by omega) (by omega)
  have hbel : Region.Sub (below ((e.withRegions s.rd s.wr).gpr .rsp) 32) (below (σ.gpr .rsp) 56) := by
    rw [State.withRegions_gpr, er]; exact Proof.Mcdt.X86_64.sub_below _ (a := 24) (by omega) (by omega)
  have hsp' : 32 ≤ ((e.withRegions s.rd s.wr).gpr .rsp).toNat := by
    rw [State.withRegions_gpr, er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt
    simp only [show (24 : BitVec 64).toNat = 24 from rfl]; omega
  refine ⟨hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hL, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    e1, e2, e3, e4, hs.rd, hs.wr]
  · exact hp.rd
  · exact hp.wr
  · exact hp.d1
  · exact hp.d2
  · exact hp.d3
  · exact hp.k1.sub_left hret
  · exact hp.k2.sub_left hret
  · exact hp.k3.sub_left hret
  · exact hp.k4.sub_left hret
  · exact hp.k1.sub_left hbel
  · exact hp.k2.sub_left hbel
  · exact hp.k3.sub_left hbel
  · exact hp.k4.sub_left hbel
  · exact hp.n1
  · exact hp.n2
  · exact hp.n3
  · exact hp.n4
  · intro _
    exact Message.preparedPk_congr (ce_bytes hs he hp.k1 (by have := hp.n1; omega_using [this])) hp.prep

theorem hpkP : vPk p (e.withRegions s.rd s.wr) = vPk p σ := by
  rw [vPk, State.withRegions_gpr, State.withRegions_mem, ce_gpr hs he (r := .rdi) (by decide) (by decide) (by decide) (by decide), ce_bytes hs he (hp.k1.sub_right (Region.sub_prefix (by simp only [preparedPublicKeyBytes]; omega_using []))) (by have := hp.n1; simp only [preparedPublicKeyBytes] at this; omega_using [this])]

theorem hmuP : vMu (e.withRegions s.rd s.wr) = vMu σ := by
  rw [vMu, State.withRegions_gpr, State.withRegions_mem, ce_gpr hs he (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_bytes hs he hp.k2 (by omega_using [])]

theorem hsigP : vSig p (e.withRegions s.rd s.wr) = vSig p σ := by
  rw [vSig, State.withRegions_gpr, State.withRegions_mem, ce_gpr hs he (r := .rdx) (by decide) (by decide) (by decide) (by decide),
    ce_bytes hs he hp.k3 (by have := hp.n3; omega_using [this])]

theorem kpostP {s' s₂ : State} (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (verifyK p).post (e.withRegions s.rd s.wr) s₂) : (verifyKP p).post σ s' := by
  have hres : res s₂ = res s' := by simp only [res, hax]
  show _ ∨ _
  have h' : _ ∨ _ := h
  rw [hpkP hp hs he, hmuP hp hs he, hsigP hp hs he, hres] at h'
  exact h'

end

theorem entryP_correct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) (σ : State)
    (hpre : VPreP p σ) :
    ∃ t s', Exec isa (entry n c 1) σ t s' ∧ abiPreserved σ s' ∧ (verifyKP p).post σ s' := by
  have hdep := hK.depth
  have hsp := hpre.sp
  have main : WP isa (entry n c 1) σ fun s' => abiPreserved σ s' ∧ (verifyKP p).post σ s' := by
    unfold entry
    refine WP.seq (WP.mono (flag_ok .r8 1 σ) fun s hs => ?_)
    have hs' : Moved .r8 1 σ s := hs
    have hsp1 : s.gpr .rsp = σ.gpr .rsp := hs'.gpr .rsp (by decide)
    refine Proof.Mcdt.X86_64.WP.mcdtCall hK.ok hK.nosp (by rw [hsp1]; omega) (rd := s.rd) (wr := s.wr)
      (fun e he => kpreP hpre hs' he) (Covers.refl _) (Covers.refl _) (fun r hr => ?_)
      fun s' _ _ hcs hf ⟨e, s₂, he, _, hg₂, hq⟩ hmx => ⟨?_, ?_⟩
    · rw [hs'.wr, hpre.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [hsp1]
      exact hpre.k4.sub_left (below_sub (by omega) (by omega))
    · refine Sign.entry_abi hsp (Nat.le_refl _) hs' (by decide) (fun r hr => ?_) (by omega) hcs hf hmx
      rw [hs'.wr, hpre.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hpre.r4
    · exact kpostP hpre hs' he (hg₂ _ (by decide) (by decide)) hq
  obtain ⟨t, s', he, ha, hq⟩ := main
  exact ⟨t, s', he, ha, hq⟩

theorem entryP_ct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) :
    ConstantTime isa (verifyKP p).pre (verifyKP p).pub (entry n c 1) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold entry
  refine RelCT.seq (relInv (I' := fun σ s => Moved .r8 1 σ s)
    (fun σ s _ (hs : s = σ) => by rw [hs]; exact flag_ok .r8 1 σ)
    (Sign.block_tr (rs := []) rfl fun _ _ _ r hr => absurd hr (List.not_mem_nil))) ?_
  refine Proof.Mcdt.X86_64.RelCT.mcdtCall hK.ok hK.ct hK.nosp fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, h₁, h₂⟩ => ?_
  have hdep := hK.depth
  have hsp := (show VPreP p σ₁ from p₁).sp
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hpub
  refine ⟨by rw [h₁.gpr .rsp (by decide), h₂.gpr .rsp (by decide), e5], by rw [h₁.gpr .rsp (by decide)]; omega,
    x.rd, x.wr, y.rd, y.wr, Covers.refl _, Covers.refl _, Covers.refl _, Covers.refl _,
    fun a b ha hb => ⟨kpreP p₁ h₁ ha, kpreP p₂ h₂ hb, ?_⟩⟩
  show _ ∧ _
  simp only [State.withRegions_gpr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ce_gpr h₁ ha (r := .rdi) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rdi) (by decide) (by decide) (by decide) (by decide), e1]
  · rw [ce_gpr h₁ ha (r := .rsi) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rsi) (by decide) (by decide) (by decide) (by decide), e2]
  · rw [ce_gpr h₁ ha (r := .rdx) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rdx) (by decide) (by decide) (by decide) (by decide), e3]
  · rw [ce_gpr h₁ ha (r := .rcx) (by decide) (by decide) (by decide) (by decide), ce_gpr h₂ hb (r := .rcx) (by decide) (by decide) (by decide) (by decide), e4]
  · rw [ce_rsp h₁ ha, ce_rsp h₂ hb, e5]
  · exact (hpkP p₁ h₁ ha).trans (e6.trans (hpkP p₂ h₂ hb).symm)
  · exact (hmuP p₁ h₁ ha).trans (e7.trans (hmuP p₂ h₂ hb).symm)
  · exact (hsigP p₁ h₁ ha).trans (e8.trans (hsigP p₂ h₂ hb).symm)
  · rw [ha.gpr _ (by decide) (by decide) (by decide), hb.gpr _ (by decide) (by decide) (by decide), h₁.r9, h₂.r9]

theorem implies {p : Params} (hsat : ∃ s, (preparedVerifyContract p X86_64.abi 56).pre s) :
    (verifyKP p).Implies (preparedVerifyContract p X86_64.abi 56) where
  pre s h := by
    sig_pre [preparedVerifyContract, preparedVerifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩
  post s s' _ h := by
    sig_post [preparedVerifyContract, preparedVerifySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [preparedVerifyContract, preparedVerifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
    have e := map_toNat_inj hb
    obtain ⟨e₁, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
    obtain ⟨e₁, e₂⟩ := List.append_inj' e₁ (by simp only [Proof.MlKem.bytesAt_length])
    exact ⟨hdi, hsi, hdx, hcx, hsp, e₁, e₂, e₃⟩
  sat := hsat

def externalSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0xA000 | .rdx => 0xB000 | .rcx => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := m
  rd := [⟨0x1000, preparedPublicKeyBytes p⟩, ⟨0xA000, 64⟩, ⟨0xB000, p.sigLen⟩]
  wr := [⟨0x10000, 8 * scratchWords p⟩]

theorem sat {P : Impl.MlDsa.X86_64.Verify.Prims} (C : Verify.PrimsOk P) {p : Params}
    (hp : p ∈ Verify.params) : ∃ s, (preparedVerifyContract p X86_64.abi 56).pre s := by
  have hsz : p.pkLen < 0x10000 ∧ preparedPublicKeyBytes p < 0x7000 := by
    simp only [Verify.params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  obtain ⟨_, s', _, _, _, hk⟩ := Verify.Prepare.preparePublic_correct C hp _
    (Message.runSat_pre hsz.1 (by omega_using [hsz]))
  refine ⟨externalSat p s'.mem, ?_⟩
  simp only [Verify.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedVerifyContract, preparedVerifySig, X86_64.abi, X86_64.argRegs] <;> sig_and_intros
  all_goals first | exact hk | rfl | decide | exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86_64.Verify.Prepared

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Spec.MlDsa
open VG.Proof.MlDsa.X86_64

theorem signPreparedEntry_verified (v : ArithImpl) {p : Params} (hp : p ∈ params) (n : String) :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.entry n
      (Impl.MlDsa.X86_64.Sign.sign (Sign.primsWith v.code) p) 1)
      (preparedSignContract p X86_64.abi 56) :=
  have hS := signFn v hp
  have hK : Sign.KernelFn p (Impl.MlDsa.X86_64.Sign.sign (Sign.primsWith v.code) p) :=
    ⟨hS.ok, hS.ct, hS.nosp, hS.depth⟩
  Verified.of_correct (Sign.Prepared.entryP_correct hK) (Sign.Prepared.entryP_ct hK)
    (Sign.Prepared.implies (Sign.Prepared.sat (Verify.prims_okWith v) hp))

theorem verifyPreparedEntry_verified (v : ArithImpl) {p : Params} (hp : p ∈ params) (n : String) :
    Verified X86_64.target (Impl.MlDsa.X86_64.Verify.entry n
      (Impl.MlDsa.X86_64.Verify.verify (Verify.primsWith v.code) p) 1)
      (preparedVerifyContract p X86_64.abi 56) :=
  have hV := verifyFn v hp
  have hK : Verify.KernelFn p (Impl.MlDsa.X86_64.Verify.verify (Verify.primsWith v.code) p) :=
    ⟨hV.ok, hV.ct, hV.nosp, hV.depth⟩
  Verified.of_correct (Verify.Prepared.entryP_correct hK) (Verify.Prepared.entryP_ct hK)
    (Verify.Prepared.implies (Verify.Prepared.sat (Verify.prims_okWith v) hp))

end VG.Proof.MlDsa.X86_64.Message
