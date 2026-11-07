module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Entry
public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr

-- separate module: the encoded-key entry's contract depends only on the verification kernel, not on
-- the message functions, so a change to either rebuilds less.

/-!
# ML-DSA verification on x86-64: the entry of an encoded key

`vg_mldsa*_verify` is `entry n c 0`: `r8 ← 0`, then a call of the verification
function `c` (`vg_mldsa*_verify_with_cache`), which, with `r8 = 0`, decodes the
key. Its contract is `verifyK0`: `verifyContract` with 40 bytes of stack, 8 more
than the function's, for the return address of the call.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep WP.keep Rel2 relStart relInv)
open VG.Proof.MlDsa.X86_64.Sign (Moved flag_ok)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The precondition of `verifyContract p X86_64.abi 40`. -/
structure VPre0 (p : Params) (σ : State) : Prop where
  sp : 40 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, p.pkLen⟩, ⟨σ.gpr .rsi, 64⟩, ⟨σ.gpr .rdx, p.sigLen⟩]
  wr : σ.wr = [⟨σ.gpr .rcx, scrLen p⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, p.pkLen⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d2 : Region.Disjoint ⟨σ.gpr .rsi, 64⟩ ⟨σ.gpr .rcx, scrLen p⟩
  d3 : Region.Disjoint ⟨σ.gpr .rdx, p.sigLen⟩ ⟨σ.gpr .rcx, scrLen p⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, p.pkLen⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, 64⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, p.sigLen⟩
  r4 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rcx, scrLen p⟩
  k1 : (below (σ.gpr .rsp) 40).Disjoint ⟨σ.gpr .rdi, p.pkLen⟩
  k2 : (below (σ.gpr .rsp) 40).Disjoint ⟨σ.gpr .rsi, 64⟩
  k3 : (below (σ.gpr .rsp) 40).Disjoint ⟨σ.gpr .rdx, p.sigLen⟩
  k4 : (below (σ.gpr .rsp) 40).Disjoint ⟨σ.gpr .rcx, scrLen p⟩
  n1 : (σ.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + 64 ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + p.sigLen ≤ 2 ^ 64
  n4 : (σ.gpr .rcx).toNat + scrLen p ≤ 2 ^ 64

/-- The contract of the entry of an encoded key. -/
def verifyK0 (p : Params) : Contract isa where
  pre := VPre0 p
  post := (verifyK p).post
  pub σ₁ σ₂ := σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧ σ₁.gpr .rdx = σ₂.gpr .rdx ∧
    σ₁.gpr .rcx = σ₂.gpr .rcx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp ∧ vPk p σ₁ = vPk p σ₂ ∧ vMu σ₁ = vMu σ₂ ∧
    vSig p σ₁ = vSig p σ₂

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 0x40000 | .rsp => 0x200000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, p.pkLen⟩, ⟨0x20000, 64⟩, ⟨0x30000, p.sigLen⟩]
  wr := [⟨0x40000, scrLen p⟩]

theorem verify_sat : ∀ p ∈ params, ∃ s, (verifyContract p X86_64.abi 40).pre s := by
  intro p hp
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa44
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa65
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa87

theorem verify_implies0 {p : Params} (hp : p ∈ params) : (verifyK0 p).Implies (verifyContract p X86_64.abi 40) where
  pre s h := by
    sig_pre [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
  post s s' _ h := by
    sig_post [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
    have e := map_toNat_inj hb
    obtain ⟨e₁, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
    obtain ⟨e₁, e₂⟩ := List.append_inj' e₁ (by simp only [Proof.MlKem.bytesAt_length])
    exact ⟨hdi, hsi, hdx, hcx, hsp, e₁, e₂, e₃⟩
  sat := verify_sat p hp


section
variable {p : Params} {σ s : State} (hp : VPre0 p σ) (hs : Moved .r8 0 σ s)
include hp hs

omit hp in
theorem ce_gpr {r : Reg} (h1 : r ≠ .rsp) (h2 : r ≠ .r8) : s.callEntry.gpr r = σ.gpr r := by
  rw [State.callEntry_gpr _ h1, hs.gpr r h2]

omit hp in
theorem ce_rsp : s.callEntry.gpr .rsp = σ.gpr .rsp - 8 := by
  rw [State.callEntry_rsp, hs.gpr .rsp (by decide)]

omit hp in
theorem ce_bytes {a : Addr} {len : Nat} (hd : (below (σ.gpr .rsp) 40).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt s.callEntry.mem a len = bytesAt σ.mem a len := by
  have hf : Frame [below (σ.gpr .rsp) 8] σ.mem s.callEntry.mem := by
    rw [State.callEntry_mem, hs.mem, hs.gpr .rsp (by decide)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine Proof.MlKem.bytesAt_frame hf (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega) (by omega))).symm

theorem kpre0 : VPre p s.callEntry := by
  have h8 : s.callEntry.gpr .r8 = 0 := by rw [State.callEntry_gpr _ (by decide), hs.r9]
  have hL : pkL p s.callEntry = p.pkLen := by simp only [pkL, h8, ite_true]
  have e1 := ce_gpr hs (r := .rdi) (by decide) (by decide)
  have e2 := ce_gpr hs (r := .rsi) (by decide) (by decide)
  have e3 := ce_gpr hs (r := .rdx) (by decide) (by decide)
  have e4 := ce_gpr hs (r := .rcx) (by decide) (by decide)
  have er := ce_rsp hs
  have hret : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (σ.gpr .rsp) 40) := by
    rw [er]; exact below_sub (sp := σ.gpr .rsp) (a := 8) (by omega) (by omega)
  have hbel : Region.Sub (below (s.callEntry.gpr .rsp) 32) (below (σ.gpr .rsp) 40) := by
    rw [er]; exact below_callee _ 32
  have hsp' : 32 ≤ (s.callEntry.gpr .rsp).toNat := by
    rw [er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt; have := hp.sp
    simp only [show (8 : BitVec 64).toNat = 8 from rfl]; omega
  refine ⟨hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hL, e1, e2, e3, e4, State.callEntry_rd, State.callEntry_wr, hs.rd, hs.wr]
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
  · intro h; exact absurd h8 h

theorem kpost0 {s' s₂ : State} (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (verifyK p).post s.callEntry s₂) : (verifyK0 p).post σ s' := by
  have hpk : vPk p s.callEntry = vPk p σ := by
    rw [vPk, ce_gpr hs (r := .rdi) (by decide) (by decide), ce_bytes hs hp.k1 (by have := hp.n1; omega)]
  have hmu : vMu s.callEntry = vMu σ := by
    rw [vMu, ce_gpr hs (r := .rsi) (by decide) (by decide), ce_bytes hs hp.k2 (by omega)]
  have hsig : vSig p s.callEntry = vSig p σ := by
    rw [vSig, ce_gpr hs (r := .rdx) (by decide) (by decide), ce_bytes hs hp.k3 (by have := hp.n3; omega)]
  have hres : res s₂ = res s' := by simp only [res, hax]
  show _ ∨ _
  have h' : _ ∨ _ := h
  rw [hpk, hmu, hsig, hres] at h'
  exact h'

end

/-- A verification function on `μ` with the flag in `r8`. -/
structure KernelFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (verifyK p).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (verifyK p).post s s'
  ct : ConstantTime isa (verifyK p).pre (verifyK p).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

theorem entry0_correct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) (σ : State)
    (hpre : VPre0 p σ) :
    ∃ t s', Exec isa (entry n c 0) σ t s' ∧ abiPreserved σ s' ∧ (verifyK0 p).post σ s' := by
  have hdep := hK.depth
  have hsp := hpre.sp
  have main : WP isa (entry n c 0) σ fun s' => abiPreserved σ s' ∧ (verifyK0 p).post σ s' := by
    unfold entry
    refine WP.seq (WP.mono (flag_ok .r8 0 σ) fun s hs => ?_)
    have hs' : Moved .r8 0 σ s := hs
    refine WP.call_mx hK.ok hK.nosp (by omega) (rd := s.rd) (wr := s.wr)
      (by rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl]; exact kpre0 hpre hs')
      (fun _ _ h => h) (fun _ _ h => h) fun s' _ _ hcs hf _ hpost hmx => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · rw [hcs r hr, hs'.gpr r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · rw [hs'.wr, hs'.gpr .rsp (by decide), hs'.mem] at hf
      refine hf.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      rcases List.mem_append.mp hr with hr | hr
      · rw [hpre.wr] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact hpre.r4
      · rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint_below _ (by omega)
    · rw [hmx, hs'.mx]
    · obtain ⟨s₂, -, hg₂, hq⟩ := hpost
      exact kpost0 hpre hs' (hg₂ _ (by decide)) hq
  obtain ⟨t, s', he, ha, hq⟩ := main
  exact ⟨t, s', he, ha, hq⟩

theorem entry0_ct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) :
    ConstantTime isa (verifyK0 p).pre (verifyK0 p).pub (entry n c 0) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold entry
  refine RelCT.seq (relInv (I' := fun σ s => Moved .r8 0 σ s)
    (fun σ s _ (hs : s = σ) => by rw [hs]; exact flag_ok .r8 0 σ)
    (Sign.block_tr (rs := []) rfl fun _ _ _ r hr => absurd hr (List.not_mem_nil))) ?_
  refine RelCT.callEx hK.ok hK.ct fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, h₁, h₂⟩ => ?_
  refine ⟨x.rd, x.wr, y.rd, y.wr, kpre0 p₁ h₁, kpre0 p₂ h₂, ?_, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ h => h, by rw [h₁.gpr .rsp (by decide), h₂.gpr .rsp (by decide), hpub.2.2.2.2.1]⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hpub
  have hpk : ∀ {σ s}, VPre0 p σ → Moved .r8 0 σ s → vPk p s.callEntry = vPk p σ := fun hp hs => by
    rw [vPk, ce_gpr hs (r := .rdi) (by decide) (by decide), ce_bytes hs hp.k1 (by have := hp.n1; omega)]
  have hmu : ∀ {σ s}, VPre0 p σ → Moved .r8 0 σ s → vMu s.callEntry = vMu σ := fun hp hs => by
    rw [vMu, ce_gpr hs (r := .rsi) (by decide) (by decide), ce_bytes hs hp.k2 (by omega)]
  have hsig : ∀ {σ s}, VPre0 p σ → Moved .r8 0 σ s → vSig p s.callEntry = vSig p σ := fun hp hs => by
    rw [vSig, ce_gpr hs (r := .rdx) (by decide) (by decide), ce_bytes hs hp.k3 (by have := hp.n3; omega)]
  show _ ∧ _
  simp only [State.withRegions_gpr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ce_gpr h₁ (r := .rdi) (by decide) (by decide), ce_gpr h₂ (r := .rdi) (by decide) (by decide), e1]
  · rw [ce_gpr h₁ (r := .rsi) (by decide) (by decide), ce_gpr h₂ (r := .rsi) (by decide) (by decide), e2]
  · rw [ce_gpr h₁ (r := .rdx) (by decide) (by decide), ce_gpr h₂ (r := .rdx) (by decide) (by decide), e3]
  · rw [ce_gpr h₁ (r := .rcx) (by decide) (by decide), ce_gpr h₂ (r := .rcx) (by decide) (by decide), e4]
  · rw [ce_rsp h₁, ce_rsp h₂, e5]
  · exact (hpk p₁ h₁).trans (e6.trans (hpk p₂ h₂).symm)
  · exact (hmu p₁ h₁).trans (e7.trans (hmu p₂ h₂).symm)
  · exact (hsig p₁ h₁).trans (e8.trans (hsig p₂ h₂).symm)
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.r9, h₂.r9]

end VG.Proof.MlDsa.X86_64.Verify
