module

public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Proof.Mcdt.X86_64
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NoSp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top

/-!
# ML-DSA key generation on x86-64: the entry

`vg_mldsa*_keygen` is `mcdtCall n c`: a call of the key generation function
`c` (`vg_mldsa*_keygen_internal`, `keyGen`), inside Intel's MXCSR prologue and
epilogue, so that the polynomial arithmetic it calls sets no MXCSR of its own.
Its contract is `kgK0`, `kgK` with 24 more bytes of stack, for the frame of
the prologue and epilogue and the return address of the call
(`Proof.Mcdt.X86_64.mcdtEntry_correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Proof.Mcdt.X86_64 (EntryOf)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-- The contract of `vg_mldsa*_keygen`: `kgK` with 56 bytes of stack. -/
def kgK0 (p : Params) : Contract isa where
  pre s :=
    56 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, 32⟩] ∧ s.wr = [⟨s.gpr .rsi, p.pkLen⟩, ⟨s.gpr .rdx, p.skLen⟩, ⟨s.gpr .rcx, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, p.pkLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, p.skLen⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, scrLen p⟩ ∧
    (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧
    (below (s.gpr .rsp) 56).Disjoint ⟨s.gpr .rcx, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + p.pkLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + scrLen p ≤ 2 ^ 64
  post := (kgK p).post
  pub := (kgK p).pub

section
variable {p : Params} {σ e : State} (hp : (kgK0 p).pre σ) (he : EntryOf σ e)
include he

theorem ke_gpr {r : Reg} (h1 : r ≠ .rsp) (h3 : r ≠ .rax) (h4 : r ≠ .rbx) :
    (e.withRegions σ.rd σ.wr).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, he.gpr r h1 h3 h4]

theorem ke_rsp : (e.withRegions σ.rd σ.wr).gpr .rsp = σ.gpr .rsp - 24 := by
  rw [State.withRegions_gpr, he.rsp]

/-- The frame and the return address of the call are below `rsp`, apart from the buffers. -/
theorem ke_bytes {a : Addr} {len : Nat} (hd : (below (σ.gpr .rsp) 56).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt (e.withRegions σ.rd σ.wr).mem a len = bytesAt σ.mem a len := by
  rw [State.withRegions_mem]
  refine VG.Proof.MlKem.bytesAt_frame he.mem (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega) (by omega))).symm

include hp in
theorem kpre0 : (kgK p).pre (e.withRegions σ.rd σ.wr) := by
  have hp' := hp
  obtain ⟨hsp, hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have e1 := ke_gpr he (r := .rdi) (by decide) (by decide) (by decide)
  have e2 := ke_gpr he (r := .rsi) (by decide) (by decide) (by decide)
  have e3 := ke_gpr he (r := .rdx) (by decide) (by decide) (by decide)
  have e4 := ke_gpr he (r := .rcx) (by decide) (by decide) (by decide)
  have er := ke_rsp he
  have hret : Region.Sub (retR (e.withRegions σ.rd σ.wr)) (below (σ.gpr .rsp) 56) := by
    rw [retR, er]; exact Proof.Mcdt.X86_64.sub_at _ (a := 24) (by omega) (by omega)
  have hbel : Region.Sub (below ((e.withRegions σ.rd σ.wr).gpr .rsp) 32) (below (σ.gpr .rsp) 56) := by
    rw [er]; exact Proof.Mcdt.X86_64.sub_below _ (a := 24) (by omega) (by omega)
  have hsp' : 32 ≤ ((e.withRegions σ.rd σ.wr).gpr .rsp).toNat := by
    rw [er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt
    simp only [show (24 : BitVec 64).toNat = 24 from rfl]; omega
  refine ⟨hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, e1, e2, e3, e4]
  · exact hrd
  · exact hwr
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · exact d5
  · exact d6
  · exact k1.sub_left hret
  · exact k2.sub_left hret
  · exact k3.sub_left hret
  · exact k4.sub_left hret
  · exact k1.sub_left hbel
  · exact k2.sub_left hbel
  · exact k3.sub_left hbel
  · exact k4.sub_left hbel
  · exact n1
  · exact n2
  · exact n3
  · exact n4

include hp in
theorem kpost0 {s₂ s' : State} (hm : Frame [below (σ.gpr .rsp) 16] s₂.mem s'.mem) (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (kgK p).post (e.withRegions σ.rd σ.wr) s₂) : (kgK0 p).post σ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, _, n1, n2, n3, _⟩ := hp'
  have hb : ∀ {a : Addr} {len : Nat}, (below (σ.gpr .rsp) 56).Disjoint ⟨a, len⟩ → len ≤ 2 ^ 64 →
      bytesAt s₂.mem a len = bytesAt s'.mem a len := fun hd hl =>
    (VG.Proof.MlKem.bytesAt_frame hm (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hd.sub_left (below_sub (by omega) (by omega))).symm) hl).symm
  show Spec.MlDsa.Outcome _ _ _
  have h' : Spec.MlDsa.Outcome _ _ _ := h
  rw [ke_gpr he (r := .rdi) (by decide) (by decide) (by decide), ke_gpr he (r := .rsi) (by decide) (by decide) (by decide),
    ke_gpr he (r := .rdx) (by decide) (by decide) (by decide), ke_bytes he k1 (by omega),
    hb k2 (by omega), hb k3 (by omega), hax] at h'
  exact h'

end

variable (v : ArithImpl) {p : Params}
  (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
include hp

omit v in
theorem keyGen0_noSp : noSpB (keyGen (primsWith .empty) p) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

omit v in
theorem keyGen0_depth : decide ((keyGen (primsWith .empty) p).depth ≤ 4) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem keyGen_noSp : NoSp (keyGen (primsWith v.code) p) :=
  noSp_of (Same.ok (keyGen_same (Comp.all _) (noSpB_of v.ok.ntt.nosp) (noSpB_of v.ok.add.nosp)
    (noSpB_of v.ok.rej4.nosp) (noSpB_of (v.ok.dotInv 4 (.inl rfl)).nosp)
    (noSpB_of (v.ok.dotInv 5 (.inr (.inl rfl))).nosp) (noSpB_of (v.ok.dotInv 7 (.inr (.inr rfl))).nosp) p)
    (keyGen0_noSp hp))

theorem keyGen_depth : (keyGen (primsWith v.code) p).depth ≤ 4 := by
  have dep : ∀ {c : Prog isa}, c.depth ≤ 3 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true h
  have dep2 : ∀ {c : Prog isa}, c.depth ≤ 2 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true (by omega)
  exact of_decide_eq_true (Same.ok (keyGen_same (depthCompN 3) (dep2 v.ok.ntt.depth) (dep2 v.ok.add.depth)
    (dep v.ok.rej4.depth) (dep2 (v.ok.dotInv 4 (.inl rfl)).depth) (dep2 (v.ok.dotInv 5 (.inr (.inl rfl))).depth)
    (dep2 (v.ok.dotInv 7 (.inr (.inr rfl))).depth) p) (keyGen0_depth hp))

omit v in
theorem keyGen0_implies : (kgK0 p).Implies (Spec.MlDsa.keyGenContract p X86_64.abi 56) :=
  { pre := by sig_implies_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, X86_64.abi, VG.X86_64.argRegs]
    post := by sig_implies_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, kgK, X86_64.abi,
      VG.X86_64.argRegs]
    pub := by
      intro s₁ s₂ _ _ h
      sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, kgK, X86_64.abi, VG.X86_64.argRegs] at h
      obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
      exact ⟨hdi, hsi, hdx, hcx, hsp, hb⟩
    sat := by
      rcases hp with rfl | rfl | rfl
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa44
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa65
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK0, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa87 }

/-- `vg_mldsa*_keygen`: the key generation function, inside Intel's MXCSR prologue and epilogue. -/
theorem keyGenEntry_verified (n : String) :
    Verified X86_64.target (Impl.Mcdt.X86_64.mcdtCall n (keyGen (primsWith v.code) p))
      (Spec.MlDsa.keyGenContract p X86_64.abi 56) := by
  have hd := keyGen_depth v hp
  refine Verified.of_correct (Proof.Mcdt.X86_64.mcdtEntry_correct (keyGen_correct (prims_okWith v) (pfacts hp))
      (keyGen_noSp v hp) (fun σ h => by have := h.1; omega) (fun σ e h he => kpre0 h he) (fun σ h r hr => ?_)
      (fun σ e s₂ s' h he hm hax hq => kpost0 h he hm hax hq))
    (Proof.Mcdt.X86_64.mcdtEntry_ct (keyGen_correct (prims_okWith v) (pfacts hp)) (keyGen_ct (prims_okWith v) (pfacts hp))
      (keyGen_noSp v hp) (fun σ h => by have := h.1; omega) (fun σ e h he => kpre0 h he)
      (fun σ₁ σ₂ _ _ h => h.2.2.2.2.1) (fun σ₁ σ₂ e₁ e₂ h₁ h₂ hpub he₁ he₂ => ?_))
    (keyGen0_implies hp)
  · obtain ⟨_, _, hwr, _, _, _, _, _, _, _, r2, r3, r4, _, k2, k3, k4, _, _, _, _⟩ := h
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨k2.sub_left (below_sub (by omega) (by omega)), r2⟩
    · exact ⟨k3.sub_left (below_sub (by omega) (by omega)), r3⟩
    · exact ⟨k4.sub_left (below_sub (by omega) (by omega)), r4⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hpub
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, k1, _, _, _, n1, _, _, _⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, l1, _, _, _, m1, _, _, _⟩ := h₂
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ke_gpr he₁ (by decide) (by decide) (by decide), ke_gpr he₂ (by decide) (by decide) (by decide), e1]
    · rw [ke_gpr he₁ (by decide) (by decide) (by decide), ke_gpr he₂ (by decide) (by decide) (by decide), e2]
    · rw [ke_gpr he₁ (by decide) (by decide) (by decide), ke_gpr he₂ (by decide) (by decide) (by decide), e3]
    · rw [ke_gpr he₁ (by decide) (by decide) (by decide), ke_gpr he₂ (by decide) (by decide) (by decide), e4]
    · rw [ke_rsp he₁, ke_rsp he₂, e5]
    · rw [ke_gpr he₁ (r := .rdi) (by decide) (by decide) (by decide), ke_gpr he₂ (r := .rdi) (by decide) (by decide) (by decide),
        ke_bytes he₁ k1 (by omega), ke_bytes he₂ l1 (by omega)]
      exact e6

theorem keyGenEntry_spSafe (n : String) :
    (Impl.Mcdt.X86_64.mcdtCall n (keyGen (primsWith v.code) p)).all (fun i => !isa.writesSp i) = true :=
  Proof.Mcdt.X86_64.mcdtCall_spSafe (keyGen_spSafe v hp)

end VG.Proof.MlDsa.X86_64.KeyGen
