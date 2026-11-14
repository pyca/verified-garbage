module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inv
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
public import VerifiedGarbage.Proof.Mcdt.X86_64

/-!
# ML-DSA signing on x86-64: the entry of an encoded key

`vg_mldsa*_sign` is `entry n c 0`: `r9 ← 0`, then a call of the signing
function `c` (`vg_mldsa*_sign_with_cache`), which, with `r9 = 0`, decodes the
key. Its contract is `signK0`, `signK` without the flag, with 24 more bytes of
stack, for the frame of Intel's MXCSR prologue and epilogue around the call
(`Impl.Mcdt.X86_64.mcdtCall`) and its return address.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep Rel2 relStart relInv)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa*_sign(sk = rdi, mu = rsi, rnd = rdx, sig = rcx, scratch = r8) -> eax`, with `D` bytes
of stack, and the leakage `signLeak`. -/
def signK0 (p : Params) (D : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, p.skLen⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, p.sigLen⟩, ⟨s.gpr .r8, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdi, p.skLen⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + scrLen p ≤ 2 ^ 64 ∧
    D ≤ (s.gpr .rsp).toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .rdi) p.skLen) (bytesAt s.mem (s.gpr .rsi) 64)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rcx) p.sigLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    signLeak p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) 64)
        (bytesAt s₁.mem (s₁.gpr .rdx) 32) =
      signLeak p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) 64)
        (bytesAt s₂.mem (s₂.gpr .rdx) 32)

/-- A state satisfying `signContract`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x3100 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK0_implies_of {p : Params} (hsat : ∃ s, (signContract p X86_64.abi 56).pre s) :
    (signK0 p 56).Implies (signContract p X86_64.abi 56) where
  pre := by sig_implies_pre [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

theorem signK0_implies {p : Params} (h3 : Ok3 p) :
    (signK0 p 56).Implies (signContract p X86_64.abi 56) := by
  refine signK0_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa44
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa65
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa87

/-- What `d ← flag` leaves. -/
structure Moved (d : Reg) (v : BitVec 64) (σ s : State) : Prop where
  gpr : ∀ r, r ≠ d → s.gpr r = σ.gpr r
  r9 : s.gpr d = v
  mem : s.mem = σ.mem
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mx : s.mxcsr = σ.mxcsr

theorem flag_ok (d : Reg) (flag : Nat) (σ : State) :
    WP isa (.block [.mov32 d (.imm (BitVec.ofNat 32 flag))]) σ
      (Moved d (BitVec.setWidth 64 (BitVec.ofNat 32 flag)) σ) := by
  refine WP.mono (WP.keep [d] (Q := fun s => s.gpr d = BitVec.setWidth 64 (BitVec.ofNat 32 flag) ∧
      s.mem = σ.mem ∧ s.mxcsr = σ.mxcsr) (by xrun <;> rfl) (by cases d <;> rfl)) fun s ⟨⟨h9, hm, hx⟩, k⟩ =>
    ⟨fun r hr => k.gpr (by simpa using hr), h9, hm, k.2.1, k.2.2, hx⟩

section
variable {p : Params} {σ s e : State} (hp : (signK0 p 56).pre σ) (hs : Moved .r9 0 σ s) (he : Proof.Mcdt.X86_64.EntryOf s e)
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
  exact (hd.sub_left (below_sub (by omega) (by omega))).symm

theorem kpre0 : (signK p 32).pre (e.withRegions s.rd s.wr) := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp'
  have h9 : (e.withRegions s.rd s.wr).gpr .r9 = 0 := by
    rw [State.withRegions_gpr, he.gpr _ (by decide) (by decide) (by decide), hs.r9]
  have hL : skL p (e.withRegions s.rd s.wr) = p.skLen := by simp only [skL, h9, ite_true]
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
    simp only [show (24 : BitVec 64).toNat = 24 from rfl]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsp', ?_⟩
  all_goals simp only [hL, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, e1, e2, e3, e4, e5,
    hs.rd, hs.wr]
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
  · intro h; exact absurd h9 h

theorem kpost0 {s' s₂ : State} (hm : Frame [below (σ.gpr .rsp) 16] s₂.mem s'.mem) (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (signK p 32).post (e.withRegions s.rd s.wr) s₂) : (signK0 p 56).post σ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, k4, _, n1, n2, n3, n4, _, _⟩ := hp'
  show Outcome _ _ _
  have h' : Outcome _ _ _ := h
  have hsig : bytesAt s₂.mem (σ.gpr .rcx) p.sigLen = bytesAt s'.mem (σ.gpr .rcx) p.sigLen :=
    (VG.Proof.MlKem.bytesAt_frame hm (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (k4.sub_left (below_sub (by omega) (by omega))).symm) (by omega)).symm
  simp only [State.withRegions_gpr, State.withRegions_mem] at h'
  rw [ce_gpr hs he (r := .rdi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr hs he (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr hs he (r := .rdx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr hs he (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_bytes hs he k1 (by omega), ce_bytes hs he k2 (by omega), ce_bytes hs he k3 (by omega), hsig, hax] at h'
  exact h'

end

/-- A signing function on `μ` with the flag in `r9`. -/
structure KernelFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (signK p 32).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK p 32).post s s'
  ct : ConstantTime isa (signK p 32).pre (signK p 32).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

/-- What the entry keeps of its caller's state, from what `WP.mcdtCall` says of the call. -/
theorem entry_abi {σ s s' : State} {D : Nat} (hD : D ≤ (σ.gpr .rsp).toNat) (h56 : 56 ≤ D)
    {d : Reg} {v : BitVec 64} (hs : Moved d v σ s) (hd : d ∉ calleeSaved)
    (hret : ∀ r ∈ s.wr, Region.Disjoint ⟨σ.gpr .rsp, 8⟩ r) {k : Nat} (hk : 8 * k + 24 ≤ D)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hf : Frame (s.wr ++ [below (s.gpr .rsp) (8 * k + 24)]) s.mem s'.mem)
    (hmx : s'.mxcsr = s.mxcsr &&& 0xFFFF) : abiPreserved σ s' := by
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rw [hcs r hr, hs.gpr r fun h => hd (h ▸ hr)]
  · rw [hs.gpr .rsp (fun h => hd (by rw [← h]; decide)), hs.mem] at hf
    refine hf.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · exact hret r hr
    · rw [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint_below _ (by omega)
  · rw [hmx, Proof.Mcdt.X86_64.ctl_mask, hs.mx]

theorem entry0_correct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) (σ : State)
    (hpre : (signK0 p 56).pre σ) :
    ∃ t s', Exec isa (entry n c 0) σ t s' ∧ abiPreserved σ s' ∧ (signK0 p 56).post σ s' := by
  have hp' := hpre
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, r4, r5, _, _, _, k4, k5, _, _, _, _, _, hsp⟩ := hp'
  have hdep := hK.depth
  have main : WP isa (entry n c 0) σ fun s' => abiPreserved σ s' ∧ (signK0 p 56).post σ s' := by
    unfold entry
    refine WP.seq (WP.mono (flag_ok .r9 0 σ) fun s hs => ?_)
    have hs' : Moved .r9 0 σ s := hs
    have hsp1 : s.gpr .rsp = σ.gpr .rsp := hs'.gpr .rsp (by decide)
    refine Proof.Mcdt.X86_64.WP.mcdtCall hK.ok hK.nosp (by rw [hsp1]; omega) (rd := s.rd) (wr := s.wr)
      (fun e he => kpre0 hpre hs' he) (Covers.refl _) (Covers.refl _) (fun r hr => ?_)
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
      exact kpost0 hpre hs' he hm₂ (hg₂ _ (by decide) (by decide)) hq
  obtain ⟨t, s', he, ha, hq⟩ := main
  exact ⟨t, s', he, ha, hq⟩

theorem entry0_ct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) :
    ConstantTime isa (signK0 p 56).pre (signK0 p 56).pub (entry n c 0) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold entry
  refine RelCT.seq (relInv (I' := fun σ s => Moved .r9 0 σ s) (fun σ s _ (hs : s = σ) => by rw [hs]; exact flag_ok .r9 0 σ)
    (block_tr (rs := []) rfl fun _ _ _ r hr => absurd hr (List.not_mem_nil))) ?_
  refine Proof.Mcdt.X86_64.RelCT.mcdtCall hK.ok hK.ct hK.nosp fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, h₁, h₂⟩ => ?_
  have hdep := hK.depth
  have q₁ := p₁; have q₂ := p₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, _, _, n1, n2, n3, _, _, hsp₁⟩ := q₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, l1, l2, l3, _, _, m1, m2, m3, _, _, _⟩ := q₂
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hpub
  refine ⟨by rw [h₁.gpr .rsp (by decide), h₂.gpr .rsp (by decide), e6], by rw [h₁.gpr .rsp (by decide)]; omega,
    x.rd, x.wr, y.rd, y.wr, Covers.refl _, Covers.refl _, Covers.refl _, Covers.refl _,
    fun a b ha hb => ⟨kpre0 p₁ h₁ ha, kpre0 p₂ h₂ hb, ?_⟩⟩
  show _ = _ ∧ _
  simp only [State.withRegions_gpr, State.withRegions_mem]
  rw [ce_gpr h₁ ha (r := .rdi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .rdx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₁ ha (r := .r8) (by decide) (by decide) (by decide) (by decide), ce_rsp h₁ ha,
    ce_gpr h₂ hb (r := .rdi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .rsi) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .rdx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .rcx) (by decide) (by decide) (by decide) (by decide),
    ce_gpr h₂ hb (r := .r8) (by decide) (by decide) (by decide) (by decide), ce_rsp h₂ hb,
    ce_bytes h₁ ha k1 (by omega), ce_bytes h₁ ha k2 (by omega), ce_bytes h₁ ha k3 (by omega),
    ce_bytes h₂ hb l1 (by omega), ce_bytes h₂ hb l2 (by omega), ce_bytes h₂ hb l3 (by omega),
    ha.gpr _ (by decide) (by decide) (by decide), hb.gpr _ (by decide) (by decide) (by decide), h₁.r9, h₂.r9]
  exact ⟨e1, e2, e3, e4, e5, by rw [e6], e7, rfl⟩

end VG.Proof.MlDsa.X86_64.Sign
