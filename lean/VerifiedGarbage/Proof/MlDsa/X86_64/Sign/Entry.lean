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

/-!
# ML-DSA signing on x86-64: the entry of an encoded key

`vg_mldsa*_sign` is `entry n c 0`: `r9 ← 0`, then a call of the signing
function `c` (`vg_mldsa*_sign_with_cache`), which, with `r9 = 0`, decodes the
key. Its contract is `signK0`, `signK` without the flag, with 8 more bytes of
stack, for the return address of the call.
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

theorem signK0_implies_of {p : Params} (hsat : ∃ s, (signContract p X86_64.abi 40).pre s) :
    (signK0 p 40).Implies (signContract p X86_64.abi 40) where
  pre := by sig_implies_pre [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContract, signSig, signK0, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

theorem signK0_implies {p : Params} (h3 : Ok3 p) :
    (signK0 p 40).Implies (signContract p X86_64.abi 40) := by
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
variable {p : Params} {σ s : State} (hp : (signK0 p 40).pre σ) (hs : Moved .r9 0 σ s)
include hp hs

omit hp in
theorem ce_gpr {r : Reg} (h1 : r ≠ .rsp) (h2 : r ≠ .r9) : s.callEntry.gpr r = σ.gpr r := by
  rw [State.callEntry_gpr _ h1, hs.gpr r h2]

omit hp in
theorem ce_rsp : s.callEntry.gpr .rsp = σ.gpr .rsp - 8 := by
  rw [State.callEntry_rsp, hs.gpr .rsp (by decide)]

omit hp in
/-- The return address of the call is below `rsp`, apart from the buffers. -/
theorem ce_bytes {a : Addr} {len : Nat} (hd : (below (σ.gpr .rsp) 40).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt s.callEntry.mem a len = bytesAt σ.mem a len := by
  have hf : Frame [below (σ.gpr .rsp) 8] σ.mem s.callEntry.mem := by
    rw [State.callEntry_mem, hs.mem, hs.gpr .rsp (by decide)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine VG.Proof.MlKem.bytesAt_frame hf (fun r hr => ?_) hl
  rw [List.mem_singleton] at hr; subst hr
  exact (hd.sub_left (below_sub (by omega) (by omega))).symm

theorem kpre0 : (signK p 32).pre s.callEntry := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp'
  have h9 : s.callEntry.gpr .r9 = 0 := by rw [State.callEntry_gpr _ (by decide), hs.r9]
  have hL : skL p s.callEntry = p.skLen := by simp only [skL, h9, ite_true]
  have e1 := ce_gpr hs (r := .rdi) (by decide) (by decide)
  have e2 := ce_gpr hs (r := .rsi) (by decide) (by decide)
  have e3 := ce_gpr hs (r := .rdx) (by decide) (by decide)
  have e4 := ce_gpr hs (r := .rcx) (by decide) (by decide)
  have e5 := ce_gpr hs (r := .r8) (by decide) (by decide)
  have er := ce_rsp hs
  have hret : Region.Sub (retR s.callEntry) (below (σ.gpr .rsp) 40) := by
    rw [retR, er]; exact below_sub (sp := σ.gpr .rsp) (a := 8) (by omega) (by omega)
  have hbel : Region.Sub (below (s.callEntry.gpr .rsp) 32) (below (σ.gpr .rsp) 40) := by
    rw [er]; exact below_callee _ 32
  have hsp' : 32 ≤ (s.callEntry.gpr .rsp).toNat := by
    rw [er, BitVec.toNat_sub]; have := (σ.gpr .rsp).isLt
    simp only [show (8 : BitVec 64).toNat = 8 from rfl]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsp', ?_⟩
  all_goals simp only [hL, e1, e2, e3, e4, e5, State.callEntry_rd, State.callEntry_wr, hs.rd, hs.wr]
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

theorem kpost0 {s' s₂ : State} (hm : s₂.mem = s'.mem) (hax : s₂.gpr .rax = s'.gpr .rax)
    (h : (signK p 32).post s.callEntry s₂) : (signK0 p 40).post σ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, _, _, n1, n2, n3, _, _, _⟩ := hp'
  show Outcome _ _ _
  have h' : Outcome _ _ _ := h
  rw [ce_gpr hs (r := .rdi) (by decide) (by decide), ce_gpr hs (r := .rsi) (by decide) (by decide),
    ce_gpr hs (r := .rdx) (by decide) (by decide), ce_gpr hs (r := .rcx) (by decide) (by decide),
    ce_bytes hs k1 (by omega), ce_bytes hs k2 (by omega), ce_bytes hs k3 (by omega), hm, hax] at h'
  exact h'

end

/-- A signing function on `μ` with the flag in `r9`. -/
structure KernelFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (signK p 32).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK p 32).post s s'
  ct : ConstantTime isa (signK p 32).pre (signK p 32).pub c
  nosp : NoSp c
  depth : c.depth ≤ 4

theorem entry0_correct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) (σ : State)
    (hpre : (signK0 p 40).pre σ) :
    ∃ t s', Exec isa (entry n c 0) σ t s' ∧ abiPreserved σ s' ∧ (signK0 p 40).post σ s' := by
  have hp' := hpre
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, r4, r5, _, _, _, _, _, _, _, _, _, _, hsp⟩ := hp'
  have hdep := hK.depth
  have main : WP isa (entry n c 0) σ fun s' => abiPreserved σ s' ∧ (signK0 p 40).post σ s' := by
    unfold entry
    refine WP.seq (WP.mono (flag_ok .r9 0 σ) fun s hs => ?_)
    have hs' : Moved .r9 0 σ s := hs
    refine WP.call_mx hK.ok hK.nosp (by omega) (rd := s.rd) (wr := s.wr)
      (by rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl]; exact kpre0 hpre hs')
      (fun _ _ h => h) (fun _ _ h => h) fun s' _ _ hcs hf _ hpost hmx => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · rw [hcs r hr, hs'.gpr r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · rw [hs'.wr, hs'.gpr .rsp (by decide), hs'.mem] at hf
      refine hf.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      rcases List.mem_append.mp hr with hr | hr
      · rw [hwr] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [r4, r5]
      · rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint_below _ (by omega)
    · rw [hmx, hs'.mx]
    · obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
      exact kpost0 hpre hs' hm₂ (hg₂ _ (by decide)) hq
  obtain ⟨t, s', he, ha, hq⟩ := main
  exact ⟨t, s', he, ha, hq⟩

theorem entry0_ct {p : Params} {n : String} {c : Prog isa} (hK : KernelFn p c) :
    ConstantTime isa (signK0 p 40).pre (signK0 p 40).pub (entry n c 0) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold entry
  refine RelCT.seq (relInv (I' := fun σ s => Moved .r9 0 σ s) (fun σ s _ (hs : s = σ) => by rw [hs]; exact flag_ok .r9 0 σ)
    (block_tr (rs := []) rfl fun _ _ _ r hr => absurd hr (List.not_mem_nil))) ?_
  refine RelCT.callEx hK.ok hK.ct fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, h₁, h₂⟩ => ?_
  refine ⟨x.rd, x.wr, y.rd, y.wr, kpre0 p₁ h₁, kpre0 p₂ h₂, ?_, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ h => h, by rw [h₁.gpr .rsp (by decide), h₂.gpr .rsp (by decide), hpub.2.2.2.2.2.1]⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hpub
  have q₁ := p₁; have q₂ := p₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, k1, k2, k3, _, _, n1, n2, n3, _, _, _⟩ := q₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, l1, l2, l3, _, _, m1, m2, m3, _, _, _⟩ := q₂
  show _ = _ ∧ _
  simp only [State.withRegions_gpr, State.withRegions_mem]
  rw [ce_gpr h₁ (r := .rdi) (by decide) (by decide), ce_gpr h₁ (r := .rsi) (by decide) (by decide),
    ce_gpr h₁ (r := .rdx) (by decide) (by decide), ce_gpr h₁ (r := .rcx) (by decide) (by decide),
    ce_gpr h₁ (r := .r8) (by decide) (by decide), ce_rsp h₁,
    ce_gpr h₂ (r := .rdi) (by decide) (by decide), ce_gpr h₂ (r := .rsi) (by decide) (by decide),
    ce_gpr h₂ (r := .rdx) (by decide) (by decide), ce_gpr h₂ (r := .rcx) (by decide) (by decide),
    ce_gpr h₂ (r := .r8) (by decide) (by decide), ce_rsp h₂,
    ce_bytes h₁ k1 (by omega), ce_bytes h₁ k2 (by omega), ce_bytes h₁ k3 (by omega),
    ce_bytes h₂ l1 (by omega), ce_bytes h₂ l2 (by omega), ce_bytes h₂ l3 (by omega),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h₁.r9, h₂.r9]
  exact ⟨e1, e2, e3, e4, e5, by rw [e6], e7, rfl⟩

end VG.Proof.MlDsa.X86_64.Sign
