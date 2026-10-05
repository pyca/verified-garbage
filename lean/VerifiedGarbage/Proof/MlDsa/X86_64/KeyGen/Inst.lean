import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.KeyGen
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base`. -/
section

/-!
# ML-DSA key generation on x86-64: the primitives, and calling them

Key generation is proven for any implementations of the primitives it calls
(`Prims`) that are verified against their contracts, with at most 16 bytes of
stack, and that change the stack pointer only by calls nested at most twice
(`Callee`, `PrimsOk`): as ML-KEM's top-level functions on x86-64
(`Proof/MlKem/X86_64/`), whose framework (layouts of buffers, calls, the
sponge) the proofs use.

A primitive may load MXCSR (as the MXCSR prologue of Intel's MCDT does), so
MXCSR's control bits (`MX`) are carried from its `abiPreserved`
(`WP.callMx`, `glueCallMx_ok`), and from code that never loads MXCSR
(`WP.mx`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen (Prims)

/-! ## The primitives -/

/-- Code `c` verified against the contract `k stk` of some stack `stk ≤ 16`,
that never writes `rsp` but by calls nested at most twice. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) : Prop where
  verified : ∃ stk, stk ≤ 16 ∧ Verified X86_64.target c (k stk)
  nosp : NoSp c
  depth : c.depth ≤ 2

/-- `vg_mldsa_rej_ntt_poly4`: verified with 24 bytes of stack, never writing `rsp` but by calls nested at
most three deep. -/
structure Callee4 (c : Prog isa) : Prop where
  verified : Verified X86_64.target c (Spec.MlDsa.rejNTT4Contract X86_64.abi 24)
  nosp : NoSp c
  depth : c.depth ≤ 3

/-- Verified implementations of the primitives key generation calls. -/
structure PrimsOk (P : VG.Impl.MlDsa.X86_64.KeyGen.Prims) : Prop where
  ntt : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86_64.abi stk)
  invNtt : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86_64.abi stk)
  mul : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.mul (fun stk => Spec.MlDsa.mulContract X86_64.abi stk)
  mulAdd : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk)
  add : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.add (fun stk => Spec.MlDsa.addContract X86_64.abi stk)
  rejNtt : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
  rejBounded : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
  power2Round : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
  simpleBitPack : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
  bitPack : VG.Proof.MlDsa.X86_64.KeyGen.Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)
  rej4 : VG.Proof.MlDsa.X86_64.KeyGen.Callee4 P.rej4

/-! ## MXCSR -/

/-- The control bits of MXCSR, which `abiPreserved` keeps. -/
abbrev MX (s : State) : BitVec 10 := s.mxcsr.extractLsb' 6 10

/-- Code that never loads MXCSR keeps it. -/
theorem WP.mx {c : Prog isa} (hc : ∀ i ∈ VG.instrs c, loadsMxcsr i = false) {s : State} {Q : State → Prop}
    (h : WP isa c s Q) : WP isa c s fun s' => Q s' ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, by rw [VG.Proof.MlDsa.X86_64.KeyGen.MX, VG.Proof.MlDsa.X86_64.KeyGen.MX, Exec.mxcsr hc he]⟩

/-- Whether no instruction of `c` loads MXCSR. -/
def noLd (c : Prog isa) : Bool := c.allInstrs fun i => !loadsMxcsr i

theorem noLd_spec {c : Prog isa} (h : VG.Proof.MlDsa.X86_64.KeyGen.noLd c = true) : ∀ i ∈ VG.instrs c, loadsMxcsr i = false := by
  unfold VG.Proof.MlDsa.X86_64.KeyGen.noLd at h
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  exact fun i hi => by simpa using h i hi

/-- `WP.call`, which also keeps MXCSR's control bits, from the callee's `abiPreserved`. -/
theorem WP.callMx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem → VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameSp he hsp (by omega)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_rsp] at hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  let s₂ := s₁.withRegions s.rd s.wr
  have hs₂ : s₂ = s₁.withRegions s.rd s.wr := rfl
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp - 8 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .rsp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .rsp (s₂.gpr .rsp + 8)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_rsp], ?_⟩
    have := habi.2.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [hsp₂, State.callEntry_rsp]; exact this
  have hrsp : (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr .rsp = s.gpr .rsp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .rsp → (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_ habi.2.2
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩⟩
  · by_cases h : r = .rsp
    · subst h; exact hrsp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · have f₀ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega) (by omega))
    have f₁ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.callEntry.mem s₁.mem :=
      Frame.sub hf fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show 8 * (c.depth + 1) = 8 * c.depth + 8 by omega]
          exact below_callee _ _
    exact Frame.trans f₀ f₁

/-- `glueCall_ok`, keeping MXCSR's control bits. -/
theorem glueCallMx_ok {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) (hgl : ∀ i ∈ glue, loadsMxcsr i = false) {s : State}
    {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep MlKem.X86_64.argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => Post s s' wr ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep MlKem.X86_64.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono (WP.mx (c := .block glue) (by simpa [VG.instrs] using hgl) hg)
    fun s1 ⟨⟨⟨hV, hm⟩, k1⟩, hx1⟩ => ?_)
  refine WP.callMx hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf hx hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], ?_⟩, hx.trans hx1, s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Lay`. -/
section

/-!
# ML-DSA key generation on x86-64: its contract, parameters and buffers

The contract the proof is written against (`kgK p`, which the shared contract
implies), the facts about the parameter sets it uses (`PFacts`), the layout of
its buffers (`seed` in `rbp`; `scratch`, `pk` and `sk` in `rbx`, `r12` and
`r13`: `kgR`, `kgW p`), and the checks of pointers into them, for any
parameter set, which `lay` proves from the offsets by `omega`.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS oSV)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The contract -/

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- `vg_mldsa*_keygen(seed = rdi, pk = rsi, sk = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def kgK (p : Params) : Contract isa where
  pre s :=
    32 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, 32⟩] ∧ s.wr = [⟨s.gpr .rsi, p.pkLen⟩, ⟨s.gpr .rdx, p.skLen⟩, ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, p.pkLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, p.skLen⟩ ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + p.pkLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + VG.Proof.MlDsa.X86_64.KeyGen.scrLen p ≤ 2 ^ 64
  post s s' :=
    Spec.MlDsa.Outcome (fun b => Spec.MlDsa.keyGenInternal p b (bytesAt s.mem (s.gpr .rdi) 32))
      ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rsi) p.pkLen, bytesAt s'.mem (s.gpr .rdx) p.skLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    Spec.MlDsa.keyGenLeak p (bytesAt s₁.mem (s₁.gpr .rdi) 32) = Spec.MlDsa.keyGenLeak p (bytesAt s₂.mem (s₂.gpr .rdi) 32)

/-! ## The layout -/

/-- The pointers the function keeps. -/
abbrev kgM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]
/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.rbp, 32)]
/-- `scratch`, `pk` and `sk`. -/
abbrev kgW (p : Params) : List (Reg × Nat) := [(.rbx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p), (.r12, p.pkLen), (.r13, p.skLen)]
abbrev kgB (p : Params) : List (Reg × Nat) := VG.Proof.MlDsa.X86_64.KeyGen.kgR ++ VG.Proof.MlDsa.X86_64.KeyGen.kgW p

theorem kgB_bases (p : Params) : ∀ b ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgB p, b.1 ∈ bases := fun b hb => by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgB, VG.Proof.MlDsa.X86_64.KeyGen.kgR, VG.Proof.MlDsa.X86_64.KeyGen.kgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]
theorem kgM_bases : ∀ q ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgM, q.1 ∈ bases := by decide

theorem kgLay {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ s : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) (h : Top VG.Proof.MlDsa.X86_64.KeyGen.kgM σ s) :
    Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s := by
  obtain ⟨_, hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have hs : VG.Proof.MlDsa.X86_64.KeyGen.scrLen p < 2 ^ 32 := by
    have := hF.k; have := hF.l; have := hF.kl; simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, scratchWords]; omega
  have hpk : p.pkLen < 2 ^ 32 := by rw [hF.pk]; have := hF.k; omega
  have hsk : p.skLen < 2 ^ 32 := by
    rw [hF.sk]; have := hF.k; have := hF.l
    rcases hF.eta with ⟨_, he⟩ | ⟨_, he⟩ <;> simp only [oT0, he] <;> omega
  refine Lay.of (fa4 (by decide) hs hpk hsk) (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa4 ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, VG.Proof.MlKem.X86_64.retR]
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d5.symm
  · exact fun _ => d6.symm
  · exact fun _ => d4
  exacts [k1, k4, k2, k3, n1, n4, n2, n3,
    mem ⟨σ.gpr .rdi, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, p.pkLen⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, p.skLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

/-! ## Checks of pointers, by `omega` -/

theorem inB_rbp (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (.rbp, o) l = decide (o + l ≤ 32) := rfl
theorem inB_rbx (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (.rbx, o) l = decide (o + l ≤ VG.Proof.MlDsa.X86_64.KeyGen.scrLen p) := rfl
theorem inB_r12 (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (.r12, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_r13 (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (.r13, o) l = decide (o + l ≤ p.skLen) := rfl
theorem inB_rbxW (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (.rbx, o) l = decide (o + l ≤ VG.Proof.MlDsa.X86_64.KeyGen.scrLen p) := rfl
theorem inB_r12W (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (.r12, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_r13W (p : Params) (o l : Nat) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (.r13, o) l = decide (o + l ≤ p.skLen) := rfl

theorem sepB_same (bs : List (Reg × Nat)) (r : Reg) (o l o' l' : Nat) :
    sepB bs (r, o) l (r, o') l' = (inB bs (r, o) l && inB bs (r, o') l' && (decide (o + l ≤ o') || decide (o' + l' ≤ o))) := by
  simp [sepB]

theorem sepB_diff (bs : List (Reg × Nat)) {r r' : Reg} (h : r ≠ r') (hw : r ∈ wRegs ∨ r' ∈ wRegs) (o l o' l' : Nat) :
    sepB bs (r, o) l (r', o') l' = (inB bs (r, o) l && inB bs (r', o') l') := by
  have h1 : (r != r') = true := bne_iff_ne.mpr h
  have h2 : (r == r') = false := beq_eq_false_iff_ne.mpr h
  have h3 : (decide (r ∈ wRegs) || decide (r' ∈ wRegs)) = true := by simpa using hw
  simp only [sepB, h1, h2, h3, Bool.false_and, Bool.or_false, Bool.and_true]

/-- The pairs of distinct registers of the layout, one of them written. -/
theorem sepB_bx_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.rbp, o') l' = (inB bs (.rbx, o) l && inB bs (.rbp, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.rbx, o') l' = (inB bs (.rbp, o) l && inB bs (.rbx, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bx_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.r12, o') l' = (inB bs (.rbx, o) l && inB bs (.r12, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.rbx, o') l' = (inB bs (.r12, o) l && inB bs (.rbx, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bx_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.r13, o') l' = (inB bs (.rbx, o) l && inB bs (.r13, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.rbx, o') l' = (inB bs (.r13, o) l && inB bs (.rbx, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.r13, o') l' = (inB bs (.r12, o) l && inB bs (.r13, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.r12, o') l' = (inB bs (.r13, o) l && inB bs (.r12, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.r12, o') l' = (inB bs (.rbp, o) l && inB bs (.r12, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.rbp, o') l' = (inB bs (.r12, o) l && inB bs (.rbp, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.r13, o') l' = (inB bs (.rbp, o) l && inB bs (.r13, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.rbp, o') l' = (inB bs (.r13, o) l && inB bs (.rbp, o') l') :=
  VG.Proof.MlDsa.X86_64.KeyGen.sepB_diff bs (by decide) (by decide) o l o' l'

/-- Unfolds the checks of pointers into the layout into arithmetic, then
`omega` (in each case of `η`). -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlKem.X86_64.keepB, VG.Proof.MlDsa.X86_64.KeyGen.sepB_same,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_bp, VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_12, VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_12,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_12, VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_bp,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_bp,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_rbp, VG.Proof.MlDsa.X86_64.KeyGen.inB_rbx,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_r12, VG.Proof.MlDsa.X86_64.KeyGen.inB_r13,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_rbxW, VG.Proof.MlDsa.X86_64.KeyGen.inB_r12W,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_r13W, List.all_cons, List.all_nil,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, VG.Spec.MlDsa.scratchWords,
        VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlDsa.X86_64.KeyGen.oSA, VG.Impl.MlDsa.X86_64.KeyGen.oSB,
        VG.Impl.MlDsa.X86_64.KeyGen.oSA4, VG.Impl.MlDsa.X86_64.KeyGen.oR4,
        VG.Impl.MlDsa.X86_64.KeyGen.oHX, VG.Impl.MlDsa.X86_64.KeyGen.oKL, VG.Impl.MlKem.X86_64.oSS,
        VG.Impl.MlKem.X86_64.oSV, VG.Impl.MlDsa.X86_64.KeyGen.oT0, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call`. -/
section

/-!
# ML-DSA key generation on x86-64: calling the primitives

A call of a primitive (`primOk`, `primTr`), with the moves of its arguments
(`glue3_ok`, …): the callee's precondition on entry, from the layout (`ceD1`,
`ceD2`, `ceWf` for the stack, and the memory of the callee's entry,
`ce_polyAt`, …), and what its postcondition says once it returns.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS lea)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## The stack of a call -/

section
variable {p : Params} {s s1 : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) (hsp : s1.gpr .rsp = s.gpr .rsp)
include L hsp

theorem ceD1 {q : VG.Impl.MlKem.X86_64.Ptr} {l : Nat} (h : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) q l = true) :
    Region.Disjoint ⟨s1.gpr .rsp - 8, 8⟩ ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩ := by
  have := ret_disj s1 (R := ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩) (by rw [hsp]; exact L.stkD h)
  simpa [VG.Proof.MlKem.X86_64.retR] using this

theorem ceD2 {n : Nat} (hn : n + 1 ≤ 16) {q : VG.Impl.MlKem.X86_64.Ptr} {l : Nat} (h : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) q l = true) :
    Region.Disjoint ⟨s1.gpr .rsp - 8 - BitVec.ofNat 64 (n + 1), n + 1⟩ ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩ := by
  have := stk_disj s1 (R := ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩) (by rw [hsp]; exact L.stkD h)
  simp only [State.callEntry_rsp] at this
  exact this.sub_left (below_sub hn (by omega))

omit L in
theorem ceWf (h24 : 24 ≤ (s.gpr .rsp).toNat) {n : Nat} (hn : n + 1 ≤ 16) : n + 1 ≤ (s1.gpr .rsp - 8).toNat := by
  rw [hsp, BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := (s.gpr .rsp).isLt
  omega

omit L in
theorem ceWf24 (h32 : 32 ≤ (s.gpr .rsp).toNat) : 24 ≤ (s1.gpr .rsp - 8).toNat := by
  rw [hsp, BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := (s.gpr .rsp).isLt
  omega

theorem ceD24 {q : VG.Impl.MlKem.X86_64.Ptr} {l : Nat} (h : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) q l = true) :
    Region.Disjoint (below (s1.gpr .rsp - 8) 24) ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩ := by
  have := stk_disj24 s1 (R := ⟨VG.Proof.MlKem.X86_64.pa s q, l⟩) (by rw [hsp]; exact L.stkD h)
  simpa only [State.callEntry_rsp] using this

end

/-! ## The memory of a call's entry -/

section
variable {s1 : State}

/-- The memory a callee starts with. -/
abbrev ceM (s1 : State) : Mem := s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)

theorem ceM_bytes {q : Addr} (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, 1024⟩) :
    ∀ k < 1024, VG.Proof.MlDsa.X86_64.KeyGen.ceM s1 (q + BitVec.ofNat 64 k) = s1.mem (q + BitVec.ofNat 64 k) :=
  fun _ hk => callEntry_bytes s1 (R := ⟨q, 1024⟩) (k16 s1 h) (show 1024 ≤ 2 ^ 64 by decide) hk

theorem ce_polyAt {q : Addr} (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.polyAt (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) q = Spec.MlDsa.polyAt s1.mem q := Proof.MlDsa.KeyGen.polyAt_congr (VG.Proof.MlDsa.X86_64.KeyGen.ceM_bytes h)

theorem ce_natPolyAt {q : Addr} (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.natPolyAt (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) q = Spec.MlDsa.natPolyAt s1.mem q := Proof.MlDsa.KeyGen.natPolyAt_congr (VG.Proof.MlDsa.X86_64.KeyGen.ceM_bytes h)

theorem ce_coeffAt {q : Addr} (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, 1024⟩) {i : Nat} (hi : i < 256) :
    Spec.MlDsa.coeffAt (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) q i = Spec.MlDsa.coeffAt s1.mem q i :=
  Proof.MlDsa.KeyGen.coeffAt_congr (VG.Proof.MlDsa.X86_64.KeyGen.ceM_bytes h) hi

theorem ce_reduced {q : Addr} (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.Reduced (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) q ↔ Spec.MlDsa.Reduced s1.mem q :=
  ⟨Proof.MlDsa.KeyGen.reduced_congr fun k hk => (VG.Proof.MlDsa.X86_64.KeyGen.ceM_bytes h k hk).symm,
    Proof.MlDsa.KeyGen.reduced_congr (VG.Proof.MlDsa.X86_64.KeyGen.ceM_bytes h)⟩

theorem ce_bytesAt' {q : Addr} {n : Nat} (hn : n < 2 ^ 64) (h : (below (s1.gpr .rsp) 32).Disjoint ⟨q, n⟩) :
    bytesAt (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) q n = bytesAt s1.mem q n := callEntry_bytesAt s1 hn (k16 s1 h)

end

/-! ## A call -/

/-- A call of a primitive, from the moves of its arguments (`V`), its
precondition on entry and the regions it may read and write. -/
theorem primOk {c : Prog isa} {kk : Nat → Contract isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c kk) {glue : List Instr} {n : String}
    (hgl : ∀ i ∈ glue, loadsMxcsr i = false) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ stk ≤ 16, ∀ s1, V s1 → s1.mem = s.mem → Keep MlKem.X86_64.argRegs s s1 →
      (kk stk).pre (s1.callEntry.withRegions rd wr))
    (hcov : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => Post s s' wr ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      ∃ stk, stk ≤ 16 ∧ ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep MlKem.X86_64.argRegs s s1 ∧
        ∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
          (kk stk).post (s1.callEntry.withRegions rd wr) s₂ := by
  obtain ⟨stk, hs, hver⟩ := hc.verified
  exact WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.glueCallMx_ok hver.1 hc.nosp (Nat.le_succ_of_le hc.depth) hgl hg (hpre stk hs) hcov hw)
    fun s' ⟨h1, h2, h3⟩ => ⟨h1, h2, stk, hs, h3⟩

/-- A block of moves leaks nothing. -/
theorem moves_tr {glue : List Instr} (h : ∀ i ∈ glue, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block glue) fun _ _ => True := block_nomem_tr h

/-- Two calls of a primitive leak the same, if their preconditions and public data do. -/
theorem primTr {c : Prog isa} {kk : Nat → Contract isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c kk) {glue : List Instr} {n : String}
    (hnm : ∀ i ∈ glue, ∀ s, isa.addrs i s = []) {P : State → State → Prop} {V : State → State → Prop}
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ stk ≤ 16, ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (kk stk).pre (x1.callEntry.withRegions rd₁ wr₁) ∧ (kk stk).pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      (kk stk).pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True := by
  obtain ⟨stk, hs, hver⟩ := hc.verified
  exact glueCall_tr hver.1 hver.2.1 (VG.Proof.MlDsa.X86_64.KeyGen.moves_tr hnm) hg (hP stk hs)

/-! ## The moves of the arguments -/

/-- `d ← v`, a 32-bit immediate. -/
theorem imm_eq {v : Nat} (h : v < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v :=
  sw_ofNat h

theorem lea_noLd (d : Reg) (q : VG.Impl.MlKem.X86_64.Ptr) : ∀ i ∈ VG.Impl.MlKem.X86_64.lea d q, loadsMxcsr i = false := by
  intro i hi; simp only [VG.Impl.MlKem.X86_64.lea, List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl

theorem imm_noLd (d : Reg) (v : Nat) : ∀ i ∈ imm d v, loadsMxcsr i = false := by
  intro i hi; simp only [imm, List.mem_singleton] at hi; subst hi; rfl

theorem imm_nomem (d : Reg) (v : Nat) : ∀ i ∈ imm d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s; simp only [imm, List.mem_singleton] at hi; subst hi; rfl

theorem noLd_append {a b : List Instr} (ha : ∀ i ∈ a, loadsMxcsr i = false) (hb : ∀ i ∈ b, loadsMxcsr i = false) :
    ∀ i ∈ a ++ b, loadsMxcsr i = false := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h, hb i h]

/-- A pointer whose register no move of arguments writes. -/
structure PtrOk (q : VG.Impl.MlKem.X86_64.Ptr) : Prop where
  off : q.2 < 2 ^ 31
  na : q.1 ∉ MlKem.X86_64.argRegs

theorem PtrOk.ne {q : VG.Impl.MlKem.X86_64.Ptr} (h : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk q) {r : Reg} (hr : r ∈ MlKem.X86_64.argRegs) : q.1 ≠ r :=
  fun e => h.na (e ▸ hr)

theorem glue2_ok {a b : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (hb : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk b) (s : State) :
    WP isa (.block (VG.Impl.MlKem.X86_64.lea .rdi a ++ VG.Impl.MlKem.X86_64.lea .rsi b)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s b) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 :=
  accGlue_ok a b ha.off hb.off (hb.ne (by decide)) s

theorem glue3_ok {a b c : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (hb : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk b) (hc : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk c) (s : State) :
    WP isa (.block (VG.Impl.MlKem.X86_64.lea .rdi a ++ VG.Impl.MlKem.X86_64.lea .rsi b ++ VG.Impl.MlKem.X86_64.lea .rdx c)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s b ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s c) ∧ s1.mem = s.mem) ∧
        Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Impl.MlKem.X86_64.lea
  xrun [VG.Proof.MlKem.X86_64.sx_ofNat ha.off, VG.Proof.MlKem.X86_64.sx_ofNat hb.off, VG.Proof.MlKem.X86_64.sx_ofNat hc.off, hb.ne (r := .rdi) (by decide),
    hc.ne (r := .rdi) (by decide), hc.ne (r := .rsi) (by decide), List.cons_append, List.nil_append]

end VG.Proof.MlDsa.X86_64.KeyGen

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS lea)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem sc_ok (o : Nat) (h : o < 2 ^ 31) : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk (VG.Impl.MlKem.X86_64.sc o) := ⟨h, show Reg.rbx ∉ MlKem.X86_64.argRegs by decide⟩

/-- The region facts of a callee's precondition, from the layout. -/
syntax "cpre " term:max term:max term:max : tactic
macro_rules
  | `(tactic| cpre $L $hsp $h24) => `(tactic| (
      and_intros
      all_goals first
        | with_reducible exact True.intro
        | with_reducible exact ceWf $hsp $h24 (by omega)
        | with_reducible exact ceD1 $L $hsp (by with_reducible assumption)
        | with_reducible exact ceD2 $L $hsp (by omega) (by with_reducible assumption)
        | with_reducible exact Lay.disj $L (by with_reducible assumption)
        | with_reducible exact Lay.nwp $L (by with_reducible assumption)
        | skip))

theorem covers2 {s : State} {p : Params} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a b : VG.Impl.MlKem.X86_64.Ptr} {la lb : Nat}
    (ha : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a la = true) (hb : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) b lb = true) :
    Covers [⟨VG.Proof.MlKem.X86_64.pa s a, la⟩, ⟨VG.Proof.MlKem.X86_64.pa s b, lb⟩] s.wr := Covers.cons (L.cW ha) (Covers.cons (L.cW hb) Covers.nil)

/-- A state of the function, where a call can be made. -/
structure Site (p : Params) (s : State) : Prop where
  lay : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s
  h32 : 32 ≤ (s.gpr .rsp).toNat

theorem Site.h24 {p : Params} {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) : 24 ≤ (s.gpr .rsp).toNat := by have := S.h32; omega

/-- The registers that hold the pointers of the layout. -/
abbrev kgRegs : List Reg := [.rbx, .rbp, .r12, .r13]

/-- Two such states with the same pointers and stack pointer. -/
structure Two (p : Params) (x y : State) : Prop where
  sx : VG.Proof.MlDsa.X86_64.KeyGen.Site p x
  sy : VG.Proof.MlDsa.X86_64.KeyGen.Site p y
  regs : ∀ r ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs, x.gpr r = y.gpr r
  rsp : x.gpr .rsp = y.gpr .rsp

theorem Two.pa {p : Params} {x y : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.Two p x y) {q : VG.Impl.MlKem.X86_64.Ptr} (hq : q.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) : VG.Proof.MlKem.X86_64.pa x q = VG.Proof.MlKem.X86_64.pa y q := by
  simp only [VG.Proof.MlKem.X86_64.pa, h.regs _ hq]

/-- The registers the moves of arguments write keep the stack pointer. -/
theorem keep_rsp {s s1 : State} (k : Keep MlKem.X86_64.argRegs s s1) : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)

theorem inB_mono {p : Params} {q : VG.Impl.MlKem.X86_64.Ptr} {l : Nat} (h : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) q l = true) : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) q l = true := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  unfold inB
  rcases q with ⟨r, o⟩
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgW, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact decide_eq_true hl

/-! ## `NTT` and `NTT⁻¹` -/

section
variable {p : Params} {f : VG.Impl.MlKem.X86_64.Ptr} (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) f 1024 (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 1024 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) f 1024 = true) (w2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 1024 = true)

include h1 in
theorem ip_pre {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (red : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS))
    (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.inPlaceContract X86_64.abi t stk).pre
      (s1.callEntry.withRegions [] [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2]
    cpre L hsp S.h24
    exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ red)

include hf h1 w1 w2 in
theorem ipAt_ok {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {c : Prog isa} {n : String}
    (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.inPlaceContract X86_64.abi t stk) {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (red : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) :
    WP isa (.seq (.block (VG.Impl.MlKem.X86_64.lea .rdi f ++ VG.Impl.MlKem.X86_64.lea .rsi (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS))) (.call n c)) s fun s' =>
      Post s s' [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (t (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.glue2_ok hf (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) s)
    (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.ip_pre h1 hs S red hv hm k) (covers_nil_wr (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2)) (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hm₂] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hf h1 w1 w2 in
theorem ipAt_tr {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {c : Prog isa} {n : String}
    (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.inPlaceContract X86_64.abi t stk) (hb : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f))
      (.seq (.block (VG.Impl.MlKem.X86_64.lea .rdi f ++ VG.Impl.MlKem.X86_64.lea .rsi (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS))) (.call n c)) fun _ _ => True := by
  have g := fun s => VG.Proof.MlDsa.X86_64.KeyGen.glue2_ok hf (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) s
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨[], _, [], _, VG.Proof.MlDsa.X86_64.KeyGen.ip_pre h1 hs T.sx rx hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.ip_pre h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_nil_wr (VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2),
        by rw [k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact covers_nil_wr (VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2),
        by rw [k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hb, T.pa (q := VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) (by decide),
    and_self]

end

/-! ## Addition -/

section
variable {p : Params} {f g : VG.Impl.MlKem.X86_64.Ptr} (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (hg : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk g) (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) f 1024 g 1024 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) f 1024 = true)

include h1 in
theorem add_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g))
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s g) (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.addContract X86_64.abi stk).pre (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s g, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2]
    cpre L hsp S.h24
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rf)
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rg)

theorem covers_rw {s : State} {p : Params} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a b : VG.Impl.MlKem.X86_64.Ptr} {la lb : Nat}
    (ha : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a la = true) (hb : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) b lb = true) :
    Covers ([⟨VG.Proof.MlKem.X86_64.pa s a, la⟩] ++ [⟨VG.Proof.MlKem.X86_64.pa s b, lb⟩]) (s.rd ++ s.wr) :=
  Covers.append_left (Covers.cons (L.cR ha) Covers.nil) (Covers.cons (L.cR (VG.Proof.MlDsa.X86_64.KeyGen.inB_mono hb)) Covers.nil)

include hf hg h1 w1 in
theorem addAt_ok {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.addContract X86_64.abi stk) {s : State}
    (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.addAt sfx c f g) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (Spec.MlDsa.add (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f))
        (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.glue2_ok hf hg s)
    (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.add_pre h1 hs S rf rg hv hm k) (VG.Proof.MlDsa.X86_64.KeyGen.covers_rw L i2 w1)
    (Covers.cons (L.cW w1) Covers.nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2, hm₂] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i1), VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i2), hm] at hpost

include hf hg h1 w1 in
theorem addAt_tr {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.addContract X86_64.abi stk)
    (hbf : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbg : g.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧
      (Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (VG.Impl.MlDsa.X86_64.KeyGen.addAt sfx c f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.glue2_ok hf hg x, VG.Proof.MlDsa.X86_64.KeyGen.glue2_ok hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.add_pre h1 hs T.sx rx.1 rx.2 hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.add_pre h1 hs T.sy ry.1 ry.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sx.lay i2 w1,
        by rw [k1.2.2]; exact Covers.cons (T.sx.lay.cW w1) Covers.nil,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sy.lay i2 w1,
        by rw [k2.2.2]; exact Covers.cons (T.sy.lay.cW w1) Covers.nil, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hbf, T.pa hbg, and_self]

end

/-! ## `MultiplyNTT` -/

section
variable {p : Params} {h f g : VG.Impl.MlKem.X86_64.Ptr} (hh : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk h) (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (hg : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk g)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) h 1024 f 1024 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) h 1024 g 1024 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) h 1024 = true)

theorem covers_rrw {s : State} {p : Params} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a b c : VG.Impl.MlKem.X86_64.Ptr} {la lb lc : Nat}
    (ha : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a la = true) (hb : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) b lb = true) (hc : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) c lc = true) :
    Covers ([⟨VG.Proof.MlKem.X86_64.pa s a, la⟩, ⟨VG.Proof.MlKem.X86_64.pa s b, lb⟩] ++ [⟨VG.Proof.MlKem.X86_64.pa s c, lc⟩]) (s.rd ++ s.wr) :=
  Covers.append_left (Covers.cons (L.cR ha) (Covers.cons (L.cR hb) Covers.nil)) (Covers.cons (L.cR (VG.Proof.MlDsa.X86_64.KeyGen.inB_mono hc)) Covers.nil)

include h1 h2 in
theorem mul_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g))
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s h ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s g) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.mulContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s g, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s h, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rf)
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i3)).mpr (hm ▸ rg)

include hh hf hg h1 h2 w1 in
theorem mulAt_ok {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.mulContract X86_64.abi stk) {s : State}
    (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mulAt sfx c h f g) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s h, 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s h) (Spec.MlDsa.multiplyNTT (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg s) (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.mul_pre h1 h2 hs S rf rg hv hm k) (VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw L i2 i3 w1)
    (Covers.cons (L.cW w1) Covers.nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i2), VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i3), hm] at hpost

include hh hf hg h1 h2 w1 in
theorem mulAt_tr {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.mulContract X86_64.abi stk)
    (hbh : h.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbf : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbg : g.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧ (Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (VG.Impl.MlDsa.X86_64.KeyGen.mulAt sfx c h f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg x, VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.mul_pre h1 h2 hs T.sx rx.1 rx.2 hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.mul_pre h1 h2 hs T.sy ry.1 ry.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw T.sx.lay i2 i3 w1,
        by rw [k1.2.2]; exact Covers.cons (T.sx.lay.cW w1) Covers.nil,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw T.sy.lay i2 i3 w1,
        by rw [k2.2.2]; exact Covers.cons (T.sy.lay.cW w1) Covers.nil, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hbh, T.pa hbf,
    T.pa hbg, and_self]

end

/-! ## `AddNTT(h, MultiplyNTT(f, g))` -/

section
variable {p : Params} {h f g : VG.Impl.MlKem.X86_64.Ptr} (hh : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk h) (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (hg : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk g)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) h 1024 f 1024 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) h 1024 g 1024 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) h 1024 = true)

include h1 h2 in
theorem mulAdd_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (rh : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s h)) (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g))
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s h ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s g) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.mulAddContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s g, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s h, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rh)
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rf)
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i3)).mpr (hm ▸ rg)

include hh hf hg h1 h2 w1 in
theorem mulAddAt_ok {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk) {s : State}
    (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (rh : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s h)) (rf : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mulAddAt sfx c h f g) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s h, 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s h) (Spec.MlDsa.add (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s h)) (Spec.MlDsa.multiplyNTT (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g)))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg s) (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.mulAdd_pre h1 h2 hs S rh rf rg hv hm k) (VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw L i2 i3 w1)
    (Covers.cons (L.cW w1) Covers.nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i1), VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i2), VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i3), hm] at hpost

include hh hf hg h1 h2 w1 in
theorem mulAddAt_tr {sfx : String} {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk)
    (hbh : h.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbf : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbg : g.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x h) ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧ (Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y h) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (VG.Impl.MlDsa.X86_64.KeyGen.mulAddAt sfx c h f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg x, VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hh hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.mulAdd_pre h1 h2 hs T.sx rx.1 rx.2.1 rx.2.2 hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.mulAdd_pre h1 h2 hs T.sy ry.1 ry.2.1 ry.2.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw T.sx.lay i2 i3 w1,
        by rw [k1.2.2]; exact Covers.cons (T.sx.lay.cW w1) Covers.nil,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rrw T.sy.lay i2 i3 w1,
        by rw [k2.2.2]; exact Covers.cons (T.sy.lay.cW w1) Covers.nil, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hbh, T.pa hbf,
    T.pa hbg, and_self]

end

/-! ## `Power2Round` -/

section
variable {p : Params} {t t1 t0 : VG.Impl.MlKem.X86_64.Ptr} (ht : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk t) (ht1 : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk t1) (ht0 : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk t0)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) t 1024 t1 1024 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) t 1024 t0 1024 = true)
  (h3 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) t1 1024 t0 1024 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) t1 1024 = true) (w2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) t0 1024 = true)

theorem covers_rww {s : State} {p : Params} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a b c : VG.Impl.MlKem.X86_64.Ptr} {la lb lc : Nat}
    (ha : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a la = true) (hb : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) b lb = true) (hc : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) c lc = true) :
    Covers ([⟨VG.Proof.MlKem.X86_64.pa s a, la⟩] ++ [⟨VG.Proof.MlKem.X86_64.pa s b, lb⟩, ⟨VG.Proof.MlKem.X86_64.pa s c, lc⟩]) (s.rd ++ s.wr) :=
  Covers.append_left (Covers.cons (L.cR ha) Covers.nil)
    (Covers.cons (L.cR (VG.Proof.MlDsa.X86_64.KeyGen.inB_mono hb)) (Covers.cons (L.cR (VG.Proof.MlDsa.X86_64.KeyGen.inB_mono hc)) Covers.nil))

include h1 h2 h3 in
theorem p2r_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (rt : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s t))
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s t ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s t1 ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s t0) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.power2RoundContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s t, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s t1, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s t0, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rt)

include ht ht1 ht0 h1 h2 h3 w1 w2 in
theorem p2rAt_ok {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
    {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (rt : Spec.MlDsa.Reduced s.mem (VG.Proof.MlKem.X86_64.pa s t)) :
    WP isa (power2RoundAt c t t1 t0) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s t1, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s t0, 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      Spec.MlDsa.NatPolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s t1)
        ((Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s t)).map fun c => (Spec.MlDsa.power2Round c).1.toNat) ∧
      Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s t0)
        ((Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s t)).map fun c => Spec.MlDsa.ofInt (Spec.MlDsa.power2Round c).2) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok ht ht1 ht0 s) (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.p2r_pre h1 h2 h3 hs S rt hv hm k) (VG.Proof.MlDsa.X86_64.KeyGen.covers_rww L i1 w1 w2)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include ht ht1 ht0 h1 h2 h3 w1 w2 in
theorem p2rAt_tr {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
    (hbt : t.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hb1 : t1.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hb0 : t0.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Spec.MlDsa.Reduced x.mem (VG.Proof.MlKem.X86_64.pa x t) ∧ Spec.MlDsa.Reduced y.mem (VG.Proof.MlKem.X86_64.pa y t))
      (power2RoundAt c t t1 t0) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok ht ht1 ht0 x, VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok ht ht1 ht0 y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.p2r_pre h1 h2 h3 hs T.sx rx hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.p2r_pre h1 h2 h3 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2,
        by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hbt, T.pa hb1,
    T.pa hb0, and_self]

end

/-! ## `RejNTTPoly` -/

section
variable {p : Params} {sd a : VG.Impl.MlKem.X86_64.Ptr} (hsd : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk sd) (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) sd 34 a 1024 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) sd 34 (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)
  (h3 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a 1024 (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a 1024 = true) (w2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)

include h1 h2 h3 in
theorem rejNtt_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s sd ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS)) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.rejNTTContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s sd, 34⟩] [⟨VG.Proof.MlKem.X86_64.pa s a, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 2048⟩]) := by
  obtain ⟨_, _, _⟩ := sepB_spec h1
  obtain ⟨_, _, _⟩ := sepB_spec h3
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24

include hsd ha h1 h2 h3 w1 w2 in
theorem rejNttAt_ok {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
    {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.rejNttAt c sd a) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 2048⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Spec.MlDsa.Reduced s'.mem (VG.Proof.MlKem.X86_64.pa s a)) ∧
      Spec.MlDsa.Outcome (fun b => Spec.MlDsa.rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sd) 34))
        ((s'.gpr .rax).setWidth 32) (Spec.MlDsa.polyAt s'.mem (VG.Proof.MlKem.X86_64.pa s a)) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hsd ha (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) s) (fun stk hs s1 hv _ k => VG.Proof.MlDsa.X86_64.KeyGen.rejNtt_pre h1 h2 h3 hs S hv k)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers_rww L i1 w1 w2) (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, hg₂, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hm₂, hg₂ .rax (by decide)] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hsd ha h1 h2 h3 w1 w2 in
theorem rejNttAt_tr {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
    (hbs : sd.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hba : a.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x sd) 34 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y sd) 34)
      (VG.Impl.MlDsa.X86_64.KeyGen.rejNttAt c sd a) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok hsd ha (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) x
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, e⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.rejNtt_pre h1 h2 h3 hs T.sx hv1 k1, VG.Proof.MlDsa.X86_64.KeyGen.rejNtt_pre h1 h2 h3 hs T.sy hv2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2,
        by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, T.pa hbs, T.pa hba, T.pa (q := VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) (by decide),
    and_true]
  refine ⟨by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp], ?_⟩
  rw [T.pa hbs] at e
  rw [VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, ← T.pa hbs]; exact T.sx.lay.stkD i1),
    VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2]; exact T.sy.lay.stkD i1), hm1, hm2, e]

end

/-! ## `RejNTTPoly` four times -/

section
variable {p : Params} {a w : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (hw : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk w)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (VG.Impl.MlKem.X86_64.sc oSA4) 136 a 4096 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (VG.Impl.MlKem.X86_64.sc oSA4) 136 w 8192 = true)
  (h3 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a 4096 w 8192 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a 4096 = true) (w2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) w 8192 = true)

include h1 h2 h3 in
theorem rej4_pre {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4) ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s w)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4), 136⟩] [⟨VG.Proof.MlKem.X86_64.pa s a, 4096⟩, ⟨VG.Proof.MlKem.X86_64.pa s w, 8192⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h3
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_pre [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv.1, hv.2.1, hv.2.2]
  exact ⟨VG.Proof.MlDsa.X86_64.KeyGen.ceWf24 hsp S.h32, trivial, trivial, L.disj h1, L.disj h2, L.disj h3, VG.Proof.MlDsa.X86_64.KeyGen.ceD1 L hsp i1, VG.Proof.MlDsa.X86_64.KeyGen.ceD1 L hsp i2,
    VG.Proof.MlDsa.X86_64.KeyGen.ceD1 L hsp i3, VG.Proof.MlDsa.X86_64.KeyGen.ceD24 L hsp i1, VG.Proof.MlDsa.X86_64.KeyGen.ceD24 L hsp i2, VG.Proof.MlDsa.X86_64.KeyGen.ceD24 L hsp i3, L.nwp i1, L.nwp i2, L.nwp i3⟩

include ha hw h1 h2 h3 w1 w2 in
theorem rej4At_ok {c : Prog isa} {sfx : String} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee4 c) {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.rej4At c sfx a w) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 4096⟩, ⟨VG.Proof.MlKem.X86_64.pa s w, 8192⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Spec.MlDsa.Reduced s'.mem (Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s a) k)) ∧
      (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Spec.MlDsa.Bounds,
          Spec.MlDsa.rejNTTPoly b.rejNTT (Spec.MlDsa.seed4 s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) k) =
            some (Spec.MlDsa.polyAt s'.mem (Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s a) k))) ∨
        ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
          Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT (Spec.MlDsa.seed4 s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) k) = none)) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.glueCallMx_ok hc.verified.1 hc.nosp hc.depth
    (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok oSA4 (by decide)) ha hw s) (fun s1 hv _ k => VG.Proof.MlDsa.X86_64.KeyGen.rej4_pre h1 h2 h3 S hv k)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers_rww L i1 w1 w2) (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2))
    fun s' ⟨hP, hx, s1, hv, hm, k, s₂, hm₂, hg₂, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hm₂, hg₂ .rax (by decide)] at hpost
  have hseed : ∀ k < 4, Spec.MlDsa.seed4 (VG.Proof.MlDsa.X86_64.KeyGen.ceM s1) (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) k = Spec.MlDsa.seed4 s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) k :=
    fun k hk => by
      unfold Spec.MlDsa.seed4
      rw [← hm]
      refine Proof.MlKem.bytesAt_congr fun i hi => ?_
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact callEntry_bytes s1 (R := ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4), 136⟩) (k16 s1 (by rw [hsp]; exact L.stkD i1))
        (show 136 ≤ 2 ^ 64 by decide) (show 34 * k + i < 136 by omega)
  obtain ⟨hr, ho⟩ := hpost
  refine ⟨hr, ?_⟩
  rcases ho with ⟨h1', hb⟩ | ⟨h0, k, hk, hn⟩
  · exact .inl ⟨h1', fun k hk => by rw [← hseed k hk]; exact hb k hk⟩
  · exact .inr ⟨h0, k, hk, by rw [← hseed k hk]; exact hn⟩

include ha hw h1 h2 h3 w1 w2 in
theorem rej4At_tr {c : Prog isa} {sfx : String} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee4 c) (hba : a.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbw : w.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc oSA4)) 136 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc oSA4)) 136)
      (VG.Impl.MlDsa.X86_64.KeyGen.rej4At c sfx a w) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => VG.Proof.MlDsa.X86_64.KeyGen.glue3_ok (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok oSA4 (by decide)) ha hw x
  refine glueCall_tr hc.verified.1 hc.verified.2.1
    (VG.Proof.MlDsa.X86_64.KeyGen.moves_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y _ => ⟨g x, g y⟩)
    fun x y x1 y1 ⟨T, e⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.rej4_pre h1 h2 h3 T.sx hv1 k1, VG.Proof.MlDsa.X86_64.KeyGen.rej4_pre h1 h2 h3 T.sy hv2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2,
        by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, T.pa hba, T.pa hbw,
    T.pa (q := VG.Impl.MlKem.X86_64.sc oSA4) (by decide), and_true]
  refine ⟨by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp], ?_⟩
  rw [T.pa (q := VG.Impl.MlKem.X86_64.sc oSA4) (by decide)] at e
  rw [VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, ← T.pa (q := VG.Impl.MlKem.X86_64.sc oSA4) (by decide)]; exact T.sx.lay.stkD i1),
    VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2]; exact T.sy.lay.stkD i1), hm1, hm2, e]

end

/-! ## Moves with immediates -/

theorem w32_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem w64_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).toNat = v := by
  simp only [BitVec.toNat_ofNat]; omega

theorem glueRB_ok {a b c : VG.Impl.MlKem.X86_64.Ptr} (v : Nat) (hv : v < 2 ^ 32) (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (hb : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk b) (hc : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk c) (s : State) :
    WP isa (.block (VG.Impl.MlKem.X86_64.lea .rdi a ++ imm .rsi v ++ VG.Impl.MlKem.X86_64.lea .rdx b ++ VG.Impl.MlKem.X86_64.lea .rcx c)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 v ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s b ∧ s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s c) ∧
        s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Impl.MlKem.X86_64.lea imm
  xrun [VG.Proof.MlKem.X86_64.sx_ofNat ha.off, VG.Proof.MlKem.X86_64.sx_ofNat hb.off, VG.Proof.MlKem.X86_64.sx_ofNat hc.off, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hv, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), hc.ne (r := .rdi) (by decide), hc.ne (r := .rsi) (by decide),
    hc.ne (r := .rdx) (by decide), List.cons_append, List.nil_append]

theorem glueSB_ok {a b : VG.Impl.MlKem.X86_64.Ptr} (v w : Nat) (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (hb : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk b) (s : State) :
    WP isa (.block (VG.Impl.MlKem.X86_64.lea .rdi a ++ imm .rsi v ++ VG.Impl.MlKem.X86_64.lea .rdx b ++ imm .rcx w)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 v ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s b ∧
        s1.gpr .rcx = BitVec.ofNat 64 w) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Impl.MlKem.X86_64.lea imm
  xrun [VG.Proof.MlKem.X86_64.sx_ofNat ha.off, VG.Proof.MlKem.X86_64.sx_ofNat hb.off, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hv, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hw, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), List.cons_append, List.nil_append]

theorem glueBP_ok {a b : VG.Impl.MlKem.X86_64.Ptr} (u v w : Nat) (hu : u < 2 ^ 32) (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a)
    (hb : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk b) (s : State) :
    WP isa (.block (VG.Impl.MlKem.X86_64.lea .rdi a ++ imm .rsi u ++ imm .rdx v ++ VG.Impl.MlKem.X86_64.lea .rcx b ++ imm .r8 w)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 u ∧ s1.gpr .rdx = BitVec.ofNat 64 v ∧
        s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s b ∧ s1.gpr .r8 = BitVec.ofNat 64 w) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Impl.MlKem.X86_64.lea imm
  xrun [VG.Proof.MlKem.X86_64.sx_ofNat ha.off, VG.Proof.MlKem.X86_64.sx_ofNat hb.off, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hu, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hv, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hw, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), hb.ne (r := .rdx) (by decide), List.cons_append, List.nil_append]

/-! ## `RejBoundedPoly` -/

section
variable {p : Params} {sd a : VG.Impl.MlKem.X86_64.Ptr} {eta : Nat} (heta : eta = 2 ∨ eta = 4) (hsd : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk sd) (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) sd 66 a 1024 = true) (h2 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) sd 66 (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)
  (h3 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) a 1024 (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)
  (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a 1024 = true) (w2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) 2048 = true)

theorem eta_lt (heta : eta = 2 ∨ eta = 4) : eta < 2 ^ 32 := by omega

include heta h1 h2 h3 in
theorem rejB_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s sd ∧ s1.gpr .rsi = BitVec.ofNat 64 eta ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s a ∧
      s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS)) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.rejBoundedContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s sd, 66⟩] [⟨VG.Proof.MlKem.X86_64.pa s a, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 2048⟩]) := by
  obtain ⟨_, _, _⟩ := sepB_spec h1
  obtain ⟨_, _, _⟩ := sepB_spec h3
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (eta_lt heta)]
    cpre L hsp S.h24
    exact heta

include heta hsd ha h1 h2 h3 w1 w2 in
theorem rejBAt_ok {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
    {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) :
    WP isa (rejBoundedAt c sd eta a) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 1024⟩, ⟨VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS), 2048⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Spec.MlDsa.Reduced s'.mem (VG.Proof.MlKem.X86_64.pa s a)) ∧
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.rejBoundedPoly eta b.rejBounded (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sd) 66)).map
        Spec.MlDsa.toRq) ((s'.gpr .rax).setWidth 32) (Spec.MlDsa.polyAt s'.mem (VG.Proof.MlKem.X86_64.pa s a)) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
      (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glueRB_ok eta (eta_lt heta) hsd ha (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) s) (fun stk hs s1 hv _ k => VG.Proof.MlDsa.X86_64.KeyGen.rejB_pre heta h1 h2 h3 hs S hv k)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers_rww L i1 w1 w2) (VG.Proof.MlDsa.X86_64.KeyGen.covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, hg₂, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hm₂, hg₂ .rax (by decide), VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (eta_lt heta)] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [hsp]; exact L.stkD i1), hm] at hpost

include heta hsd ha h1 h2 h3 w1 w2 in
theorem rejBAt_tr {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
    (hbs : sd.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hba : a.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Spec.MlDsa.rejBoundedLeak eta (bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x sd) 66) =
      Spec.MlDsa.rejBoundedLeak eta (bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y sd) 66)) (rejBoundedAt c sd eta a) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => VG.Proof.MlDsa.X86_64.KeyGen.glueRB_ok eta (eta_lt heta) hsd ha (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok VG.Impl.MlKem.X86_64.oSS (by decide)) x
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _)) (lea_nomem _ _))
      (lea_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, e⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.rejB_pre heta h1 h2 h3 hs T.sx hv1 k1, VG.Proof.MlDsa.X86_64.KeyGen.rejB_pre heta h1 h2 h3 hs T.sy hv2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers2 T.sy.lay w1 w2,
        by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, T.pa hbs, T.pa hba,
    T.pa (q := VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS) (by decide), VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (eta_lt heta), and_true]
  refine ⟨by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp], ?_⟩
  rw [T.pa hbs] at e
  rw [VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, ← T.pa hbs]; exact T.sx.lay.stkD i1),
    VG.Proof.MlDsa.X86_64.KeyGen.ce_bytesAt' (by decide) (by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2]; exact T.sy.lay.stkD i1), hm1, hm2, e]

end

/-! ## `SimpleBitPack` -/

section
variable {p : Params} {f out : VG.Impl.MlKem.X86_64.Ptr} {b len : Nat} (hb : b ∈ Spec.MlDsa.simpleBitPackBounds)
  (hl : len = 32 * Spec.MlDsa.bitlen b) (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (ho : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk out)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) f 1024 out len = true) (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) out len = true)

theorem sbp_lt (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) : b < 2 ^ 32 := by
  simp only [Spec.MlDsa.simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbpLen_lt (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) (hl : len = 32 * Spec.MlDsa.bitlen b) : len < 2 ^ 32 := by
  simp only [Spec.MlDsa.simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> subst hl <;> decide

include hb hl h1 in
theorem sbp_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s)
    (hbd : ∀ i < 256, (Spec.MlDsa.coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s f) i).toNat ≤ b)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 b ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s out ∧
      s1.gpr .rcx = BitVec.ofNat 64 len) (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.simpleBitPackContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s out, len⟩]) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.sbp_lt hb), VG.Proof.MlDsa.X86_64.KeyGen.w64_toNat (VG.Proof.MlDsa.X86_64.KeyGen.sbpLen_lt hb hl)]
    cpre L hsp S.h24
    · exact hb
    · exact hl
    · intro i hi
      rw [VG.Proof.MlDsa.X86_64.KeyGen.ce_coeffAt (by rw [hsp]; exact L.stkD i1) hi, hm]
      exact hbd i hi

include hb hl hf ho h1 w1 in
theorem sbpAt_ok {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
    {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (hbd : ∀ i < 256, (Spec.MlDsa.coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s f) i).toNat ≤ b) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.simpleBitPackAt c f b out len) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s out, len⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) len = Spec.MlDsa.simpleBitPack (Spec.MlDsa.natPolyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) b := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _))
      (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glueSB_ok b len (VG.Proof.MlDsa.X86_64.KeyGen.sbp_lt hb) (VG.Proof.MlDsa.X86_64.KeyGen.sbpLen_lt hb hl) hf ho s) (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.sbp_pre hb hl h1 hs S hbd hv hm k)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers_rw L i1 w1) (Covers.cons (L.cW w1) Covers.nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hm₂, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.sbp_lt hb), VG.Proof.MlDsa.X86_64.KeyGen.w64_toNat (VG.Proof.MlDsa.X86_64.KeyGen.sbpLen_lt hb hl)] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_natPolyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hb hl hf ho h1 w1 in
theorem sbpAt_tr {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
    (hbf : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbo : out.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (∀ i < 256, (Spec.MlDsa.coeffAt x.mem (VG.Proof.MlKem.X86_64.pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (Spec.MlDsa.coeffAt y.mem (VG.Proof.MlKem.X86_64.pa y f) i).toNat ≤ b)) (VG.Impl.MlDsa.X86_64.KeyGen.simpleBitPackAt c f b out len) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => VG.Proof.MlDsa.X86_64.KeyGen.glueSB_ok b len (VG.Proof.MlDsa.X86_64.KeyGen.sbp_lt hb) (VG.Proof.MlDsa.X86_64.KeyGen.sbpLen_lt hb hl) hf ho x
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _)) (lea_nomem _ _))
      (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.sbp_pre hb hl h1 hs T.sx rx hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.sbp_pre hb hl h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sx.lay i1 w1,
        by rw [k1.2.2]; exact Covers.cons (T.sx.lay.cW w1) Covers.nil,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sy.lay i1 w1,
        by rw [k2.2.2]; exact Covers.cons (T.sy.lay.cW w1) Covers.nil, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2,
    T.rsp, T.pa hbf, T.pa hbo, and_self]

end

/-! ## `BitPack` -/

section
variable {p : Params} {f out : VG.Impl.MlKem.X86_64.Ptr} {a b len : Nat} (hab : (a, b) ∈ Spec.MlDsa.bitPackParams)
  (hl : len = 32 * Spec.MlDsa.bitlen (a + b)) (hf : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk f) (ho : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk out)
  (h1 : sepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) f 1024 out len = true) (w1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) out len = true)

/-- The coefficients a `BitPack` to `(a, b)` packs. -/
def PackIn (m : Mem) (q : Addr) (a b : Nat) : Prop :=
  Spec.MlDsa.Reduced m q ∧ ∀ i < 256, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt m q i).toNat Spec.MlDsa.q ∧
    Spec.MlDsa.modPm (Spec.MlDsa.coeffAt m q i).toNat Spec.MlDsa.q ≤ b

theorem bp_lt (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) : a < 2 ^ 32 ∧ b < 2 ^ 32 := by
  simp only [Spec.MlDsa.bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpLen_lt (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hl : len = 32 * Spec.MlDsa.bitlen (a + b)) :
    len < 2 ^ 32 := by
  simp only [Spec.MlDsa.bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> subst hl <;> decide

include hab hl h1 in
theorem bp_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (hin : VG.Proof.MlDsa.X86_64.KeyGen.PackIn s.mem (VG.Proof.MlKem.X86_64.pa s f) a b)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 a ∧ s1.gpr .rdx = BitVec.ofNat 64 b ∧
      s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s out ∧ s1.gpr .r8 = BitVec.ofNat 64 len) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.bitPackContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩] [⟨VG.Proof.MlKem.X86_64.pa s out, len⟩]) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  have hk : (below (s1.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s f, 1024⟩ := by rw [hsp]; exact L.stkD i1
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).1, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).2,
      VG.Proof.MlDsa.X86_64.KeyGen.w64_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bpLen_lt hab hl)]
    cpre L hsp S.h24
    · exact hab
    · exact hl
    · exact (VG.Proof.MlDsa.X86_64.KeyGen.ce_reduced hk).mpr (hm ▸ hin.1)
    · intro i hi
      rw [VG.Proof.MlDsa.X86_64.KeyGen.ce_coeffAt hk hi, hm]
      exact hin.2 i hi

include hab hl hf ho h1 w1 in
theorem bpAt_ok {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)
    {s : State} (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p s) (hin : VG.Proof.MlDsa.X86_64.KeyGen.PackIn s.mem (VG.Proof.MlKem.X86_64.pa s f) a b) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.bitPackAt c f a b out len) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s out, len⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) len = Spec.MlDsa.bitPack ((Spec.MlDsa.polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)).map
        fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) a b := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.primOk hc (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.noLd_append (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _))
      (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.lea_noLd _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.imm_noLd _ _))
    (VG.Proof.MlDsa.X86_64.KeyGen.glueBP_ok a b len (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).1 (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).2 (VG.Proof.MlDsa.X86_64.KeyGen.bpLen_lt hab hl) hf ho s)
    (fun stk hs s1 hv hm k => VG.Proof.MlDsa.X86_64.KeyGen.bp_pre hab hl h1 hs S hin hv hm k)
    (VG.Proof.MlDsa.X86_64.KeyGen.covers_rw L i1 w1) (Covers.cons (L.cW w1) Covers.nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k
  sig_post [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hm₂, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).1, VG.Proof.MlDsa.X86_64.KeyGen.w32_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).2,
    VG.Proof.MlDsa.X86_64.KeyGen.w64_toNat (VG.Proof.MlDsa.X86_64.KeyGen.bpLen_lt hab hl)] at hpost
  rwa [VG.Proof.MlDsa.X86_64.KeyGen.ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hab hl hf ho h1 w1 in
theorem bpAt_tr {c : Prog isa} (hc : VG.Proof.MlDsa.X86_64.KeyGen.Callee c fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)
    (hbf : f.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) (hbo : out.1 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ VG.Proof.MlDsa.X86_64.KeyGen.PackIn x.mem (VG.Proof.MlKem.X86_64.pa x f) a b ∧ VG.Proof.MlDsa.X86_64.KeyGen.PackIn y.mem (VG.Proof.MlKem.X86_64.pa y f) a b)
      (VG.Impl.MlDsa.X86_64.KeyGen.bitPackAt c f a b out len) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => VG.Proof.MlDsa.X86_64.KeyGen.glueBP_ok a b len (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).1 (VG.Proof.MlDsa.X86_64.KeyGen.bp_lt hab).2 (VG.Proof.MlDsa.X86_64.KeyGen.bpLen_lt hab hl) hf ho x
  refine VG.Proof.MlDsa.X86_64.KeyGen.primTr hc (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _))
      (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _)) (lea_nomem _ _)) (VG.Proof.MlDsa.X86_64.KeyGen.imm_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.KeyGen.bp_pre hab hl h1 hs T.sx rx hv1 hm1 k1, VG.Proof.MlDsa.X86_64.KeyGen.bp_pre hab hl h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sx.lay i1 w1,
        by rw [k1.2.2]; exact Covers.cons (T.sx.lay.cW w1) Covers.nil,
        by rw [k2.2.1, k2.2.2]; exact VG.Proof.MlDsa.X86_64.KeyGen.covers_rw T.sy.lay i1 w1,
        by rw [k2.2.2]; exact Covers.cons (T.sy.lay.cW w1) Covers.nil, by rw [VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2,
    VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k1, VG.Proof.MlDsa.X86_64.KeyGen.keep_rsp k2, T.rsp, T.pa hbf, T.pa hbo, and_self]

end

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Mask`. -/
section

/-!
# ML-DSA key generation on x86-64: masking a sampled polynomial

After each sampler, `mask a` ANDs its result (0 or 1, in `eax`) into `r15`,
and each coefficient of the polynomial at `a` with `-eax`: the polynomial is
kept if the sampler succeeded, and zeroed if it failed (`mask_ok`), without a
branch (`mask_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc lea at_)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params coeffAt)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {N i j : Nat} (hN : N ≤ 2 ^ 20) (hi : i < N) (hj : j < N)
    (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-! ## One coefficient -/

abbrev maskBody : List Instr := [.mov32 .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rdi 0)), .alu32 .and .rax (.reg .r8),
  .store32 (VG.Impl.MlKem.X86_64.at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (h1 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block VG.Proof.MlDsa.X86_64.KeyGen.maskBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rdi) 32 &&& (s.gpr .r8).setWidth 32) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

/-! ## The polynomial -/

/-- The coefficients after masking with the 32 bits `r`, 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    x &&& (BitVec.setWidth 64 (0 - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [VG.Proof.MlKem.X86_64.ifp rfl, show (BitVec.setWidth 64 (0 - (1 : BitVec 32))).setWidth 32 = BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

abbrev maskPre (a : VG.Impl.MlKem.X86_64.Ptr) (N : Nat) : List Instr :=
  [.alu32 .and .r15 (.reg .rax), .mov32 .r8 (.imm 0), .alu32 .sub .r8 (.reg .rax)] ++ VG.Impl.MlKem.X86_64.lea .rdi a ++ imm .rcx N

theorem maskPre_ok {a : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (h15 : a.1 ≠ .r15) {N : Nat} (hN : N < 2 ^ 32) (s : State) :
    WP isa (.block (VG.Proof.MlDsa.X86_64.KeyGen.maskPre a N)) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
        s'.gpr .r8 = BitVec.setWidth 64 (0 - (s.gpr .rax).setWidth 32) ∧ s'.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a ∧
        s'.gpr .rcx = BitVec.ofNat 64 N) ∧ Keep [.r15, .r8, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Proof.MlDsa.X86_64.KeyGen.maskPre VG.Impl.MlKem.X86_64.lea imm
  xrun [VG.Proof.MlKem.X86_64.sx_ofNat ha.off, VG.Proof.MlDsa.X86_64.KeyGen.imm_eq hN, h15, ha.ne (r := .r8) (by decide),
    ha.ne (r := .rdi) (by decide), List.cons_append, List.nil_append]

theorem maskN_ok {p : Params} {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (ha15 : a.1 ≠ .r15)
    {N : Nat} (hN0 : 0 < N) (hN : N ≤ 2 ^ 20) (w : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a (4 * N) = true)
    (hr : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mask a N) s fun s' => PostB s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 4 * N⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
      ∀ i < N, coeffAt s'.mem (VG.Proof.MlKem.X86_64.pa s a) i =
        if (s.gpr .rax).setWidth 32 = 1 then coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s a) i else 0 := by
  have hW : InRegions s.wr (VG.Proof.MlKem.X86_64.pa s a) (4 * N) := L.cW w _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hn : (VG.Proof.MlKem.X86_64.pa s a).toNat + 4 * N ≤ 2 ^ 64 := L.nwp (VG.Proof.MlDsa.X86_64.KeyGen.inB_mono w)
  refine WP.mono (WP.mx (c := VG.Impl.MlDsa.X86_64.KeyGen.mask a N) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (Q := fun s' => PostB s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 4 * N⟩] ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
      ∀ i < N, coeffAt s'.mem (VG.Proof.MlKem.X86_64.pa s a) i =
        if (s.gpr .rax).setWidth 32 = 1 then coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s a) i else 0) ?_)
    fun s' ⟨⟨hP, h15, hc⟩, hx⟩ => ⟨hP, hx, h15, hc⟩
  unfold VG.Impl.MlDsa.X86_64.KeyGen.mask
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.maskPre_ok ha ha15 (N := N) (by omega) s) fun s1 ⟨⟨hm1, h15, h8, hdi, hcx⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := N) (by omega) hN0 (fun i s' =>
      s'.gpr .rdi = VG.Proof.MlKem.X86_64.pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .r8 = s1.gpr .r8 ∧ s'.gpr .r15 = s1.gpr .r15 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨VG.Proof.MlKem.X86_64.pa s a, 4 * N⟩] s.mem s'.mem ∧
      (∀ j < N, coeffAt s'.mem (VG.Proof.MlKem.X86_64.pa s a) j =
        if j < i then coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s a) j &&& (s1.gpr .r8).setWidth 32 else coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s a) j) ∧
      Keep [.r15, .r8, .rdi, .rcx, .rax] s s')
    (fun i hi s' ⟨hdi', h8', h15', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi, add_ofNat_zero], rfl, rfl, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j _ => by rw [VG.Proof.MlKem.X86_64.ifn (Nat.not_lt_zero j), hm1], k1.mono (by decide)⟩ hcx)
    fun s' ⟨_, h8', h15', hrd', hwr', hf, hc, kk⟩ => ⟨⟨hrd', hwr', fun r hr => kk.gpr ?_, kk.gpr (by decide),
      hf.mono fun _ hr => List.mem_append_left _ hr⟩, ?_, ?_⟩
  · have hc4 : (⟨VG.Proof.MlKem.X86_64.pa s a, 4 * N⟩ : Region).Contains (VG.Proof.MlKem.X86_64.pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      contains_offset' (by omega) (by omega)
    have hin : InRegions s'.wr (s'.gpr .rdi) 4 := by
      rw [hwr', hdi']; exact inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .rdi) 4 :=
      let ⟨r, hr, hc⟩ := hin; ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.maskBody_ok s' hin0 hin)
      fun s'' ⟨⟨hm, hdi'', hcx'', hz⟩, k'⟩ => ⟨⟨?_, by rw [k'.gpr (by decide), h8'],
        by rw [k'.gpr (by decide), h15'], k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_,
        (kk.trans k').mono (by decide)⟩, hcx'', hz⟩
    · rw [hdi'', hdi', show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, VG.Proof.MlKem.X86_64.off_add]; rfl
    · rw [hm, hdi']; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, hdi', VG.Proof.MlDsa.X86_64.KeyGen.coeffAt_writeW32 _ _ hN hj (by omega), h8']
      by_cases e : i = j
      · subst e
        rw [VG.Proof.MlKem.X86_64.ifp rfl, VG.Proof.MlKem.X86_64.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [VG.Proof.MlKem.X86_64.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [VG.Proof.MlKem.X86_64.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [VG.Proof.MlKem.X86_64.ifp hji, VG.Proof.MlKem.X86_64.ifp (by omega)]
        · rw [VG.Proof.MlKem.X86_64.ifn hji, VG.Proof.MlKem.X86_64.ifn (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, bases] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [h15', h15]
  · intro j hj
    rw [hc j hj, VG.Proof.MlKem.X86_64.ifp hj, h8, VG.Proof.MlDsa.X86_64.KeyGen.and_mask hr]
theorem mask_ok {p : Params} {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a : VG.Impl.MlKem.X86_64.Ptr} (ha : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk a) (ha15 : a.1 ≠ .r15)
    (w : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) a 1024 = true) (hr : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mask a) s fun s' => PostB s s' [⟨VG.Proof.MlKem.X86_64.pa s a, 1024⟩] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧
      ∀ i < 256, coeffAt s'.mem (VG.Proof.MlKem.X86_64.pa s a) i =
        if (s.gpr .rax).setWidth 32 = 1 then coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s a) i else 0 :=
  VG.Proof.MlDsa.X86_64.KeyGen.maskN_ok L ha ha15 (N := 256) (by decide) (by decide) w hr

/-! ## Constant time -/

/-- The check is the same for every offset: its hint is computed once, for offset 0. -/
theorem mask_taint : ∀ j < 128, (taint.check (X86_64.Taint.ofRegs [.rbx]) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP j)))
    (VG.Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc 0)))).isSome = true := by decide +kernel

theorem mask_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP j))) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (VG.Proof.MlDsa.X86_64.KeyGen.mask_taint j hj)

/-- The same for the four polynomials from `oP j`. -/
theorem mask4_taint : ∀ j < 128, (taint.check (X86_64.Taint.ofRegs [.rbx]) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP j)) 1024)
    (VG.Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc 0) 1024))).isSome = true := by decide +kernel

theorem mask4_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP j)) 1024) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (VG.Proof.MlDsa.X86_64.KeyGen.mask4_taint j hj)

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inv`. -/
section

/-!
# ML-DSA key generation on x86-64: what holds throughout, and pieces

What holds of the state throughout (`KC`: `Top`, the seed `ξ` at `seed`, and
MXCSR's control bits), and a piece of code (`Piece p I J c`): it takes each
run from `I` to `J` (`ok`), and two runs related by `I` leak the same (`tr`).
Pieces compose (`Piece.seq`, `Piece.seqR`), which proves correctness and
constant time together.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ)).2.2

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  top : Top VG.Proof.MlDsa.X86_64.KeyGen.kgM σ s
  xi : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.rbp, 0)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ
  mx : VG.Proof.MlDsa.X86_64.KeyGen.MX s = VG.Proof.MlDsa.X86_64.KeyGen.MX σ

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (p : Params) (ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)) : Bool := topChk (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.rbp, 0) 32

/-- A piece that writes `ws` keeps `K1`. -/
def k1Chk (p : Params) (ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ws && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc oHX) 128 && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc oSA) 32 && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) 64 &&
    keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65)) 1 && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * 0)) 32 &&
    keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * 1)) 32 && keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * 2)) 32 &&
    keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * 3)) 32

section
variable {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
include hF hp

theorem KC.lay {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s) : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s := VG.Proof.MlDsa.X86_64.KeyGen.kgLay hF hp h.top

theorem KC.site {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s) : VG.Proof.MlDsa.X86_64.KeyGen.Site p s := ⟨h.lay hF hp, by rw [h.top.rsp]; exact hp.1⟩

theorem KC.step {s s' : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s) {ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (hP : PPostB s s' ws) (hx : VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s)
    (hc : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ws = true) : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.kcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP VG.Proof.MlDsa.X86_64.KeyGen.kgM_bases hc.1, by rw [L.keepBytes hP hc.2]; exact h.xi, hx.trans h.mx⟩

end

theorem kc_two {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ₁ σ₂ x y : State} (p₁ : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ₁) (p₂ : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ₂)
    (pub : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub σ₁ σ₂) (h₁ : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ₁ x) (h₂ : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ₂ y) : VG.Proof.MlDsa.X86_64.KeyGen.Two p x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.site hF p₁, h₂.site hF p₂, fun r hr => ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

/-! ## Pieces -/

/-- Two runs of the function, from entry states that satisfy the
precondition and agree on the public data, each related by `I` to its
entry state. -/
abbrev R (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (p : Params) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p I) c fun _ _ => True

section
variable {p : Params} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : VG.Proof.MlDsa.X86_64.KeyGen.Piece p I J c₁) (h₂ : VG.Proof.MlDsa.X86_64.KeyGen.Piece p J K c₂) : VG.Proof.MlDsa.X86_64.KeyGen.Piece p I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : VG.Proof.MlDsa.X86_64.KeyGen.Piece p I J c)
    (hI : ∀ σ s, (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ → I' σ s → I σ s) (hJ : ∀ σ s, (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ → J σ s → J' σ s) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → VG.Proof.MlDsa.X86_64.KeyGen.Piece p (I k) (I (k + 1)) (f k)) →
      VG.Proof.MlDsa.X86_64.KeyGen.Piece p (I a) (I (a + n)) (VG.Impl.MlKem.X86_64.seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (R := fun k => VG.Proof.MlDsa.X86_64.KeyGen.R p (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ₁ → (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ₂ → (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.X86_64.KeyGen

namespace VG.Proof.MlDsa.X86_64.KeyGen

/-- `lay`, which also unfolds the checks of pieces (`kcChk`, `copyChk`, `hashChk`, …). -/
syntax "layk" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| layk) => `(tactic| layk [])
  | `(tactic| layk [$ls,*]) => `(tactic| lay [VG.Proof.MlDsa.X86_64.KeyGen.kcChk, VG.Proof.MlDsa.X86_64.KeyGen.k1Chk, VG.Proof.MlKem.X86_64.topChk, VG.Proof.MlKem.X86_64.copyChk,
      VG.Proof.MlKem.X86_64.hashChk, VG.Proof.MlKem.X86_64.pieceChk, VG.Proof.MlKem.X86_64.kabsChk,
      VG.Proof.MlKem.X86_64.ksqzChk, VG.Proof.MlKem.X86_64.kChk, VG.Proof.MlKem.X86_64.rdOk,
      VG.Proof.MlKem.X86_64.wrOk, List.range_succ, List.range_zero, List.all_append, List.nil_append,
      List.all_cons, List.all_nil, VG.Impl.MlKem.X86_64.oSV, $ls,*])


section
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params)

theorem keepB_append {bs : List (Reg × Nat)} {ws₁ ws₂ : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} {q : VG.Impl.MlKem.X86_64.Ptr} {l : Nat}
    (h₁ : keepB bs ws₁ q l = true) (h₂ : keepB bs ws₂ q l = true) : keepB bs (ws₁ ++ ws₂) q l = true := by
  simp only [keepB, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

theorem kcChk_append {p : Params} {ws₁ ws₂ : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ws₁ = true)
    (h₂ : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ws₂ = true) : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p (ws₁ ++ ws₂) = true := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.kcChk, topChk, List.all_append, Bool.and_eq_true, List.all_eq_true] at *
  exact ⟨⟨fun k hk => VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.1.1 k hk) (h₂.1.1 k hk), h₁.1.2, h₂.1.2⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append h₁.2 h₂.2⟩

theorem k1Chk_append {p : Params} {ws₁ ws₂ : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p ws₁ = true)
    (h₂ : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p ws₂ = true) : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p (ws₁ ++ ws₂) = true := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.k1Chk, Bool.and_eq_true] at *
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a₁, b₁⟩, c₁⟩, d₁⟩, e₁⟩, f₁⟩, g₁⟩, h₁⟩, i₁⟩ := h₁
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a₂, b₂⟩, c₂⟩, d₂⟩, e₂⟩, f₂⟩, g₂⟩, h₂⟩, i₂⟩ := h₂
  exact ⟨⟨⟨⟨⟨⟨⟨⟨VG.Proof.MlDsa.X86_64.KeyGen.kcChk_append a₁ a₂, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append b₁ b₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append c₁ c₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append d₁ d₂⟩,
    VG.Proof.MlDsa.X86_64.KeyGen.keepB_append e₁ e₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append f₁ f₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append g₁ g₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append h₁ h₂⟩, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append i₁ i₂⟩

/-- `k1Chk` of a write to `scratch` from `oSS` on, proved once for any region. -/
theorem k1Chk_rbx {p : Params} {o n : Nat} (h1 : VG.Impl.MlKem.X86_64.oSS ≤ o) (h2 : o + n ≤ VG.Proof.MlDsa.X86_64.KeyGen.scrLen p) :
    VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [((.rbx, o), n)] = true := by
  simp only [VG.Impl.MlKem.X86_64.oSS] at h1
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords] at h2
  layk

end

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Seeds`. -/
section

/-!
# ML-DSA key generation on x86-64: the prologue and the seeds

The prologue saves the callee-saved registers and keeps the pointers
(`pro_piece`); then `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed
of `RejNTTPoly` and `ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`,
`K1`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB copy hashAt topPro at_)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs in the layout -/

theorem Two.lrel {p : Params} {x y : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.Two p x y) : LRel VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) x y :=
  ⟨h.sx.lay, h.sy.lay, fun b hb => h.regs _ (by
    simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgR, VG.Proof.MlDsa.X86_64.KeyGen.kgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [VG.Proof.MlDsa.X86_64.KeyGen.kgRegs]), h.rsp⟩

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem Two.step {p : Params} {c : Prog isa} (htr : RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.Two p) c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlDsa.X86_64.KeyGen.Site p x → WP isa c x fun x' => ∃ W, PostB x x' W) : RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.Two p) c (VG.Proof.MlDsa.X86_64.KeyGen.Two p) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) (fun x y h => ⟨hok x h.sx, hok y h.sy⟩)
    fun x y x' y' h ⟨_, hx⟩ ⟨_, hy⟩ => ⟨⟨h.sx.lay.post hx (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p), by rw [hx.rsp]; exact h.sx.h32⟩,
      ⟨h.sy.lay.post hy (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p), by rw [hy.rsp]; exact h.sy.h32⟩,
      fun r hr => by
        have hb : r ∈ bases := by simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
                                  rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [hx.bs r hb, hy.bs r hb]; exact h.regs r hr, by rw [hx.rsp, hy.rsp]; exact h.rsp⟩

theorem two_rbx {p : Params} {x y : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.Two p x y) : ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.regs .rbx (by decide)

/-! ## Pieces with the sponge, a byte or a copy -/

section
variable {p : Params} {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s)
include L

theorem setB_okM {q : VG.Impl.MlKem.X86_64.Ptr} {v : Nat} (hr : q.1 ≠ .rax) (hv : v < 256) (hc : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) q 1 = true) :
    WP isa (.block (VG.Impl.MlKem.X86_64.setB q v)) s fun s' => (PPost s s' [(q, 1)] ∧ bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s q) 1 = [BitVec.ofNat 8 v]) ∧
      VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s :=
  WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (setB_okL L hr hv hc)

theorem copy_okM {dst src : VG.Impl.MlKem.X86_64.Ptr} {n : Nat} (hsr : src.1 ≠ .rdi) (hc : copyChk (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) dst src n = true) :
    WP isa (VG.Impl.MlKem.X86_64.copy dst src n) s fun s' => (PPost s s' [(dst, n)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s dst) n = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s src) n) ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s :=
  WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (copy_okL L hsr hc)

end

theorem absorb_noLd : VG.Proof.MlDsa.X86_64.KeyGen.noLd Impl.Sha3.X86_64.Stream.absorb = true := by decide +kernel
theorem pad_noLd : VG.Proof.MlDsa.X86_64.KeyGen.noLd Impl.Sha3.X86_64.Stream.pad = true := by decide +kernel
theorem squeeze_noLd : VG.Proof.MlDsa.X86_64.KeyGen.noLd Impl.Sha3.X86_64.Stream.squeeze = true := by decide +kernel

theorem noLd_seq {a b : Prog isa} (ha : VG.Proof.MlDsa.X86_64.KeyGen.noLd a = true) (hb : VG.Proof.MlDsa.X86_64.KeyGen.noLd b = true) : VG.Proof.MlDsa.X86_64.KeyGen.noLd (.seq a b) = true := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.noLd, Code.allInstrs] at ha hb ⊢; rw [ha, hb]; rfl

theorem noLd_call {n : String} {b : Prog isa} (hb : VG.Proof.MlDsa.X86_64.KeyGen.noLd b = true) : VG.Proof.MlDsa.X86_64.KeyGen.noLd (.call n b) = true := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.noLd, Code.allInstrs] at hb ⊢; exact hb

theorem absAll_noLd (rate : Nat) : ∀ (ps : List (VG.Impl.MlKem.X86_64.Ptr × Nat)) (pos : Nat), VG.Proof.MlDsa.X86_64.KeyGen.noLd (VG.Impl.MlKem.X86_64.absAll rate ps pos) = true
  | [], _ => rfl
  | _ :: ps, _ => VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (by rfl) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_call VG.Proof.MlDsa.X86_64.KeyGen.absorb_noLd)) (VG.Proof.MlDsa.X86_64.KeyGen.absAll_noLd rate ps _)

theorem hash_noLd (ps : List (VG.Impl.MlKem.X86_64.Ptr × Nat)) (rate suffix : Nat) (out : VG.Impl.MlKem.X86_64.Ptr) (len : Nat) :
    VG.Proof.MlDsa.X86_64.KeyGen.noLd (hashAt ps rate suffix out len) = true :=
  VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (by rfl) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (VG.Proof.MlDsa.X86_64.KeyGen.absAll_noLd rate ps 0) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (by rfl) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_call VG.Proof.MlDsa.X86_64.KeyGen.pad_noLd))
    (VG.Proof.MlDsa.X86_64.KeyGen.noLd_seq (by rfl) (VG.Proof.MlDsa.X86_64.KeyGen.noLd_call VG.Proof.MlDsa.X86_64.KeyGen.squeeze_noLd))))

theorem hash_okM {p : Params} {ps : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} {rate suffix : Nat} {out : VG.Impl.MlKem.X86_64.Ptr} {len : Nat}
    (hc : hashChk (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) ps rate out len = true) (hsuf : suffix < 256) {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) :
    WP isa (hashAt ps rate suffix out len) s fun s' => (PPost s s' [(VG.Impl.MlKem.X86_64.sc 0, 200), (VG.Impl.MlKem.X86_64.sc 200, 640), (out, len)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) len =
        Spec.Sha3.squeezeFrom rate (Proof.MlKem.padded rate (BitVec.ofNat 8 suffix) (pieces s ps)) 0 len) ∧
      VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s :=
  WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (VG.Proof.MlDsa.X86_64.KeyGen.hash_noLd ps rate suffix out len)) (hash_ok (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p) hc hsuf L)

/-! ## The prologue -/

theorem pro_eq : VG.Impl.MlDsa.X86_64.KeyGen.pro = [.store (VG.Impl.MlKem.X86_64.at_ .rcx 840) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .rcx 848) .rbp, .store (VG.Impl.MlKem.X86_64.at_ .rcx 856) .r12,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 864) .r13, .store (VG.Impl.MlKem.X86_64.at_ .rcx 872) .r14, .store (VG.Impl.MlKem.X86_64.at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) :
    WP isa (.block VG.Impl.MlDsa.X86_64.KeyGen.pro) σ fun s => VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨_, hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hS : ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have hs : 888 ≤ VG.Proof.MlDsa.X86_64.KeyGen.scrLen p := by have := hF.k; simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords]; omega
  have hs2 : VG.Proof.MlDsa.X86_64.KeyGen.scrLen p < 2 ^ 64 := by
    have := hF.k; have := hF.l; have := hF.kl; simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords]; omega
  have c : ∀ o, o + 8 ≤ 888 → (⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' (by omega) (by omega)
  have w : ∀ o, o + 8 ≤ 888 → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlDsa.X86_64.KeyGen.pro_eq]
  refine WP.mono (WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (WP.keep [.rbx, .rbp, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide))) fun s ⟨⟨⟨hm, hbx, hbp, h12, h13, h15⟩, k⟩, hx⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h12 h13, fun j hj => ?_, ?_⟩, ?_, hx⟩
  · simp only [VG.Proof.MlKem.X86_64.pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [VG.Proof.MlKem.X86_64.pa, hbp, add_ofNat_zero]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using d3) (by decide)

theorem pro_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => s = σ) (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s ∧ s.gpr .r15 = 1) (.block VG.Impl.MlDsa.X86_64.KeyGen.pro) :=
  ⟨fun σ s hp hs => by subst hs; exact VG.Proof.MlDsa.X86_64.KeyGen.pro_ok hF hp,
    taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂
      exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)⟩

/-! ## The seeds -/

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte := Spec.MlDsa.H (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds, with `ρ` copied to the first `j` seeds of `oSA4`. -/
structure K1R (p : Params) (j : Nat) (σ s : State) : Prop where
  kc : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s
  hx : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oHX)) 128 = VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ
  sa : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ
  sb : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 64 = VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ
  z : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65))) 1 = [0]
  sa4 : ∀ k < j, bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * k))) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ

/-- After the seeds. -/
abbrev K1 (p : Params) (σ s : State) : Prop := VG.Proof.MlDsa.X86_64.KeyGen.K1R p 4 σ s

theorem K1.step {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {s s' : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s)
    {ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (hP : PPostB s s' ws) (hx : VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s) (hc : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p ws = true) : VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s' := by
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, a0⟩, a1⟩, a2⟩, a3⟩ := hc
  have L := h.kc.lay hF hp
  refine ⟨h.kc.step hF hp hP hx h0, by rw [L.keepBytes hP h1]; exact h.hx, by rw [L.keepBytes hP h2]; exact h.sa,
    by rw [L.keepBytes hP h3]; exact h.sb, by rw [L.keepBytes hP h4]; exact h.z, fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [L.keepBytes hP a0]; exact h.sa4 0 hk
  · rw [L.keepBytes hP a1]; exact h.sa4 1 hk
  · rw [L.keepBytes hP a2]; exact h.sa4 2 hk
  · rw [L.keepBytes hP a3]; exact h.sa4 3 hk

theorem shake31' : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem hx_eq (p : Params) (σ : State) :
    VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ = Spec.Sha3.squeezeFrom 136 (Proof.MlKem.padded 136 (BitVec.ofNat 8 31)
      (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ]))) 0 128 := by
  rw [VG.Proof.MlDsa.X86_64.KeyGen.hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, VG.Proof.MlDsa.X86_64.KeyGen.shake31',
    List.append_assoc, ← Proof.MlKem.shake256_eq]; rfl

theorem rho_eq (p : Params) (σ : State) : VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ = (VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ = ((VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ = ((VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ).drop 96).take 32 := rfl

/-- Two bytes, at `scratch + o` and `scratch + o + 1`. -/
theorem setTwo_ok {p : Params} {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {o a b : Nat} (ha : a < 256) (hb : b < 256)
    (h1 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (VG.Impl.MlKem.X86_64.sc o) 1 = true) (h2 : inB (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) (VG.Impl.MlKem.X86_64.sc (o + 1)) 1 = true)
    (hk : keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) [(VG.Impl.MlKem.X86_64.sc (o + 1), 1)] (VG.Impl.MlKem.X86_64.sc o) 1 = true) :
    WP isa (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc o) a ++ VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (o + 1)) b)) s fun s' =>
      PPost s s' [(VG.Impl.MlKem.X86_64.sc o, 1), (VG.Impl.MlKem.X86_64.sc (o + 1), 1)] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  have hr : Reg.rbx ≠ .rax := by decide
  have hc : ∀ w ∈ [(VG.Impl.MlKem.X86_64.sc (o + 1), 1)], w.1.1 ∈ calleeSaved := fun w hw => by
    rw [List.mem_singleton] at hw; subst hw; exact rbx_cs
  refine WP.block_append (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setB_okM L (q := VG.Impl.MlKem.X86_64.sc o) (v := a) hr ha h1)
    fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setB_okM (L.post hP₁.b (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)) (q := VG.Impl.MlKem.X86_64.sc (o + 1)) (v := b)
      hr hb h2) fun s₂ ⟨⟨hP₂, hb₂⟩, hx₂⟩ => ⟨PPost.app hP₁ hP₂ hc, hx₂.trans hx₁, ?_⟩)
  have L₁ := L.post hP₁.b (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  have e1 : VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc o) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc o) := hP₁.pa rbx_cs
  have k1 := L₁.keepBytes hP₂.b hk
  rw [hP₂.pa rbx_cs, e1] at k1
  have e : VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc o) + BitVec.ofNat 64 1 = VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc (o + 1)) := by rw [hP₁.pa rbx_cs]; exact VG.Proof.MlKem.X86_64.off_add _ _ _
  rw [show 2 = 1 + 1 from rfl, Proof.MlKem.bytesAt_add, k1, hb₁, e, hb₂]
  rfl

theorem setKL_ok {p : Params} {s : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    WP isa (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc oKL) a ++ VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oKL + 1)) b)) s fun s' =>
      PPost s s' [(VG.Impl.MlKem.X86_64.sc oKL, 1), (VG.Impl.MlKem.X86_64.sc (oKL + 1), 1)] ∧ VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oKL)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] :=
  VG.Proof.MlDsa.X86_64.KeyGen.setTwo_ok L ha hb (by lay) (by lay) (by lay)

/-- `ρ` to seed `j` of `oSA4`. -/
theorem copyR_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {j : Nat} (hj : j < 4) {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.K1R p j σ s) :
    WP isa (VG.Impl.MlKem.X86_64.copy (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * j)) (VG.Impl.MlKem.X86_64.sc oHX) 32) s fun s' => VG.Proof.MlDsa.X86_64.KeyGen.K1R p (j + 1) σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  have hk := hF.k; have hl := hF.l
  have L := h.kc.lay hF hp
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L (dst := VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * j)) (src := VG.Impl.MlKem.X86_64.sc oHX) (n := 32) (by decide) (by layk))
    fun s' ⟨⟨hP, hb⟩, hx⟩ => ⟨⟨h.kc.step hF hp hP.b hx (by layk), by rw [L.keepBytes hP.b (by layk)]; exact h.hx,
      by rw [L.keepBytes hP.b (by layk)]; exact h.sa, by rw [L.keepBytes hP.b (by layk)]; exact h.sb,
      by rw [L.keepBytes hP.b (by layk)]; exact h.z, fun k hk' => ?_⟩, hP.cs .r15 (by decide)⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP.b (by layk)]; exact h.sa4 k hk'
  · rw [hP.pa rbx_cs, hb, ← Proof.MlKem.bytesAt_take s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oHX)) (show 32 ≤ 128 by decide), h.hx, ← VG.Proof.MlDsa.X86_64.KeyGen.rho_eq]

theorem seeds_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (VG.Impl.MlDsa.X86_64.KeyGen.seeds p) s fun s' => VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s' ∧ s'.gpr .r15 = 1 := by
  have hk := hF.k; have hl := hF.l
  have L := h.lay hF hp
  unfold VG.Impl.MlDsa.X86_64.KeyGen.seeds
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setKL_ok L (a := p.k) (b := p.ℓ) (by omega) (by omega)) fun s₁ ⟨hP₁, hx₁, hb₁⟩ => ?_)
  have h₁ := h.step hF hp hP₁.b hx₁ (by layk)
  have L₁ := h₁.lay hF hp
  have e₁ : ∀ o, VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc o) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc o) := fun o => hP₁.pa rbx_cs
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.hash_okM (ps := [((.rbp, 0), 32), (VG.Impl.MlKem.X86_64.sc oKL, 2)]) (rate := 136) (suffix := 31)
    (out := VG.Impl.MlKem.X86_64.sc oHX) (len := 128) (by layk) (by decide) L₁) fun s₂ ⟨⟨hP₂, ho₂⟩, hx₂⟩ => ?_)
  have h₂ := h₁.step hF hp hP₂.b hx₂ (by layk)
  have L₂ := h₂.lay hF hp
  have e₂ : ∀ o, VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlKem.X86_64.sc o) = VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc o) := fun o => hP₂.pa rbx_cs
  have hpc : pieces s₁ [((.rbp, 0), 32), (VG.Impl.MlKem.X86_64.sc oKL, 2)] = VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ]) := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.xi, e₁, hb₁]; rfl
  rw [hpc, ← VG.Proof.MlDsa.X86_64.KeyGen.hx_eq, ← e₂] at ho₂
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L₂ (dst := VG.Impl.MlKem.X86_64.sc oSA) (src := VG.Impl.MlKem.X86_64.sc oHX) (n := 32) (by decide) (by layk))
    fun s₃ ⟨⟨hP₃, hb₃⟩, hx₃⟩ => ?_)
  have h₃ := h₂.step hF hp hP₃.b hx₃ (by layk)
  have L₃ := h₃.lay hF hp
  have e₃ : ∀ o, VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlKem.X86_64.sc o) = VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlKem.X86_64.sc o) := fun o => hP₃.pa rbx_cs
  have hx3 : bytesAt s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlKem.X86_64.sc oHX)) 128 = VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ := by rw [L₂.keepBytes hP₃.b (by layk)]; exact ho₂
  rw [← Proof.MlKem.bytesAt_take s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlKem.X86_64.sc oHX)) (show 32 ≤ 128 by decide), ho₂, ← VG.Proof.MlDsa.X86_64.KeyGen.rho_eq, ← e₃] at hb₃
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L₃ (dst := VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) (src := VG.Impl.MlKem.X86_64.sc (oHX + 32)) (n := 64) (by decide) (by layk))
    fun s₄ ⟨⟨hP₄, hb₄⟩, hx₄⟩ => ?_)
  have h₄ := h₃.step hF hp hP₄.b hx₄ (by layk)
  have L₄ := h₄.lay hF hp
  have e₄ : ∀ o, VG.Proof.MlKem.X86_64.pa s₄ (VG.Impl.MlKem.X86_64.sc o) = VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlKem.X86_64.sc o) := fun o => hP₄.pa rbx_cs
  have hsb : bytesAt s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlKem.X86_64.sc (oHX + 32))) 64 = VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ := by
    rw [VG.Proof.MlDsa.X86_64.KeyGen.rho'_eq, ← hx3, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide), VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.off_add]
  rw [hsb, ← e₄] at hb₄
  refine WP.seq (WP.mono (WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (setB_okL L₄ (p := VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65)) (v := 0) (by decide)
    (by decide) (by lay))) fun s₅ ⟨⟨hP₅, hb₅⟩, hx₅⟩ => ?_)
  have h₅ : VG.Proof.MlDsa.X86_64.KeyGen.K1R p 0 σ s₅ := ⟨h₄.step hF hp hP₅.b hx₅ (by layk),
    by rw [L₄.keepBytes hP₅.b (by layk), L₃.keepBytes hP₄.b (by layk)]; exact hx3,
    by rw [L₄.keepBytes hP₅.b (by layk), L₃.keepBytes hP₄.b (by layk)]; exact hb₃,
    by rw [L₄.keepBytes hP₅.b (by layk)]; exact hb₄, by rw [hP₅.pa rbx_cs]; exact hb₅,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have f₅ : s₅.gpr .r15 = 1 := by
    rw [hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h15]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copyR_ok hF hp (j := 0) (by decide) h₅) fun s₆ ⟨h₆, f₆⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copyR_ok hF hp (j := 1) (by decide) h₆) fun s₇ ⟨h₇, f₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copyR_ok hF hp (j := 2) (by decide) h₇) fun s₈ ⟨h₈, f₈⟩ => ?_)
  exact WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copyR_ok hF hp (j := 3) (by decide) h₈) fun s₉ ⟨h₉, f₉⟩ =>
    ⟨h₉, by rw [f₉, f₈, f₇, f₆, f₅]⟩

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc oKL) v ++ VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_tr {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.Two p) (VG.Impl.MlDsa.X86_64.KeyGen.seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  unfold VG.Impl.MlDsa.X86_64.KeyGen.seeds
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h) (VG.Proof.MlDsa.X86_64.KeyGen.setKL_taint p.k (by omega) p.ℓ (by omega)))
    fun x S => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setKL_ok S.lay (a := p.k) (b := p.ℓ) (by omega) (by omega)) fun _ h => ⟨_, h.1.b⟩) ?_
  refine RelCT.seq (Two.step (RelCT.mono (hash_tr (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p) (ps := [((.rbp, 0), 32), (VG.Impl.MlKem.X86_64.sc oKL, 2)]) (rate := 136)
      (suffix := 31) (out := VG.Impl.MlKem.X86_64.sc oHX) (len := 128) (by layk) (by decide)) (fun _ _ h => h.lrel) fun _ _ h => h)
    fun x S => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.hash_okM (ps := [((.rbp, 0), 32), (VG.Impl.MlKem.X86_64.sc oKL, 2)]) (rate := 136) (suffix := 31)
      (out := VG.Impl.MlKem.X86_64.sc oHX) (len := 128) (by layk) (by decide) S.lay) fun _ h => ⟨_, h.1.1.b⟩) ?_
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h) (by taint_decide))
    fun x S => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM S.lay (dst := VG.Impl.MlKem.X86_64.sc oSA) (src := VG.Impl.MlKem.X86_64.sc oHX) (n := 32) (by decide) (by layk))
      fun _ h => ⟨_, h.1.1.b⟩) ?_
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h) (by taint_decide))
    fun x S => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM S.lay (dst := VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) (src := VG.Impl.MlKem.X86_64.sc (oHX + 32)) (n := 64) (by decide) (by layk))
      fun _ h => ⟨_, h.1.1.b⟩) ?_
  exact taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h) (by taint_decide)

theorem seeds_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s ∧ s.gpr .r15 = 1) (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s ∧ s.gpr .r15 = 1) (VG.Impl.MlDsa.X86_64.KeyGen.seeds p) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.seeds_ok hF hp h.1 h.2,
    VG.Proof.MlDsa.X86_64.KeyGen.rel_of (VG.Proof.MlDsa.X86_64.KeyGen.seeds_tr hF) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp`. -/
section

/-!
# ML-DSA key generation on x86-64: the samplers

The entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the
first `e` entries of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is
reduced (and those of `s₁ ‖ s₂` small), and `r15` is 1 if every sampler
succeeded, with the polynomials those of the standard for some bounds, or 0 if
key generation fails within the least bounds (`Good`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly
  keyGenInternal toRq polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Bounds.Le bmax)
open VG.Spec.Sha3 (bytesAt)

/-! ## Polynomials kept by a piece -/

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (hP : PPostB s s' ws)
  {q : VG.Impl.MlKem.X86_64.Ptr} (hc : keepB (rbs ++ wbs) ws q 1024 = true)
include L hP hc

theorem polyAt_frame' : polyAt s'.mem (VG.Proof.MlKem.X86_64.pa s' q) = polyAt s.mem (VG.Proof.MlKem.X86_64.pa s q) := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.polyAt_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this)

theorem polyIs_frame' {f : Poly} (h : PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s q) f) : PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s' q) f := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.polyIs_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this) h

theorem reduced_frame' (h : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s q)) : Reduced s'.mem (VG.Proof.MlKem.X86_64.pa s' q) := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.reduced_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this) h

end

/-! ## What the samplers leave -/

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

/-- `r15` after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1 if they
are those of the standard, `A` and `S`, for some bounds; 0 if key generation
fails within the least bounds. -/
def Good (p : Params) (σ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 64) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ) = none)

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.sP p r')) (toRq (S r')) ∧ VG.Proof.MlDsa.X86_64.KeyGen.Small p.η (S r')) ∧ VG.Proof.MlDsa.X86_64.KeyGen.Good p σ e r A S (s.gpr .r15)

theorem KSamp.keep {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {e r : Nat} {s s' : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e r s) {ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (hP : PPostB s s' ws) (hx : VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s)
    (hc : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p ws = true) (ha : ∀ e' < e, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlDsa.X86_64.KeyGen.aP e') 1024 = true)
    (hs : ∀ r' < r, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlDsa.X86_64.KeyGen.sP p r') 1024 = true) (h15 : s'.gpr .r15 = s.gpr .r15) :
    VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e r s' := by
  have L := h.k1.kc.lay hF hp
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.step hF hp hP hx hc, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h15]; exact hG⟩
  · exact VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (ha e' he') (hA e' he')
  · exact ⟨VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hs r' hr') (hS r' hr').1, (hS r' hr').2⟩

/-! ## A masked polynomial -/

theorem polyAt_coeff {m m' : Mem} {q : Addr} (h : ∀ i < 256, coeffAt m' q i = coeffAt m q i) :
    polyAt m' q = polyAt m q :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, h i hi]

/-- Kept if the sampler succeeded. -/
theorem masked_one {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r = 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    polyAt m' q = polyAt m q ∧ (Reduced m q → Reduced m' q) := by
  have h' : ∀ i < 256, coeffAt m' q i = coeffAt m q i := fun i hi => by rw [h i hi, ifp hr]
  exact ⟨VG.Proof.MlDsa.X86_64.KeyGen.polyAt_coeff h', fun hq i hi => by rw [h' i hi]; exact hq i hi⟩

/-- Zero if it failed. -/
theorem masked_zero {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r ≠ 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (toRq (Vector.replicate 256 0)) := by
  have h' : ∀ i < 256, coeffAt m' q i = 0 := fun i hi => by rw [h i hi, ifn hr]
  refine ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩
  simp only [polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
  rfl

theorem small_zero (η : Nat) : VG.Proof.MlDsa.X86_64.KeyGen.Small η (Vector.replicate 256 0) := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

theorem outcome_01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α}
    (h : Spec.MlDsa.Outcome f r out) : r = 0 ∨ r = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem r15_and {v : BitVec 64} (hv : v = 0 ∨ v = 1) {r : BitVec 32} (hr : r = 0 ∨ r = 1) :
    BitVec.setWidth 64 (v.setWidth 32 &&& r) = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

theorem good_01 {p : Params} {σ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 64}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.Good p σ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem sc1_bases (o n : Nat) : ∀ w ∈ [(VG.Impl.MlKem.X86_64.sc o, n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; exact rbx_bases

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) :
    seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

theorem k1_aP {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {e : Nat} (he : e < p.k * p.ℓ) : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [(VG.Impl.MlDsa.X86_64.KeyGen.aP e, 1024)] = true := by
  have := hF.k; have := hF.l
  exact VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_rbx (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem k1_sP {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [(VG.Impl.MlDsa.X86_64.KeyGen.sP p r, 1024)] = true := by
  have := hF.k; have := hF.l
  exact VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_rbx (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem k1_ss {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [(VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 2048)] = true := by
  have := hF.k; have := hF.l
  exact VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_rbx (Nat.le_refl _) (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlKem.X86_64.oSS]; omega)

theorem expA_ok {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
    {e : Nat} (he : e < p.k * p.ℓ) {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e 0 s) : WP isa (expA P p e) s (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by omega) (by omega)
    (by lay) (by lay) (by lay)) fun s₁ ⟨hP₁, hx₁, hb₁⟩ => ?_)
  have h₁ : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e 0 s₁ := by
    refine h.keep hF hp hP₁.b hx₁ ?_ (fun e' he' => ?_) (fun _ h => absurd h (Nat.not_lt_zero _))
      (hP₁.cs .r15 (by decide))
    · layk
    · layk
  have S₁ := h₁.k1.kc.site hF hp
  have hseed : bytesAt s₁.mem (VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc oSA)) 34 = seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, h₁.k1.sa,
      show VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc oSA) + BitVec.ofNat 64 32 = VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc (oSA + 32)) from VG.Proof.MlKem.X86_64.off_add _ _ _, hP₁.pa rbx_cs, hb₁,
      VG.Proof.MlDsa.X86_64.KeyGen.seedA_eq]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rejNttAt_ok (sd := VG.Impl.MlKem.X86_64.sc oSA) (a := VG.Impl.MlDsa.X86_64.KeyGen.aP e) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt S₁) fun s₂ ⟨hP₂, hx₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have hP₂' : PPostB s₁ s₂ [(VG.Impl.MlDsa.X86_64.KeyGen.aP e, 1024), (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 2048)] := hP₂.b
  have L₂ := S₁.lay.post hP₂'  (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  have hr01 := VG.Proof.MlDsa.X86_64.KeyGen.outcome_01 hout
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mask_ok L₂ (a := VG.Impl.MlDsa.X86_64.KeyGen.aP e) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (show Reg.rbx ≠ .r15 by decide) (by lay) hr01)
    fun s₃ ⟨hP₃, hx₃, h15, hco⟩ => ?_
  have hP₃' : PPostB s₂ s₃ [(VG.Impl.MlDsa.X86_64.KeyGen.aP e, 1024)] := hP₃
  have hP₁₃ := PPostB.app hP₂' hP₃' (VG.Proof.MlDsa.X86_64.KeyGen.sc1_bases _ _)
  have L₁ := S₁.lay
  have e₂ : VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlDsa.X86_64.KeyGen.aP e) = VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlDsa.X86_64.KeyGen.aP e) := hP₂'.pa rbx_bases
  have e₃ : VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.aP e) = VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlDsa.X86_64.KeyGen.aP e) := hP₃'.pa rbx_bases
  rw [e₂] at hco
  obtain ⟨A, S, hA, _, hG⟩ := h₁.ex
  have h15₂ : s₂.gpr .r15 = s₁.gpr .r15 := hP₂.cs .r15 (by decide)
  rw [h15₂, VG.Proof.MlDsa.X86_64.KeyGen.r15_and (VG.Proof.MlDsa.X86_64.KeyGen.good_01 hG) hr01] at h15
  refine ⟨h₁.k1.step hF hp hP₁₃ (hx₃.trans hx₂)
    (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_, _]) (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_]) (VG.Proof.MlDsa.X86_64.KeyGen.k1_aP hF he) (VG.Proof.MlDsa.X86_64.KeyGen.k1_ss hF)) (VG.Proof.MlDsa.X86_64.KeyGen.k1_aP hF he)),
    fun e' => if e' = e then polyAt s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.aP e))
    else A e', S, fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]
      exact VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L₁ hP₁₃ (by layk) (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rw [e₃, e₂]
      by_cases h1 : (s₂.gpr .rax).setWidth 32 = 1
      · exact (VG.Proof.MlDsa.X86_64.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (VG.Proof.MlDsa.X86_64.KeyGen.masked_zero h1 hco).1
  · rw [h15]
    have hq' : e = p.ℓ * (e / p.ℓ) + e % p.ℓ := (Nat.div_add_mod e p.ℓ).symm
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e ∨ e' = e) with he' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, e₃, e₂, (VG.Proof.MlDsa.X86_64.KeyGen.masked_one ho hco).1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

/-! ## Constant time -/

theorem rho_pub {p : Params} {σ₁ σ₂ : State} (pub : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub σ₁ σ₂) : VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ₁ = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

theorem rej_pub {p : Params} {σ₁ σ₂ : State} (pub : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

theorem Two.post {p : Params} {x y x' y' : State} (T : VG.Proof.MlDsa.X86_64.KeyGen.Two p x y) {W₁ W₂ : List Region} (hx : PostB x x' W₁)
    (hy : PostB y y' W₂) : VG.Proof.MlDsa.X86_64.KeyGen.Two p x' y' :=
  ⟨⟨T.sx.lay.post hx (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p), by rw [hx.rsp]; exact T.sx.h32⟩,
    ⟨T.sy.lay.post hy (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p), by rw [hy.rsp]; exact T.sy.h32⟩,
    fun r hr => by
      have hb : r ∈ bases := by simp only [VG.Proof.MlDsa.X86_64.KeyGen.kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
                                rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [hx.bs r hb, hy.bs r hb]; exact T.regs r hr, by rw [hx.rsp, hy.rsp]; exact T.rsp⟩

/-- A piece that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {p : Params} {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.KeyGen.Two p x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB y y' W)) :
    RelCT isa P c (VG.Proof.MlDsa.X86_64.KeyGen.Two p) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) hok fun x y _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (hP x y h).post hx hy

theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oSA + 32)) v ++ VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

theorem expA_tr {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · e 0)) (expA P p e) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc oSA)) 32 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc oSA)) 32)
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, by rw [h₁.k1.sa, h₂.k1.sa, VG.Proof.MlDsa.X86_64.KeyGen.rho_pub pub]⟩
  unfold expA
  -- The seed, then the call and the mask.
  let F := fun (x x' : State) => (∃ W, PostB x x' W) ∧
    bytesAt x'.mem (VG.Proof.MlKem.X86_64.pa x' (VG.Impl.MlKem.X86_64.sc oSA)) 34 = bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc oSA)) 32 ++ [BitVec.ofNat 8 (e % p.ℓ),
      BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, VG.Proof.MlDsa.X86_64.KeyGen.Site p x → WP isa (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oSA + 32)) (e % p.ℓ) ++ VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (oSA + 33)) (e / p.ℓ))) x
      (F x) := fun x S =>
    WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setTwo_ok S.lay (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by omega) (by omega) (by lay) (by lay)
      (by lay)) fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁.b⟩, by
        rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, S.lay.keepBytes hP₁.b (by layk),
          show VG.Proof.MlKem.X86_64.pa x' (VG.Impl.MlKem.X86_64.sc oSA) + BitVec.ofNat 64 32 = VG.Proof.MlKem.X86_64.pa x' (VG.Impl.MlKem.X86_64.sc (oSA + 32)) from VG.Proof.MlKem.X86_64.off_add _ _ _, hP₁.pa rbx_cs, hb]⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h.1) (VG.Proof.MlDsa.X86_64.KeyGen.setIJ_taint _ (by omega) _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.sx, hF1 y h.1.sy⟩)
    (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc oSA)) 34 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc oSA)) 34)
    fun x y x' y' ⟨T, e32⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ => ⟨T.post hx hy, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p x) => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rejNttAt_ok (sd := VG.Impl.MlKem.X86_64.sc oSA) (a := VG.Impl.MlDsa.X86_64.KeyGen.aP e) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide))
    (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt S)
    fun _ h => (⟨_, h.1.b⟩ : ∃ W, PostB x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.X86_64.KeyGen.rejNttAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
      (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide))
      fun x y h => ⟨ok x h.1.sx, ok y h.1.sy⟩)
    (VG.Proof.MlDsa.X86_64.KeyGen.mask_tr (j := e) (by omega) fun x y h => h.regs .rbx (by decide))

/-! ## An entry of `s₁ ‖ s₂` -/

theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]

theorem eta_of {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

/-- The seed of `RejBoundedPoly`, once its index is set. -/
theorem sbSeed {p : Params} {s s' : State} (L : Lay VG.Proof.MlDsa.X86_64.KeyGen.kgR (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) s) {r : Nat} (hr : r < 256)
    (hP : PPost s s' [(VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64), 1)]) (hb : bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64))) 1 = [BitVec.ofNat 8 r])
    {ρ' : List Byte} (h64 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 64 = ρ') (h65 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65))) 1 = [0]) :
    bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s' (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 66 = seedS ρ' r := by
  have k64 := L.keepBytes hP.b (p := VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) (l := 64) (by lay)
  have k65 := L.keepBytes hP.b (p := VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65)) (l := 1) (by lay)
  rw [hP.pa rbx_cs] at k64 k65 ⊢
  rw [show 66 = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, k64, h64,
    show VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) + BitVec.ofNat 64 64 = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64)) from VG.Proof.MlKem.X86_64.off_add _ _ _, hb,
    show VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) + BitVec.ofNat 64 (64 + 1) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65)) from VG.Proof.MlKem.X86_64.off_add _ _ _, k65, h65, VG.Proof.MlDsa.X86_64.KeyGen.seedS_eq _ hr,
    List.append_assoc]
  rfl

theorem expS_ok {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
    {r : Nat} (hr : r < p.ℓ + p.k) {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) (r + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  unfold expS
  refine WP.seq (WP.mono (WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (setB_okL L (p := VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64)) (v := r) (by decide) (by omega)
    (by lay))) fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => ?_)
  have h₁ : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) r s₁ := by
    refine h.keep hF hp hP₁.b hx₁ ?_ (fun e' he' => ?_) (fun r' hr' => ?_) (hP₁.cs .r15 (by decide))
    · layk
    · layk
    · layk
  have S₁ := h₁.k1.kc.site hF hp
  have hseed := VG.Proof.MlDsa.X86_64.KeyGen.sbSeed L (by omega) hP₁ hb₁ h.k1.sb h.k1.z
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rejBAt_ok (sd := VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) (a := VG.Impl.MlDsa.X86_64.KeyGen.sP p r) (VG.Proof.MlDsa.X86_64.KeyGen.eta_of hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide))
    (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejBounded S₁)
    fun s₂ ⟨hP₂, hx₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have hP₂' : PPostB s₁ s₂ [(VG.Impl.MlDsa.X86_64.KeyGen.sP p r, 1024), (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 2048)] := hP₂.b
  have L₂ := S₁.lay.post hP₂' (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  have hr01 := VG.Proof.MlDsa.X86_64.KeyGen.outcome_01 hout
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mask_ok L₂ (a := VG.Impl.MlDsa.X86_64.KeyGen.sP p r) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (show Reg.rbx ≠ .r15 by decide)
    (by lay) hr01) fun s₃ ⟨hP₃, hx₃, h15, hco⟩ => ?_
  have hP₃' : PPostB s₂ s₃ [(VG.Impl.MlDsa.X86_64.KeyGen.sP p r, 1024)] := hP₃
  have hP₁₃ := PPostB.app hP₂' hP₃' (VG.Proof.MlDsa.X86_64.KeyGen.sc1_bases _ _)
  have L₁ := S₁.lay
  have e₂ : VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r) = VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r) := hP₂'.pa rbx_bases
  have e₃ : VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r) = VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r) := hP₃'.pa rbx_bases
  rw [e₂] at hco
  obtain ⟨A, S, hA, hS, hG⟩ := h₁.ex
  have h15₂ : s₂.gpr .r15 = s₁.gpr .r15 := hP₂.cs .r15 (by decide)
  rw [h15₂, VG.Proof.MlDsa.X86_64.KeyGen.r15_and (VG.Proof.MlDsa.X86_64.KeyGen.good_01 hG) hr01] at h15
  have k1 := h₁.k1.step hF hp hP₁₃ (hx₃.trans hx₂)
    (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_, _]) (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_]) (VG.Proof.MlDsa.X86_64.KeyGen.k1_sP hF hr) (VG.Proof.MlDsa.X86_64.KeyGen.k1_ss hF)) (VG.Proof.MlDsa.X86_64.KeyGen.k1_sP hF hr))
  have kA : ∀ e' < p.k * p.ℓ, PolyIs s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.aP e')) (A e') := fun e' he' =>
    VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L₁ hP₁₃ (by layk) (hA e' he')
  have kS : ∀ r' < r, PolyIs s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r')) (toRq (S r')) ∧ VG.Proof.MlDsa.X86_64.KeyGen.Small p.η (S r') := fun r' hr' =>
    ⟨VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L₁ hP₁₃ (by layk) (hS r' hr').1, (hS r' hr').2⟩
  by_cases ho : (s₂.gpr .rax).setWidth 32 = 1
  · -- The sampler succeeded.
    obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ) r)).map toRq =
        some (polyAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlDsa.X86_64.KeyGen.sP p r))) := by
      rcases hout with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at ho; exact absurd ho (by decide)
    obtain ⟨x, hx, htx⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨k1, A, fun r' => if r' = r then x else S r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂, htx, ← (VG.Proof.MlDsa.X86_64.KeyGen.masked_one ho hco).1]
        exact ⟨⟨(VG.Proof.MlDsa.X86_64.KeyGen.masked_one ho hco).2 (hred ho), rfl⟩, Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    · rw [h15]
      rcases hG with ⟨h1, b, hbA, hbS⟩ | ⟨h0, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' =>
          Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hbA e' he'),
          fun r' hr' => ?_⟩
        dsimp only
        rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejBounded
            (hbS r' hr')
        · rw [ifp rfl]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejBounded hx
      · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
        exact .inr ⟨rfl, hn⟩
  · -- It failed: the polynomial is zero.
    have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (VG.Proof.MlDsa.X86_64.KeyGen.rho'Of p σ) r) = none := by
      rcases hout with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h ho
      · exact Option.map_eq_none_iff.mp h
    refine ⟨k1, A, fun r' => if r' = r then Vector.replicate 256 0 else S r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂]
        exact ⟨VG.Proof.MlDsa.X86_64.KeyGen.masked_zero ho hco, VG.Proof.MlDsa.X86_64.KeyGen.small_zero _⟩
    · rw [h15, ifn (fun h => ho h.2)]
      exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩

theorem setS_taint : ∀ v < 16, (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

theorem expS_tr {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (p.k * p.ℓ) r)) (expS P p r) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ ∃ ρ₁ ρ₂ : List Byte, bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 64 = ρ₁ ∧
      bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65))) 1 = [0] ∧ bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 64 = ρ₂ ∧
      bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65))) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₁ r) = Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₂ r))
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, _, _, h₁.k1.sb, h₁.k1.z, h₂.k1.sb,
      h₂.k1.z, VG.Proof.MlDsa.X86_64.KeyGen.rej_pub pub hr⟩
  unfold expS
  let F := fun (x x' : State) => (∃ W, PostB x x' W) ∧ ∀ ρ' : List Byte, bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 64 = ρ' →
    bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 65))) 1 = [0] → bytesAt x'.mem (VG.Proof.MlKem.X86_64.pa x' (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 66 = seedS ρ' r
  have hF1 : ∀ x, VG.Proof.MlDsa.X86_64.KeyGen.Site p x → WP isa (.block (VG.Impl.MlKem.X86_64.setB (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64)) r)) x (F x) := fun x S =>
    WP.mono (WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (setB_okL S.lay (p := VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oSB + 64)) (v := r) (by decide) (by omega)
      (by lay))) fun x' ⟨⟨hP₁, hb⟩, _⟩ => ⟨⟨_, hP₁.b⟩, fun _ h64 h65 => VG.Proof.MlDsa.X86_64.KeyGen.sbSeed S.lay (by omega) hP₁ hb h64 h65⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h.1) (VG.Proof.MlDsa.X86_64.KeyGen.setS_taint _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.sx, hF1 y h.1.sy⟩)
    (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 66) =
      Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB)) 66))
    fun x y x' y' ⟨T, _, _, a1, a2, a3, a4, a5⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ =>
      ⟨T.post hx hy, by rw [bx _ a1 a2, by' _ a3 a4, a5]⟩) ?_
  have ok := fun x (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p x) => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rejBAt_ok (sd := VG.Impl.MlKem.X86_64.sc VG.Impl.MlDsa.X86_64.KeyGen.oSB) (a := VG.Impl.MlDsa.X86_64.KeyGen.sP p r) (VG.Proof.MlDsa.X86_64.KeyGen.eta_of hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide))
    (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejBounded S)
    fun _ h => (⟨_, h.1.b⟩ : ∃ W, PostB x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.X86_64.KeyGen.rejBAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.eta_of hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by decide))
      (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejBounded
      (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide))
      fun x y h => ⟨ok x h.1.sx, ok y h.1.sy⟩)
    (VG.Proof.MlDsa.X86_64.KeyGen.mask_tr (j := p.k * p.ℓ + r) (by omega) fun x y h => h.regs .rbx (by decide))

/-! ## The pieces -/

theorem expA_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {e : Nat} (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · e 0) (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (e + 1) 0) (expA P p e) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.expA_ok hP hF hp he h, VG.Proof.MlDsa.X86_64.KeyGen.expA_tr hP hF he⟩

theorem expS_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (p.k * p.ℓ) r) (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (p.k * p.ℓ) (r + 1)) (expS P p r) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.expS_ok hP hF hp hr h, VG.Proof.MlDsa.X86_64.KeyGen.expS_tr hP hF hr⟩

theorem KSamp.zero {p : Params} {σ s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s) (h15 : s.gpr .r15 = 1) : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _),
    .inl ⟨h15, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) 0 s) (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (VG.Impl.MlKem.X86_64.seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => VG.Proof.MlDsa.X86_64.KeyGen.expS_piece hP hF (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp4`. -/
section

/-!
# ML-DSA key generation on x86-64: four entries of `Â` at a time

`expA4 g` sets the indices of entries `4g, …, 4g + 3` of `Â` in the four seeds
at `oSA4` (`slot_piece`), samples the four polynomials with one call of
`vg_mldsa_rej_ntt_poly4`, and masks them with its result (`call_piece`): it
takes `KSamp (4g)` to `KSamp (4g + 4)` (`expA4_piece`), and `expAll`, the
groups and then the last `kℓ mod 4` entries one at a time, takes `K1` to
`KSamp (kℓ)` (`sampAll_piece`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly coeffAt polyAt Reduced PolyIs poly4 seed4 minBounds)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seeds -/

/-- After the first `e` entries of `Â`, with the seeds of entries `e, …, e + j - 1` at `oSA4`. -/
structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e 0 s
  done : ∀ k < j, bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * k))) 34 = seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)

theorem slot_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {e j : Nat} (he : e + 4 ≤ p.k * p.ℓ)
    (hj : j < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.GS p σ e j s) : WP isa (.block (setSR p e j)) s (VG.Proof.MlDsa.X86_64.KeyGen.GS p σ e (j + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.ks.k1.kc.lay hF hp
  have hq : (e + j) / p.ℓ < 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hr : (e + j) % p.ℓ < 256 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  unfold setSR
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.setTwo_ok L (o := oSA4 + 34 * j + 32) hr hq (by lay) (by lay) (by lay))
    fun s' ⟨hP, hx, hb⟩ => ⟨h.ks.keep hF hp hP.b hx (by layk) (fun e' he' => by layk)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (hP.cs .r15 (by decide)), fun k hk => ?_⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP.b (by layk)]; exact h.done k hk'
  · rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, L.keepBytes hP.b (by layk), h.ks.k1.sa4 k hj,
      show VG.Proof.MlKem.X86_64.pa s' (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * k)) + BitVec.ofNat 64 32 = VG.Proof.MlKem.X86_64.pa s' (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * k + 32)) from VG.Proof.MlKem.X86_64.off_add _ _ _,
      hP.pa rbx_cs, hb, VG.Proof.MlDsa.X86_64.KeyGen.seedA_eq]

theorem slot_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {e j : Nat} (he : e + 4 ≤ p.k * p.ℓ) (hj : j < 4) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.GS p · e j) (VG.Proof.MlDsa.X86_64.KeyGen.GS p · e (j + 1)) (.block (setSR p e j)) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.slot_ok hF hp he hj h,
    VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := VG.Proof.MlDsa.X86_64.KeyGen.Two p) (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h) (hc := .block []) (by with_unfolding_all rfl))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.ks.k1.kc h₂.ks.k1.kc⟩

theorem seed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.GS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) k = seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := by
  unfold seed4
  rw [show VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4) + BitVec.ofNat 64 (34 * k) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (oSA4 + 34 * k)) from VG.Proof.MlKem.X86_64.off_add _ _ _]
  exact h.done k hk

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds are those of the entries, from `ρ`. -/
theorem GS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.GS p σ e 4 s) :
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4)) 136 = seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oSA4) + BitVec.ofNat 64 (34 * k)) 34 =
      seedA (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := fun k hk => VG.Proof.MlDsa.X86_64.KeyGen.seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, add_ofNat_zero] at b0
  rw [VG.Proof.MlDsa.X86_64.KeyGen.bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-! ## The four polynomials -/

theorem coeffAt_poly4 (m : Mem) (a : Addr) (k j : Nat) : coeffAt m (VG.Spec.MlDsa.poly4 a k) j = coeffAt m a (256 * k + j) := by
  unfold coeffAt VG.Spec.MlDsa.poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega]

theorem pa_poly4 (s : State) (e k : Nat) : VG.Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP e)) k = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (e + k)) := by
  unfold VG.Spec.MlDsa.poly4
  rw [show VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP e) + BitVec.ofNat 64 (1024 * k) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP e + 1024 * k)) from VG.Proof.MlKem.X86_64.off_add _ _ _,
    show VG.Impl.MlDsa.X86_64.KeyGen.oP e + 1024 * k = VG.Impl.MlDsa.X86_64.KeyGen.oP (e + k) by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega]

/-- One bound for the four polynomials. -/
theorem bound4 {ρ : Nat → List Byte} {x : Nat → Poly} (h : ∀ k < 4, ∃ b : Spec.MlDsa.Bounds,
    rejNTTPoly b.rejNTT (ρ k) = some (x k)) : ∃ n : Nat, ∀ k < 4, rejNTTPoly n (ρ k) = some (x k) := by
  obtain ⟨b0, h0⟩ := h 0 (by decide)
  obtain ⟨b1, h1⟩ := h 1 (by decide)
  obtain ⟨b2, h2⟩ := h 2 (by decide)
  obtain ⟨b3, h3⟩ := h 3 (by decide)
  refine ⟨max (max b0.rejNTT b1.rejNTT) (max b2.rejNTT b3.rejNTT), fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h1
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h2
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h3

theorem call_ok {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
    {g : Nat} (hg : 4 * g + 4 ≤ p.k * p.ℓ) {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.GS p σ (4 * g) 4 s) :
    WP isa (.seq (VG.Impl.MlDsa.X86_64.KeyGen.rej4At P.rej4 P.sfx (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) (VG.Impl.MlKem.X86_64.sc (oR4 p))) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) 1024)) s
      (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (4 * g + 4) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S := h.ks.k1.kc.site hF hp
  have L := S.lay
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rej4At_ok (a := VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) (w := VG.Impl.MlKem.X86_64.sc (oR4 p)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [oR4, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rej4 S)
    fun s₂ ⟨hP₂, hx₂, hred, hout⟩ => ?_)
  have hP₂' : PPostB s s₂ [(VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g), 4096), (VG.Impl.MlKem.X86_64.sc (oR4 p), 8192)] := hP₂.b
  have L₂ := L.post hP₂' (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  have hr01 : (s₂.gpr .rax).setWidth 32 = 0 ∨ (s₂.gpr .rax).setWidth 32 = 1 := by
    rcases hout with ⟨h1, _⟩ | ⟨h0, _⟩
    exacts [.inr h1, .inl h0]
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.maskN_ok L₂ (a := VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) (N := 1024) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (show Reg.rbx ≠ .r15 by decide) (by decide) (by decide) (by lay) hr01) fun s₃ ⟨hP₃, hx₃, h15, hco⟩ => ?_
  have hP₃' : PPostB s₂ s₃ [(VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g), 4 * 1024)] := hP₃
  have hP₁₃ := PPostB.app hP₂' hP₃' (VG.Proof.MlDsa.X86_64.KeyGen.sc1_bases _ _)
  have e₂ : VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) = VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) := hP₂'.pa rbx_bases
  rw [e₂] at hco
  have hco4 : ∀ k < 4, ∀ i < 256, coeffAt s₃.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g))) k) i =
      if (s₂.gpr .rax).setWidth 32 = 1 then coeffAt s₂.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g))) k) i else 0 :=
    fun k hk i hi => by rw [VG.Proof.MlDsa.X86_64.KeyGen.coeffAt_poly4, VG.Proof.MlDsa.X86_64.KeyGen.coeffAt_poly4]; exact hco _ (by omega)
  -- Entry `4g + k` is polynomial `k` from `aP (4g)`.
  have e₃ : ∀ k, VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g + k)) = VG.Spec.MlDsa.poly4 (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g))) k := fun k => by
    rw [VG.Proof.MlDsa.X86_64.KeyGen.pa_poly4]; exact hP₁₃.pa rbx_bases
  obtain ⟨A, S', hA, _, hG⟩ := h.ks.ex
  have h15₂ : s₂.gpr .r15 = s.gpr .r15 := hP₂.cs .r15 (by decide)
  rw [h15₂, VG.Proof.MlDsa.X86_64.KeyGen.r15_and (VG.Proof.MlDsa.X86_64.KeyGen.good_01 hG) hr01] at h15
  have ka : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [(VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g), 4096)] = true := VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_rbx (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)
  have kr : VG.Proof.MlDsa.X86_64.KeyGen.k1Chk p [(VG.Impl.MlKem.X86_64.sc (oR4 p), 8192)] = true := VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_rbx (by simp only [oR4, VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlKem.X86_64.oSS]; omega)
    (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, oR4, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)
  refine ⟨h.ks.k1.step hF hp hP₁₃ (hx₃.trans hx₂) (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_, _]) (VG.Proof.MlDsa.X86_64.KeyGen.k1Chk_append (ws₁ := [_]) ka kr) ka),
    fun e' => if e' < 4 * g then A e'
    else polyAt s₃.mem (VG.Proof.MlKem.X86_64.pa s₃ (VG.Impl.MlDsa.X86_64.KeyGen.aP e')), S', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    by_cases hlt : e' < 4 * g
    · rw [ifp hlt]
      exact VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP₁₃ (by layk) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, e' = 4 * g + k := ⟨e' - 4 * g, by omega⟩
      rw [e₃]
      by_cases h1 : (s₂.gpr .rax).setWidth 32 = 1
      · exact (VG.Proof.MlDsa.X86_64.KeyGen.masked_one h1 (hco4 k (by omega))).2 (hred h1 k (by omega))
      · exact (VG.Proof.MlDsa.X86_64.KeyGen.masked_zero h1 (hco4 k (by omega))).1
  · rw [h15]
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, hb4⟩ | ⟨ho, k, hk, hn⟩
      · obtain ⟨n, hn⟩ := VG.Proof.MlDsa.X86_64.KeyGen.bound4 hb4
        refine .inl ⟨by rw [ifp ⟨h1, ho⟩], { b with rejNTT := max b.rejNTT n }, fun e' he' => ?_,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        by_cases hlt : e' < 4 * g
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k, rfl⟩ : ∃ k, e' = 4 * g + k := ⟨e' - 4 * g, by omega⟩
          have hk : k < 4 := by omega
          rw [e₃, (VG.Proof.MlDsa.X86_64.KeyGen.masked_one ho (hco4 k hk)).1, ← VG.Proof.MlDsa.X86_64.KeyGen.seed4_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [VG.Proof.MlDsa.X86_64.KeyGen.seed4_eq h hk] at hn
        have hq : (4 * g + k) / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega)
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega)) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

theorem call_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {g : Nat}
    (hg : 4 * g + 4 ≤ p.k * p.ℓ) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.GS p · (4 * g) 4) (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (4 * g + 4) 0)
      (.seq (VG.Impl.MlDsa.X86_64.KeyGen.rej4At P.rej4 P.sfx (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) (VG.Impl.MlKem.X86_64.sc (oR4 p))) (VG.Impl.MlDsa.X86_64.KeyGen.mask (VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) 1024)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.call_ok hP hF hp hg h, VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧
      bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlKem.X86_64.sc oSA4)) 136 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlKem.X86_64.sc oSA4)) 136) ?_
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.ks.k1.kc h₂.ks.k1.kc,
      by rw [h₁.seeds, h₂.seeds, VG.Proof.MlDsa.X86_64.KeyGen.rho_pub pub]⟩⟩
  have ok := fun x (S : VG.Proof.MlDsa.X86_64.KeyGen.Site p x) => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.rej4At_ok (a := VG.Impl.MlDsa.X86_64.KeyGen.aP (4 * g)) (w := VG.Impl.MlKem.X86_64.sc (oR4 p)) (sfx := P.sfx)
    (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [oR4, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay)
    (by lay) (by lay) hP.rej4 S) fun _ h => (⟨_, h.1.b⟩ : ∃ W, PostB x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.X86_64.KeyGen.rej4At_tr (sfx := P.sfx) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
      (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [oR4, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rej4
      (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide))
      fun x y h => ⟨ok x h.1.sx, ok y h.1.sy⟩)
    (VG.Proof.MlDsa.X86_64.KeyGen.mask4_tr (j := 4 * g) (by omega) fun x y h => h.regs .rbx (by decide))

/-! ## The pieces -/

theorem expA4_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {g : Nat}
    (hg : 4 * g + 4 ≤ p.k * p.ℓ) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (4 * g) 0) (VG.Proof.MlDsa.X86_64.KeyGen.KSamp p · (4 * g + 4) 0) (expA4 P p g) := by
  unfold expA4
  exact Piece.mono ((VG.Proof.MlDsa.X86_64.KeyGen.slot_piece hF hg (j := 0) (by decide)).seq ((VG.Proof.MlDsa.X86_64.KeyGen.slot_piece hF hg (j := 1) (by decide)).seq
    ((VG.Proof.MlDsa.X86_64.KeyGen.slot_piece hF hg (j := 2) (by decide)).seq ((VG.Proof.MlDsa.X86_64.KeyGen.slot_piece hF hg (j := 3) (by decide)).seq (VG.Proof.MlDsa.X86_64.KeyGen.call_piece hP hF hg)))))
    (fun _ _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ _ _ h => h

/-- The entries of `Â`. -/
theorem sampAll_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.K1 p σ s ∧ s.gpr .r15 = 1) (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) 0 s) (expAll P p) := by
  unfold expAll
  refine Piece.seq (J := fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (4 * (p.k * p.ℓ / 4)) 0 s) ?_ ?_
  · refine Piece.mono (Piece.seqR (I := fun g σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (4 * g) 0 s) (p.k * p.ℓ / 4) 0
      fun g _ hg => Piece.mono (VG.Proof.MlDsa.X86_64.KeyGen.expA4_piece hP hF (g := g) (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_)
      (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
    · rw [show 4 * (g + 1) = 4 * g + 4 by omega]; exact h
    · simpa using h
  · refine Piece.mono (Piece.seqR (I := fun e σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ e 0 s) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
      fun e h1 h2 => VG.Proof.MlDsa.X86_64.KeyGen.expA_piece hP hF (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
    rwa [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega] at h

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestBase`. -/
section

/-!
# ML-DSA key generation on x86-64: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `r15` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc copy seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : VG.Proof.MlDsa.X86_64.KeyGen.KC p σ s
  r15 : s.gpr .r15 = R
  good : VG.Proof.MlDsa.X86_64.KeyGen.Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, VG.Proof.MlDsa.X86_64.KeyGen.Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)) (if j < nj then VG.Spec.MlDsa.ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r12, 0)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ
  sk0 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 0)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ
  sk1 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 32)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ
  packs : ∀ r < np, bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 128 + lenS p * r)) (lenS p) = VG.Spec.MlDsa.bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r12, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, oT0 p + 416 * i)) 416 = VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096

/-- A piece that writes `ws` keeps what `KR` says. -/
structure KRChk (p : Params) (np nj nr : Nat) (ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)) : Prop where
  kc : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ws = true
  aS : ∀ e < p.k * p.ℓ, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlDsa.X86_64.KeyGen.aP e) 1024 = true
  s2 : ∀ i < p.k, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i)) 1024 = true
  s1 : ∀ j < p.ℓ, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (VG.Impl.MlDsa.X86_64.KeyGen.sP p j) 1024 = true
  pk0 : keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r12, 0) 32 = true
  sk0 : keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r13, 0) 32 = true
  sk1 : keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r13, 32) 32 = true
  packs : ∀ r < np, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r13, 128 + lenS p * r) (lenS p) = true
  rows : ∀ i < nr, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r12, 32 + 320 * i) 320 = true ∧ keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ws (.r13, oT0 p + 416 * i) 416 = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      first
        | layk [($hF).pk, ($hF).sk]
        | rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [($hF).pk, ($hF).sk, hlen]))

/-- The checks of two pieces of writes, for both. -/
theorem KRChk.append {p : Params} {np nj nr : Nat} {ws₁ ws₂ : List (VG.Impl.MlKem.X86_64.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr ws₁)
    (h₂ : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr ws₂) : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr (ws₁ ++ ws₂) :=
  ⟨VG.Proof.MlDsa.X86_64.KeyGen.kcChk_append h₁.kc h₂.kc, fun e he => VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.s2 i hi) (h₂.s2 i hi), fun j hj => VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.s1 j hj) (h₂.s1 j hj),
    VG.Proof.MlDsa.X86_64.KeyGen.keepB_append h₁.pk0 h₂.pk0, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append h₁.sk0 h₂.sk0, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append h₁.sk1 h₂.sk1,
    fun r hr => VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.rows i hi).1 (h₂.rows i hi).1, VG.Proof.MlDsa.X86_64.KeyGen.keepB_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! The checks of a write to one region, proved once for any region (`krchk` on a
literal list of writes costs seconds). -/

/-- A write to `scratch` outside the saved registers and the polynomials. -/
theorem KRChk.rbx {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ VG.Impl.MlKem.X86_64.oSV ∨ VG.Impl.MlKem.X86_64.oSV + 48 ≤ o)
    (h2 : o + n ≤ VG.Impl.MlDsa.X86_64.KeyGen.oP 0 ∨ VG.Impl.MlDsa.X86_64.KeyGen.oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o) (h3 : o + n ≤ VG.Proof.MlDsa.X86_64.KeyGen.scrLen p) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr [((.rbx, o), n)] := by
  simp only [VG.Impl.MlKem.X86_64.oSV, VG.Impl.MlDsa.X86_64.KeyGen.oP] at h1 h2
  simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords] at h3
  krchk hF

/-- A write to `pk` after the rows so far. -/
theorem KRChk.r12 {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : 32 + 320 * nr ≤ o) (h2 : o + n ≤ p.pkLen) : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr [((.r12, o), n)] := by
  rw [hF.pk] at h2
  krchk hF

/-- A write to `sk` after `ρ` and `K`, outside the entries packed and the rows so far. -/
theorem KRChk.r13 {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h0 : 64 ≤ o) (hp : o + n ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + n ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + n ≤ p.skLen) : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr [((.r13, o), n)] := by
  rw [hF.sk] at h2
  simp only [oT0] at hr h2
  have := hF.k; have := hF.l; have := hF.kl
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> rw [hlen] at hp hr h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
  layk [hF.pk, hF.sk, hlen]

theorem KR.keep {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np nj nr s) {ws : List (VG.Impl.MlKem.X86_64.Ptr × Nat)}
    (hP : PPostB s s' ws) (hx : VG.Proof.MlDsa.X86_64.KeyGen.MX s' = VG.Proof.MlDsa.X86_64.KeyGen.MX s) (h15 : s'.gpr .r15 = s.gpr .r15) (hc : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p np nj nr ws) :
    VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hx hc.kc, h15.trans h.r15, h.good, h.small,
    fun e he => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.aS e he) (h.aS e he), fun i hi => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.s1 j hj) (h.s1 j hj), by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

theorem r12_bases (o n : Nat) : ∀ w ∈ [(((.r12, o) : VG.Impl.MlKem.X86_64.Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.r12 ∈ bases; decide

theorem r13_bases (o n : Nat) : ∀ w ∈ [(((.r13, o) : VG.Impl.MlKem.X86_64.Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.r13 ∈ bases; decide

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (VG.Proof.MlDsa.X86_64.KeyGen.KR0 p σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  unfold copies
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L (dst := (.r12, 0)) (src := VG.Impl.MlKem.X86_64.sc oHX) (n := 32) (by decide)
    (by layk [hF.pk, hF.sk])) fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => ?_)
  have L₁ := L.post hP₁.b (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L₁ (dst := (.r13, 0)) (src := VG.Impl.MlKem.X86_64.sc oHX) (n := 32) (by decide)
    (by layk [hF.pk, hF.sk])) fun s₂ ⟨⟨hP₂, hb₂⟩, hx₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p)
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.copy_okM L₂ (dst := (.r13, 32)) (src := VG.Impl.MlKem.X86_64.sc (oHX + 96)) (n := 32) (by decide)
    (by layk [hF.pk, hF.sk])) fun s₃ ⟨⟨hP₃, hb₃⟩, hx₃⟩ => ?_
  have hP := PPostB.app (PPostB.app hP₁.b hP₂.b (VG.Proof.MlDsa.X86_64.KeyGen.r13_bases _ _)) hP₃.b (VG.Proof.MlDsa.X86_64.KeyGen.r13_bases _ _)
  have hx : VG.Proof.MlDsa.X86_64.KeyGen.MX s₃ = VG.Proof.MlDsa.X86_64.KeyGen.MX s := hx₃.trans (hx₂.trans hx₁)
  have h15 : s₃.gpr .r15 = s.gpr .r15 := by
    rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have hc : VG.Proof.MlDsa.X86_64.KeyGen.kcChk p ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) = true ∧
      (∀ e < p.k * p.ℓ, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (VG.Impl.MlDsa.X86_64.KeyGen.aP e) 1024 = true) ∧
      (∀ r < p.ℓ + p.k, keepB (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (VG.Impl.MlDsa.X86_64.KeyGen.sP p r) 1024
        = true) := by
    exact ⟨by layk [hF.pk, hF.sk], fun _ _ => by layk [hF.pk, hF.sk], fun _ _ => by layk [hF.pk, hF.sk]⟩
  -- The bytes of `HX`, and `ρ`, `K`.
  have hHX₁ : bytesAt s₁.mem (VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc oHX)) 128 = VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ := by rw [L.keepBytes hP₁.b (by layk [hF.pk])]; exact h.k1.hx
  have hHX₂ : bytesAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlKem.X86_64.sc oHX)) 128 = VG.Proof.MlDsa.X86_64.KeyGen.hxOf p σ := by
    rw [L₁.keepBytes hP₂.b (by layk [hF.pk, hF.sk])]; exact hHX₁
  have e1 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc oHX)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ := by
    rw [VG.Proof.MlDsa.X86_64.KeyGen.rho_eq, ← h.k1.hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e1' : bytesAt s₁.mem (VG.Proof.MlKem.X86_64.pa s₁ (VG.Impl.MlKem.X86_64.sc oHX)) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ := by
    rw [VG.Proof.MlDsa.X86_64.KeyGen.rho_eq, ← hHX₁, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e2 : bytesAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (VG.Impl.MlKem.X86_64.sc (oHX + 96))) 32 = VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ := by
    rw [VG.Proof.MlDsa.X86_64.KeyGen.kOf_eq, ← hHX₂, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.off_add]
  refine ⟨A, S, s.gpr .r15, ⟨h.k1.kc.step hF hp hP hx hc.1, h15, hG, fun r hr => (hS r hr).2,
    fun e he => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.2.1 e he) (hA e he),
    fun i hi => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.2.2 _ (by omega)) (hS (p.ℓ + i) (by omega)).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP (hc.2.2 j (by omega)) (hS j (by omega)).1,
    ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [L₂.keepBytes hP₃.b (by layk [hF.pk, hF.sk]),
      L₁.keepBytes hP₂.b (by layk [hF.pk, hF.sk]),
      hP₁.pa (by decide), hb₁, e1]
  · rw [L₂.keepBytes hP₃.b (by layk [hF.pk, hF.sk]),
      hP₂.pa (by decide), hb₂, e1']
  · rw [hP₃.pa (by decide), hb₃, e2]

theorem copies_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.X86_64.KeyGen.KR0 p) copies :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.X86_64.KeyGen.copies_ok hF hp h,
    VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := VG.Proof.MlDsa.X86_64.KeyGen.Two p) (taintRel [.rbx, .r12, .r13] (fun x y h r hr => h.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) (by taint_decide))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestPack`. -/
section

/-!
# ML-DSA key generation on x86-64: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : VG.Proof.MlDsa.X86_64.KeyGen.Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem packIn_of {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x))
    (hs : VG.Proof.MlDsa.X86_64.KeyGen.Small η x) : VG.Proof.MlDsa.X86_64.KeyGen.PackIn m q η η := by
  refine ⟨h.1, fun i hi => ?_⟩
  have hx := VG.Proof.MlDsa.X86_64.KeyGen.small_mem hs hi
  rw [VG.Proof.MlDsa.X86_64.KeyGen.coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : VG.Proof.MlDsa.X86_64.KeyGen.Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem eta_params {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : (p.η, p.η) ∈ Spec.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) : PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.sP p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

/-! ## `BitPack` of `s₁ ‖ s₂` -/

theorem chk_packS {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p r 0 0 [((.r13, 128 + lenS p * r), lenS p)] := by
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  exact KRChk.r13 hF (Nat.le_of_lt hr) (Nat.zero_le _) (by omega) (.inr (Nat.le_refl _)) (.inl hle)
    (by rw [hF.sk]; omega)

theorem packS_ok {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
    {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R r 0 0 s) : WP isa (packS P p r) s (VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have hS := h.sPoly hr
  unfold packS
  rcases hF.eta with ⟨he, hlen⟩ | ⟨he, hlen⟩ <;>
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.bpAt_ok (VG.Proof.MlDsa.X86_64.KeyGen.eta_params hF) (VG.Proof.MlDsa.X86_64.KeyGen.lenS_eq p) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    ⟨by rw [hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk, hlen])
    (by lay [hF.pk, hF.sk, hlen]) hP.bitPack S₀ (VG.Proof.MlDsa.X86_64.KeyGen.packIn_of (VG.Proof.MlDsa.X86_64.KeyGen.eta_le hF) hS (h.small r hr)))
    fun s' ⟨hP', hx, hb⟩ => ?_ <;>
  · have hP'' : PPostB s s' [((.r13, 128 + lenS p * r), lenS p)] := hP'.b
    have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_packS hF hr)
    refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
      fun r' hr' => ?_, hk'.rows⟩
    rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
    · exact hk'.packs r' hr'
    · rw [hP'.pa (show Reg.r13 ∈ calleeSaved by decide), hb, hS.2, Proof.MlDsa.KeyGen.modPm_toRq (VG.Proof.MlDsa.X86_64.KeyGen.small_big (VG.Proof.MlDsa.X86_64.KeyGen.eta_le hF) (h.small r' hr))]

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np nj nr s

theorem packS_tr {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p r 0 0)) (packS P p r) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ VG.Proof.MlDsa.X86_64.KeyGen.PackIn x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.sP p r)) p.η p.η ∧
    VG.Proof.MlDsa.X86_64.KeyGen.PackIn y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.sP p r)) p.η p.η) ?_ fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, VG.Proof.MlDsa.X86_64.KeyGen.packIn_of (VG.Proof.MlDsa.X86_64.KeyGen.eta_le hF) (h₁.sPoly hr) (h₁.small r hr),
        VG.Proof.MlDsa.X86_64.KeyGen.packIn_of (VG.Proof.MlDsa.X86_64.KeyGen.eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩
  unfold packS
  rcases hF.eta with ⟨he, hlen⟩ | ⟨he, hlen⟩ <;>
  exact VG.Proof.MlDsa.X86_64.KeyGen.bpAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.eta_params hF) (VG.Proof.MlDsa.X86_64.KeyGen.lenS_eq p) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    ⟨by rw [hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk, hlen])
    (by lay [hF.pk, hF.sk, hlen]) hP.bitPack (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.r13 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem packS_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p r 0 0) (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.packS_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, VG.Proof.MlDsa.X86_64.KeyGen.packS_tr hP hF hr⟩

/-! ## `NTT` of `s₁` -/

theorem nttS_ok {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ)
    {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) j 0 s) : WP isa (nttS P p j) s (VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  unfold nttS VG.Impl.MlDsa.X86_64.KeyGen.nttAt
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.ipAt_ok (t := VG.Spec.MlDsa.ntt) (f := VG.Impl.MlDsa.X86_64.KeyGen.sP p j) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay)
    hP.ntt S₀ hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(VG.Impl.MlDsa.X86_64.KeyGen.sP p j, 1024), (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  have L := S₀.lay
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact ⟨h.kc.step hF hp hP'' hx (by layk [hF.pk, hF.sk]), (hP'.cs .r15 (by decide)).trans h.r15, h.good,
    h.small, fun e he => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP'' (by layk [hF.pk, hF.sk]) (h.aS e he),
    fun i hi => VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP'' (by layk [hF.pk, hF.sk]) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP''.pa (p := VG.Impl.MlDsa.X86_64.KeyGen.sP p j') rbx_bases, ← hS.2]; exact hb
      else by
        have := VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP'' (by layk [hF.pk, hF.sk]) (h.s1 j' hj')
        by_cases hlt : j' < j
        · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this
        · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this,
    by rw [L.keepBytes hP'' (by layk [hF.pk, hF.sk])]; exact h.pk0,
    by rw [L.keepBytes hP'' (by layk [hF.pk, hF.sk])]; exact h.sk0,
    by rw [L.keepBytes hP'' (by layk [hF.pk, hF.sk])]; exact h.sk1,
    fun r hr => by
      rw [L.keepBytes hP'' (by rcases hlen with hlen | hlen <;> layk [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem nttS_tr {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {j : Nat} (hj : j < p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.X86_64.KeyGen.R p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) j 0)) (nttS P p j) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.sP p j))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, (h₁.s1 j hj).1,
      (h₂.s1 j hj).1⟩
  unfold nttS VG.Impl.MlDsa.X86_64.KeyGen.nttAt
  exact VG.Proof.MlDsa.X86_64.KeyGen.ipAt_tr (t := VG.Spec.MlDsa.ntt) (f := VG.Impl.MlDsa.X86_64.KeyGen.sP p j) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) (by lay) hP.ntt
    (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem nttS_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) j 0) (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.nttS_ok hP hF hp hj h) fun _ h => ⟨A, S, R, h⟩, VG.Proof.MlDsa.X86_64.KeyGen.nttS_tr hP hF hj⟩

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestRow`. -/
section

/-!
# ML-DSA key generation on x86-64: the rows of `t`

Row `i` of `t`: the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`mul_ok`,
`mulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`inv_ok`, `addS2_ok`), then
`Power2Round` (`p2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`sbp_ok`, `bp_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- In row `i`, with `f` holding what the row computed so far. -/
def KRow (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (A : Nat → Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (tP p)) (g A S)

theorem KR.polyA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (VG.Proof.MlDsa.X86_64.KeyGen.idx_lt hi hj)

theorem KR.polyS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)) (VG.Spec.MlDsa.ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem tP_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk (tP p) :=
  VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem tP1_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk (t1P p) :=
  VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem tP0_ok {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : VG.Proof.MlDsa.X86_64.KeyGen.PtrOk (t0P p) :=
  VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (VG.Spec.MlDsa.power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem packIn_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)) :
    VG.Proof.MlDsa.X86_64.KeyGen.PackIn m q 4095 4096 := by
  refine ⟨h.1, fun j hj => ?_⟩
  rw [VG.Proof.MlDsa.X86_64.KeyGen.coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  omega

/-! ## The checks of the writes of a row, once each -/

/-- Polynomial `j` of `scratch` after `s₁ ‖ s₂`. -/
theorem chk_poly {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(VG.Impl.MlKem.X86_64.sc (VG.Impl.MlDsa.X86_64.KeyGen.oP (p.k * p.ℓ + p.ℓ + p.k + j)), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact KRChk.rbx hF (by omega) (by omega) (.inr (by simp only [VG.Impl.MlKem.X86_64.oSV, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (.inr (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)

theorem chk_t {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024)] := by
  have := VG.Proof.MlDsa.X86_64.KeyGen.chk_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024), (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (VG.Proof.MlDsa.X86_64.KeyGen.chk_t hF hi).append (ws₁ := [_]) (KRChk.rbx (o := VG.Impl.MlKem.X86_64.oSS) (n := 1024) hF (by omega)
    (by omega) (.inr (by decide)) (.inl (by decide))
    (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords, VG.Impl.MlKem.X86_64.oSS]; omega))

theorem chk_p2r {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(t1P p, 1024), (t0P p, 1024)] :=
  (VG.Proof.MlDsa.X86_64.KeyGen.chk_poly hF hi (j := 1) (by decide)).append (ws₁ := [_]) (VG.Proof.MlDsa.X86_64.KeyGen.chk_poly hF hi (j := 2) (by decide))

theorem chk_sbp {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [((.r12, 32 + 320 * i), 320)] :=
  KRChk.r12 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega)

theorem chk_bp {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [((.r13, oT0 p + 416 * i), 416)] := by
  have := hF.k; have := hF.l
  refine KRChk.r13 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega) (.inr (by simp only [oT0]; omega))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega)

section
variable {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) {i : Nat}
  (hi : i < p.k)
include hP hF hp hi


/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem mul_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mulAt P.sfx P.mul (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i)) (VG.Impl.MlDsa.X86_64.KeyGen.sP p 0)) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => dotK p A S i 1) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := VG.Proof.MlDsa.X86_64.KeyGen.idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  have S₀ := h.kc.site hF hp
  have hA := h.polyA hi (j := 0) (by omega)
  rw [Nat.add_zero] at hA
  have hS := h.polyS (j := 0) (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mulAt_ok (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (by lay) (by lay) (by lay) hP.mul S₀ hA.1 hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.KeyGen.tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem mulAdd_ok {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => dotK p A S i j) A S s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.mulAddAt P.sfx P.mulAdd (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i + j)) (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => dotK p A S i (j + 1)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [VG.Proof.MlDsa.X86_64.KeyGen.tIs] at ht
  have hx0 := VG.Proof.MlDsa.X86_64.KeyGen.idx_lt hi hj
  have S₀ := h.kc.site hF hp
  have hA := h.polyA hi hj
  have hS := h.polyS hj
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mulAddAt_ok (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega))
    (by lay) (by lay) (by lay) hP.mulAdd S₀ ht.1 hA.1 hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.KeyGen.tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hS.2, ← ht.2]
  exact hb

/-- `t = NTT⁻¹(t)`. -/
theorem inv_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => dotK p A S i p.ℓ) A S s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.invNttAt P.sfx P.invNtt (tP p)) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [VG.Proof.MlDsa.X86_64.KeyGen.tIs] at ht
  have S₀ := h.kc.site hF hp
  unfold VG.Impl.MlDsa.X86_64.KeyGen.invNttAt
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.ipAt_ok (t := VG.Spec.MlDsa.nttInv) (f := tP p) (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (by lay) (by lay) (by lay) hP.invNtt S₀ ht.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024), (VG.Impl.MlKem.X86_64.sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_inv hF hi), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.KeyGen.tIs, hP''.pa (p := tP p) rbx_bases, ← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.addAt P.sfx P.add (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i))) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => tK p A S i) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [VG.Proof.MlDsa.X86_64.KeyGen.tIs] at ht
  have S₀ := h.kc.site hF hp
  have hS := h.s2 i hi
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.addAt_ok (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) hP.add S₀ ht.1 hS.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.KeyGen.tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.X86_64.KeyGen.tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [VG.Proof.MlDsa.X86_64.KeyGen.tIs] at ht
  have S₀ := h.kc.site hF hp
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.p2rAt_ok (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.tP1_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.tP0_ok hF) (by lay) (by lay) (by lay) (by lay) (by lay)
    hP.power2Round S₀ ht.1) fun s' ⟨hP', hx, h1, h0⟩ => ?_
  have hP'' : PPostB s s' [(t1P p, 1024), (t0P p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_p2r hF hi), ?_, ?_⟩
  · rw [hP''.pa (p := t1P p) rbx_bases, Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP''.pa (p := t0P p) rbx_bases, ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) s fun s' =>
      VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s' (.r12, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.sbpAt_ok (by decide) (by decide) (VG.Proof.MlDsa.X86_64.KeyGen.tP1_ok hF)
    ⟨by omega, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk]) (by lay [hF.pk]) hP.simpleBitPack S₀
    fun j hj => ?_) fun s' ⟨hP', hx, hb⟩ => ?_
  · rw [show (coeffAt s.mem (VG.Proof.MlKem.X86_64.pa s (t1P p)) j).toNat = (t1K p A S i)[j]'hj from by
      rw [← h1]; simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn]]
    simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
    omega
  · have hP'' : PPostB s s' [((.r12, 32 + 320 * i), 320)] := hP'.b
    refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_sbp hF hi),
      VG.Proof.MlDsa.X86_64.KeyGen.polyIs_frame' L hP'' (by lay [hF.pk]) h0, ?_⟩
    rw [hP''.pa (p := (.r12, 32 + 320 * i)) (show Reg.r12 ∈ bases by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2))
    (h1 : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r12, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023) :
    WP isa (VG.Impl.MlDsa.X86_64.KeyGen.bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) s
      (VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.bpAt_ok (by decide) (by decide) (VG.Proof.MlDsa.X86_64.KeyGen.tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk])
    (by lay [hF.pk, hF.sk]) hP.bitPack S₀ (VG.Proof.MlDsa.X86_64.KeyGen.packIn_t0 h0)) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [((.r13, oT0 p + 416 * i), 416)] := hP'.b
  have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (VG.Proof.MlDsa.X86_64.KeyGen.chk_bp hF hi)
  refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by rw [L.keepBytes hP'' (by lay [hF.pk, hF.sk])]; exact h1, ?_⟩
    rw [hP''.pa (p := (.r13, oT0 p + 416 * i')) (show Reg.r13 ∈ bases by decide), hb, h0.2, VG.Proof.MlDsa.X86_64.KeyGen.modPm_t0]
    rfl

end

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => dotK p A S i 1))
    (VG.Impl.MlDsa.X86_64.KeyGen.mulAt P.sfx P.mul (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i)) (VG.Impl.MlDsa.X86_64.KeyGen.sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := VG.Proof.MlDsa.X86_64.KeyGen.idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mul_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i))) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.sP p 0))) ∧
    (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i))) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.sP p 0)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => by
      have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
      rw [Nat.add_zero] at a₁ a₂
      exact ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨a₁.1, (h₁.polyS (j := 0) (by omega)).1⟩,
        ⟨a₂.1, (h₂.polyS (j := 0) (by omega)).1⟩⟩
  exact VG.Proof.MlDsa.X86_64.KeyGen.mulAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay)
    (by lay) hP.mul (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)
    (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem mulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => dotK p A S i j)) (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => dotK p A S i (j + 1)))
      (VG.Impl.MlDsa.X86_64.KeyGen.mulAddAt P.sfx P.mulAdd (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i + j)) (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := VG.Proof.MlDsa.X86_64.KeyGen.idx_lt hi hj
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.mulAdd_ok hP hF hp hi hj h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (tP p)) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i + j))) ∧
    Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.sP p j))) ∧ (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (tP p)) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.aP (p.ℓ * i + j))) ∧
    Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.sP p j)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩,
        ⟨t₂.1, (h₂.polyA hi hj).1, (h₂.polyS hj).1⟩⟩
  exact VG.Proof.MlDsa.X86_64.KeyGen.mulAddAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay)
    (by lay) (by lay) hP.mulAdd (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)
    (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem inv_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => dotK p A S i p.ℓ))
    (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ))) (VG.Impl.MlDsa.X86_64.KeyGen.invNttAt P.sfx P.invNtt (tP p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.inv_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (tP p)) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  unfold VG.Impl.MlDsa.X86_64.KeyGen.invNttAt
  exact VG.Proof.MlDsa.X86_64.KeyGen.ipAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (by lay) (by lay) (by lay) hP.invNtt (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem addS2_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)))
    (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (VG.Impl.MlDsa.X86_64.KeyGen.addAt P.sfx P.add (tP p) (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (tP p)) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (tP p)) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (VG.Impl.MlDsa.X86_64.KeyGen.sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  exact VG.Proof.MlDsa.X86_64.KeyGen.addAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.sc_ok _ (by simp only [VG.Impl.MlDsa.X86_64.KeyGen.oP]; omega)) (by lay) (by lay) hP.add
    (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)

theorem p2r_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.p2rIs p i))
    (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (tP p)) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact VG.Proof.MlDsa.X86_64.KeyGen.p2rAt_tr (VG.Proof.MlDsa.X86_64.KeyGen.tP_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.tP1_ok hF) (VG.Proof.MlDsa.X86_64.KeyGen.tP0_ok hF) (by lay) (by lay) (by lay) (by lay) (by lay) hP.power2Round
    (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r12, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.p2rIs p i)) (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.sbpIs p i))
    (VG.Impl.MlDsa.X86_64.KeyGen.simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ (∀ j < 256, (coeffAt x.mem (VG.Proof.MlKem.X86_64.pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (VG.Proof.MlKem.X86_64.pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, VG.Proof.MlDsa.X86_64.KeyGen.t1_bound t₁.1, VG.Proof.MlDsa.X86_64.KeyGen.t1_bound t₂.1⟩
  exact VG.Proof.MlDsa.X86_64.KeyGen.sbpAt_tr (by decide) (by decide) (VG.Proof.MlDsa.X86_64.KeyGen.tP1_ok hF) ⟨by omega, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩
    (by lay [hF.pk]) (by lay [hF.pk]) hP.simpleBitPack (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)
    (show Reg.r12 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

theorem bp_piece : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.sbpIs p i)) (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (VG.Impl.MlDsa.X86_64.KeyGen.bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.X86_64.KeyGen.Two p x y ∧ VG.Proof.MlDsa.X86_64.KeyGen.PackIn x.mem (VG.Proof.MlKem.X86_64.pa x (t0P p)) 4095 4096 ∧
    VG.Proof.MlDsa.X86_64.KeyGen.PackIn y.mem (VG.Proof.MlKem.X86_64.pa y (t0P p)) 4095 4096) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, VG.Proof.MlDsa.X86_64.KeyGen.packIn_t0 t₁.1, VG.Proof.MlDsa.X86_64.KeyGen.packIn_t0 t₂.1⟩
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact VG.Proof.MlDsa.X86_64.KeyGen.bpAt_tr (by decide) (by decide) (VG.Proof.MlDsa.X86_64.KeyGen.tP0_ok hF)
    ⟨by rcases hlen with hl | hl <;> simp only [oT0, hl] <;> omega,
      show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk])
    (by lay [hF.pk, hF.sk]) hP.bitPack (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide) (show Reg.r13 ∈ VG.Proof.MlDsa.X86_64.KeyGen.kgRegs by decide)

end

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top`. -/
section

/-!
# ML-DSA key generation on x86-64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The function, piece by piece, for any parameter set of Table 1 and any
verified implementations of the primitives (`keyGen_piece`): it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds; it leaks only
the pointers, `ρ` and what `RejBoundedPoly` leaks; so it meets the shared
contract (`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR topEpi oSV)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (VG.Proof.MlDsa.X86_64.KeyGen.mul_piece hP hF hi).seq (Piece.seq ?_ ((VG.Proof.MlDsa.X86_64.KeyGen.inv_piece hP hF hi).seq ((VG.Proof.MlDsa.X86_64.KeyGen.addS2_piece hP hF hi).seq
    ((VG.Proof.MlDsa.X86_64.KeyGen.p2r_piece hP hF hi).seq ((VG.Proof.MlDsa.X86_64.KeyGen.sbp_piece hP hF hi).seq (VG.Proof.MlDsa.X86_64.KeyGen.bp_piece hP hF hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.X86_64.KeyGen.RowI p i (VG.Proof.MlDsa.X86_64.KeyGen.tIs p fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.X86_64.KeyGen.mulAdd_piece hP hF hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.X86_64.KeyGen.flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R np nj p.k s) :
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r12, 0)) p.pkLen = pkK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) := by
  rw [hF.pk, Proof.MlKem.bytesAt_add, h.pk0, show VG.Proof.MlKem.X86_64.pa s (.r12, 0) = s.gpr .r12 + BitVec.ofNat 64 0 from rfl,
    add_ofNat_zero, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r12) 32 320 p.k, pkK, VG.Proof.MlDsa.X86_64.KeyGen.t1Max_eq]
  exact congrArg _ (VG.Proof.MlDsa.X86_64.KeyGen.flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 64)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ)) 64) :
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 0)) p.skLen = skK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) (VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ) := by
  have e0 : VG.Proof.MlKem.X86_64.pa s (.r13, 0) = s.gpr .r13 := by rw [VG.Proof.MlKem.X86_64.pa, add_ofNat_zero]
  have h0 : bytesAt s.mem (s.gpr .r13) 32 = VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ := by rw [← e0]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .r13 + BitVec.ofNat 64 32) 32 = VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .r13 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ)) 64 := htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, e0, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r13) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r13) (oT0 p) 416 p.k, skK]
  rw [VG.Proof.MlDsa.X86_64.KeyGen.flatMap_congr_mem (g := fun r => VG.Spec.MlDsa.bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    VG.Proof.MlDsa.X86_64.KeyGen.flatMap_congr_mem (g := fun i => VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.X86_64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (.r13, 64)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ)) 64

theorem trHash_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) : VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) (VG.Proof.MlDsa.X86_64.KeyGen.KFin p) (trHash p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hc : hashChk (VG.Proof.MlDsa.X86_64.KeyGen.kgB p) (VG.Proof.MlDsa.X86_64.KeyGen.kgW p) [((.r12, 0), p.pkLen)] 136 (.r13, 64) 64 = true := by
    layk [hF.pk, hF.sk]
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := VG.Proof.MlDsa.X86_64.KeyGen.Two p) (RelCT.mono (hash_tr (VG.Proof.MlDsa.X86_64.KeyGen.kgB_bases p) hc (by decide))
    (fun _ _ h => h.lrel) fun _ _ h => h) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHash
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.hash_okM hc (by decide) L) fun s' ⟨⟨hP', ho⟩, hx⟩ => ⟨A, S, R, ?_, ?_⟩
  · have hc : VG.Proof.MlDsa.X86_64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ p.k [(VG.Impl.MlKem.X86_64.sc 0, 200), (VG.Impl.MlKem.X86_64.sc 200, 640), ((.r13, 64), 64)] :=
      (KRChk.rbx hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords]; omega)).append (ws₁ := [_])
      ((KRChk.rbx hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, Spec.MlDsa.scratchWords]; omega)).append (ws₁ := [_])
      (KRChk.r13 hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega)))
    exact h.keep hF hp hP'.b hx (hP'.cs .r15 (by decide)) hc
  · simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, VG.Proof.MlDsa.X86_64.KeyGen.pk_bytes hF h] at ho
    rw [hP'.pa (show Reg.r13 ∈ calleeSaved by decide), ho, VG.Proof.MlDsa.X86_64.KeyGen.shake31', ← Proof.MlKem.shake256_eq]
    rfl

/-! ## The return -/

theorem outcome_of {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (hl : 0 < p.ℓ) (hG : VG.Proof.MlDsa.X86_64.KeyGen.Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ)) (R.setWidth 32)
      (pkK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ), skK p A S (VG.Proof.MlDsa.X86_64.KeyGen.rhoOf p σ) (VG.Proof.MlDsa.X86_64.KeyGen.kOf p σ)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (VG.Proof.MlDsa.X86_64.KeyGen.xiOf σ) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (VG.Proof.MlDsa.X86_64.KeyGen.idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem epi_piece {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (VG.Proof.MlDsa.X86_64.KeyGen.KFin p) (fun σ s => abiPreserved σ s ∧ (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).post σ s) (.block VG.Impl.MlKem.X86_64.topEpi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, VG.Proof.MlDsa.X86_64.KeyGen.rel_of (Q := VG.Proof.MlDsa.X86_64.KeyGen.Two p) (taintRel [.rbx] (fun x y h => VG.Proof.MlDsa.X86_64.KeyGen.two_rbx h)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => VG.Proof.MlDsa.X86_64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.pa s (VG.Impl.MlKem.X86_64.sc (VG.Impl.MlKem.X86_64.oSV + 8 * k))) 8 := fun k hk =>
    L.cR (p := VG.Impl.MlKem.X86_64.sc (VG.Impl.MlKem.X86_64.oSV + 8 * k)) (l := 8) (by lay) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (WP.mx (VG.Proof.MlDsa.X86_64.KeyGen.noLd_spec (by rfl)) (topEpi_ok h.kc.top hin)) fun s' ⟨⟨hr, hg, hm⟩, hx⟩ =>
    ⟨⟨hg.1, hg.2, by rw [← VG.Proof.MlDsa.X86_64.KeyGen.MX, ← VG.Proof.MlDsa.X86_64.KeyGen.MX, hx, h.kc.mx]⟩, ?_⟩
  have e12 : VG.Proof.MlKem.X86_64.pa s (.r12, 0) = σ.gpr .rsi := by rw [VG.Proof.MlKem.X86_64.pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : VG.Proof.MlKem.X86_64.pa s (.r13, 0) = σ.gpr .rdx := by rw [VG.Proof.MlKem.X86_64.pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Spec.MlDsa.Outcome _ _ _
  rw [hr, h.r15, hm, ← e12, ← e13, VG.Proof.MlDsa.X86_64.KeyGen.pk_bytes hF h, VG.Proof.MlDsa.X86_64.KeyGen.sk_bytes hF h htr]
  exact VG.Proof.MlDsa.X86_64.KeyGen.outcome_of (by have := hF.l; omega) h.good

/-! ## The function -/

theorem rest_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => VG.Proof.MlDsa.X86_64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.X86_64.KeyGen.KFin p) (rest P p) := by
  unfold rest
  refine (VG.Proof.MlDsa.X86_64.KeyGen.copies_piece hF).seq (Piece.seq (J := VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) 0 0) ?_ (Piece.seq (J := VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ 0) ?_
    (Piece.seq (J := VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) ?_ (VG.Proof.MlDsa.X86_64.KeyGen.trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => VG.Proof.MlDsa.X86_64.KeyGen.KRx p r 0 0) (p.ℓ + p.k) 0 fun r _ hr => VG.Proof.MlDsa.X86_64.KeyGen.packS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) j 0) p.ℓ 0 fun j _ hj => VG.Proof.MlDsa.X86_64.KeyGen.nttS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => VG.Proof.MlDsa.X86_64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) p.k 0 fun i _ hi => VG.Proof.MlDsa.X86_64.KeyGen.row_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.X86_64.KeyGen.Piece p (fun σ s => s = σ) (fun σ s => abiPreserved σ s ∧ (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).post σ s) (keyGen P p) :=
  (VG.Proof.MlDsa.X86_64.KeyGen.pro_piece hF).seq ((VG.Proof.MlDsa.X86_64.KeyGen.seeds_piece hF).seq ((VG.Proof.MlDsa.X86_64.KeyGen.sampAll_piece hP hF).seq ((VG.Proof.MlDsa.X86_64.KeyGen.sampS_piece hP hF).seq
    ((VG.Proof.MlDsa.X86_64.KeyGen.rest_piece hP hF).seq (VG.Proof.MlDsa.X86_64.KeyGen.epi_piece hF)))))

theorem keyGen_correct {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) (σ : State) (hp : (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre σ) :
    ∃ t s', Exec isa (keyGen P p) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).post σ s' :=
  (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_piece hP hF).ok σ σ hp rfl

theorem keyGen_ct {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) {p : Params} (hF : VG.Proof.MlDsa.X86_64.KeyGen.PFacts p) :
    ConstantTime isa (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pre (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).pub (keyGen P p) :=
  relStart (Q := fun _ _ => True) (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_piece hP hF).tr

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, VG.Proof.MlDsa.X86_64.KeyGen.scrLen p⟩]

theorem keyGen_implies (p : Params) (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    (VG.Proof.MlDsa.X86_64.KeyGen.kgK p).Implies (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  { pre := by sig_implies_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs]
    post := by sig_implies_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs]
    pub := by
      intro s₁ s₂ _ _ h
      sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs] at h
      obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
      exact ⟨hdi, hsi, hdx, hcx, hsp, hb⟩
    sat := by
      rcases hp with rfl | rfl | rfl
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using VG.Proof.MlDsa.X86_64.KeyGen.keyGenSat Spec.MlDsa.mlDsa44
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using VG.Proof.MlDsa.X86_64.KeyGen.keyGenSat Spec.MlDsa.mlDsa65
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, VG.Proof.MlDsa.X86_64.KeyGen.kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using VG.Proof.MlDsa.X86_64.KeyGen.keyGenSat Spec.MlDsa.mlDsa87 }

end VG.Proof.MlDsa.X86_64.KeyGen

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen (Prims keyGen)

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls. -/
theorem keyGen_verified {P : VG.Impl.MlDsa.X86_64.KeyGen.Prims} (hP : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk P) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86_64.target (keyGen P p) (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  Verified.of_correct (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_correct hP (VG.Proof.MlDsa.X86_64.KeyGen.pfacts hp)) (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_ct hP (VG.Proof.MlDsa.X86_64.KeyGen.pfacts hp)) (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_implies p hp)

end VG.Proof.MlDsa.X86_64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst`. -/
section

/-!
# ML-DSA key generation on x86-64, with this library's primitives

The x86-64 implementations of the primitives (`prims`) are verified, use at
most 16 bytes of stack (24 for `vg_mldsa_rej_ntt_poly4`), and never write
`rsp` but by calls nested at most twice (three times for
`vg_mldsa_rej_ntt_poly4`), with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), so key generation with them is verified
(`keyGen_verifiedWith`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl Comp Same Same.ok Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

/-- A function of the polynomial arithmetic satisfies what the proofs of key generation need of it. -/
theorem calleeOf {k : Nat → Contract isa} {c : Prog isa} (h : FnOk k c) : VG.Proof.MlDsa.X86_64.KeyGen.Callee c k :=
  ⟨⟨0, by decide, h.ver⟩, h.nosp, h.depth⟩

theorem prims_okWith (v : ArithImpl) : VG.Proof.MlDsa.X86_64.KeyGen.PrimsOk (primsWith v.code) where
  ntt := VG.Proof.MlDsa.X86_64.KeyGen.calleeOf v.ok.ntt
  invNtt := VG.Proof.MlDsa.X86_64.KeyGen.calleeOf v.ok.invNtt
  mul := VG.Proof.MlDsa.X86_64.KeyGen.calleeOf v.ok.mul
  mulAdd := VG.Proof.MlDsa.X86_64.KeyGen.calleeOf v.ok.mulAdd
  add := VG.Proof.MlDsa.X86_64.KeyGen.calleeOf v.ok.add
  rejNtt := (⟨⟨16, by decide, Sample.rejNTT_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    VG.Proof.MlDsa.X86_64.KeyGen.Callee prims.rejNtt _)
  rejBounded := (⟨⟨16, by decide, Sample.rejBounded_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    VG.Proof.MlDsa.X86_64.KeyGen.Callee prims.rejBounded _)
  power2Round := (⟨⟨0, by decide, Round.power2Round_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    VG.Proof.MlDsa.X86_64.KeyGen.Callee prims.power2Round _)
  simpleBitPack := (⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, nosp_of (by decide +kernel),
    by decide +kernel⟩ : VG.Proof.MlDsa.X86_64.KeyGen.Callee prims.simpleBitPack _)
  bitPack := (⟨⟨0, by decide, Pack.bitPack_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    VG.Proof.MlDsa.X86_64.KeyGen.Callee prims.bitPack _)
  rej4 := ⟨v.ok.rej4.ver, v.ok.rej4.nosp, v.ok.rej4.depth⟩

/-! For any implementation of the polynomial arithmetic, that key
generation never writes `rsp` is checked by evaluating it with every
function of it empty (`keyGen_same`, as `sign_same`). -/

theorem keyGen_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h2 : mc B.invNtt = true) (h3 : mc B.mul = true) (h4 : mc B.mulAdd = true) (h5 : mc B.add = true)
    (h6 : mc B.rej4 = true) (p : Spec.MlDsa.Params) : Same m (keyGen (primsWith B) p) (keyGen (primsWith .empty) p) := by
  unfold keyGen
  same_tac hm

theorem keyGen0_sp {p : Spec.MlDsa.Params}
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    (keyGen (primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

variable (v : ArithImpl) {p : Spec.MlDsa.Params}
  (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
include hp

theorem keyGen_spSafe : (keyGen (primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (VG.Proof.MlDsa.X86_64.KeyGen.keyGen_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.invNtt.sp) (Code.allInstrs_of_all v.ok.mul.sp)
    (Code.allInstrs_of_all v.ok.mulAdd.sp) (Code.allInstrs_of_all v.ok.add.sp)
    (Code.allInstrs_of_all v.ok.rej4.sp) p) (VG.Proof.MlDsa.X86_64.KeyGen.keyGen0_sp hp))

theorem keyGen_verifiedWith :
    Verified X86_64.target (keyGen (primsWith v.code) p) (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  VG.Proof.MlDsa.X86_64.KeyGen.keyGen_verified (VG.Proof.MlDsa.X86_64.KeyGen.prims_okWith v) p hp

end VG.Proof.MlDsa.X86_64.KeyGen

end
