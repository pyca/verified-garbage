import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Impl.MlKem.X86_64.EncapsH

/-!
# ML-KEM on x86-64: encapsulation, its contract, layout, entry and hashes

For a parameter set `L`: the contract the proof is written against
(`encapsK L`, which the shared contract implies, and which requires `h` to be
`H(ek)`), the layout of the function's buffers (`ek` and `m` in `r14` and
`rbp`, which may overlap each other; `scratch`, `key`, `ct` in `rbx`, `r12`,
`r13`; and `h` in `rsi`, until it is copied), what holds throughout (`EC`:
`Top`, and `ek` and `m` at their pointers), the checks of the layout every
piece needs (`EcWf L`), the prologue, `h` copied to `H` (`hCopy_ok`) and
`G(m ‖ H(ek))` (`hashes_ok`), and the context `K-PKE.Encrypt` runs in
(`ecC`, which also keeps `K`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemEncapsH L (ek = rdi, h = rsi, m = rdx, key = rcx, ct = r8, scratch = r9) -> eax`, with 32 bytes of stack. -/
def encapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.ekLen⟩, ⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, 32⟩, ⟨s.gpr .r8, L.ctLen⟩, ⟨s.gpr .r9, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rcx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .r8, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .r9, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r9, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r9, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 32⟩ ⟨s.gpr .r8, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rcx, 32⟩ ⟨s.gpr .r9, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .r8, L.ctLen⟩ ⟨s.gpr .r9, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, L.ctLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .r9, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, L.ctLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r9, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.ekLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + L.ctLen ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + L.scr ≤ 2 ^ 64 ∧
    bytesAt s.mem (s.gpr .rsi) 32 = H (bytesAt s.mem (s.gpr .rdi) L.ekLen)
  post s s' :=
    Outcome (fun iters => encapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.ekLen)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rcx) 32, bytesAt s'.mem (s.gpr .r8) L.ctLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    ekRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.ekLen) = ekRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.ekLen)

theorem pw6 {α : Type} {R : α → α → Prop} {a b c d e f : α} (hab : R a b) (hac : R a c) (had : R a d)
    (hae : R a e) (haf : R a f) (hbc : R b c) (hbd : R b d) (hbe : R b e) (hbf : R b f) (hcd : R c d) (hce : R c e)
    (hcf : R c f) (hde : R d e) (hdf : R d f) (hef : R e f) : [a, b, c, d, e, f].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩

theorem fa6 {α : Type} {p : α → Prop} {a b c d e f : α} (ha : p a) (hb : p b) (hc : p c) (hd : p d) (he : p e)
    (hf : p f) : ∀ x ∈ [a, b, c, d, e, f], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

namespace Encaps

open VG.Impl.MlKem.X86_64.EncapsH

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev ecM : List (Reg × Reg) := [(.rbx, .r9), (.rbp, .rdx), (.r12, .rcx), (.r13, .r8), (.r14, .rdi)]
/-- `ek` and `m`. -/
abbrev ecR : List (Reg × Nat) := [(.r14, L.ekLen), (.rbp, 32)]
/-- `scratch`, `key` and `ct`. -/
abbrev ecW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32), (.r13, L.ctLen)]
abbrev ecB : List (Reg × Nat) := ecR L ++ ecW L

/-- The buffers of the entry: those of encapsulation, and `h` at `rsi`. -/
abbrev ecRH : List (Reg × Nat) := ecR L ++ [(.rsi, 32)]

theorem ecB_bases : ∀ b ∈ ecB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [bases]

/-- A piece that writes `ws` keeps `EC`. -/
def ecChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (ecB L) ws && keepB (ecB L) ws (.r14, 0) L.ekLen && keepB (ecB L) ws (.rbp, 0) 32

def eckChk (ws : List (Ptr × Nat)) : Bool := ecChk L ws && keepB (ecB L) ws (sc oG) 32

/-- The writes of `G`. -/
abbrev hW₃ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]

/-- What every piece of encapsulation needs of the layout, evaluated for each parameter set. -/
structure EcWf : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ ecB L, b.2 < 2 ^ 32
  smallH : ∀ b ∈ ecRH L ++ ecW L, b.2 < 2 ^ 32
  -- `h` to `H`
  hc : copyChk (ecRH L ++ ecW L) (ecW L) (sc oH) (.rsi, 0) 32 = true
  hcK : ecChk L [(sc oH, 32)] = true
  -- the hashes
  h₁ : copyChk (ecB L) (ecW L) (sc oM) (.rbp, 0) 32 = true
  h₁K : ecChk L [(sc oM, 32)] = true
  h₁H : keepB (ecB L) [(sc oM, 32)] (sc oH) 32 = true
  h₃ : hashChk (ecB L) (ecW L) [(sc oM, 32), (sc oH, 32)] 72 (sc oG) 64 = true
  h₃K : ecChk L (hW₃) = true
  h₃M : keepB (ecB L) (hW₃) (sc oM) 32 = true
  enc : Enc.encChk L (ecB L) (ecW L) (eckChk L) (.r14, 0) = true
  -- the outputs
  o₁ : copyChk (ecB L) (ecW L) (.r12, 0) (sc oG) 32 = true
  o₁K : ecChk L [((.r12, 0), 32)] = true
  o₁C : keepB (ecB L) [((.r12, 0), 32)] (sc L.oCT) L.ctLen = true
  o₂ : copyChk (ecB L) (ecW L) (.r13, 0) (sc L.oCT) L.ctLen = true
  o₂K : ecChk L [((.r13, 0), L.ctLen)] = true
  o₂G : keepB (ecB L) [((.r13, 0), L.ctLen)] (.r12, 0) 32 = true
  sv : ∀ k < 6, inB (ecB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (ecB L) (sc 0) 1 = true ∧ inB (ecB L) (.r12, 0) 1 = true ∧ inB (ecB L) (.r13, 0) 1 = true ∧
    inB (ecB L) (.r14, 0) 1 = true
  hT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (sc oM) (.rbp, 0) 32)
    h).isSome = true
  oT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r12, 0) (sc oG) 32)
    h).isSome = true
  oT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r13, 0) (sc L.oCT) L.ctLen)
    h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r14]) (copy (sc oSB) (.r14, 0 + 384 * L.k) 32)
    h).isSome = true

theorem ecM_bases : ∀ p ∈ ecM, p.1 ∈ bases := by decide

section
variable {L : Kem} {σ : State}

/-- The layout, with `h` at `rsi` (before it is copied). -/
theorem ecLayH (W : EcWf L) (hp : (encapsK L).pre σ) {s : State} (h : Top ecM σ s) (hsi : s.gpr .rsi = σ.gpr .rsi) :
    Lay (ecRH L) (ecW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, r1, r2, r3, r4, r5, r6, k1, k2, k3, k4, k5,
    k6, n1, n2, n3, n4, n5, n6, _⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r9 := h.regs (.rbx, .r9) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdx := h.regs (.rbp, .rdx) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rcx := h.regs (.r12, .rcx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .r8 := h.regs (.r13, .r8) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.smallH (pw6 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa6 ?_ ?_ ?_ ?_ ?_ ?_)
    (fa6 ?_ ?_ ?_ ?_ ?_ ?_) (fa6 ?_ ?_ ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa6 ?_ ?_ ?_ ?_ ?_ ?_) <;>
    simp only [e1, e2, e3, e4, e5, hsi, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d9
  · exact fun _ => d7
  · exact fun _ => d8
  · exact fun _ => d6
  · exact fun _ => d4
  · exact fun _ => d5
  · exact fun _ => d11.symm
  · exact fun _ => d12.symm
  · exact fun _ => d10
  exacts [k1, k3, k2, k6, k4, k5, n1, n3, n2, n6, n4, n5,
    mem ⟨σ.gpr .rdi, L.ekLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rsi, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r9, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rcx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .r8, L.ctLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r3, r2, r6, r4, r5]

/-- The layout of encapsulation. -/
theorem ecLay (W : EcWf L) (hp : (encapsK L).pre σ) {s : State} (h : Top ecM σ s) : Lay (ecR L) (ecW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, r1, r2, r3, r4, r5, r6, k1, k2, k3, k4, k5,
    k6, n1, n2, n3, n4, n5, n6, _⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r9 := h.regs (.rbx, .r9) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdx := h.regs (.rbp, .rdx) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rcx := h.regs (.r12, .rcx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .r8 := h.regs (.r13, .r8) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_)
    (fa5 ?_ ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, e5, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d9
  · exact fun _ => d7
  · exact fun _ => d8
  · exact fun _ => d11.symm
  · exact fun _ => d12.symm
  · exact fun _ => d10
  exacts [k1, k3, k6, k4, k5, n1, n3, n6, n4, n5,
    mem ⟨σ.gpr .rdi, L.ekLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r9, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rcx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .r8, L.ctLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r3, r6, r4, r5]

end

/-- `ek`, `m`, and `G(m ‖ H(ek))`. -/
abbrev ecEk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.ekLen
abbrev ecMs (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) 32
abbrev ecG (L : Kem) (σ : State) : List Byte × List Byte := G (ecMs σ ++ H (ecEk L σ))

/-- What holds throughout. -/
structure EC (L : Kem) (σ s : State) : Prop where
  top : Top ecM σ s
  ek : bytesAt s.mem (pa s (.r14, 0)) L.ekLen = ecEk L σ
  m : bytesAt s.mem (pa s (.rbp, 0)) 32 = ecMs σ

section
variable {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ)
include W hp

theorem EC.lay {s : State} (h : EC L σ s) : Lay (ecR L) (ecW L) s := ecLay W hp h.top

theorem EC.step {s s' : State} (h : EC L σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : ecChk L ws = true) : EC L σ s' := by
  simp only [ecChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP ecM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.ek,
    by rw [L₀.keepBytes hP hc.2]; exact h.m⟩

end

/-- What `K-PKE.Encrypt` keeps: `EC`, and `K` at `G`. -/
structure ECK (L : Kem) (σ s : State) : Prop where
  ec : EC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (ecG L σ).1

theorem ECK.step {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) {s s' : State} (h : ECK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : eckChk L ws = true) : ECK L σ s' := by
  simp only [eckChk, Bool.and_eq_true] at hc
  exact ⟨h.ec.step W hp hP hc.1, by rw [(h.ec.lay W hp).keepBytes hP hc.2]; exact h.k⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def ecC {L : Kem} (W : EcWf L) (σ : State) : Ctx (ecR L) (ecW L) where
  Out s := (encapsK L).pre σ ∧ ECK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay h := h.2.ec.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def ecCA {L : Kem} (W : EcWf L) : Ctx (ecR L) (ecW L) where
  Out s := ∃ σ, (encapsK L).pre σ ∧ ECK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay := fun ⟨_, hp, h⟩ => h.ec.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

theorem pro_eq : pro = [.store (at_ .r9 840) .rbx, .store (at_ .r9 848) .rbp, .store (at_ .r9 856) .r12,
    .store (at_ .r9 864) .r13, .store (at_ .r9 872) .r14, .store (at_ .r9 880) .r15, .mov .rbx (.reg .r9),
    .mov .rbp (.reg .rdx), .mov .r12 (.reg .rcx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rdi),
    .mov32 .r15 (.imm 1)] := rfl

/-- After the prologue: `EC`, `h` still at `rsi` and as it was, and `r15 = 1`. -/
structure ProOut (L : Kem) (σ s : State) : Prop where
  ec : EC L σ s
  rsi : s.gpr .rsi = σ.gpr .rsi
  h : bytesAt s.mem (σ.gpr .rsi) 32 = H (ecEk L σ)
  r15 : s.gpr .r15 = 1

theorem pro_ok {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) :
    WP isa (.block pro) σ (ProOut L σ) := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, r1, r2, r3, r4, r5, r6, k1, k2, k3, k4, k5,
    k6, n1, n2, n3, n4, n5, n6, hh⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .r9, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .r9, L.scr⟩ : Region).Contains (σ.gpr .r9 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .r9 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r9 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r9 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r9 ∧ s.gpr .rbp = σ.gpr .rdx ∧ s.gpr .r12 = σ.gpr .rcx ∧ s.gpr .r13 = σ.gpr .r8 ∧
    s.gpr .r14 = σ.gpr .rdi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r9, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hek := W.small (.r14, L.ekLen) (by simp)
  refine ⟨⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h12 h13 h14, fun j hj => ?_, ?_⟩, ?_, ?_⟩, k.gpr (by decide), ?_, h15⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r9) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r6) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d3) (by simp only at hek; omega)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d9) (by decide)
  · rw [bytesAt_frame hf (by simpa using d6) (by decide)]; exact hh

/-- `h` copied to `H`. -/
theorem hCopy_ok {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) {s : State}
    (h : ProOut L σ s) :
    WP isa hCopy s fun s' => EC L σ s' ∧ bytesAt s'.mem (pa s' (sc oH)) 32 = H (ecEk L σ) ∧ s'.gpr .r15 = 1 := by
  have L₀ := ecLayH W hp h.ec.top h.rsi
  unfold hCopy
  refine WP.mono (copy_okL L₀ (dst := sc oH) (src := (.rsi, 0)) (n := 32) (by decide) W.hc) fun s' ⟨hP, hb⟩ => ?_
  refine ⟨h.ec.step W hp hP.b W.hcK, ?_, ?_⟩
  · rw [hP.pa rbx_cs, hb, pa, h.rsi, add_ofNat_zero, h.h]
  · rw [hP.cs .r15 (by decide), h.r15]

/-! ## `G(m ‖ H(ek))` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {L : Kem} (W : EcWf L) (σ s : State) : Prop :=
  Enc.EIn L (ecC W σ) (.r14, 0) (ecEk L σ) (ecMs σ) (ecG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {L : Kem} (W : EcWf L) {σ : State} (hp : (encapsK L).pre σ) {s : State}
    (h : EC L σ s) (hH : bytesAt s.mem (pa s (sc oH)) 32 = H (ecEk L σ)) (h15 : s.gpr .r15 = 1) :
    WP isa hashes s (EncI W σ) := by
  have L₀ := h.lay W hp
  unfold hashes
  -- `m` to `M`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  rw [h.m] at hb₁
  have hH₁ : bytesAt s₁.mem (pa s₁ (sc oH)) 32 = H (ecEk L σ) := by rw [L₀.keepBytes hP₁.b W.h₁H, hH]
  -- `G(m ‖ H(ek))`.
  refine WP.mono (hash_ok (ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64)
    W.h₃ (show 6 < 256 by decide) L₁) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have k₃ := k₁.step W hp hP₃.b W.h₃K
  rw [← hP₁.pa rbx_cs] at hb₁
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hb₁, hH₁, KeyGen.sha3Suffix6] at hb₃
  rw [← sha3_512_eq, ← hP₃.pa rbx_cs] at hb₃
  have hK : bytesAt s₃.mem (pa s₃ (sc oG)) 32 = (ecG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₃]; rfl
  have hr : bytesAt s₃.mem (pa s₃ sigP) 32 = (ecG L σ).2 := by
    have e := bytesAt_drop s₃.mem (pa s₃ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₃.mem (pa s₃ (sc oG)) 64).drop 32 = bytesAt s₃.mem (pa s₃ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₃]; rfl
  refine ⟨⟨⟨hp, k₃, hK⟩, k₃.ek, ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₃.b W.h₃M, hb₁]
  · rw [hP₃.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

end Encaps

end VG.Proof.MlKem.X86_64
