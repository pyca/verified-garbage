module

public import VerifiedGarbage.Impl.MlDsa.X86_64.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Seeds
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.MlDsa.X86_64.PkTr
meta import VerifiedGarbage.Spec.MlDsa.PkTr
meta import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
meta import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base
meta import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on x86-64: `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. The function
(`Impl/MlDsa/X86_64/PkTr.lean`) in ML-KEM's setting of top-level functions
(`Proof/MlKem/X86_64/`): the contract the proof is written against (`ptK p`,
which the shared contract implies, `ptK_implies`), the layout (`pk` in
`r12`, read; `scratch` and `tr` in `rbx` and `r13`, written), the prologue
(`pro_ok`, as key generation's), the hash (`hash_ok`, `hash_tr`) and the
epilogue (`topEpi_ok`). Nothing is leaked but the pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.PkTr

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc topEpi oSV at_)
open VG.Impl.MlDsa.X86_64.PkTr
open VG.Proof.MlDsa.X86_64.KeyGen (MX noLd noLd_spec noLd_seq hash_noLd shake31')
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- `vg_mldsa*_pk_tr(pk = rdi, tr = rsi, scratch = rdx)`, with 32 bytes of stack. -/
def ptK (p : Params) : Contract isa where
  pre s :=
    32 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, p.pkLen⟩] ∧ s.wr = [⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, p.pkLen⟩ ⟨s.gpr .rsi, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, p.pkLen⟩ ⟨s.gpr .rdx, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rdx, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, p.pkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, scrLen p⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, p.pkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + scrLen p ≤ 2 ^ 64
  post s s' := bytesAt s'.mem (s.gpr .rsi) 64 = Spec.MlDsa.pkTr (bytesAt s.mem (s.gpr .rdi) p.pkLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## The layout -/

/-- The pointers the function keeps. -/
abbrev ptM : List (Reg × Reg) := [(.rbx, .rdx), (.r12, .rdi), (.r13, .rsi)]
/-- `pk`. -/
abbrev ptR (p : Params) : List (Reg × Nat) := [(.r12, p.pkLen)]
/-- `scratch` and `tr`. -/
abbrev ptW (p : Params) : List (Reg × Nat) := [(.rbx, scrLen p), (.r13, 64)]

theorem ptB_bases (p : Params) : ∀ b ∈ ptR p ++ ptW p, b.1 ∈ bases := fun b hb => by
  simp only [ptR, ptW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp [bases]
theorem ptM_bases : ∀ q ∈ ptM, q.1 ∈ bases := by decide

/-- The parameter sets. -/
abbrev PS (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

theorem scr_lt {p : Params} (hp : PS p) : 888 ≤ scrLen p ∧ scrLen p < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem pk_lt {p : Params} (hp : PS p) : p.pkLen < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem pw3 {α : Type} {R : α → α → Prop} {a b c : α} (hab : R a b) (hac : R a c) (hbc : R b c) :
    [a, b, c].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac⟩, hbc⟩

theorem ptLay {p : Params} (hp' : PS p) {σ s : State} (hp : (ptK p).pre σ) (h : Top ptM σ s) :
    Lay (ptR p) (ptW p) s := by
  obtain ⟨_, hrd, hwr, d1, d2, d3, r1, r2, r3, k1, k2, k3, n1, n2, n3⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rdx := h.regs (.rbx, .rdx) (by decide)
  have e2 : s.gpr .r12 = σ.gpr .rdi := h.regs (.r12, .rdi) (by decide)
  have e3 : s.gpr .r13 = σ.gpr .rsi := h.regs (.r13, .rsi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of (fa3 (pk_lt hp') (scr_lt hp').2 (by decide)) (pw3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa3 ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa3 ?_ ?_ ?_) <;> simp only [e1, e2, e3, h.rsp, retR]
  exacts [fun _ => d2, fun _ => d1, fun _ => d3.symm, k1, k3, k2, n1, n3, n2,
    mem ⟨σ.gpr .rdi, p.pkLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rdx, scrLen p⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, 64⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r3, r2]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  top : Top ptM σ s
  pk : bytesAt s.mem (pa s (.r12, 0)) p.pkLen = bytesAt σ.mem (σ.gpr .rdi) p.pkLen
  mx : MX s = MX σ

/-- After the hash. -/
structure KH (p : Params) (σ s : State) : Prop where
  top : Top ptM σ s
  tr : bytesAt s.mem (pa s (.r13, 0)) 64 = Spec.MlDsa.pkTr (bytesAt σ.mem (σ.gpr .rdi) p.pkLen)
  mx : MX s = MX σ

/-- Two runs of the function, each related by `I` to an entry state. -/
abbrev R (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (ptK p).pre (ptK p).pub I

/-! ## The prologue -/

theorem pro_eq : pro = [.store (at_ .rdx 840) .rbx, .store (at_ .rdx 848) .rbp, .store (at_ .rdx 856) .r12,
    .store (at_ .rdx 864) .r13, .store (at_ .rdx 872) .r14, .store (at_ .rdx 880) .r15, .mov .rbx (.reg .rdx),
    .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {p : Params} (hp' : PS p) {σ : State} (hp : (ptK p).pre σ) :
    WP isa (.block pro) σ (KC p σ) := by
  have hp'' := hp
  obtain ⟨_, hrd, hwr, d1, d2, d3, r1, r2, r3, k1, k2, k3, n1, n2, n3⟩ := hp''
  have hS : ⟨σ.gpr .rdx, scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have hs : 888 ≤ scrLen p := (scr_lt hp').1
  have hs2 : scrLen p < 2 ^ 64 := by have := (scr_lt hp').2; omega
  have c : ∀ o, o + 8 ≤ 888 → (⟨σ.gpr .rdx, scrLen p⟩ : Region).Contains (σ.gpr .rdx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' (by omega_arith) (by omega_arith)
  have w : ∀ o, o + 8 ≤ 888 → InRegions σ.wr (σ.gpr .rdx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega_arith); have w1 := w 848 (by omega_arith); have w2 := w 856 (by omega_arith)
  have w3 := w 864 (by omega_arith); have w4 := w 872 (by omega_arith); have w5 := w 880 (by omega_arith)
  rw [pro_eq]
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.WP.mx (noLd_spec (by rfl)) (WP.keep [.rbx, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rdx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rdx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rdx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rdx ∧ s.gpr .r12 = σ.gpr .rdi ∧ s.gpr .r13 = σ.gpr .rsi)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide))) fun s ⟨⟨⟨hm, hbx, h12, h13⟩, k⟩, hx⟩ => ?_
  have hf : Frame [⟨σ.gpr .rdx, scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega_arith))).writeW (List.mem_singleton_self _) _ (c 856 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega_arith))).writeW (List.mem_singleton_self _) _ (c 872 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega_arith)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa3 hbx h12 h13, fun j hj => ?_, ?_⟩, ?_, hx⟩
  · simp only [pa, hbx, hm]
    exact VG.Proof.MlKem.X86_64.stores_read σ.mem (σ.gpr .rdx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r3) (by decide)
  · rw [pa, h12, add_ofNat_zero]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using d2) (by omega_arith)

theorem pro_tr (p : Params) : RelCT isa (R p fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rdx, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa3 pub.2.2.1 pub.1 pub.2.1) (by taint_decide)

/-! ## The hash -/

theorem hash_chk {p : Params} (hp : PS p) :
    hashChk (ptR p ++ ptW p) (ptW p) [((.r12, 0), p.pkLen)] 136 (.r13, 0) 64 = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem top_chk {p : Params} (hp : PS p) :
    topChk (ptR p ++ ptW p) [(sc 0, 200), (sc 200, 640), ((.r13, 0), 64)] = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem hash_ok' {p : Params} (hp' : PS p) {σ s : State} (hp : (ptK p).pre σ) (h : KC p σ s) :
    WP isa (hash p) s (KH p σ) := by
  have L := ptLay hp' hp h.top
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.WP.mx (noLd_spec (hash_noLd _ _ _ _ _))
    (hash_ok (ptB_bases p) (hash_chk hp') (by decide) L)) fun s' ⟨⟨hP, ho⟩, hx⟩ => ?_
  refine ⟨h.top.step L hP.b ptM_bases (top_chk hp'), ?_, hx.trans h.mx⟩
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.pk] at ho
  rw [hP.pa (show Reg.r13 ∈ calleeSaved by decide), ho, shake31', ← Proof.MlKem.shake256_eq]
  rfl

theorem two {p : Params} (hp' : PS p) {σ₁ σ₂ x y : State} (p₁ : (ptK p).pre σ₁) (p₂ : (ptK p).pre σ₂)
    (pub : (ptK p).pub σ₁ σ₂) (h₁ : KC p σ₁ x) (h₂ : KC p σ₂ y) : LRel (ptR p) (ptW p) x y := by
  obtain ⟨e1, e2, e3, e4⟩ := pub
  refine ⟨ptLay hp' p₁ h₁.top, ptLay hp' p₂ h₂.top, fun b hb => ?_, by rw [h₁.top.rsp, h₂.top.rsp, e4]⟩
  simp only [ptR, ptW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rw [h₁.top.regs (.r12, .rdi) (by decide), h₂.top.regs (.r12, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rdx) (by decide), h₂.top.regs (.rbx, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rsi) (by decide), h₂.top.regs (.r13, .rsi) (by decide), e2]

theorem hash_tr' {p : Params} (hp' : PS p) : RelCT isa (R p (KC p)) (hash p) fun _ _ => True :=
  RelCT.mono (hash_tr (ptB_bases p) (hash_chk hp') (by decide))
    (fun _ _ ⟨_, _, p₁, p₂, pub, h₁, h₂⟩ => two hp' p₁ p₂ pub h₁ h₂) fun _ _ h => h

/-! ## The epilogue -/

theorem epi_ok {p : Params} (hp' : PS p) {σ s : State} (hp : (ptK p).pre σ) (h : KH p σ s) :
    WP isa (.block topEpi) s fun s' => abiPreserved σ s' ∧ (ptK p).post σ s' := by
  have L := ptLay hp' hp h.top
  have hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
    L.cR (p := sc (oSV + 8 * k)) (l := 8) (by
      rcases hp' with rfl | rfl | rfl <;> rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (VG.Proof.MlDsa.X86_64.KeyGen.WP.mx (noLd_spec (by rfl)) (topEpi_ok h.top hin))
    fun s' ⟨⟨_, hg, hm⟩, hx⟩ => ⟨⟨hg.1, hg.2, by rw [← MX, ← MX, hx, h.mx]⟩, ?_⟩
  have e13 : pa s (.r13, 0) = σ.gpr .rsi := by rw [pa, h.top.regs (.r13, .rsi) (by decide), add_ofNat_zero]
  show bytesAt s'.mem (σ.gpr .rsi) 64 = _
  rw [hm, ← e13]
  exact h.tr

theorem epi_tr (p : Params) : RelCT isa (R p (KH p)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.top.regs (.rbx, .rdx) (by decide), h₂.top.regs (.rbx, .rdx) (by decide), pub.2.2.1]) (by taint_decide)

/-! ## The function -/

theorem pkTr_correct {p : Params} (hp' : PS p) (σ : State) (hp : (ptK p).pre σ) :
    ∃ t s', Exec isa (pkTr p) σ t s' ∧ abiPreserved σ s' ∧ (ptK p).post σ s' :=
  WP.seq (WP.mono (pro_ok hp' hp) fun _ h => WP.seq (WP.mono (hash_ok' hp' hp h) fun _ h' => epi_ok hp' hp h'))

theorem pkTr_ct {p : Params} (hp' : PS p) : ConstantTime isa (ptK p).pre (ptK p).pub (pkTr p) :=
  relStart (RelCT.seq (relInv (fun σ s hp hs => by subst hs; exact pro_ok hp' hp) (pro_tr p))
    (RelCT.seq (relInv (fun σ s hp hs => hash_ok' hp' hp hs) (hash_tr' hp')) (epi_tr p)))

/-- A state satisfying `pkTrContract`'s precondition. -/
def pkTrSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x2000, 64⟩, ⟨0x10000, scrLen p⟩]

theorem ptK_implies (p : Params) (hp : PS p) : (ptK p).Implies (Spec.MlDsa.pkTrContract p X86_64.abi 32) :=
  { pre := by sig_implies_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs]
    post := by sig_implies_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs]
    pub := by
      intro s₁ s₂ _ _ h
      sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs] at h
      obtain ⟨hsp, hdi, hsi, hdx⟩ := h
      exact ⟨hdi, hsi, hdx, hsp⟩
    sat := by
      rcases hp with rfl | rfl | rfl
      · sig_implies_sat [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs]
          [pkTrSat] using pkTrSat mlDsa44
      · sig_implies_sat [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs]
          [pkTrSat] using pkTrSat mlDsa65
      · sig_implies_sat [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, ptK, X86_64.abi, VG.X86_64.argRegs]
          [pkTrSat] using pkTrSat mlDsa87 }

theorem pkTr_verified (p : Params) (hp : PS p) :
    Verified X86_64.target (pkTr p) (Spec.MlDsa.pkTrContract p X86_64.abi 32) :=
  Verified.of_correct (pkTr_correct hp) (pkTr_ct hp) (ptK_implies p hp)

theorem pkTr44_verified : Verified X86_64.target (pkTr mlDsa44) (Spec.MlDsa.pkTrContract mlDsa44 X86_64.abi 32) :=
  pkTr_verified _ (.inl rfl)
theorem pkTr65_verified : Verified X86_64.target (pkTr mlDsa65) (Spec.MlDsa.pkTrContract mlDsa65 X86_64.abi 32) :=
  pkTr_verified _ (.inr (.inl rfl))
theorem pkTr87_verified : Verified X86_64.target (pkTr mlDsa87) (Spec.MlDsa.pkTrContract mlDsa87 X86_64.abi 32) :=
  pkTr_verified _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86_64.PkTr
