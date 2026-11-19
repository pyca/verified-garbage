module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
public import VerifiedGarbage.Proof.MlKem.X86_64.KgRow
import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.PolyW
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public import VerifiedGarbage.Impl.MlKem.X86_64.KeyGenH16
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeKgRows
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.X86_64.DcDec

/-! ### `MlKem.X86_64.KgNtt`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_keygen_ntt`

The contract (`kgNttK`) and the steps of `KpkeKgRows.kgNtt`: the prologue
saves the callee-saved registers in `scratch` (`KpkeMul.slots`) and keeps
the pointers in registers; `s` widened to `u32`s in `s` (`widenIn_ok`);
`keygen_mul`'s first loop in the MXCSR region (`step_ok`, as
`KgMul.nttStep16_ok`): `NTT(s[j])` in place and `NTT(e[j])` to `e[j]`;
`ByteEncode₁₂(ŝ[j])` to `dk` (`enc12In_ok`); the epilogue.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open DecMul (in_c sub_c sub_c0 sub_v)
open EncMul (hiR sub_hi in_vec)
open KgMul (vv_dis vr_dis vc0_dis vc_dis)

/-- `vg_mlkem*_kpke_keygen_ntt(dk = rdi, s = rsi, e = rdx, se = rcx, scratch = r8)` of rank `k`. -/
def kgNttK (k : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rcx, 1024 * k⟩] ∧
    s.wr = [⟨s.gpr .rdi, 384 * k⟩, ⟨s.gpr .rsi, 1024 * k⟩, ⟨s.gpr .rdx, 1024 * k⟩, ⟨s.gpr .r8, 4096⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * k⟩ ⟨s.gpr .rsi, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * k⟩ ⟨s.gpr .rdx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * k⟩ ⟨s.gpr .rcx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * k⟩ ⟨s.gpr .r8, 4096⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 1024 * k⟩ ⟨s.gpr .rdx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 1024 * k⟩ ⟨s.gpr .rcx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 1024 * k⟩ ⟨s.gpr .r8, 4096⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 1024 * k⟩ ⟨s.gpr .rcx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 1024 * k⟩ ⟨s.gpr .r8, 4096⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 1024 * k⟩ ⟨s.gpr .r8, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 384 * k⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 1024 * k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 1024 * k⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 1024 * k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, 4096⟩ ∧
    (s.gpr .rdi).toNat + 384 * k ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 1024 * k ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 1024 * k ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 1024 * k ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 4096 ≤ 2 ^ 64 ∧
    VecReducedW 16 s.mem (s.gpr .rcx) (2 * k)
  post s s' :=
    let ŝ := (vecAtW 16 s.mem (s.gpr .rcx) k).map ntt
    VecIs s'.mem (s.gpr .rsi) k ŝ ∧
      VecIs s'.mem (s.gpr .rdx) k ((vecAtW 16 s.mem (s.gpr .rcx + BitVec.ofNat 64 (512 * k)) k).map ntt) ∧
      bytesAt s'.mem (s.gpr .rdi) (384 * k) = encodeVec ŝ
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace KgNtt

/-- The facts of the precondition, by name. -/
structure EP (k : Nat) (σ : State) : Prop where
  rd : σ.rd = [⟨σ.gpr .rcx, 1024 * k⟩]
  wr : σ.wr = [⟨σ.gpr .rdi, 384 * k⟩, vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, cR (σ.gpr .r8)]
  dS : Region.Disjoint ⟨σ.gpr .rdi, 384 * k⟩ (vR (σ.gpr .rsi) k)
  dE : Region.Disjoint ⟨σ.gpr .rdi, 384 * k⟩ (vR (σ.gpr .rdx) k)
  dR : Region.Disjoint ⟨σ.gpr .rdi, 384 * k⟩ ⟨σ.gpr .rcx, 1024 * k⟩
  dC : Region.Disjoint ⟨σ.gpr .rdi, 384 * k⟩ (cR (σ.gpr .r8))
  sE : Region.Disjoint (vR (σ.gpr .rsi) k) (vR (σ.gpr .rdx) k)
  sR : Region.Disjoint (vR (σ.gpr .rsi) k) ⟨σ.gpr .rcx, 1024 * k⟩
  sC : Region.Disjoint (vR (σ.gpr .rsi) k) (cR (σ.gpr .r8))
  eR : Region.Disjoint (vR (σ.gpr .rdx) k) ⟨σ.gpr .rcx, 1024 * k⟩
  eC : Region.Disjoint (vR (σ.gpr .rdx) k) (cR (σ.gpr .r8))
  rC : Region.Disjoint ⟨σ.gpr .rcx, 1024 * k⟩ (cR (σ.gpr .r8))
  xD : (retR σ).Disjoint ⟨σ.gpr .rdi, 384 * k⟩
  xS : (retR σ).Disjoint (vR (σ.gpr .rsi) k)
  xE : (retR σ).Disjoint (vR (σ.gpr .rdx) k)
  xR : (retR σ).Disjoint ⟨σ.gpr .rcx, 1024 * k⟩
  xC : (retR σ).Disjoint (cR (σ.gpr .r8))
  nD : (σ.gpr .rdi).toNat + 384 * k ≤ 2 ^ 64
  nS : (σ.gpr .rsi).toNat + 1024 * k ≤ 2 ^ 64
  nE : (σ.gpr .rdx).toNat + 1024 * k ≤ 2 ^ 64
  nR : (σ.gpr .rcx).toNat + 1024 * k ≤ 2 ^ 64
  nC : (σ.gpr .r8).toNat + 4096 ≤ 2 ^ 64
  red : VecReducedW 16 σ.mem (σ.gpr .rcx) (2 * k)

theorem ep {k : Nat} {σ : State} (hp : (kgNttK k).pre σ) : EP k σ :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := hp
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

/-- Polynomial `j` of `se`, as on entry. -/
abbrev wid (σ : State) (j : Nat) : Poly := polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j))

/-- The regions the function may change. -/
abbrev chg (k : Nat) (σ : State) : List Region :=
  [cR (σ.gpr .r8), vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, ⟨σ.gpr .rdi, 384 * k⟩]

/-- What holds throughout the function entered in `σ`. -/
structure B (k : Nat) (σ s : State) : Prop where
  rbx : s.gpr .rbx = σ.gpr .r8
  r13 : s.gpr .r13 = σ.gpr .rdi
  rsp : s.gpr .rsp = σ.gpr .rsp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  saved : Spill.Saved s.mem (σ.gpr .r8) σ.gpr KpkeMul.slots
  frame : Frame (chg k σ) σ.mem s.mem

section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

theorem slots_in {p : Reg × Nat} (hp : p ∈ KpkeMul.slots) : InRegions σ.wr (Spill.slot (σ.gpr .r8) p.2) 8 :=
  ⟨cR (σ.gpr .r8), by rw [E.wr]; simp, in_c (by have := DecMul.slots_bound p hp; omega_arith)⟩

/-- `se`'s polynomial `j` is still as on entry. -/
theorem B.se {s : State} (h : B k σ s) {j : Nat} (hj : j < 2 * k) :
    PolyIsW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j)) (wid σ j) := by
  obtain hs : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * j), 512⟩ ⟨σ.gpr .rcx, 1024 * k⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine polyIsW16_frame h.frame (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [E.rC.sub_left hs, E.sR.symm.sub_left hs, E.eR.symm.sub_left hs, E.dR.symm.sub_left hs]
  · have := E.red j hj
    rwa [show 32 * 16 * j = 512 * j by omega_arith] at this

end

/-- A region the steps write: in `s`, `e` or `dk`, or below the saved registers in `scratch`. -/
abbrev WOk (k : Nat) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨σ.gpr .r8, 3072⟩ ∨ Region.Sub r (vR (σ.gpr .rsi) k) ∨ Region.Sub r (vR (σ.gpr .rdx) k) ∨
    Region.Sub r ⟨σ.gpr .rdi, 384 * k⟩

section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

theorem wok_slot {r : Region} (hr : WOk k σ r) {p : Reg × Nat} (hp : p ∈ KpkeMul.slots) :
    Region.Disjoint ⟨Spill.slot (σ.gpr .r8) p.2, 8⟩ r := by
  obtain hb := DecMul.slots_bound p hp
  have nC := E.nC
  obtain hs : Region.Sub ⟨Spill.slot (σ.gpr .r8) p.2, 8⟩ (cR (σ.gpr .r8)) := sub_c (by omega_arith)
  rcases hr with hr | hr | hr | hr
  · exact (Offset.disjoint_base (σ.gpr .r8) (d := p.2) (n := 8) (k := 3072) (by omega_arith) (by omega_arith)).sub_right hr
  · exact (E.sC.symm.sub_left hs).sub_right hr
  · exact (E.eC.symm.sub_left hs).sub_right hr
  · exact (E.dC.symm.sub_left hs).sub_right hr

omit E in
theorem wok_chg {r : Region} (hr : WOk k σ r) : ∃ r' ∈ chg k σ, Region.Sub r r' := by
  rcases hr with hr | hr | hr | hr
  · exact ⟨cR (σ.gpr .r8), by simp, fun x hx => Region.sub_prefix (by decide) x (hr x hx)⟩
  · exact ⟨_, by simp, hr⟩
  · exact ⟨_, by simp, hr⟩
  · exact ⟨_, by simp, hr⟩

theorem B.step {s s' : State} (h : B k σ s) {W : List Region} (hP : IPost s s' W) (hW : ∀ r ∈ W, WOk k σ r) :
    B k σ s' :=
  ⟨by rw [hP.cs .rbx (by decide), h.rbx], by rw [hP.cs .r13 (by decide), h.r13],
    by rw [hP.cs .rsp (by decide), h.rsp], hP.rd.trans h.rd, hP.wr.trans h.wr,
    h.saved.frame hP.frame fun p hp r hr => wok_slot E (hW r hr) hp,
    h.frame.trans (hP.frame.sub fun r hr => wok_chg (hW r hr))⟩

theorem B.stepF {s s' : State} (h : B k σ s) {W : List Region} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, WOk k σ r) :
    B k σ s' :=
  h.step E ⟨hrd, hwr, hcs, hf⟩ hW

/-- After the prologue. -/
theorem pro_ok {Q : State → Prop} {rest : Prog isa}
    (h : ∀ s, B k σ s → s.gpr .r12 = σ.gpr .rsi → s.gpr .rbp = σ.gpr .rdx → s.gpr .r15 = σ.gpr .rcx →
      WP isa rest s Q) :
    WP isa (.seq (.block KpkeKgRows.proN) rest) σ Q := by
  unfold KpkeKgRows.proN
  rw [EncMul.saveE_eq]
  refine WP.seq (Spill.save_then .r8 KpkeMul.slots (fun p hp => slots_in E hp) ?_)
  refine WP.mono (Q := fun (s : State) => s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .r13 = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧
      s.gpr .rbp = σ.gpr .rdx ∧ s.gpr .r15 = σ.gpr .rcx ∧ s.gpr .rsp = σ.gpr .rsp ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = Spill.saveMem σ.mem (σ.gpr .r8) σ.gpr KpkeMul.slots)
    (by vrunm)
    fun s ⟨hbx, h13, h12, hbp, h15, hsp, hrd, hwr, hm⟩ => h s ⟨hbx, h13, hsp, hrd, hwr, by
      rw [hm]; exact Spill.saveMem_saved _ _ _ _ (by decide), by
      rw [hm]
      exact (Spill.saveMem_frame_base σ.mem (σ.gpr .r8) σ.gpr KpkeMul.slots (L := 4096)
        (fun p hp' => by have := DecMul.slots_bound p hp'; omega_arith) (by decide)).mono (by simp)⟩ h12 hbp h15

/-- After `j` polynomials of `s` widened. -/
structure WI (k : Nat) (σ : State) (j : Nat) (s : State) : Prop extends B k σ s where
  r12 : s.gpr .r12 = σ.gpr .rsi
  rbp : s.gpr .rbp = σ.gpr .rdx
  r15 : s.gpr .r15 = σ.gpr .rcx
  w : ∀ j' < j, PolyIs s.mem (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j')) (wid σ j')

theorem wide_ok (hk : k ≤ 4) {j : Nat} (hj : j < k) {s : State} (h : WI k σ j s) :
    WP isa (KpkeKgRows.wideS j) s (WI k σ (j + 1)) := by
  have nS := E.nS
  have nR := E.nR
  obtain eb : pa s ((.r15, 512 * j) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * j) := by simp only [pa, h.r15]
  obtain ef : pa s ((.r12, 1024 * j) : Ptr) = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) := by simp only [pa, h.r12]
  obtain hsS : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * j), 512⟩ ⟨σ.gpr .rcx, 1024 * k⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine WP.mono (widenIn_ok (b := (.r15, 512 * j)) (f := (.r12, 1024 * j)) (F := wid σ j) (by omega_arith) (by omega_arith) (by simp) (by rw [eb]; exact h.se E (by omega_arith))
    (by rw [eb, ef]; exact (E.sR.sub_left (sub_v _ hj)).sub_right hsS)
    (by
      rw [eb, ef, h.rd, h.wr, E.rd, E.wr]
      exact covers_append (covers_one ⟨⟨σ.gpr .rcx, 1024 * k⟩, by simp, Offset.contains_base (n := 512) _ (by omega_arith) (by omega_arith)⟩)
        (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩))
    (by rw [ef, h.wr, E.wr]; exact covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩))
    fun s' ⟨hP, hq⟩ => ?_
  rw [ef] at hP hq
  refine ⟨h.toB.step E hP fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (sub_v _ hj)),
    by rw [hP.cs .r12 (by decide), h.r12], by rw [hP.cs .rbp (by decide), h.rbp],
    by rw [hP.cs .r15 (by decide), h.r15], fun j' hj' => ?_⟩
  rcases (by omega_arith : j' < j ∨ j' = j) with hj'' | rfl
  · exact polyIs_frame hP.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega_arith) (by omega_arith) hj (by omega_arith)) (h.w j' hj'')
  · exact hq

end

/-- `e`'s polynomial `j`, as on entry. -/
abbrev ewid (k : Nat) (σ : State) (j : Nat) : Poly :=
  polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j))

/-- After `j` iterations of the loop of the transforms. -/
structure NI (k : Nat) (σ : State) (j : Nat) (s : State) : Prop extends B k σ s where
  r12 : s.gpr .r12 = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)
  r15 : s.gpr .r15 = σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j)
  rbp : s.gpr .rbp = σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)
  sdone : ∀ j' < j, PolyIs s.mem (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j')) (ntt (wid σ j'))
  srest : ∀ j', j ≤ j' → j' < k → PolyIs s.mem (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j')) (wid σ j')
  tdone : ∀ j' < j, PolyIs s.mem (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j')) (ntt (ewid k σ j'))

section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

set_option linter.unusedSimpArgs false in
/-- An iteration of the loop: `NTT(s[j])` in place, and `NTT(e[j])` of `u16`s to `e[j]`. -/
theorem step_ok (hk : k ≤ 4) {j : Nat} (hj : j < k) {s : State} (h : NI k σ j s) :
    WP isa KpkeMul.nttK16 s fun s' => NI k σ (j + 1) s' ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some (s.gpr .r14 - 1 == 0) := by
  have nS := E.nS
  have nE := E.nE
  have nR := E.nR
  have nC := E.nC
  obtain hsr : s.rd = [⟨σ.gpr .rcx, 1024 * k⟩] := by rw [h.rd, E.rd]
  obtain hsw : s.wr = [⟨σ.gpr .rdi, 384 * k⟩, vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, cR (σ.gpr .r8)] := by
    rw [h.wr, E.wr]
  obtain hS := h.srest j (Nat.le_refl _) hj
  unfold KpkeMul.nttK16 KpkeMul.nttKg
  -- `NTT(s[j])` in place
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = σ.gpr .r8 ∧ s1.gpr .r10 = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [h.r12, h.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  obtain hsp1 : s1.gpr .rsp = σ.gpr .rsp := by rw [k1.gpr (by decide), h.rsp]
  obtain dSC : (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (σ.gpr .r8)) :=
    (E.sC.sub_left (sub_v _ hj)).sub_right (sub_c0 _)
  obtain dEC : (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (σ.gpr .r8)) :=
    (E.eC.sub_left (sub_v _ hj)).sub_right (sub_c0 _)
  refine WP.seq (WP.inline (k := nttOK) BodiesOk.avx2.nttO (rd := [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) BodiesOk.avx2.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, dSC, dSC, E.xS.sub_right (sub_v _ hj), E.xC.sub_right (sub_c0 _), hS.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩)
      (covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩)
        (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩))
  · rw [k1.2.2, hsw]
    exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩)
      (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1, hS.2] at hpost2
  rw [hm1] at hf2
  obtain g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by
    rw [habi2.1 r hr, k1.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)]
  obtain wS : ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)], WOk k σ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inr (.inl (sub_v _ hj)), .inl (Region.sub_prefix (by decide))]
  obtain hb2 : B k σ s2 := h.toB.stepF E (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2 hf2 wS
  obtain eA : σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j) =
      σ.gpr .rcx + BitVec.ofNat 64 (512 * (k + j)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  obtain hE : PolyIsW 16 s2.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j)) (ewid k σ j) := by
    simp only [ewid]; rw [eA]; exact hb2.se E (by omega_arith)
  obtain hsub : Region.Sub (sR (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j)))
      ⟨σ.gpr .rcx, 1024 * k⟩ := by rw [eA]; exact Offset.sub_base _ (by omega_arith)
  -- `NTT(e[j])` to `e[j]`
  refine WP.seq (WP.mono (Q := fun (s3 : State) =>
      s3.gpr .rdi = σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j) ∧
      s3.gpr .rsi = σ.gpr .r8 ∧ s3.gpr .r10 = σ.gpr .rdx + BitVec.ofNat 64 (1024 * j) ∧ s3.mem = s2.mem ∧
      Keep [.rdi, .rsi, .r10] s2 s3) (by
        vrunm [g2 .r15 (by decide), g2 .rbx (by decide), g2 .rbp (by decide), h.r15, h.rbx, h.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, h3r10, hm3, k3⟩ => ?_)
  obtain hsp3 : s3.gpr .rsp = σ.gpr .rsp := by rw [k3.gpr (by decide), hb2.rsp]
  refine WP.seq (WP.inline (k := nttO16K) nttOBY16_correct
    (rd := [sR (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j))])
    (wr := [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)]) ?_ ?_ ?_
    (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_) (by decide +kernel))
  · simp only [nttO16K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h3di, h3si, h3r10, hsp3, hm3, retR]
    exact ⟨trivial, trivial, (E.rC.sub_left hsub).sub_right (sub_c0 _), dEC, E.xE.sub_right (sub_v _ hj),
      E.xC.sub_right (sub_c0 _), hE.1⟩
  · rw [k3.2.1, k3.2.2, hb2.rd, hb2.wr, E.rd, E.wr]
    exact covers_append (covers_one ⟨⟨σ.gpr .rcx, 1024 * k⟩, by simp, by
      rw [eA]; exact Offset.contains_base (n := 512) _ (by omega_arith) (by omega_arith)⟩)
      (covers_append (covers_one ⟨vR (σ.gpr .rdx) k, by simp, in_vec _ (by omega_arith) hj⟩)
        (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩))
  · rw [k3.2.2, hb2.wr, E.wr]
    exact covers_append (covers_one ⟨vR (σ.gpr .rdx) k, by simp, in_vec _ (by omega_arith) hj⟩)
      (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩)
  simp only [nttO16K, State.withRegions_gpr, State.withRegions_mem, h3di, h3r10, hm3, hE.2] at hpost4
  rw [hm3] at hf4
  obtain g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by
    rw [habi4.1 r hr, k3.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide), g2 r hr]
  obtain wE : ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)], WOk k σ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inr (.inr (.inl (sub_v _ hj))), .inl (Region.sub_prefix (by decide))]
  obtain g34 : ∀ r ∈ calleeSaved, s4.gpr r = s2.gpr r := fun r hr => by
    rw [habi4.1 r hr]
    exact k3.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain hb4 : B k σ s4 := hb2.stepF E (by rw [hrd4, k3.2.1]) (by rw [hwr4, k3.2.2]) g34 hf4 wE
  -- what the writes keep
  obtain fS2 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, (E.sC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  obtain fS4 : ∀ {j'}, j' < k → ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis E.sE hj' hj, (E.sC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  obtain fT2 : ∀ {j'}, j' < k → ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis E.sE.symm hj' hj, (E.eC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  obtain fT4 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega_arith) hj' hj hne, (E.eC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  -- the next `j`
  vrunm [g4 .r12 (by decide), g4 .r15 (by decide), g4 .rbp (by decide), g4 .r14 (by decide), h.r12, h.r15,
    h.rbp, DecMul.sx1024, sx512]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun j' hj' => ?_, fun j' hj1 hj2 => ?_, fun j' hj' => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rbx
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.r13
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]; exact hb4.rsp
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hb4.rd
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hb4.wr
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.saved
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; exact hb4.frame
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    refine polyIs_frame hf4 (fS4 (by omega_arith)) ?_
    by_cases hje : j' = j
    · subst hje; exact hpost2
    · exact polyIs_frame hf2 (fS2 (by omega_arith) hje) (h.sdone j' (by omega_arith))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf4 (fS4 hj2) (polyIs_frame hf2 (fS2 hj2 (by omega_arith)) (h.srest j' (by omega_arith) hj2))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases hje : j' = j
    · subst hje; exact hpost4
    · exact polyIs_frame hf4 (fT4 (by omega_arith) hje) (polyIs_frame hf2 (fT2 (by omega_arith)) (h.tdone j' (by omega_arith)))

end

section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

/-- `B` across steps that keep `rbx`, `r13` and `rsp` and write only regions `WOk` allows. -/
theorem B.stepR {s s' : State} (h : B k σ s) {W : List Region} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hbx : s'.gpr .rbx = s.gpr .rbx) (h13 : s'.gpr .r13 = s.gpr .r13) (hsp : s'.gpr .rsp = s.gpr .rsp)
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, WOk k σ r) : B k σ s' :=
  ⟨hbx.trans h.rbx, h13.trans h.r13, hsp.trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    h.saved.frame hf fun _ hp r hr => wok_slot E (hW r hr) hp,
    h.frame.trans (hf.sub fun r hr => wok_chg (hW r hr))⟩

omit E in
theorem mx_wok : ∀ r ∈ [mxR (σ.gpr .r8)], WOk k σ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact .inl (Offset.sub_base _ (by decide))

/-- The transforms, in the MXCSR region. -/
theorem ntts_ok {L : Kem} (hL : L.k = k) (hk : k ≤ 4) (hk0 : 0 < k)
    {s : State} (h : WI k σ k s) :
    WP isa (KpkeKgRows.nttsN L) s (NI k σ k) := by
  have nC := E.nC
  obtain hcw : cR (σ.gpr .r8) ∈ σ.wr := by rw [E.wr]; simp
  unfold KpkeKgRows.nttsN
  rw [hL]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r15 = σ.gpr .rcx + BitVec.ofNat 64 (512 * k) ∧
      s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.mem = s.mem ∧ Keep [.r15, .r14] s s1) (by
        vrunm [h.r15, sx_ofNat (show 512 * k < 2 ^ 31 by omega_arith)]
        refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
        · apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          omega_arith
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h115, h114, hm1, k1⟩ => ?_)
  obtain h1bx : s1.gpr .rbx = σ.gpr .r8 := by rw [k1.gpr (by decide), h.rbx]
  refine WP.mono (noMx_ok (sP := σ.gpr .r8)
    (Q := NI k σ k) (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, hq4, hf5, k5⟩ => ?_
  · have k12 := k1.trans k2
    rw [hm1] at f2
    obtain hb2 : B k σ s2 := h.toB.stepR E (by rw [k12.2.1]) (by rw [k12.2.2]) (k12.gpr (by decide))
      (k12.gpr (by decide)) (k12.gpr (by decide)) f2 mx_wok
    refine wp_countdown (cnt := .r14) (N := k) (by omega_arith) hk0 (NI k σ) (fun j hj u hI _ => step_ok E hk hj hI)
      (fun u hN => hN) ⟨hb2, ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun j' _ hj' => ?_,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩ (by rw [k2.gpr (by decide), h114])
    · rw [k12.gpr (by decide), h.r12, Nat.mul_zero, add_ofNat_zero]
    · rw [k2.gpr (by decide), h115, Nat.mul_zero, add_ofNat_zero]
    · rw [k12.gpr (by decide), h.rbp, Nat.mul_zero, add_ofNat_zero]
    · exact polyIs_frame f2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (E.sC.sub_left (sub_v _ hj')).sub_right (sub_c (by decide))) (h.w j' hj')
  · have fm : ∀ {p : Addr} {n i : Nat}, (vR p n).Disjoint (cR (σ.gpr .r8)) → i < n →
        ∀ r ∈ [mxR (σ.gpr .r8)], (pR (p + BitVec.ofNat 64 (1024 * i))).Disjoint r := fun h hi r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vc_dis h hi (by decide)
    exact ⟨hq4.toB.stepR E k5.2.1 k5.2.2 (k5.gpr (by decide)) (k5.gpr (by decide)) (k5.gpr (by decide)) hf5 mx_wok,
      by rw [k5.gpr (by decide), hq4.r12], by rw [k5.gpr (by decide), hq4.r15], by rw [k5.gpr (by decide), hq4.rbp],
      fun j hj => polyIs_frame hf5 (fm E.sC hj) (hq4.sdone j hj),
      fun j h1 h2 => absurd h2 (by omega_arith),
      fun j hj => polyIs_frame hf5 (fm E.eC hj) (hq4.tdone j hj)⟩

/-- After `j` encodings of `ŝ` to `dk`. -/
structure DI (k : Nat) (σ : State) (j : Nat) (s : State) : Prop extends B k σ s where
  r12 : s.gpr .r12 = σ.gpr .rsi
  shat : ∀ j' < k, PolyIs s.mem (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j')) (ntt (wid σ j'))
  ehat : ∀ j' < k, PolyIs s.mem (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j')) (ntt (ewid k σ j'))
  dk : ∀ j' < j, bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (384 * j')) 384 = encode12 (ntt (wid σ j'))

theorem enc_ok {A : Prims} (hA : PrimsOk A) (hn : A.enc12.noCalls = true) (hk : k ≤ 4) {j : Nat} (hj : j < k)
    {s : State} (h : DI k σ j s) : WP isa (KpkeKgRows.encS A j) s (DI k σ (j + 1)) := by
  have nS := E.nS
  have nD := E.nD
  obtain ep : pa s ((.r12, 1024 * j) : Ptr) = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) := by simp only [pa, h.r12]
  obtain eq : pa s ((.r13, 384 * j) : Ptr) = σ.gpr .rdi + BitVec.ofNat 64 (384 * j) := by simp only [pa, h.r13]
  obtain hsub : Region.Sub ⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ ⟨σ.gpr .rdi, 384 * k⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain hsr : s.rd ++ s.wr = [⟨σ.gpr .rcx, 1024 * k⟩] ++
      [⟨σ.gpr .rdi, 384 * k⟩, vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, cR (σ.gpr .r8)] := by rw [h.rd, h.wr, E.rd, E.wr]
  obtain hT : TwoHi (.r12, 1024 * j) (.r13, 384 * j) 1024 384 s :=
    { off := ⟨by omega_arith, by omega_arith⟩
      d := by rw [ep, eq]; exact (E.dS.symm.sub_left (sub_v _ hj)).sub_right hsub
      rP := by rw [ep, show retR s = retR σ by simp only [retR, h.rsp]]; exact E.xS.sub_right (sub_v _ hj)
      rQ := by rw [eq, show retR s = retR σ by simp only [retR, h.rsp]]; exact E.xD.sub_right hsub
      c := by
        rw [ep, eq, hsr]
        exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega_arith) hj⟩)
          (covers_one ⟨⟨σ.gpr .rdi, 384 * k⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      w := by
        rw [eq, h.wr, E.wr]
        exact covers_one ⟨⟨σ.gpr .rdi, 384 * k⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ }
  refine WP.mono (enc12In_ok hA.enc12.ok hn (by simp [NA]) hT (by rw [ep]; exact (h.shat j hj).1))
    fun s' ⟨hP, hb⟩ => ?_
  rw [ep, eq, (h.shat j hj).2] at hb
  rw [eq] at hP
  obtain dW : ∀ {r : Region}, r.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ →
      ∀ r' ∈ [(⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ : Region)], r.Disjoint r' := fun hd r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  refine ⟨h.toB.step E hP fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr hsub)),
    by rw [hP.cs .r12 (by decide), h.r12], fun j' hj' => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · exact polyIs_frame hP.frame (dW ((E.dS.symm.sub_left (sub_v _ hj')).sub_right hsub)) (h.shat j' hj')
  · exact polyIs_frame hP.frame (dW ((E.dE.symm.sub_left (sub_v _ hj')).sub_right hsub)) (h.ehat j' hj')
  · rcases (by omega_arith : j' < j ∨ j' = j) with hj'' | rfl
    · rw [bytesAt_frame hP.frame (dW (Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by omega_arith)]
      exact h.dk j' hj''
    · exact hb

end

theorem kgNtt_wp {A : Prims} (hA : PrimsOk A) (hn : A.enc12.noCalls = true) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
    {σ : State} (hp : (kgNttK L.k).pre σ) :
    WP isa (KpkeKgRows.kgNtt L A) σ fun s' => gprPreserved σ s' ∧ (kgNttK L.k).post σ s' := by
  obtain E := ep hp
  obtain hk4 : L.k ≤ 4 := by omega_arith
  have nS := E.nS
  have nC := E.nC
  unfold KpkeKgRows.kgNtt
  refine pro_ok E fun s1 hb h12 hbp h15 => ?_
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => WI L.k σ j s) L.k 0
    (fun j _ hj s h => wide_ok E hk4 (by omega_arith) h) s1 ⟨hb, h12, hbp, h15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  refine WP.seq (WP.mono (ntts_ok E rfl hk4 (by omega_arith) h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (Q := fun (s4 : State) => s4.gpr .r12 = σ.gpr .rsi ∧ s4.mem = s3.mem ∧ Keep [.r12] s3 s4)
    (by
      vrunm [h3.r12, sx_ofNat (show 1024 * L.k < 2 ^ 31 by omega_arith)]
      refine ⟨BitVec.add_sub_cancel _ _, fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s4 ⟨h412, hm4, k4⟩ => ?_)
  obtain hb4 : B L.k σ s4 := h3.toB.stepR E k4.2.1 k4.2.2 (k4.gpr (by decide)) (k4.gpr (by decide))
    (k4.gpr (by decide)) (W := []) (by rw [hm4]; exact Frame.refl _ _) (fun _ h => absurd h (by simp))
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => DI L.k σ j s) L.k 0
    (fun j _ hj s h => enc_ok E hA hn hk4 (by omega_arith) h) s4 ⟨hb4, h412,
      fun j hj => by rw [hm4]; exact h3.sdone j hj, fun j hj => by rw [hm4]; exact h3.tdone j hj,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s5 h5 => ?_)
  rw [Nat.zero_add] at h5
  obtain hsv5 : Spill.Saved s5.mem (s5.gpr .rbx) σ.gpr KpkeMul.slots := by rw [h5.rbx]; exact h5.saved
  rw [DecMul.restore_eq]
  refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots σ.gpr s5 (by decide) (fun p hp' => ?_) hsv5)
    fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [h5.rsp]), ?_⟩, ?_, ?_, ?_⟩
  · rw [h5.rbx, h5.rd, h5.wr, E.rd, E.wr]
    exact ⟨cR (σ.gpr .r8), by simp, in_c (by have := DecMul.slots_bound p hp'; omega_arith)⟩
  · rw [hm']
    refine h5.frame.readW (r := retR σ) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [E.xC, E.xS, E.xE, E.xD]
  · refine ⟨by rw [List.length_map, vecAtW_length], fun i hi => ?_⟩
    rw [hm', KgMul.getD_get _ (by rw [List.length_map, vecAtW_length]; exact hi), EncMulY.vecAtW16_map_get _ _ hi]
    exact h5.shat i hi
  · refine ⟨by rw [List.length_map, vecAtW_length], fun i hi => ?_⟩
    rw [hm', KgMul.getD_get _ (by rw [List.length_map, vecAtW_length]; exact hi), EncMulY.vecAtW16_map_get _ _ hi]
    exact h5.ehat i hi
  · show bytesAt _ _ _ = _
    rw [hm']
    refine KpkeKg.enc_eq (L := L) (by rw [List.length_map, vecAtW_length]) fun i hi => ?_
    rw [KgMul.getD_get _ (by rw [List.length_map, vecAtW_length]; exact hi), EncMulY.vecAtW16_map_get _ _ hi]
    exact h5.dk i hi

end KgNtt

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.KgH16Base`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.FragKgRows`, which only this module used -/

section

/-!
# ML-KEM on x86-64: the calls of K-PKE key generation a row at a time

As the call of `vg_mlkem*_kpke_keygen` (`FragKpke.lean`): what a call of
`vg_mlkem*_kpke_keygen_ntt` or `vg_mlkem*_kpke_keygen_row`
(`KpkeKgRows.lean`) needs of the state (`KgNttH`, `KgRowH`) and of a layout
(`knChk`, `krChk`), what it computes, as of the caller's memory
(`kgNttAt_okL`, `kgRowAt_okL`), and that two runs leak the same
(`kgNttAt_trL`, `kgRowAt_trL`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The two functions of K-PKE key generation a row at a time of the
parameter set `L`: each one's contract, met by its code. -/
structure KgRowsOk (L : Kem) : Prop where
  ntt : CalleeOk (kgNttK L.k) (KpkeKgRows.kgNtt L .avx2)
  row : CalleeOk (kgRowK L.k) (KpkeKgRows.kgRow L .avx2)

/-! ## `vg_mlkem*_kpke_keygen_ntt` -/

/-- What a call of `vg_mlkem*_kpke_keygen_ntt` of rank `k` needs. -/
structure KgNttH (k : Nat) (dk s e se z : Ptr) (st : State) : Prop where
  off : dk.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ se.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  red : VecReducedW 16 st.mem (pa st se) (2 * k)
  dS : Region.Disjoint ⟨pa st dk, 384 * k⟩ (vR (pa st s) k)
  dE : Region.Disjoint ⟨pa st dk, 384 * k⟩ (vR (pa st e) k)
  dR : Region.Disjoint ⟨pa st dk, 384 * k⟩ ⟨pa st se, 1024 * k⟩
  dC : Region.Disjoint ⟨pa st dk, 384 * k⟩ (cR (pa st z))
  sE : Region.Disjoint (vR (pa st s) k) (vR (pa st e) k)
  sR : Region.Disjoint (vR (pa st s) k) ⟨pa st se, 1024 * k⟩
  sC : Region.Disjoint (vR (pa st s) k) (cR (pa st z))
  eR : Region.Disjoint (vR (pa st e) k) ⟨pa st se, 1024 * k⟩
  eC : Region.Disjoint (vR (pa st e) k) (cR (pa st z))
  rC : Region.Disjoint ⟨pa st se, 1024 * k⟩ (cR (pa st z))
  kD : (below (st.gpr .rsp) 32).Disjoint ⟨pa st dk, 384 * k⟩
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kE : (below (st.gpr .rsp) 32).Disjoint (vR (pa st e) k)
  kR : (below (st.gpr .rsp) 32).Disjoint ⟨pa st se, 1024 * k⟩
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  nD : (pa st dk).toNat + 384 * k ≤ 2 ^ 64
  nS : (pa st s).toNat + 1024 * k ≤ 2 ^ 64
  nE : (pa st e).toNat + 1024 * k ≤ 2 ^ 64
  nR : (pa st se).toNat + 1024 * k ≤ 2 ^ 64
  nZ : (pa st z).toNat + 4096 ≤ 2 ^ 64
  c : Covers ([⟨pa st se, 1024 * k⟩] ++ [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)] st.wr

theorem knPre {k : Nat} {dk s e se z : Ptr} {st s1 : State} (H : KgNttH k dk s e se z st)
    (hv : s1.gpr .rdi = pa st dk ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st e ∧ s1.gpr .rcx = pa st se ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgNttK k).pre (s1.callEntry.withRegions [⟨pa st se, 1024 * k⟩]
      [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgNttK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.dS, H.dE, H.dR, H.dC, H.sE, H.sR, H.sC, H.eR, H.eC, H.rC,
    ret_disj s1 (by rw [hsp]; exact H.kD), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kE), ret_disj s1 (by rw [hsp]; exact H.kR),
    ret_disj s1 (by rw [hsp]; exact H.kZ), H.nD, H.nS, H.nE, H.nR, H.nZ, ?_⟩
  rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (n := 1024 * k) (by have := H.nR; omega_using [this])
    (by rw [hsp]; exact H.kR) i (by omega_using [hi])).trans (by rw [hm]))]
  exact H.red

section
variable {L : Kem} (hK : KgRowsOk L)
include hK

theorem kgNttAt_ok {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z) {st : State}
    (H : KgNttH L.k dk s e se z st) :
    WP isa (L.kgNttAt dk s e se z) st fun s' =>
      Post st s' [⟨pa st dk, 384 * L.k⟩, vR (pa st s) L.k, vR (pa st e) L.k, cR (pa st z)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAtW 16 st.mem (pa st se) L.k).map ntt) ∧
      VecIs s'.mem (pa st e) L.k ((vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec ((vecAtW 16 st.mem (pa st se) L.k).map ntt) := by
  refine WP.mono (glueCall_ok hK.ntt.ok hK.ntt.nosp (by rw [hK.ntt.depth]; decide)
    (kmGlue_ok dk s e se z H.off hs he hse hz st) (fun s1 hv hm k => knPre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hR := H.nR
  have eS : vecAtW 16 s1.callEntry.mem (pa st se) L.k = vecAtW 16 st.mem (pa st se) L.k :=
    vecAtW16_congr fun i hi =>
      (ce_mem s1 (n := 1024 * L.k) (by omega_using [hR]) (by rw [hsp]; exact H.kR) i (by omega_using [hi])).trans (by rw [hm])
  have eE : vecAtW 16 s1.callEntry.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k =
      vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k :=
    vecAtW16_congr fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (ce_mem s1 (n := 1024 * L.k) (by omega_using [hR]) (by rw [hsp]; exact H.kR) _ (by omega_using [hi])).trans (by rw [hm])
  simp only [kgNttK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂, eS, eE] at hq
  exact hq

theorem kgNttAt_tr {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z) :
    RelCT isa (fun x y' => KgNttH L.k dk s e se z x ∧ KgNttH L.k dk s e se z y' ∧ x.gpr dk.1 = y'.gpr dk.1 ∧
      x.gpr s.1 = y'.gpr s.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr se.1 = y'.gpr se.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgNttAt dk s e se z) fun _ _ => True :=
  glueCall_tr hK.ntt.ok hK.ntt.ct (V := fun x x1 => ((x1.gpr .rdi = pa x dk ∧
      x1.gpr .rsi = pa x s ∧ x1.gpr .rdx = pa x e ∧ x1.gpr .rcx = pa x se ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok dk s e se z hx.off hs he hse hz x,
      kmGlue_ok dk s e se z hy'.off hs he hse hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, knPre hx hv1 hm1 k1, knPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgNttK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## `vg_mlkem*_kpke_keygen_row` -/

/-- What a call of `vg_mlkem*_kpke_keygen_row` of rank `k` needs. -/
structure KgRowH (k : Nat) (ek a s e z : Ptr) (st : State) : Prop where
  off : ek.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReducedW 16 st.mem (pa st a) k
  redS : VecReduced st.mem (pa st s) k
  redE : Reduced st.mem (pa st e)
  kA : Region.Disjoint ⟨pa st ek, 384⟩ ⟨pa st a, 512 * k⟩
  kS : Region.Disjoint ⟨pa st ek, 384⟩ (vR (pa st s) k)
  kE : Region.Disjoint ⟨pa st ek, 384⟩ (pR (pa st e))
  kC : Region.Disjoint ⟨pa st ek, 384⟩ (cR (pa st z))
  aE : Region.Disjoint ⟨pa st a, 512 * k⟩ (pR (pa st e))
  aC : Region.Disjoint ⟨pa st a, 512 * k⟩ (cR (pa st z))
  sE : Region.Disjoint (vR (pa st s) k) (pR (pa st e))
  sC : Region.Disjoint (vR (pa st s) k) (cR (pa st z))
  eC : Region.Disjoint (pR (pa st e)) (cR (pa st z))
  xK : (below (st.gpr .rsp) 32).Disjoint ⟨pa st ek, 384⟩
  xA : (below (st.gpr .rsp) 32).Disjoint ⟨pa st a, 512 * k⟩
  xS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  xE : (below (st.gpr .rsp) 32).Disjoint (pR (pa st e))
  xZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  nK : (pa st ek).toNat + 384 ≤ 2 ^ 64
  nA : (pa st a).toNat + 512 * k ≤ 2 ^ 64
  nS : (pa st s).toNat + 1024 * k ≤ 2 ^ 64
  nE : (pa st e).toNat + 1024 ≤ 2 ^ 64
  nZ : (pa st z).toNat + 4096 ≤ 2 ^ 64
  c : Covers ([⟨pa st a, 512 * k⟩, vR (pa st s) k] ++ [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)] st.wr

theorem krPre {k : Nat} {ek a s e z : Ptr} {st s1 : State} (H : KgRowH k ek a s e z st)
    (hv : s1.gpr .rdi = pa st ek ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st s ∧ s1.gpr .rcx = pa st e ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgRowK k).pre (s1.callEntry.withRegions [⟨pa st a, 512 * k⟩, vR (pa st s) k]
      [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgRowK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.kA, H.kS, H.kE, H.kC, H.aE, H.aC, H.sE, H.sC, H.eC,
    ret_disj s1 (by rw [hsp]; exact H.xK), ret_disj s1 (by rw [hsp]; exact H.xA),
    ret_disj s1 (by rw [hsp]; exact H.xS), ret_disj s1 (by rw [hsp]; exact H.xE),
    ret_disj s1 (by rw [hsp]; exact H.xZ), H.nK, H.nA, H.nS, H.nE, H.nZ, ?_, fun i hi => ?_, ?_⟩
  · rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (n := 512 * k) (by have := H.nA; omega_using [this])
      (by rw [hsp]; exact H.xA) i hi).trans (by rw [hm]))]
    exact H.redA
  · rw [ce_reduced s1 (by rw [hsp]; exact H.xS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.xE), hm]; exact H.redE

section
variable {L : Kem} (hK : KgRowsOk L)
include hK

theorem kgRowAt_ok {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z) {st : State}
    (H : KgRowH L.k ek a s e z st) :
    WP isa (L.kgRowAt ek a s e z) st fun s' =>
      Post st s' [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)] ∧
      bytesAt s'.mem (pa st ek) 384 =
        encode12 (add (dot (vecAtW 16 st.mem (pa st a) L.k) (vecAt st.mem (pa st s) L.k)) (polyAt st.mem (pa st e))) := by
  refine WP.mono (glueCall_ok hK.row.ok hK.row.nosp (by rw [hK.row.depth]; decide)
    (kmGlue_ok ek a s e z H.off ha hs he hz st) (fun s1 hv hm k => krPre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hA := H.nA
  have eA : vecAtW 16 s1.callEntry.mem (pa st a) L.k = vecAtW 16 st.mem (pa st a) L.k :=
    vecAtW16_congr fun i hi =>
      (ce_mem s1 (n := 512 * L.k) (by omega_using [hA]) (by rw [hsp]; exact H.xA) i hi).trans (by rw [hm])
  simp only [kgRowK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂, eA,
    ce_vecAt s1 (by rw [hsp]; exact H.xS), ce_polyAt s1 (by rw [hsp]; exact H.xE), hm] at hq
  exact hq

theorem kgRowAt_tr {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z) :
    RelCT isa (fun x y' => KgRowH L.k ek a s e z x ∧ KgRowH L.k ek a s e z y' ∧ x.gpr ek.1 = y'.gpr ek.1 ∧
      x.gpr a.1 = y'.gpr a.1 ∧ x.gpr s.1 = y'.gpr s.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgRowAt ek a s e z) fun _ _ => True :=
  glueCall_tr hK.row.ok hK.row.ct (V := fun x x1 => ((x1.gpr .rdi = pa x ek ∧
      x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x s ∧ x1.gpr .rcx = pa x e ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok ek a s e z hx.off ha hs he hz x,
      kmGlue_ok ek a s e z hy'.off ha hs he hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, krPre hx hv1 hm1 k1, krPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgRowK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

/-- The layout of a call of `vg_mlkem*_kpke_keygen_ntt`. -/
def knChk (bs wbs : List (Reg × Nat)) (k : Nat) (dk s e se z : Ptr) : Bool :=
  wrOk bs wbs dk (384 * k) && wrOk bs wbs s (1024 * k) && wrOk bs wbs e (1024 * k) && rdOk bs se (1024 * k) &&
    wrOk bs wbs z 4096 &&
    sepB bs dk (384 * k) s (1024 * k) && sepB bs dk (384 * k) e (1024 * k) && sepB bs dk (384 * k) se (1024 * k) &&
    sepB bs dk (384 * k) z 4096 && sepB bs s (1024 * k) e (1024 * k) && sepB bs s (1024 * k) se (1024 * k) &&
    sepB bs s (1024 * k) z 4096 && sepB bs e (1024 * k) se (1024 * k) && sepB bs e (1024 * k) z 4096 &&
    sepB bs se (1024 * k) z 4096

/-- The layout of a call of `vg_mlkem*_kpke_keygen_row`. -/
def krChk (bs wbs : List (Reg × Nat)) (k : Nat) (ek a s e z : Ptr) : Bool :=
  wrOk bs wbs ek 384 && rdOk bs a (512 * k) && rdOk bs s (1024 * k) && wrOk bs wbs e 1024 &&
    wrOk bs wbs z 4096 &&
    sepB bs ek 384 a (512 * k) && sepB bs ek 384 s (1024 * k) && sepB bs ek 384 e 1024 && sepB bs ek 384 z 4096 &&
    sepB bs a (512 * k) e 1024 && sepB bs a (512 * k) z 4096 && sepB bs s (1024 * k) e 1024 &&
    sepB bs s (1024 * k) z 4096 && sepB bs e 1024 z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (La : Lay rbs wbs st)
include La

theorem KgNttH.of {k : Nat} {dk s e se z : Ptr} (hc : knChk (rbs ++ wbs) wbs k dk s e se z = true)
    (red : VecReducedW 16 st.mem (pa st se) (2 * k)) : KgNttH k dk s e se z st := by
  simp only [knChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hod, hrd⟩, hwd⟩, ⟨⟨hos, hrs⟩, hws⟩⟩, ⟨⟨hoe, hre⟩, hwe⟩⟩, ⟨hor, hrr⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩,
    s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩ := hc
  exact ⟨⟨hod, hos, hoe, hor, hoz⟩, red, La.disj s1, La.disj s2, La.disj s3, La.disj s4, La.disj s5,
    La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.disj s10, La.stkD hrd, La.stkD hrs, La.stkD hre,
    La.stkD hrr, La.stkD hrz, La.nwp hrd, La.nwp hrs, La.nwp hre, La.nwp hrr, La.nwp hrz,
    covers_append (covers_cons (La.cR hrr) covers_nil)
      (covers_cons (La.cR hrd) (covers_cons (La.cR hrs) (covers_cons (La.cR hre) (covers_cons (La.cR hrz) covers_nil)))),
    covers_cons (La.cW hwd) (covers_cons (La.cW hws) (covers_cons (La.cW hwe) (covers_cons (La.cW hwz) covers_nil)))⟩

theorem KgRowH.of {k : Nat} {ek a s e z : Ptr} (hc : krChk (rbs ++ wbs) wbs k ek a s e z = true)
    (redA : VecReducedW 16 st.mem (pa st a) k) (redS : VecReduced st.mem (pa st s) k)
    (redE : Reduced st.mem (pa st e)) : KgRowH k ek a s e z st := by
  simp only [krChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hrk⟩, hwk⟩, ⟨hoa, hra⟩⟩, ⟨hos, hrs⟩⟩, ⟨⟨hoe, hre⟩, hwe⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩,
    s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩ := hc
  exact ⟨⟨hok, hoa, hos, hoe, hoz⟩, redA, redS, redE, La.disj s1, La.disj s2, La.disj s3, La.disj s4,
    La.disj s5, La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.stkD hrk, La.stkD hra, La.stkD hrs,
    La.stkD hre, La.stkD hrz, La.nwp hrk, La.nwp hra, La.nwp hrs, La.nwp hre, La.nwp hrz,
    covers_append (covers_cons (La.cR hra) (covers_cons (La.cR hrs) covers_nil))
      (covers_cons (La.cR hrk) (covers_cons (La.cR hre) (covers_cons (La.cR hrz) covers_nil))),
    covers_cons (La.cW hwk) (covers_cons (La.cW hwe) (covers_cons (La.cW hwz) covers_nil))⟩

end

theorem knChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {dk s e se z : Ptr} (hc : knChk bs wbs k dk s e se z = true) :
    inB bs dk (384 * k) = true ∧ inB bs s (1024 * k) = true ∧ inB bs e (1024 * k) = true ∧
      inB bs se (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [knChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, wrOk_in h2, wrOk_in h3, rdOk_in h4, wrOk_in h5⟩

theorem krChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {ek a s e z : Ptr} (hc : krChk bs wbs k ek a s e z = true) :
    inB bs ek 384 = true ∧ inB bs a (512 * k) = true ∧ inB bs s (1024 * k) = true ∧
      inB bs e 1024 = true ∧ inB bs z 4096 = true := by
  simp only [krChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4, wrOk_in h5⟩

section
variable {L : Kem} (hK : KgRowsOk L) {rbs wbs : List (Reg × Nat)}
include hK

theorem kgNttAt_okL {st : State} (La : Lay rbs wbs st) {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se)
    (hz : NA z) (hc : knChk (rbs ++ wbs) wbs L.k dk s e se z = true)
    (red : VecReducedW 16 st.mem (pa st se) (2 * L.k)) :
    WP isa (L.kgNttAt dk s e se z) st fun s' =>
      PPost st s' [(dk, 384 * L.k), (s, 1024 * L.k), (e, 1024 * L.k), (z, 4096)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAtW 16 st.mem (pa st se) L.k).map ntt) ∧
      VecIs s'.mem (pa st e) L.k ((vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec ((vecAtW 16 st.mem (pa st se) L.k).map ntt) :=
  kgNttAt_ok hK hs he hse hz (KgNttH.of La hc red)

theorem kgNttAt_trL {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z)
    (hc : knChk (rbs ++ wbs) wbs L.k dk s e se z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧ VecReducedW 16 x.mem (pa x se) (2 * L.k) ∧
      VecReducedW 16 y'.mem (pa y' se) (2 * L.k))
      (L.kgNttAt dk s e se z) fun _ _ => True :=
  RelCT.mono (kgNttAt_tr hK hs he hse hz) (fun _ _ ⟨e, r1, r2⟩ =>
    ⟨KgNttH.of e.1 hc r1, KgNttH.of e.2.1 hc r2, e.eq (knChk_in hc).1, e.eq (knChk_in hc).2.1,
      e.eq (knChk_in hc).2.2.1, e.eq (knChk_in hc).2.2.2.1, e.eq (knChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

theorem kgRowAt_okL {st : State} (La : Lay rbs wbs st) {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e)
    (hz : NA z) (hc : krChk (rbs ++ wbs) wbs L.k ek a s e z = true)
    (redA : VecReducedW 16 st.mem (pa st a) L.k) (redS : VecReduced st.mem (pa st s) L.k)
    (redE : Reduced st.mem (pa st e)) :
    WP isa (L.kgRowAt ek a s e z) st fun s' => PPost st s' [(ek, 384), (e, 1024), (z, 4096)] ∧
      bytesAt s'.mem (pa st ek) 384 =
        encode12 (add (dot (vecAtW 16 st.mem (pa st a) L.k) (vecAt st.mem (pa st s) L.k)) (polyAt st.mem (pa st e))) :=
  kgRowAt_ok hK ha hs he hz (KgRowH.of La hc redA redS redE)

theorem kgRowAt_trL {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z)
    (hc : krChk (rbs ++ wbs) wbs L.k ek a s e z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReducedW 16 x.mem (pa x a) L.k ∧ VecReduced x.mem (pa x s) L.k ∧ Reduced x.mem (pa x e)) ∧
      (VecReducedW 16 y'.mem (pa y' a) L.k ∧ VecReduced y'.mem (pa y' s) L.k ∧ Reduced y'.mem (pa y' e)))
      (L.kgRowAt ek a s e z) fun _ _ => True :=
  RelCT.mono (kgRowAt_tr hK ha hs he hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨KgRowH.of e.1 hc r1 r2 r3, KgRowH.of e.2.1 hc r4 r5 r6, e.eq (krChk_in hc).1, e.eq (krChk_in hc).2.1,
      e.eq (krChk_in hc).2.2.1, e.eq (krChk_in hc).2.2.2.1, e.eq (krChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64

end

end


/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`, before the rows

`kemKeyGenH16` (`KeyGenH16.lean`) up to its rows: what it needs of the layout
(`KgH16Wf`, evaluated for each parameter set), what holds while it samples
the noise (`KN`) and from the noise's transforms on (`KH`), and the pieces:
the outputs of `PRF₂` (`prfs_ok`) and `s ‖ e` (`se_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace KeyGenH

open KeyGen KeyGen16 VG.Impl.MlKem.X86_64.Top16 VG.Impl.MlKem.X86_64.KeyGenH16

variable (K : Kem16)

/-! ## The regions -/

/-- `ŝ[j]` and `ê[j]` (`u32`s), row `j` of `ek`, and the sponge's state and blocks. -/
abbrev shP (j : Nat) : Ptr := sc (oSH + 1024 * j)
abbrev ehP (j : Nat) : Ptr := sc (oEH + 1024 * j)
abbrev ekP (j : Nat) : Ptr := (.r12, 384 * j)
abbrev hsP : Ptr := sc (Encaps16.oHS K)
abbrev hbP : Ptr := sc (Encaps16.oHB K)

/-- `ρ` (twice) and `σ`. -/
abbrev baseR : List (Ptr × Nat) := [(sc oG, 32), (sigP, 32), (sc oSB, 32)]
abbrev shR : List (Ptr × Nat) := (List.range 3).map fun j => (shP j, 1024)
/-- `ê[j]` for `i ≤ j < 3`. -/
abbrev ehR (i : Nat) : List (Ptr × Nat) := (List.range (3 - i)).map fun j => (ehP (i + j), 1024)
abbrev dkR : List (Ptr × Nat) := [((.r13, 0), 1152)]
abbrev ekR (i : Nat) : List (Ptr × Nat) := (List.range i).map fun j => (ekP j, 384)
abbrev aR (e : Nat) : List (Ptr × Nat) := (List.range e).map fun e' => (aP K e', 512)
abbrev prR : List (Ptr × Nat) := (List.range 6).map fun N => (prfO K N, 128)
abbrev rR (n : Nat) : List (Ptr × Nat) := (List.range n).map fun N => (rP K N, 512)
/-- The polynomials of `s ‖ e` but `N`. -/
abbrev rRx (N : Nat) : List (Ptr × Nat) := ((List.range 6).filter (· ≠ N)).map fun N' => (rP K N', 512)
/-- `σ`, copied for the fragment of row 0, and its outputs of `PRF₂`. -/
abbrev psP : Ptr := sc (K.oW + Sample4.oPS)
abbrev poP (N : Nat) : Ptr := sc (K.oW + Sample4.oPO + 128 * N)
abbrev poR : List (Ptr × Nat) := (List.range 2).map fun N => (poP K N, 128)

/-- What the matrix's fragments and rows keep: `ê[j]` from `ie` on, the
first `ik` rows of `ek` and the first `e` entries of `Â`. -/
abbrev liveG (ie ik e : Nat) : List (Ptr × Nat) := baseR ++ shR ++ ehR ie ++ dkR ++ ekR ik ++ aR K e
abbrev liveR (i e : Nat) : List (Ptr × Nat) := liveG K i i e

/-- A piece writing `ws` keeps `KC` and every region of `rs`. -/
def keepAll (ws rs : List (Ptr × Nat)) : Bool :=
  kcChk K.L ws && rs.all fun r => keepB (kgB K.L) ws r.1 r.2

/-- What `vg_mlkem768_kpke_keygen_ntt` and `vg_mlkem768_kpke_keygen_row` write. -/
abbrev ntW : List (Ptr × Nat) := [((.r13, 0), 384 * 3), (sc oSH, 1024 * 3), (sc oEH, 1024 * 3), (sc oZK, 4096)]
abbrev rowW (i : Nat) : List (Ptr × Nat) := [(ekP i, 384), (ehP i, 1024), (sc oZK, 4096)]
abbrev smW (i : Nat) : List (Ptr × Nat) := [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)]

/-- The blocks of `ek` the fragment of row `i` copies. -/
def cpChk (i : Nat) : Bool :=
  (hm i).1 == 0 || (copyChk (kgB K.L) (kgW K.L) (hbP K) (.r12, 136 * (hm i).2) (136 * (hm i).1) &&
    keepAll K [(hbP K, 136 * (hm i).1)] (liveR K i (3 * i) ++ [(hsP K, 200)]))

/-- The seeds of the fragment of row `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (kgB K.L) (kgW K.L) J &&
    keepAll K (seedW J) (liveR K i (3 * i) ++ [(hsP K, 200), (hbP K, 136 * (hm i).1)])

/-- The sampling of the fragment of row `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (kgB K.L) (kgW K.L) (K.oA + 512 * (3 * i)) K.oW && keepAll K (smW K i) (liveR K i (3 * i))

/-- Row `i` of `t̂`. -/
def rwChk (i : Nat) : Bool :=
  krChk (kgB K.L) (kgW K.L) 3 (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) &&
    keepAll K (rowW i) (liveG K (i + 1) i (3 * i + 3) ++ [(hsP K, 200)])

/-- What key generation hashing `ek` in the matrix's fragments needs of the
layout, evaluated for each parameter set. -/
structure KgH16Wf : Prop extends KgWfB K.L where
  k3 : K.L.k = 3
  ek : K.L.ekLen = 1184
  -- the noise but `PRF₂(σ, 0)` and `PRF₂(σ, 1)`
  pr : (prfsChk (kgB K.L) (kgW K.L) 4 (K.oPR + 256) (K.oW / 32) &&
    keepAll K (prfsW 4 (K.oPR + 256) (K.oW / 32)) baseR) = true
  se : ∀ N < 6, (twoChk (kgB K.L) (kgW K.L) (prfO K N) 128 (rP K N) 512 &&
    keepAll K [(rP K N, 512)] (baseR ++ prR K ++ rR K N)) = true
  -- row 0 of `Â` with `PRF₂(σ, 0)` and `PRF₂(σ, 1)`
  c0 : (copyChk (kgB K.L) (kgW K.L) (psP K) sigP 32 && keepAll K [(psP K, 32)] (baseR ++ rR K 6)) = true
  sd0 : ((List.range 4).all fun J => seedsChk (kgB K.L) (kgW K.L) J &&
    keepAll K (seedW J) (baseR ++ rR K 6 ++ [(psP K, 32)])) = true
  sm0 : (s4_16Chk (kgB K.L) (kgW K.L) K.oA K.oW && keepAll K (smW K 0) (baseR ++ rR K 6)) = true
  hz : (inB (kgW K.L) (hsP K) 200 && keepAll K [(hsP K, 200)] (baseR ++ rR K 6 ++ aR K 3 ++ poR K)) = true
  cP : ∀ N < 2, (twoChk (kgB K.L) (kgW K.L) (poP K N) 128 (rP K N) 512 &&
    keepAll K [(rP K N, 512)] (baseR ++ rRx K N ++ aR K 3 ++ poR K ++ [(hsP K, 200)])) = true
  -- the transforms
  nt : (knChk (kgB K.L) (kgW K.L) 3 (.r13, 0) (sc oSH) (sc oEH) (sc K.oR) (sc oZK) &&
    keepAll K ntW (baseR ++ aR K 3 ++ [(hsP K, 200)])) = true
  -- the rows
  cp : ∀ i < 3, cpChk K i = true
  sd : ∀ i < 3, sdChk K i = true
  sm : ∀ i < 3, smChk K i = true
  rw : ∀ i < 3, rwChk K i = true
  flg : ∀ i < 3, (keepAll K [] (liveR K i (3 * i + 3)) && keepB (kgB K.L) [] (hsP K) 200) = true
  -- the tail: the sponge's state kept by the copies of `ρ` and `ek`, copied to
  -- the sponge functions' state, and the rest of `ek` absorbed
  tS : (keepB (kgB K.L) (finW₁ K.L) (hsP K) 200 && keepB (kgB K.L) (finW₂ K.L) (hsP K) 200) = true
  tC : (copyChk (kgB K.L) (kgW K.L) (sc 0) (hsP K) 200 &&
    keepAll K [(sc 0, 200)] [((.r12, 0), 1184), ((.r13, 0), 1152), ((.r13, 1152), 1184)]) = true
  tH : hashChk (kgB K.L) (kgW K.L) [((.r12, 680), 504)] 136 (.r13, 384 * K.L.k + K.L.ekLen) 32 = true

variable {K}

theorem keepAll_spec {ws rs : List (Ptr × Nat)} (h : keepAll K ws rs = true) :
    kcChk K.L ws = true ∧ ∀ r ∈ rs, keepB (kgB K.L) ws r.1 r.2 = true := by
  simp only [keepAll, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem pa_off (s : State) (o d : Nat) : pa s (sc o) + BitVec.ofNat 64 d = pa s (sc (o + d)) := by
  simp only [pa]; rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## While the noise is sampled -/

/-- After `G(d ‖ k)`, the outputs of `PRF₂` from `PRF₂(σ, 2)` on, and the
polynomials of `s ‖ e` from 2 to `n`. -/
structure KN (K : Kem16) (n : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  r15 : s.gpr .r15 = 1
  prf : ∀ N < 6, 2 ≤ N → bytesAt s.mem (pa s (prfO K N)) 128 = prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ N < n, 2 ≤ N → PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

/-! ## From the transforms on -/

/-- Row `j` of `t̂`, encoded. -/
abbrev tRow (L : Kem) (σ : State) (j : Nat) : List Byte := encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) j)

/-- The blocks of `pad(ek)` the sponge has absorbed before the fragment of row `i`. -/
def hAbs : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | _ => 5

/-- Before row `i` of `t̂`, with the first `e` entries of `Â` sampled. -/
structure KH (K : Kem16) (σ : State) (i e : Nat) (s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  sh : ∀ j < 3, PolyIs s.mem (pa s (shP j)) (KPke.kgS K.L.p (kgD σ) j)
  eh : ∀ j < 3, i ≤ j → PolyIs s.mem (pa s (ehP j)) (KPke.kgE K.L.p (kgD σ) j)
  dk : bytesAt s.mem (pa s (.r13, 0)) 1152 = KPke.dkPKE K.L.p (kgD σ)
  mat : MatB16 K.L.k K.oA (rhoK K.L σ) e s
  ok : allOk K.L.k (rhoK K.L σ) e → (∀ j < i, bytesAt s.mem (pa s (ekP j)) 384 = tRow K.L σ j) ∧
    stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) (hAbs (e / 3))

/-- What holds of the regions besides `Â`, `ek` and the sponge, from `ê[i]` on. -/
structure KS (K : Kem16) (σ : State) (i : Nat) (s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  sh : ∀ j < 3, PolyIs s.mem (pa s (shP j)) (KPke.kgS K.L.p (kgD σ) j)
  eh : ∀ j < 3, i ≤ j → PolyIs s.mem (pa s (ehP j)) (KPke.kgE K.L.p (kgD σ) j)
  dk : bytesAt s.mem (pa s (.r13, 0)) 1152 = KPke.dkPKE K.L.p (kgD σ)

theorem KH.ks {i e : Nat} {σ s : State} (h : KH K σ i e s) : KS K σ i s := ⟨h.kc, h.rho, h.sb, h.sh, h.eh, h.dk⟩

theorem KH.of {i e : Nat} {σ s : State} (h : KS K σ i s) (hm : MatB16 K.L.k K.oA (rhoK K.L σ) e s)
    (ho : allOk K.L.k (rhoK K.L σ) e → (∀ j < i, bytesAt s.mem (pa s (ekP j)) 384 = tRow K.L σ j) ∧
      stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) (hAbs (e / 3))) : KH K σ i e s :=
  ⟨h.kc, h.rho, h.sb, h.sh, h.eh, h.dk, hm, ho⟩

/-- `ρ`, `ŝ`, `ê` from `ie` on, and `dk_PKE`. -/
abbrev statR (ie : Nat) : List (Ptr × Nat) := baseR ++ shR ++ ehR ie ++ dkR

section
variable (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- A piece that writes `ws`, keeps the regions of `rs` and `r15`, keeps
the facts about them. -/
theorem KH.keepG {i i' e : Nat} (hi : i ≤ i') {s s' : State} (h : KH K σ i e s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ liveG K i' i e, keepB (kgB K.L) ws r.1 r.2 = true)
    (hrow : allOk K.L.k (rhoK K.L σ) e → ∀ j, i ≤ j → j < i' → bytesAt s'.mem (pa s' (ekP j)) 384 = tRow K.L σ j)
    (hhs : allOk K.L.k (rhoK K.L σ) e → keepB (kgB K.L) ws (hsP K) 200 = true) : KH K σ i' e s' := by
  have L₀ := h.kc.lay W.toKgWfB hp
  have m : ∀ r, r ∈ liveG K i' i e → keepB (kgB K.L) ws r.1 r.2 = true := hk
  have mB : ∀ r ∈ baseR, r ∈ liveG K i' i e := fun r h =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ h))))
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, fun j hj => ?_, fun j hj hij => ?_, ?_,
    ⟨by rw [h15]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP
      (m _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))) (h.mat.mat e' he' f hf)⟩,
    fun ho => ⟨fun j hj => ?_, ?_⟩⟩
  · rw [L₀.keepBytes hP (m (sc oG, 32) (mB _ (by simp)))]; exact h.rho
  · rw [L₀.keepBytes hP (m (sc oSB, 32) (mB _ (by simp)))]; exact h.sb
  · exact L₀.keepPoly hP (m _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))))))
      (h.sh j hj)
  · have hm : (ehP j, 1024) ∈ liveG K i' i e := List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j - i', List.mem_range.2 (by omega_using [hj, hij]),
        by rw [Nat.add_sub_cancel' hij]⟩))))
    exact L₀.keepPoly hP (m _ hm) (h.eh j hj (by omega_using [hi, hij]))
  · rw [L₀.keepBytes hP (m _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)))))]; exact h.dk
  · by_cases hji : j < i
    · rw [L₀.keepBytes hP (m _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨j, List.mem_range.2 hji, rfl⟩))))]; exact (h.ok ho).1 j hji
    · exact hrow ho j (by omega_using [hji]) hj
  · rw [EkF.stateAt_keep L₀ hP (hhs ho)]; exact (h.ok ho).2

theorem KS.keep {i i' : Nat} (hi : i ≤ i') {s s' : State} (h : KS K σ i s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ statR i', keepB (kgB K.L) ws r.1 r.2 = true) : KS K σ i' s' := by
  have L₀ := h.kc.lay W.toKgWfB hp
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, fun j hj => ?_, fun j hj hij => ?_, ?_⟩
  · rw [L₀.keepBytes hP (hk (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP (hk (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly hP (hk _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))) (h.sh j hj)
  · exact L₀.keepPoly hP (hk (ehP j, 1024) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨j - i', List.mem_range.2 (by omega_using [hj, hij]), by rw [Nat.add_sub_cancel' hij]⟩)))) (h.eh j hj (by omega_using [hi, hij]))
  · rw [L₀.keepBytes hP (hk _ (List.mem_append_right _ (List.mem_singleton_self _)))]; exact h.dk

theorem KH.keep {i e : Nat} {s s' : State} (h : KH K σ i e s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ liveR K i e, keepB (kgB K.L) ws r.1 r.2 = true)
    (hhs : allOk K.L.k (rhoK K.L σ) e → keepB (kgB K.L) ws (hsP K) 200 = true) : KH K σ i e s' :=
  h.keepG W hp (Nat.le_refl _) hP h15 hkc hk (fun _ _ h₁ h₂ => absurd h₂ (by omega_using [h₁])) hhs

end

section
variable (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The outputs of `PRF₂` from `PRF₂(σ, 2)` on. -/
theorem prfs_ok (v : Sample4Impl) {s : State} (h : KA K.L σ s) (h15 : s.gpr .r15 = 1) :
    WP isa (v.callee.prfs 2 4 (K.oPR + 256) (K.oW / 32)) s (KN K 2 σ) := by
  have hc := W.pr
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases K.L) (by omega_using []) hc.1) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b (hr (sigP, 32) (.tail _ (.head _)))
  refine ⟨h.kc.step W.toKgWfB hp hP.b hkc, by rw [L₀.keepBytes hP.b (hr (sc oG, 32) (by simp))]; exact h.rho,
    hσ.trans h.sig, by rw [L₀.keepBytes hP.b (hr (sc oSB, 32) (by simp))]; exact h.sb,
    by rw [hP.cs .r15 (by decide)]; exact h15, fun N hN h2 => ?_, fun _ h h2 => absurd h (by omega_using [h2])⟩
  have := hb (N - 2) (by omega_using [hN])
  rw [show K.oPR + 256 + 128 * (N - 2) = K.oPR + 128 * N by omega_using [h2], show 2 + (N - 2) = N by omega_using [h2]] at this
  rw [Top16.prfO, hP.pa rbx_cs, this, h.sig]

/-- `s ‖ e`, polynomial `N`. -/
theorem se_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 6) (h2 : 2 ≤ N) {s : State} (h : KN K N σ s) :
    WP isa (cbdN K A N) s (KN K (N + 1) σ) := by
  have hc := W.se N hN
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.prf N hN h2, ← hP₁.pa rbx_cs] at hp₁
  have k : ∀ r ∈ baseR ++ prR K ++ rR K N, keepB (kgB K.L) [(rP K N, 512)] r.1 r.2 = true := hr
  refine ⟨h.kc.step W.toKgWfB hp hP₁.b hkc, ?_, ?_, ?_, by rw [hP₁.cs .r15 (by decide)]; exact h.r15,
    fun N' hN' h2' => ?_, fun N' hN' h2' => ?_⟩
  · rw [L₀.keepBytes hP₁.b (k (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP₁.b (k (sigP, 32) (List.mem_append_left _ (List.mem_append_left _ (.tail _ (.head _)))))]; exact h.sig
  · rw [L₀.keepBytes hP₁.b (k (sc oSB, 32) (by simp))]; exact h.sb
  · rw [L₀.keepBytes hP₁.b (k (prfO K N', 128) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))))]; exact h.prf N' hN' h2'
  · rcases (by omega_using [hN'] : N' < N ∨ N' = N) with hN' | rfl
    · exact L₀.keepPoly16 hP₁.b (k (rP K N', 512) (List.mem_append_right _
        (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))) (h.se N' hN' h2')
    · exact hp₁

end

theorem vecIs_get {m : Mem} {p : Addr} {f : Nat → Poly} (h : VecIs m p 3 ((List.range 3).map f)) {j : Nat}
    (hj : j < 3) : PolyIs m (p + BitVec.ofNat 64 (1024 * j)) (f j) := by
  have := h.2 j hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this

end KeyGenH

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.KgH16Rows`, which this module and modules that import it used -/

section

/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`, the rows

The fragment that samples three entries of `Â` while the sponge of `H`
absorbs `m` blocks (`sampleHAtM16_ok`, as `sampleHAt16_ok`), and the rows of
`kemKeyGenH16`: the fragment of row `i` (`frag_ok`), which absorbs the
blocks of `pad(ek)` that the rows before it wrote (`hb_eq`, `habs_take`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- What the fragment absorbing `m` blocks leaves. -/
structure SHPostM16 (m oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  hs : stateAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS) =
    SH.habs (stateAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS))
      (fun i => bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oHB + 136 * i)) 136) m

theorem SHPostM16.b {m oa oz : Nat} {s s' : State} (h : SHPostM16 m oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem shPreM16 (m : Nat) {oa oz : Nat} {s s1 : State} (h : SHH16 oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    (sampleHMKW true m).pre (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have := shPre16 h hv k
  rw [sampleHKW_eq] at this
  exact this

/-- The fragment absorbing `m` blocks inlined, on the seeds at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAtM16_ok {m : Nat} {b : Prog isa} (hb : BatchHMOk16 m b) {oa oz : Nat} {s : State}
    (h : SHH16 oa oz s) : WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPostM16 m oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  obtain hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  obtain hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  obtain hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPreM16 m h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      (sampleHMKW true m).post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleHMKW, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨hax, hres, hhs⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hhs

/-- What the fragment computing `m` outputs of `PRF₂`, from `PRF₂(σ, N₀)`, leaves. -/
structure SHPostP16 (N₀ m oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  pout : ∀ N < m, bytesAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oPO + 128 * N)) 128 =
    prf 2 (bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oPS) 32) (BitVec.ofNat 8 (N₀ + N))

theorem SHPostP16.b {N₀ m oa oz : Nat} {s s' : State} (h : SHPostP16 N₀ m oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The fragment computing `PRF₂(σ, N₀)`, …, `PRF₂(σ, N₀ + m - 1)` inlined, on
the seeds at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAtP16_ok {N₀ m : Nat} {b : Prog isa} (hb : BatchPOk16 N₀ m b) {oa oz : Nat} {s : State}
    (h : SHH16 oa oz s) : WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPostP16 N₀ m oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  obtain hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  obtain hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPre16 h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      (samplePNKW N₀ m).post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [samplePNKW, SH.Post3, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨⟨hax, hres⟩, hpo⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hpo

namespace KeyGenH

open KeyGen KeyGen16 VG.Impl.MlKem.X86_64.Top16 VG.Impl.MlKem.X86_64.KeyGenH16

theorem hm_spec : ∀ i < 3, (hm i).2 = hAbs i ∧ (hm i).2 + (hm i).1 = hAbs (i + 1) ∧
    136 * hAbs (i + 1) ≤ 384 * i ∧ (hm i).1 ≤ 3 := by decide

/-- Absorbing whole blocks of `E` from the state before block `t`. -/
theorem habs_take (E : List Byte) (t : Nat) :
    ∀ n, 136 * (t + n) ≤ E.length →
      SH.habs (HSponge.hstate E t) (fun j => (E.drop (136 * (t + j))).take 136) n = HSponge.hstate E (t + n)
  | 0, _ => rfl
  | n + 1, h => by
    show Spec.Sha3.keccakF (Proof.Sha3.xorAt (SH.habs _ _ n) 0 _) = _
    rw [habs_take E t n (by omega_using [h]), ← Nat.add_assoc]
    exact HSponge.hstate_full (by omega_using [h])

/-- The first `i` rows of `ek`. -/
theorem ekK_take (L : Kem) (σ : State) (hk : L.k = 3) {i : Nat} (hi : i ≤ 3) :
    (ekK L σ).take (384 * i) = KPke.catK (tRow L σ) i := by
  obtain hl : ∀ j, (tRow L σ j).length = 384 := fun _ => encode12_length _
  obtain e3 : KPke.catK (tRow L σ) L.p.k = KPke.catK (tRow L σ) i ++
      ((List.range (3 - i)).map (i + ·)).flatMap (tRow L σ) := by
    rw [show L.p.k = i + (3 - i) by rw [show L.p.k = 3 from hk]; omega_using [hi], KPke.catK_eq, KPke.catK_eq,
      List.range_add, List.flatMap_append]
  obtain hli : (KPke.catK (tRow L σ) i).length = 384 * i := KPke.catK_length hl i
  show (KPke.ekPKE L.p (aHat (rhoK L σ)) (kgD σ)).take (384 * i) = _
  rw [KPke.ekPKE, show (fun j => encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) j)) = tRow L σ from rfl, e3,
    List.append_assoc, List.take_left' hli]

theorem pa_add (s : State) (r : Reg) (o d : Nat) : pa s (r, o) + BitVec.ofNat 64 d = pa s (r, o + d) := by
  simp only [pa]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ekK_length {L : Kem} (σ : State) : (ekK L σ).length = L.ekLen := KPke.ekPKE_length _ _

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The blocks of `ek` that the fragment of row `i` absorbs, to `HB`. -/
theorem cp_ok {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i) s) :
    WP isa (if (hm i).1 = 0 then .block [] else copy (sc (Encaps16.oHB K)) (.r12, 136 * (hm i).2) (136 * (hm i).1)) s
      fun s' => KH K σ i (3 * i) s' ∧ (allOk K.L.k (rhoK K.L σ) (3 * i) →
        bytesAt s'.mem (pa s' (hbP K)) (136 * (hm i).1) = ((ekK K.L σ).drop (136 * (hm i).2)).take (136 * (hm i).1)) := by
  obtain ⟨e2, e21, hb, hm3⟩ := hm_spec i hi
  by_cases h0 : (hm i).1 = 0
  · rw [ite_eq_left h0]
    exact WP.block_nil ⟨h, fun _ => by rw [h0]; simp [bytesAt]⟩
  · rw [ite_eq_right h0]
    obtain hc := W.cp i hi
    simp only [cpChk, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at hc
    obtain ⟨hcc, hk⟩ := hc
    obtain ⟨hkc, hr⟩ := keepAll_spec hk
    obtain L₀ := h.kc.lay W.toKgWfB hp
    refine WP.mono (copy_okL L₀ (show Reg.r12 ≠ .rdi by decide) hcc) fun s' ⟨hP, hb'⟩ =>
      ⟨h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
        (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _))), fun ho => ?_⟩
    rw [hP.pa rbx_cs, hb']
    obtain hcat : bytesAt s.mem (pa s (.r12, 0)) (384 * i) = KPke.catK (tRow K.L σ) i :=
      bytesAt_catK s.mem s .r12 0 384 _ i fun j hj => by rw [Nat.zero_add]; exact (h.ok ho).1 j hj
    rw [← ekK_take K.L σ W.k3 (by omega_using [hi])] at hcat
    have := bytesAt_slice s.mem (pa s (.r12, 0)) (k := 136 * (hm i).2) (c := 136 * (hm i).1) (len := 384 * i)
      (by omega_using [e21, hb])
    rw [hcat, List.drop_take, List.take_take, Nat.min_eq_left (by omega_using [e21, hb]), pa_add, Nat.zero_add] at this
    exact this.symm

/-- While the seeds of the fragment of row `i` are written. -/
structure SI (K : Kem16) (σ : State) (i J : Nat) (s : State) : Prop where
  kh : KH K σ i (3 * i) s
  sd : SeedsIs (rhoK K.L σ) K.L.k (3 * i) J s
  hb : allOk K.L.k (rhoK K.L σ) (3 * i) →
    bytesAt s.mem (pa s (hbP K)) (136 * (hm i).1) = ((ekK K.L σ).drop (136 * (hm i).2)).take (136 * (hm i).1)

theorem seedI_ok {i : Nat} (hi : i < 3) {J : Nat} (hJ : J < 4) {s : State} (h : SI K σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SI K σ i (J + 1)) := by
  obtain hsd := W.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨hs, hk⟩ := hsd J hJ
  obtain ⟨hkc, hr⟩ := keepAll_spec hk
  obtain L₀ := h.kh.kc.lay W.toKgWfB hp
  refine WP.mono (seed_step L₀ (kgB_bases K.L) (by omega_using [hi, hJ]) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.kh.keep W hp hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
      (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_cons_self ..))), hS, fun ho => ?_⟩
  rw [L₀.keepBytes hP.b (hr (hbP K, 136 * (hm i).1) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]
  exact h.hb ho

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The sampling of the fragment of row `i`: entries `3i` to `3i + 2` of `Â`,
and the blocks of `ek` absorbed. -/
theorem sm_ok (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {i : Nat} (hi : i < 3)
    {s : State} (h : SI K σ i 4 s) :
    WP isa (Encaps.sampleHAt (b (hm i).1) (sc (K.oA + 512 * (3 * i))) (sc K.oW)) s (KH K σ i (3 * i + 3)) := by
  obtain ⟨e2, e21, hbd, hm3⟩ := hm_spec i hi
  obtain hsm := W.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  obtain ⟨hkc, hr⟩ := keepAll_spec hsm.2
  obtain L₅ := h.kh.kc.lay W.toKgWfB hp
  obtain hE : (ekK K.L σ).length = 1184 := by rw [ekK_length, W.ek]
  refine WP.mono (sampleHAtM16_ok (v.batchHM16 b hb _ hm3) (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  obtain ha : ∀ e' < 3 * i, keepB (kgR ++ kgW K.L) (smW K i) (aP K e') 512 = true := fun e' he' =>
    hr (aP K e', 512) (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))
  refine KH.of (h.kh.ks.keep W hp (Nat.le_refl _) h₆.b hkc fun r hr' =>
    hr r (List.mem_append_left _ (List.mem_append_left _ hr'))) ?_ fun ho => ?_
  · refine EkF16.MatB16.three (K := K) h.kh.mat L₅ h₆.b ha ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq h.sd (k := k) (by omega_using [hk]))]
    · have := h₆.res t ht f (by rw [seed4_eq h.sd (by omega_using [ht])]; exact hf)
      rwa [poly4W, pBytes_true, pa_off] at this
  · have ho' := (EkF.allOk_add3.1 ho).1
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [L₅.keepBytes h₆.b (hr (ekP j, 384) (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))]
      exact (h.kh.ok ho').1 j hj
    · have eHS : ∀ t : State, pa t (hsP K) = pa t (sc K.oW) + BitVec.ofNat 64 Sample4.oHS := fun t => by
        rw [pa_off]; rfl
      obtain e0 := (h.kh.ok ho').2
      rw [show 3 * i / 3 = i by omega_using [], eHS] at e0
      rw [h₆.b.pa rbx_bases, eHS, h₆.hs, e0, EkF.habs_congr _ (hm i).1
        (g := fun j => ((ekK K.L σ).drop (136 * ((hm i).2 + j))).take 136) fun j hj => ?_, ← e2,
        habs_take _ _ _ (by omega_using [hi, e21, hbd, hE]), e21, show (3 * i + 3) / 3 = i + 1 by omega_using []]
      obtain hb := h.hb ho'
      have := bytesAt_slice s.mem (pa s (hbP K)) (k := 136 * j) (c := 136) (len := 136 * (hm i).1) (by omega_using [hj])
      rw [hb, List.drop_take, List.take_take, Nat.min_eq_left (by omega_using [hj]), List.drop_drop, pa_off,
        show Encaps16.oHB K + 136 * j = K.oW + (Sample4.oHB + 136 * j) by simp only [Encaps16.oHB]; omega_using [],
        ← pa_off, show 136 * (hm i).2 + 136 * j = 136 * ((hm i).2 + j) by omega_using []] at this
      exact this.symm

end

/-- An entry of `Â` among the first `e`, once they all succeeded. -/
theorem aHat_part {k : Nat} {ρ : List Byte} {e : Nat} (h : allOk k ρ e) {e' : Nat} (he : e' < e) :
    sampleNTT minIterations (matSeed ρ (e' / k) (e' % k)) = some (aHat ρ (e' / k) (e' % k)) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (h e' he)
  rw [aHat, hf]; rfl

theorem r15_ok {k : Nat} {ρ : List Byte} {e : Nat} {r : BitVec 64} (h : r = if allOk k ρ e then 1 else 0)
    (hne : r.setWidth 32 ≠ 0) : allOk k ρ e := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_no {k : Nat} {ρ : List Byte} {e : Nat} {r : BitVec 64} (h : r = if allOk k ρ e then 1 else 0)
    (he : r.setWidth 32 = 0) : ¬ allOk k ρ e := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

/-- With an entry failed, the rows are not needed. -/
theorem KH.skip {K : Kem16} {σ s : State} {i e : Nat} (h : KH K σ i e s) (ho : ¬ allOk K.L.k (rhoK K.L σ) e) :
    KH K σ (i + 1) e s :=
  ⟨h.kc, h.rho, h.sb, h.sh, fun j hj hij => h.eh j hj (by omega_using [hij]), h.dk, h.mat, fun h' => absurd h' ho⟩

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- Row `i` of `t̂`, encoded to `ek`. -/
theorem row_ok (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i + 3) s)
    (ho : allOk K.L.k (rhoK K.L σ) (3 * i + 3)) : WP isa (rowAt K i) s (KH K σ (i + 1) (3 * i + 3)) := by
  have k3 := W.k3
  obtain hc := W.rw i hi
  simp only [rwChk, Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  obtain hkr : krChk (kgB K.L) (kgW K.L) K.L.k (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) = true := by
    rw [k3]; exact hc.1
  obtain L₀ := h.kc.lay W.toKgWfB hp
  obtain he : ∀ j < 3, sampleNTT minIterations (matSeed (rhoK K.L σ) i j) = some (aHat (rhoK K.L σ) i j) := by
    intro j hj
    have := aHat_part ho (e' := 3 * i + j) (by omega_using [hj])
    rwa [k3, show (3 * i + j) / 3 = i by omega_using [hj], show (3 * i + j) % 3 = j by omega_using [hj]] at this
  obtain hA : ∀ j < 3, PolyIsW 16 s.mem (pa s (sc (K.oA + 512 * (3 * i) + 512 * j))) (aHat (rhoK K.L σ) i j) := by
    intro j hj
    have := h.mat.mat (3 * i + j) (by omega_using [hj]) _ (by
      rw [k3, show (3 * i + j) / 3 = i by omega_using [hj], show (3 * i + j) % 3 = j by omega_using [hj]]; exact he j hj)
    rwa [show K.oA + 512 * (3 * i + j) = K.oA + 512 * (3 * i) + 512 * j by omega_using []] at this
  obtain redA : VecReducedW 16 s.mem (pa s (aP K (3 * i))) K.L.k := fun j hj => by
    rw [aP, sc_w16]; exact (hA j (by omega_using [k3, hj])).1
  obtain redS : VecReduced s.mem (pa s (sc oSH)) K.L.k := fun j hj => by
    rw [pa_off]; exact (h.sh j (by omega_using [k3, hj])).1
  obtain ep : rowAt K i = K.L.kgRowAt (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) := by
    rw [rowAt, k3]
  rw [ep]
  refine WP.mono (kgRowAt_okL hK L₀ rbx_na rbx_na rbx_na rbx_na hkr redA redS (h.eh i hi (Nat.le_refl _)).1)
    fun s' ⟨hP, hb⟩ => ?_
  refine h.keepG W hp (Nat.le_succ _) hP.b (hP.cs .r15 (by decide)) hkc (fun r hr' => hr r (List.mem_append_left _ hr'))
    (fun _ j hj hj' => ?_) (fun _ => hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain rfl : j = i := by omega_using [hj, hj']
  rw [hP.pa r12_cs, hb]
  obtain eA : vecAtW 16 s.mem (pa s (aP K (3 * j))) K.L.k = (List.range 3).map (aHat (rhoK K.L σ) j) := by
    rw [k3]; simp only [vecAtW]
    refine List.map_congr_left fun t ht => ?_
    rw [aP, sc_w16]; exact (hA t (List.mem_range.mp ht)).2
  obtain eS : vecAt s.mem (pa s (sc oSH)) K.L.k = (List.range 3).map (KPke.kgS K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAt]
    refine List.map_congr_left fun t ht => ?_
    rw [pa_off]; exact (h.sh t (List.mem_range.mp ht)).2
  rw [eA, eS, (h.eh j hi (Nat.le_refl _)).2, KPke.dot_eq_dotK, tRow, KPke.kgT, show K.L.p.k = 3 from k3]

/-- Row `i`, if every `SampleNTT` so far succeeded. -/
theorem rowIf_ok (hK : KgRowsOk K.L) {i : Nat} (hi : i < 3) {s : State} (h : KH K σ i (3 * i + 3) s) :
    WP isa (ifOk (rowAt K i)) s (KH K σ (i + 1) (3 * i + 3)) := by
  obtain hf := W.flg i hi
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hkc, hr⟩ := keepAll_spec hf.1
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · exact row_ok W hp hK hi (h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2)
      (r15_ok h.mat.r15 hne)
  · exact (h.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2).skip (r15_no h.mat.r15 he)

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The fragment of row `i`: entries `3i` to `3i + 2` of `Â`, and the blocks
of `ek` that the rows before it wrote absorbed. -/
theorem frag_ok (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {i : Nat} (hi : i < 3)
    {s : State} (h : KH K σ i (3 * i) s) : WP isa (frag K b i) s (KH K σ i (3 * i + 3)) := by
  have k3 := W.k3
  obtain sd : ∀ J < 4, ∀ t, SI K σ i J t → WP isa (seedAt J ((3 * i + J) / 3) ((3 * i + J) % 3)) t (SI K σ i (J + 1)) :=
    fun J hJ t ht => by have := seedI_ok W hp hi hJ ht; rwa [k3] at this
  unfold frag
  refine WP.seq (WP.mono (cp_ok W hp hi h) fun s₁ ⟨h₁, hb₁⟩ => ?_)
  obtain i₁ : SI K σ i 0 s₁ := ⟨h₁, ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hb₁⟩
  obtain s0 := sd 0 (by decide) s₁ i₁
  rw [show (3 * i + 0) / 3 = i by omega_using [], show (3 * i + 0) % 3 = 0 by omega_using []] at s0
  refine WP.seq (WP.mono s0 fun s₂ i₂ => ?_)
  obtain s1 := sd 1 (by decide) s₂ i₂
  rw [show (3 * i + 1) / 3 = i by omega_using [], show (3 * i + 1) % 3 = 1 by omega_using []] at s1
  refine WP.seq (WP.mono s1 fun s₃ i₃ => ?_)
  obtain s2 := sd 2 (by decide) s₃ i₃
  rw [show (3 * i + 2) / 3 = i by omega_using [], show (3 * i + 2) % 3 = 2 by omega_using []] at s2
  refine WP.seq (WP.mono s2 fun s₄ i₄ => ?_)
  obtain s3 := sd 3 (by decide) s₄ i₄
  rw [show (3 * i + 3) / 3 = i + 1 by omega_using [], show (3 * i + 3) % 3 = 0 by omega_using []] at s3
  refine WP.seq (WP.mono s3 fun s₅ i₅ => ?_)
  rw [Top16.aP, k3]
  exact sm_ok W hp v hb hi i₅

end

theorem stateAt_of_bytes {m m' : Mem} {p q : Addr} (h : bytesAt m p 200 = bytesAt m' q 200) :
    stateAt m p = stateAt m' q :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [Proof.Sha3.byteOf_stateAt _ _ hi, Proof.Sha3.byteOf_stateAt _ _ hi]
    have := congrArg (fun l => l[i]?) h
    simpa [bytesAt, List.getElem?_map, List.getElem?_range hi] using this

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- `ρ` to `ek`, `ek` to `dk`, `H(ek)` from the sponge's state, and `z`. -/
theorem tail_ok {s : State} (h : KH K σ 3 9 s) (ho : allOk K.L.k (rhoK K.L σ) 9) :
    WP isa (tail K) s (KFin K.L σ) := by
  have k3 := W.k3
  have hek := W.ek
  obtain L₀ := h.kc.lay W.toKgWfB hp
  have Wb := W.toKgWfB
  obtain hE : (ekK K.L σ).length = 1184 := by rw [ekK_length, hek]
  obtain rows : bytesAt s.mem (pa s (.r12, 0)) (384 * K.L.k) =
      KPke.catK (fun i => encode12 (KPke.kgT K.L.p (aHat (rhoK K.L σ)) (kgD σ) i)) K.L.k := by
    rw [k3]; exact bytesAt_catK s.mem s .r12 0 384 _ 3 fun j hj => by
      rw [Nat.zero_add]; exact (h.ok ho).1 j hj
  obtain hs0 : stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := (h.ok ho).2
  obtain h15 : s.gpr .r15 = 1 := by rw [h.mat.r15, ifp ho]
  have tS := W.tS
  simp only [Bool.and_eq_true] at tS
  have tC := W.tC
  simp only [Bool.and_eq_true] at tC
  obtain ⟨tCK, tCr⟩ := keepAll_spec tC.2
  obtain ⟨hrate, hk, hps, hsq, hna, hocs⟩ := hashChk_spec W.tH
  unfold tail
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 384 * K.L.k)) (src := sc oG) (n := 32) (by decide) Wb.f₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  obtain k₁ := h.kc.step Wb hp hP₁.b Wb.f₁K
  obtain L₁ := k₁.lay Wb hp
  obtain hek₁ : bytesAt s₁.mem (pa s₁ (.r12, 0)) K.L.ekLen = ekK K.L σ := by
    rw [Kem.ekLen, Params.ekLen, bytesAt_split, show 0 + 384 * K.L.p.k = 384 * K.L.k from Nat.zero_add _,
      hP₁.pa (p := (.r12, 384 * K.L.k)) r12_cs, hb₁, h.rho, ekK, KPke.ekPKE, L₀.keepBytes hP₁.b Wb.f₁E]
    exact congrArg (· ++ _) rows
  obtain hs₁ : stateAt s₁.mem (pa s₁ (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := by
    rw [EkF.stateAt_keep L₀ hP₁.b tS.1]; exact hs0
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 384 * K.L.k)) (src := (.r12, 0)) (n := K.L.ekLen) (by decide) Wb.f₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  obtain k₂ := k₁.step Wb hp hP₂.b Wb.f₂K
  obtain L₂ := k₂.lay Wb hp
  rw [hek₁] at hb₂
  obtain hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) K.L.ekLen = ekK K.L σ := by
    rw [L₁.keepBytes hP₂.b Wb.f₂E]; exact hek₁
  obtain hs₂ : stateAt s₂.mem (pa s₂ (hsP K)) = HSponge.hstate (ekK K.L σ) 5 := by
    rw [EkF.stateAt_keep L₁ hP₂.b tS.2]; exact hs₁
  -- the sponge's state to the sponge functions' state
  refine WP.seq (WP.mono (copy_okL L₂ (dst := sc 0) (src := hsP K) (n := 200) (show Reg.rbx ≠ .rdi by decide) tC.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  obtain k₃ := k₂.step Wb hp hP₃.b tCK
  obtain L₃ := k₃.lay Wb hp
  obtain hR₃ : Spec.Sha3.Repr s₃.mem (pa s₃ (sc 0)) 136 ((ekK K.L σ).take 680) := by
    show stateAt _ _ = _
    rw [hP₃.pa rbx_cs, stateAt_of_bytes hb₃, hs₂, HSponge.hstate, ite_eq_left (by rw [hE]; decide)]
    rfl
  obtain ek₃ : bytesAt s₃.mem (pa s₃ (.r12, 0)) 1184 = ekK K.L σ := by
    rw [L₂.keepBytes hP₃.b (tCr ((.r12, 0), 1184) (by simp)), ← hek]; exact hek₂
  -- the rest of `ek`, the padding and the squeeze
  rw [show K.L.ekLen - 136 * hDone = 504 by rw [hek]; rfl, show 136 * hDone = 680 from rfl]
  refine WP.seq (WP.mono (absAll_ok (kgB_bases K.L) hrate [((.r12, 680), 504)] L₃ 0 _ hps (by decide)
    (by rw [List.length_take, hE]; rfl) hR₃) fun s₄ ⟨hP₄, hR₄⟩ => ?_)
  obtain epc : (ekK K.L σ).take 680 ++ pieces s₃ [((.r12, 680), 504)] = ekK K.L σ := by
    have := bytesAt_slice s₃.mem (pa s₃ (.r12, 0)) (k := 680) (c := 504) (len := 1184) (by omega_using [])
    rw [ek₃, pa_add, Nat.zero_add] at this
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← this,
      List.take_of_length_le (show (List.drop 680 (ekK K.L σ)).length ≤ 504 by rw [List.length_drop, hE]),
      List.take_append_drop]
  rw [epc] at hR₄
  obtain L₄ := L₃.post hP₄.b (kgB_bases K.L)
  refine WP.seq (WP.mono (kpad_ok (show 6 < 256 by decide) (KPadH.of L₄ hk hrate (pos := 504 % 136) (by decide)))
    fun s₅ ⟨hP₅, hS₅⟩ => ?_)
  have hP₅' : PPost s₄ s₅ [(sc 0, 200), (sc 200, 640)] := hP₅
  obtain L₅ := L₄.post hP₅.b (kgB_bases K.L)
  obtain e4 : pa s₄ (sc 0) = pa s₃ (sc 0) := hP₄.pa (by decide)
  obtain hS := hS₅ (ekK K.L σ) (by rw [e4]; exact hR₄) (by rw [hE])
  refine WP.seq (WP.mono (ksqz_ok hna (KSqzH.of L₅ hsq hrate)) fun s₆ ⟨hP₆, ho₆⟩ => ?_)
  have hP₆' : PPost s₅ s₆ [(sc 0, 200), ((.r13, 384 * K.L.k + K.L.ekLen), 32), (sc 200, 640)] := hP₆
  obtain hP₃₆ : PPost s₃ s₆ (finW₃ K.L) :=
    PPost.trans (PPost.trans hP₄ hP₅' (by decide)
      (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h <;> simp [h])
      (fun w hw => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h <;> simp [h]))
      hP₆' (cs3 (by decide) hocs (by decide)) (fun w hw => hw) sub_acb
  obtain k₆ := k₃.step Wb hp hP₃₆.b Wb.f₃K
  obtain L₆ := k₆.lay Wb hp
  obtain e5 : pa s₅ (sc 0) = pa s₄ (sc 0) := hP₅.pa (by decide)
  obtain hH : bytesAt s₆.mem (pa s₃ (.r13, 384 * K.L.k + K.L.ekLen)) 32 = H (ekK K.L σ) := by
    rw [← hP₄.pa hocs, ← hP₅.pa hocs, ho₆, e5, hS, sha3Suffix6, H_eq]
  -- `z`
  refine WP.mono (copy_okL L₆ (dst := (.r13, 384 * K.L.k + K.L.ekLen + 32)) (src := (.rbp, 32)) (n := 32) (by decide)
    Wb.f₄) fun s₇ ⟨hP₇, hb₇⟩ => ?_
  obtain k₇ := k₆.step Wb hp hP₇.b Wb.f₄K
  rw [k₆.z] at hb₇
  refine ⟨k₇, ?_, ?_, ?_⟩
  · rw [hP₇.cs .r15 (by decide), hP₃₆.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h15]
  · rw [L₆.keepBytes hP₇.b Wb.f₄E, L₃.keepBytes hP₃₆.b Wb.f₃E, hek]; exact ek₃
  · have dS := Wb.dkS
    have dE := Wb.dkE
    obtain hP' := PPost.app hP₃₆ hP₇ (by simp [calleeSaved])
    rw [show K.L.dkLen = 384 * K.L.k + K.L.ekLen + 32 + 32 by
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega_using [],
      bytesAt_split, bytesAt_split, bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₇.pa (p := (.r13, 384 * K.L.k + K.L.ekLen + 32)) r13_cs, hb₇,
      L₆.keepBytes hP₇.b Wb.dkH, hP₃₆.pa (p := (.r13, 384 * K.L.k + K.L.ekLen)) r13_cs, hH,
      L₃.keepBytes hP'.b dE, L₂.keepBytes hP₃.b (by rw [k3, hek]; exact tCr ((.r13, 1152), 1184) (by simp)),
      hP₂.pa (p := (.r13, 384 * K.L.k)) r13_cs, hb₂, dkK]
    rw [L₃.keepBytes hP'.b (keepB_sub dS fun w hw => by
        rcases List.mem_append.1 hw with h | h
        exacts [List.mem_append_left _ (List.mem_append_right _ h), List.mem_append_right _ h]),
      L₂.keepBytes hP₃.b (by rw [k3]; exact tCr ((.r13, 0), 1152) (by simp)),
      L₁.keepBytes hP₂.b (keepB_sub dS fun w hw =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))),
      L₀.keepBytes hP₁.b (keepB_sub dS fun w hw =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)))]
    obtain hdk : bytesAt s.mem (pa s (.r13, 0)) (384 * K.L.k) = KPke.dkPKE K.L.p (kgD σ) := by rw [k3]; exact h.dk
    rw [hdk]

end

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The last row and the tail, if every `SampleNTT` succeeded. -/
theorem last_ok (hK : KgRowsOk K.L) {s : State} (h₅ : KH K σ 2 9 s) :
    WP isa (ifOk (.seq (rowAt K 2) (tail K))) s (KEnd K.L σ) := by
  have k3 := W.k3
  obtain hf := W.flg 2 (by decide)
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hkc, hr⟩ := keepAll_spec hf.1
  obtain e9 : K.L.k * K.L.k = 9 := by rw [k3]
  refine ifOk_ok (fun s₆ hP hne => ?_) fun s₆ hP he => ?_
  · have ho := r15_ok h₅.mat.r15 hne
    obtain h₆ := h₅.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2
    refine WP.seq (WP.mono (row_ok W hp hK (i := 2) (by decide) h₆ ho) fun s₇ h₇ => ?_)
    refine WP.mono (tail_ok W hp h₇ ho) fun s' hf' => ⟨hf'.kc, by rw [hf'.r15, e9, ifp ho], fun _ => hf'⟩
  · have h₆ := h₅.keep W hp hP.b (hP.cs .r15 (by decide)) hkc hr fun _ => hf.2
    obtain ho := r15_no h₅.mat.r15 he
    exact ⟨h₆.kc, by rw [e9]; exact h₆.mat.r15, fun h => absurd (by rwa [e9] at h) ho⟩

end

/-! ## Row 0, with `PRF₂(σ, 0)` and `PRF₂(σ, 1)` -/

/-- From the noise on, before the transforms: `ρ`, `σ` and the polynomials
of `s ‖ e` from 2 on. -/
structure KM (K : Kem16) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  se : ∀ N < 6, 2 ≤ N → PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

theorem KN.km {K : Kem16} {σ s : State} (h : KN K 6 σ s) : KM K σ s := ⟨h.kc, h.rho, h.sig, h.sb, h.se⟩

/-- After row 0 of `Â`: its entries, and the outputs of `PRF₂(σ, 0)` and
`PRF₂(σ, 1)`; the polynomials of `s ‖ e` below `n0` too; and the sponge's
state zeroed, if `hz`. -/
structure KG (K : Kem16) (σ : State) (n0 : Nat) (hz : Bool) (s : State) : Prop extends KM K σ s where
  se0 : ∀ N < n0, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)
  mat : MatB16 K.L.k K.oA (rhoK K.L σ) 3 s
  pout : ∀ N < 2, bytesAt s.mem (pa s (poP K N)) 128 = prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  hs : hz = true → stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) 0

section
variable {K : Kem16} (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem KM.keep {s s' : State} (h : KM K σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hkc : kcChk K.L ws = true) (hk : ∀ r ∈ baseR ++ rR K 6, keepB (kgB K.L) ws r.1 r.2 = true) : KM K σ s' := by
  obtain L₀ := h.kc.lay W.toKgWfB hp
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, ?_, fun N hN h2 => ?_⟩
  · rw [L₀.keepBytes hP (hk (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP (hk (sigP, 32) (by simp))]; exact h.sig
  · rw [L₀.keepBytes hP (hk (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly16 hP (hk (rP K N, 512) (List.mem_append_right _ (List.mem_map.2 ⟨N, List.mem_range.2 hN, rfl⟩)))
      (h.se N hN h2)

/-- While the seeds of row 0 are written, after `σ`'s copy. -/
structure S0 (K : Kem16) (σ : State) (J : Nat) (s : State) : Prop where
  km : KM K σ s
  r15 : s.gpr .r15 = 1
  sd : SeedsIs (rhoK K.L σ) K.L.k 0 J s
  ps : bytesAt s.mem (pa s (psP K)) 32 = KPke.kgSigma K.L.p (kgD σ)

theorem seed0_ok {J : Nat} (hJ : J < 4) {s : State} (h : S0 K σ J s) :
    WP isa (seedAt J ((0 + J) / K.L.k) ((0 + J) % K.L.k)) s (S0 K σ (J + 1)) := by
  have hsd := W.sd0
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨hs, hk⟩ := hsd J hJ
  obtain ⟨hkc, hr⟩ := keepAll_spec hk
  obtain L₀ := h.km.kc.lay W.toKgWfB hp
  refine WP.mono (seed_step L₀ (kgB_bases K.L) (by omega_using [hJ]) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.km.keep W hp hP.b hkc (fun r hr' => hr r (List.mem_append_left _ hr')), by rw [hP.cs .r15 (by decide)]; exact h.r15,
      hS, ?_⟩
  rw [L₀.keepBytes hP.b (hr (psP K, 32) (List.mem_append_right _ (List.mem_singleton_self _)))]
  exact h.ps

/-- Row 0 of `Â`, and `PRF₂(σ, 0)` and `PRF₂(σ, 1)`. -/
theorem frag0_ok (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hb : v.callee.batchP16 = some p) {s : State}
    (h : KN K 6 σ s) :
    WP isa (frag0 K p) s (KG K σ 0 false) := by
  have k3 := W.k3
  have hc0 := W.c0
  simp only [Bool.and_eq_true] at hc0
  obtain ⟨hkc0, hr0⟩ := keepAll_spec hc0.2
  obtain L₀ := h.kc.lay W.toKgWfB hp
  obtain sd : ∀ J < 4, ∀ t, S0 K σ J t → WP isa (seedAt J ((0 + J) / 3) ((0 + J) % 3)) t (S0 K σ (J + 1)) :=
    fun J hJ t ht => by have := seed0_ok W hp hJ ht; rwa [k3] at this
  unfold frag0
  refine WP.seq (WP.mono (copy_okL L₀ (dst := psP K) (src := sigP) (n := 32) (by decide) hc0.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  obtain i₁ : S0 K σ 0 s₁ := ⟨h.km.keep W hp hP₁.b hkc0 hr0, by rw [hP₁.cs .r15 (by decide)]; exact h.r15,
    ⟨by rw [L₀.keepBytes hP₁.b (hr0 (sc oSB, 32) (by simp))]; exact h.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_cs, hb₁, h.sig]⟩
  obtain s0 := sd 0 (by decide) s₁ i₁
  refine WP.seq (WP.mono s0 fun s₂ i₂ => ?_)
  obtain s1 := sd 1 (by decide) s₂ i₂
  refine WP.seq (WP.mono s1 fun s₃ i₃ => ?_)
  obtain s2 := sd 2 (by decide) s₃ i₃
  refine WP.seq (WP.mono s2 fun s₄ i₄ => ?_)
  obtain s3 := sd 3 (by decide) s₄ i₄
  refine WP.seq (WP.mono s3 fun s₅ i₅ => ?_)
  have hsm := W.sm0
  simp only [Bool.and_eq_true] at hsm
  obtain ⟨hkc, hr⟩ := keepAll_spec hsm.2
  obtain L₅ := i₅.km.kc.lay W.toKgWfB hp
  rw [Top16.aP, Nat.mul_zero, Nat.add_zero]
  refine WP.mono (sampleHAtP16_ok (v.batchP16 p hb (0, 2) (by decide)) (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  obtain km₆ := i₅.km.keep W hp h₆.b hkc hr
  refine ⟨km₆, fun _ h => absurd h (Nat.not_lt_zero _), ?_, fun N hN => ?_, fun h => absurd h (by decide)⟩
  · have m₀ := MatB16.zero K.L.k K.oA (rhoK K.L σ) i₅.r15
    have := EkF16.MatB16.three (K := K) m₀ L₅ h₆.b (fun e' he' => absurd he' (Nat.not_lt_zero _)) ?_ fun t ht f hf => ?_
    · simpa using this
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega_using [hk]))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega_using [ht])]; simpa using hf)
      rwa [poly4W, pBytes_true, pa_off] at this
  · have e := h₆.pout N hN
    rw [pa_off, pa_off, i₅.ps, Nat.zero_add] at e
    rw [h₆.b.pa rbx_bases, poP, Nat.add_assoc]; exact e

/-- The sponge's state zeroed. -/
theorem hzG_ok {s : State} (h : KG K σ 0 false s) : WP isa (.block (Encaps16.hzero K)) s (KG K σ 0 true) := by
  have hc := W.hz
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  obtain L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (EkF16.hzero16_ok L₀ hc.1) fun s' ⟨hP, hz⟩ => ?_
  refine ⟨h.toKM.keep W hp hP.b hkc fun r hr' => hr r (List.mem_append_left _ (List.mem_append_left _ hr')),
    fun _ h => absurd h (Nat.not_lt_zero _),
    ⟨by rw [hP.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP.b
      (hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))))
      (h.mat.mat e' he' f hf)⟩, fun N hN => ?_, fun _ => ?_⟩
  · rw [L₀.keepBytes hP.b (hr (poP K N, 128) (List.mem_append_right _ (List.mem_map.2 ⟨N, List.mem_range.2 hN, rfl⟩)))]
    exact h.pout N hN
  · rw [hP.pa rbx_cs, hz]; exact (HSponge.hstate_zero _).symm

/-- `s ‖ e`, polynomial `N < 2`, from row 0's outputs of `PRF₂`. -/
theorem cbdP_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2) {s : State} (h : KG K σ N true s) :
    WP isa (cbdP K A N) s (KG K σ (N + 1) true) := by
  obtain hc := W.cP N hN
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  obtain L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.pout N hN, ← hP₁.pa rbx_cs] at hp₁
  obtain mx : ∀ N' < 6, N' ≠ N → (rP K N', 512) ∈ rRx K N := fun N' h₁ h₂ =>
    List.mem_map.2 ⟨N', List.mem_filter.2 ⟨List.mem_range.2 h₁, by simpa using h₂⟩, rfl⟩
  refine ⟨⟨h.kc.step W.toKgWfB hp hP₁.b hkc, ?_, ?_, ?_, fun N' hN' h2 => ?_⟩, fun N' hN' => ?_,
    ⟨by rw [hP₁.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP₁.b
      (hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))))) (h.mat.mat e' he' f hf)⟩, fun N' hN' => ?_, fun _ => ?_⟩
  · rw [L₀.keepBytes hP₁.b (hr (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP₁.b (hr (sigP, 32) (by simp))]; exact h.sig
  · rw [L₀.keepBytes hP₁.b (hr (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly16 hP₁.b (hr (rP K N', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mx N' hN' (by omega_using [hN, h2]))))))) (h.se N' hN' h2)
  · rcases (by omega_using [hN'] : N' < N ∨ N' = N) with hN'' | rfl
    · exact L₀.keepPoly16 hP₁.b (hr (rP K N', 512) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (mx N' (by omega_using [hN, hN']) (by omega_using [hN'']))))))) (h.se0 N' hN'')
    · exact hp₁
  · rw [L₀.keepBytes hP₁.b (hr (poP K N', 128) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))))]
    exact h.pout N' hN'
  · rw [EkF.stateAt_keep L₀ hP₁.b (hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))]
    exact h.hs rfl

/-- `vg_mlkem768_kpke_keygen_ntt`: `ŝ`, `ê` and `dk_PKE`; before row 0's `t̂`. -/
theorem nttG_ok (hK : KgRowsOk K.L) {s : State} (h : KG K σ 2 true s) : WP isa (nttAt K) s (KH K σ 0 3) := by
  have hc := W.nt
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  obtain L₀ := h.kc.lay W.toKgWfB hp
  have k3 := W.k3
  obtain se : ∀ N < 6, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N) := fun N hN => by
    rcases (by omega_using [] : N < 2 ∨ 2 ≤ N) with h2 | h2
    exacts [h.se0 N h2, h.se N hN h2]
  obtain red : VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k) := fun N hN => by
    rw [sc_w16]; exact (se N (by omega_using [k3, hN])).1
  rw [← k3] at hc
  refine WP.mono (kgNttAt_okL hK L₀ rbx_na rbx_na rbx_na rbx_na hc.1 red) fun s' ⟨hP, hS, hE, hD⟩ => ?_
  obtain eS : (vecAtW 16 s.mem (pa s (sc K.oR)) K.L.k).map ntt = (List.range 3).map (KPke.kgS K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgS]
    rw [sc_w16, (se j (by have := List.mem_range.mp hj; omega_using [this])).2]
  obtain eE : (vecAtW 16 s.mem (pa s (sc K.oR) + BitVec.ofNat 64 (512 * K.L.k)) K.L.k).map ntt =
      (List.range 3).map (KPke.kgE K.L.p (kgD σ)) := by
    rw [k3]; simp only [vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgE]
    rw [w16_off, pa_off, show K.oR + (512 * 3 + 512 * j) = K.oR + 512 * (3 + j) by omega_using []]
    have := (se (3 + j) (by have := List.mem_range.mp hj; omega_using [this])).2
    rw [Top16.rP] at this
    rw [this, show K.L.p.k = 3 from k3]
  rw [eS, k3] at hS; rw [eE, k3] at hE; rw [eS, k3] at hD
  obtain hA : ∀ e' < 3, keepB (kgB K.L) ntW (aP K e') 512 = true := fun e' he' =>
    hr (aP K e', 512) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩)))
  refine ⟨h.kc.step W.toKgWfB hp hP.b (by rw [k3]; exact hkc), ?_, ?_, fun j hj => ?_, fun j hj _ => ?_, ?_,
    ⟨by rw [hP.cs .r15 (by decide)]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP.b
      (by rw [k3]; exact hA e' he') (h.mat.mat e' he' f hf)⟩,
    fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩⟩
  · rw [L₀.keepBytes hP.b (by rw [k3]; exact hr (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP.b (by rw [k3]; exact hr (sc oSB, 32) (by simp))]; exact h.sb
  · rw [hP.pa rbx_cs, ← pa_off]; exact vecIs_get hS hj
  · rw [hP.pa rbx_cs, ← pa_off]; exact vecIs_get hE hj
  · rw [hP.pa r13_cs, hD, KPke.dkPKE, KPke.catK_eq, show K.L.p.k = 3 from k3]
    simp only [encodeVec, List.flatMap_map]
  · rw [EkF.stateAt_keep L₀ hP.b (by rw [k3]; exact hr (hsP K, 200) (List.mem_append_right _ (List.mem_singleton_self _)))]
    exact h.hs rfl

/-- The rows, and the tail if every `SampleNTT` succeeded. -/
theorem rows_ok (hK : KgRowsOk K.L) (v : Sample4Impl) {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b)
    {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) {s : State} (h : KN K 6 σ s) :
    WP isa (rows K b p v.callee.arith) s (KEnd K.L σ) := by
  unfold rows
  refine WP.seq (WP.mono (frag0_ok W hp v hpb h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hzG_ok W hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (cbdP_ok W hp v.arith (N := 0) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (cbdP_ok W hp v.arith (N := 1) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (nttG_ok W hp hK h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (rowIf_ok W hp hK (i := 0) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (frag_ok W hp v hb (i := 1) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (rowIf_ok W hp hK (i := 1) (by decide) h₇) fun s₈ h₈ => ?_)
  exact WP.seq (WP.mono (frag_ok W hp v hb (i := 2) (by decide) h₈) fun s₉ h₉ => last_ok W hp hK h₉)

end

theorem kemKeyGenH16_correct {K : Kem16} (hK : KgRowsOk K.L) (v : Sample4Impl) (W : KgH16Wf K)
    {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {p : Nat → Nat → Prog isa}
    (hpb : v.callee.batchP16 = some p) (hctl : ctlOk (kemKeyGenH16 K v.callee b p) = true) (σ : State) (hp : (keyGenK K.L).pre σ) :
    ∃ t s', Exec isa (kemKeyGenH16 K v.callee b p) σ t s' ∧ abiPreserved σ s' ∧ (keyGenK K.L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toKgWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok W.toKgWfB hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (prfs_ok W hp v h₂ h15') fun s₃ h₃ =>
        WP.seq (WP.mono (seqR_ok (I := fun k => KN K k σ) 4 2 (fun k hk hk' s hs => se_ok W hp v.arith (by omega_using [hk']) hk hs)
            s₃ h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (rows_ok W hp hK v hb hpb h₄) fun s₆ h₆ =>
            WP.mono (topEpi_ok h₆.kc.top (h₆.hin W.toKgWfB hp)) fun s₇ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toKgWfB h₆ hr hm⟩ : gprPreserved σ s₇ ∧ (keyGenK K.L).post σ s₇))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end KeyGenH

end VG.Proof.MlKem.X86_64

end

end

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
theorem sampleHAtP16_tr {N₀ m : Nat} {b : Prog isa} (hb : BatchPOk16 N₀ m b) {oa oz : Nat} :
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
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (regionModel.relCT_inline (Pre := (samplePNKW N₀ m).pre)
      (Pub := (samplePNKW N₀ m).pub) (fun s hs => let ⟨t, s', e, _, p⟩ := hb.ok s hs; ⟨t, s', e, p⟩) hb.ct ?_)
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
    (rel2_of (v.prfs_tr (kgB_bases K.L) (by omega_using []) hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
      kc_lrel Wb p₁ p₂ pub h₁.1.kc h₂.1.kc)

theorem se_tr (v : Sample4Impl) :
    RelCT isa (R K.L (KN K 2)) (seqR (cbdN K v.callee.arith) 2 4) (R K.L (KN K 6)) := by
  have Wb := W.toKgWfB
  exact seqR_tr (R := fun k => R K.L (KN K k)) 4 2 fun N hN hN' =>
    relInv (fun σ s hp hs => se_ok W hp v.arith (by omega_using [hN']) hN hs)
      (rel2_of (cbd2_16At_trL v.arith rbx_na (by
          have h := W.se N (by omega_using [hN']); simp only [Bool.and_eq_true] at h; exact h.1))
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
    rcases (by omega_using [] : N < 2 ∨ 2 ≤ N) with h2 | h2
    exacts [(h.se0 N h2).1, (h.se N (by rw [k3] at hN; omega_using [hN]) h2).1]
  exact rel2_of (kgNttAt_trL hK rbx_na rbx_na rbx_na rbx_na hkn) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel Wb p₁ p₂ pub h₁.kc h₂.kc, red h₁, red h₂⟩

end

/-- After the noise, for the seed `ρ` of `Â`. -/
abbrev KNρ (K : Kem16) (ρ : List Byte) (x : State) : Prop :=
  ∃ σ, (keyGenK K.L).pre σ ∧ KN K 6 σ x ∧ rhoK K.L σ = ρ

section
variable (W : KgH16Wf K) (T : KgH16T K)
include W T

theorem frag0_tr (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) :
    RelCT isa (R K.L (KN K 6)) (frag0 K p) fun _ _ => True := by
  have Wb := W.toKgWfB
  have k3 := W.k3
  have hsd := W.sd0
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := W.sm0
  simp only [Bool.and_eq_true] at hsm
  have c4 := hsm.1
  have hB := v.batchP16 p hpb (0, 2) (by decide)
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
      have := seed_tr (kgB_bases K.L) (ρ := ρ) (n := K.L.k) (e₀ := 0) (K := J) (by omega_using [hJ]) hJ
        (by rw [k3]; omega_using [hJ]) (by rw [k3]; omega_using []) (hsd J hJ).1
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
      have := seed_tr (kgB_bases K.L) (ρ := ρ) (n := K.L.k) (e₀ := 3 * i) (K := J) (by omega_using [hi, hJ]) hJ
        (by rw [k3]; omega_using [hi, hJ]) (by rw [k3]; omega_using []) (hsd J hJ).1
      rwa [show (3 * i + J) / K.L.k = (3 * i + J) / 3 by rw [k3],
        show (3 * i + J) % K.L.k = (3 * i + J) % 3 by rw [k3]] at this
    have s0 := st 0 (by decide)
    rw [show (3 * i + 0) / 3 = i by omega_using [], show (3 * i + 0) % 3 = 0 by omega_using []] at s0
    have s1 := st 1 (by decide)
    rw [show (3 * i + 1) / 3 = i by omega_using [], show (3 * i + 1) % 3 = 1 by omega_using []] at s1
    have s2 := st 2 (by decide)
    rw [show (3 * i + 2) / 3 = i by omega_using [], show (3 * i + 2) % 3 = 2 by omega_using []] at s2
    have s3 := st 3 (by decide)
    rw [show (3 * i + 3) / 3 = i + 1 by omega_using [], show (3 * i + 3) % 3 = 0 by omega_using []] at s3
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
  · have := h.mat.mat (3 * i + j) (by rw [k3] at hj; omega_using [hj]) _ (aHat_part ho (e' := 3 * i + j) (by rw [k3] at hj; omega_using [hj]))
    rw [aP, sc_w16, show K.oA + 512 * (3 * i) + 512 * j = K.oA + 512 * (3 * i + j) by omega_using []]
    exact this.1
  · rw [pa_off]; exact (h.sh j (by omega_using [k3, hj])).1

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
    (hb : v.callee.batchHM16 = some b) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) :
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
    {b : Nat → Prog isa} (hb : v.callee.batchHM16 = some b) {p : Nat → Nat → Prog isa}
    (hpb : v.callee.batchP16 = some p) :
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
