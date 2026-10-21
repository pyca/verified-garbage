module

public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeKgRows
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.InlinePrim

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
  ⟨cR (σ.gpr .r8), by rw [E.wr]; simp, in_c (by have := DecMul.slots_bound p hp; omega)⟩

/-- `se`'s polynomial `j` is still as on entry. -/
theorem B.se {s : State} (h : B k σ s) {j : Nat} (hj : j < 2 * k) :
    PolyIsW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j)) (wid σ j) := by
  have hs : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * j), 512⟩ ⟨σ.gpr .rcx, 1024 * k⟩ :=
    Offset.sub_base _ (by omega)
  refine polyIsW16_frame h.frame (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [E.rC.sub_left hs, E.sR.symm.sub_left hs, E.eR.symm.sub_left hs, E.dR.symm.sub_left hs]
  · have := E.red j hj
    rwa [show 32 * 16 * j = 512 * j by omega] at this

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
  have hb := DecMul.slots_bound p hp
  have nC := E.nC
  have hs : Region.Sub ⟨Spill.slot (σ.gpr .r8) p.2, 8⟩ (cR (σ.gpr .r8)) := sub_c (by omega)
  rcases hr with hr | hr | hr | hr
  · exact (Offset.disjoint_base (σ.gpr .r8) (d := p.2) (n := 8) (k := 3072) (by omega) (by omega)).sub_right hr
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

theorem wok_ret {r : Region} (hr : WOk k σ r) : (retR σ).Disjoint r := by
  rcases hr with hr | hr | hr | hr
  · exact (E.xC.sub_right (Region.sub_prefix (by decide))).sub_right hr
  · exact E.xS.sub_right hr
  · exact E.xE.sub_right hr
  · exact E.xD.sub_right hr

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
        (fun p hp' => by have := DecMul.slots_bound p hp'; omega) (by decide)).mono (by simp)⟩ h12 hbp h15

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
  have eb : pa s ((.r15, 512 * j) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * j) := by simp only [pa, h.r15]
  have ef : pa s ((.r12, 1024 * j) : Ptr) = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) := by simp only [pa, h.r12]
  have hsS : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * j), 512⟩ ⟨σ.gpr .rcx, 1024 * k⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.mono (widenIn_ok (b := (.r15, 512 * j)) (f := (.r12, 1024 * j)) (F := wid σ j) (by omega) (by omega) (by simp) (by rw [eb]; exact h.se E (by omega))
    (by rw [eb, ef]; exact (E.sR.sub_left (sub_v _ hj)).sub_right hsS)
    (by
      rw [eb, ef, h.rd, h.wr, E.rd, E.wr]
      exact covers_append (covers_one ⟨⟨σ.gpr .rcx, 1024 * k⟩, by simp, Offset.contains_base (n := 512) _ (by omega) (by omega)⟩)
        (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩))
    (by rw [ef, h.wr, E.wr]; exact covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩))
    fun s' ⟨hP, hq⟩ => ?_
  rw [ef] at hP hq
  refine ⟨h.toB.step E hP fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (sub_v _ hj)),
    by rw [hP.cs .r12 (by decide), h.r12], by rw [hP.cs .rbp (by decide), h.rbp],
    by rw [hP.cs .r15 (by decide), h.r15], fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj'' | rfl
  · exact polyIs_frame hP.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact vv_dis _ (by omega) (by omega) hj (by omega)) (h.w j' hj'')
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
  have hsr : s.rd = [⟨σ.gpr .rcx, 1024 * k⟩] := by rw [h.rd, E.rd]
  have hsw : s.wr = [⟨σ.gpr .rdi, 384 * k⟩, vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, cR (σ.gpr .r8)] := by
    rw [h.wr, E.wr]
  have hS := h.srest j (Nat.le_refl _) hj
  unfold KpkeMul.nttK16 KpkeMul.nttKg
  -- `NTT(s[j])` in place
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) ∧
      s1.gpr .rsi = σ.gpr .r8 ∧ s1.gpr .r10 = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) ∧ s1.mem = s.mem ∧
      Keep [.rdi, .rsi, .r10] s s1) (by
        vrunm [h.r12, h.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, h1si, h1r10, hm1, k1⟩ => ?_)
  have hsp1 : s1.gpr .rsp = σ.gpr .rsp := by rw [k1.gpr (by decide), h.rsp]
  have dSC : (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (σ.gpr .r8)) :=
    (E.sC.sub_left (sub_v _ hj)).sub_right (sub_c0 _)
  have dEC : (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j))).Disjoint (pR (σ.gpr .r8)) :=
    (E.eC.sub_left (sub_v _ hj)).sub_right (sub_c0 _)
  refine WP.seq (WP.inline (k := nttOK) BodiesOk.avx2.nttO (rd := [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j))])
    (wr := [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)]) ?_ ?_ ?_
    (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_) BodiesOk.avx2.nc.1)
  · simp only [nttOK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
      h1di, h1si, h1r10, hsp1, hm1, retR]
    exact ⟨trivial, trivial, dSC, dSC, E.xS.sub_right (sub_v _ hj), E.xC.sub_right (sub_c0 _), hS.1⟩
  · rw [k1.2.1, k1.2.2, hsr, hsw]
    exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩)
      (covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩)
        (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩))
  · rw [k1.2.2, hsw]
    exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩)
      (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩)
  simp only [nttOK, State.withRegions_gpr, State.withRegions_mem, h1di, h1r10, hm1, hS.2] at hpost2
  rw [hm1] at hf2
  have g2 : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => by
    rw [habi2.1 r hr, k1.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)]
  have wS : ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)], WOk k σ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inr (.inl (sub_v _ hj)), .inl (Region.sub_prefix (by decide))]
  have hb2 : B k σ s2 := h.toB.stepF E (by rw [hrd2, k1.2.1]) (by rw [hwr2, k1.2.2]) g2 hf2 wS
  have eA : σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j) =
      σ.gpr .rcx + BitVec.ofNat 64 (512 * (k + j)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  have hE : PolyIsW 16 s2.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j)) (ewid k σ j) := by
    simp only [ewid]; rw [eA]; exact hb2.se E (by omega)
  have hsub : Region.Sub (sR (σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j)))
      ⟨σ.gpr .rcx, 1024 * k⟩ := by rw [eA]; exact Offset.sub_base _ (by omega)
  -- `NTT(e[j])` to `e[j]`
  refine WP.seq (WP.mono (Q := fun (s3 : State) =>
      s3.gpr .rdi = σ.gpr .rcx + BitVec.ofNat 64 (512 * k) + BitVec.ofNat 64 (512 * j) ∧
      s3.gpr .rsi = σ.gpr .r8 ∧ s3.gpr .r10 = σ.gpr .rdx + BitVec.ofNat 64 (1024 * j) ∧ s3.mem = s2.mem ∧
      Keep [.rdi, .rsi, .r10] s2 s3) (by
        vrunm [g2 .r15 (by decide), g2 .rbx (by decide), g2 .rbp (by decide), h.r15, h.rbx, h.rbp]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, h3r10, hm3, k3⟩ => ?_)
  have hsp3 : s3.gpr .rsp = σ.gpr .rsp := by rw [k3.gpr (by decide), hb2.rsp]
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
      rw [eA]; exact Offset.contains_base (n := 512) _ (by omega) (by omega)⟩)
      (covers_append (covers_one ⟨vR (σ.gpr .rdx) k, by simp, in_vec _ (by omega) hj⟩)
        (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩))
  · rw [k3.2.2, hb2.wr, E.wr]
    exact covers_append (covers_one ⟨vR (σ.gpr .rdx) k, by simp, in_vec _ (by omega) hj⟩)
      (covers_one ⟨cR (σ.gpr .r8), by simp, DecMul.in_c0 _⟩)
  simp only [nttO16K, State.withRegions_gpr, State.withRegions_mem, h3di, h3r10, hm3, hE.2] at hpost4
  rw [hm3] at hf4
  have g4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by
    rw [habi4.1 r hr, k3.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide), g2 r hr]
  have wE : ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)], WOk k σ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inr (.inr (.inl (sub_v _ hj))), .inl (Region.sub_prefix (by decide))]
  have g34 : ∀ r ∈ calleeSaved, s4.gpr r = s2.gpr r := fun r hr => by
    rw [habi4.1 r hr]
    exact k3.gpr (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hb4 : B k σ s4 := hb2.stepF E (by rw [hrd4, k3.2.1]) (by rw [hwr4, k3.2.2]) g34 hf4 wE
  -- what the writes keep
  have fS2 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega) hj' hj hne, (E.sC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  have fS4 : ∀ {j'}, j' < k → ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis E.sE hj' hj, (E.sC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  have fT2 : ∀ {j'}, j' < k → ∀ r ∈ [pR (σ.gpr .rsi + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vr_dis E.sE.symm hj' hj, (E.eC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
  have fT4 : ∀ {j'}, j' < k → j' ≠ j → ∀ r ∈ [pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j)), pR (σ.gpr .r8)],
      (pR (σ.gpr .rdx + BitVec.ofNat 64 (1024 * j'))).Disjoint r := fun hj' hne r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [vv_dis _ (by omega) hj' hj hne, (E.eC.sub_left (sub_v _ hj')).sub_right (sub_c0 _)]
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
    refine polyIs_frame hf4 (fS4 (by omega)) ?_
    by_cases hje : j' = j
    · subst hje; exact hpost2
    · exact polyIs_frame hf2 (fS2 (by omega) hje) (h.sdone j' (by omega))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact polyIs_frame hf4 (fS4 hj2) (polyIs_frame hf2 (fS2 hj2 (by omega)) (h.srest j' (by omega) hj2))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    by_cases hje : j' = j
    · subst hje; exact hpost4
    · exact polyIs_frame hf4 (fT4 (by omega) hje) (polyIs_frame hf2 (fT2 (by omega)) (h.tdone j' (by omega)))

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
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r14, .r15, .rbp]
      (.loop KpkeMul.nttK16 .ne) = true) {s : State} (h : WI k σ k s) :
    WP isa (KpkeKgRows.nttsN L) s (NI k σ k) := by
  have nC := E.nC
  have hcw : cR (σ.gpr .r8) ∈ σ.wr := by rw [E.wr]; simp
  unfold KpkeKgRows.nttsN
  rw [hL]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r15 = σ.gpr .rcx + BitVec.ofNat 64 (512 * k) ∧
      s1.gpr .r14 = BitVec.ofNat 64 k ∧ s1.mem = s.mem ∧ Keep [.r15, .r14] s s1) (by
        vrunm [h.r15, sx_ofNat (show 512 * k < 2 ^ 31 by omega)]
        refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
        · apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h115, h114, hm1, k1⟩ => ?_)
  have h1bx : s1.gpr .rbx = σ.gpr .r8 := by rw [k1.gpr (by decide), h.rbx]
  have h0 : InRegions s1.wr (σ.gpr .r8 + BitVec.ofNat 64 768) 4 := by
    rw [k1.2.2, h.wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s1.wr (σ.gpr .r8 + BitVec.ofNat 64 772) 4 := by
    rw [k1.2.2, h.wr]; exact ⟨_, hcw, in_c (by decide)⟩
  show WP isa (withMxcsr .rbx 768 _) s1 _
  refine WP.mono (withMxcsr_ok' (r := .rbx) ⟨by decide, by decide⟩ _ ⟨by decide, by decide⟩ h1bx h0 h4 hwo
    (Q := NI k σ k) (fun s2 k2 f2 => ?_)) fun s5 ⟨s4, hq4, hf5, k5⟩ => ?_
  · have k12 := k1.trans k2
    rw [hm1] at f2
    have hb2 : B k σ s2 := h.toB.stepR E (by rw [k12.2.1]) (by rw [k12.2.2]) (k12.gpr (by decide))
      (k12.gpr (by decide)) (k12.gpr (by decide)) f2 mx_wok
    refine wp_countdown (cnt := .r14) (N := k) (by omega) hk0 (NI k σ) (fun j hj u hI _ => step_ok E hk hj hI)
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
      fun j h1 h2 => absurd h2 (by omega),
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
  have ep : pa s ((.r12, 1024 * j) : Ptr) = σ.gpr .rsi + BitVec.ofNat 64 (1024 * j) := by simp only [pa, h.r12]
  have eq : pa s ((.r13, 384 * j) : Ptr) = σ.gpr .rdi + BitVec.ofNat 64 (384 * j) := by simp only [pa, h.r13]
  have hsub : Region.Sub ⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ ⟨σ.gpr .rdi, 384 * k⟩ :=
    Offset.sub_base _ (by omega)
  have hsr : s.rd ++ s.wr = [⟨σ.gpr .rcx, 1024 * k⟩] ++
      [⟨σ.gpr .rdi, 384 * k⟩, vR (σ.gpr .rsi) k, vR (σ.gpr .rdx) k, cR (σ.gpr .r8)] := by rw [h.rd, h.wr, E.rd, E.wr]
  have hT : TwoHi (.r12, 1024 * j) (.r13, 384 * j) 1024 384 s :=
    { off := ⟨by omega, by omega⟩
      d := by rw [ep, eq]; exact (E.dS.symm.sub_left (sub_v _ hj)).sub_right hsub
      rP := by rw [ep, show retR s = retR σ by simp only [retR, h.rsp]]; exact E.xS.sub_right (sub_v _ hj)
      rQ := by rw [eq, show retR s = retR σ by simp only [retR, h.rsp]]; exact E.xD.sub_right hsub
      c := by
        rw [ep, eq, hsr]
        exact covers_append (covers_one ⟨vR (σ.gpr .rsi) k, by simp, in_vec _ (by omega) hj⟩)
          (covers_one ⟨⟨σ.gpr .rdi, 384 * k⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
      w := by
        rw [eq, h.wr, E.wr]
        exact covers_one ⟨⟨σ.gpr .rdi, 384 * k⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩ }
  refine WP.mono (enc12In_ok hA.enc12.ok hn (by simp [NA]) hT (by rw [ep]; exact (h.shat j hj).1))
    fun s' ⟨hP, hb⟩ => ?_
  rw [ep, eq, (h.shat j hj).2] at hb
  rw [eq] at hP
  have dW : ∀ {r : Region}, r.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ →
      ∀ r' ∈ [(⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * j), 384⟩ : Region)], r.Disjoint r' := fun hd r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  refine ⟨h.toB.step E hP fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inr hsub)),
    by rw [hP.cs .r12 (by decide), h.r12], fun j' hj' => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · exact polyIs_frame hP.frame (dW ((E.dS.symm.sub_left (sub_v _ hj')).sub_right hsub)) (h.shat j' hj')
  · exact polyIs_frame hP.frame (dW ((E.dE.symm.sub_left (sub_v _ hj')).sub_right hsub)) (h.ehat j' hj')
  · rcases (by omega : j' < j ∨ j' = j) with hj'' | rfl
    · rw [bytesAt_frame hP.frame (dW (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))) (by omega)]
      exact h.dk j' hj''
    · exact hb

end

theorem kgNtt_wp {A : Prims} (hA : PrimsOk A) (hn : A.enc12.noCalls = true) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r14, .r15, .rbp]
      (.loop KpkeMul.nttK16 .ne) = true) {σ : State} (hp : (kgNttK L.k).pre σ) :
    WP isa (KpkeKgRows.kgNtt L A) σ fun s' => gprPreserved σ s' ∧ (kgNttK L.k).post σ s' := by
  have E := ep hp
  have hk4 : L.k ≤ 4 := by omega
  have nS := E.nS
  have nC := E.nC
  unfold KpkeKgRows.kgNtt
  refine pro_ok E fun s1 hb h12 hbp h15 => ?_
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => WI L.k σ j s) L.k 0
    (fun j _ hj s h => wide_ok E hk4 (by omega) h) s1 ⟨hb, h12, hbp, h15, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  refine WP.seq (WP.mono (ntts_ok E rfl hk4 (by omega) hwo h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (Q := fun (s4 : State) => s4.gpr .r12 = σ.gpr .rsi ∧ s4.mem = s3.mem ∧ Keep [.r12] s3 s4)
    (by
      vrunm [h3.r12, sx_ofNat (show 1024 * L.k < 2 ^ 31 by omega)]
      refine ⟨BitVec.add_sub_cancel _ _, fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s4 ⟨h412, hm4, k4⟩ => ?_)
  have hb4 : B L.k σ s4 := h3.toB.stepR E k4.2.1 k4.2.2 (k4.gpr (by decide)) (k4.gpr (by decide))
    (k4.gpr (by decide)) (W := []) (by rw [hm4]; exact Frame.refl _ _) (fun _ h => absurd h (by simp))
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => DI L.k σ j s) L.k 0
    (fun j _ hj s h => enc_ok E hA hn hk4 (by omega) h) s4 ⟨hb4, h412,
      fun j hj => by rw [hm4]; exact h3.sdone j hj, fun j hj => by rw [hm4]; exact h3.tdone j hj,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s5 h5 => ?_)
  rw [Nat.zero_add] at h5
  have hsv5 : Spill.Saved s5.mem (s5.gpr .rbx) σ.gpr KpkeMul.slots := by rw [h5.rbx]; exact h5.saved
  rw [DecMul.restore_eq]
  refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots σ.gpr s5 (by decide) (fun p hp' => ?_) hsv5)
    fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by rw [h5.rsp]), ?_⟩, ?_, ?_, ?_⟩
  · rw [h5.rbx, h5.rd, h5.wr, E.rd, E.wr]
    exact ⟨cR (σ.gpr .r8), by simp, in_c (by have := DecMul.slots_bound p hp'; omega)⟩
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
