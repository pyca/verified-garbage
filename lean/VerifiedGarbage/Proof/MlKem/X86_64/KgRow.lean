module

public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeKgRows
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
import VerifiedGarbage.Proof.MlKem.X86_64.RowY
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
import VerifiedGarbage.Proof.MlKem.X86_64.AccY
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_keygen_row`

The contract (`kgRowK`) and the steps of `KpkeKgRows.kgRow`: the prologue
saves the callee-saved registers in `scratch` (`KpkeMul.slots`, as
`keygen_mul` does) and keeps the pointers in registers; the table of the
products; a row of `keygen_mul` (`RowY.rowYg_ok`) in the MXCSR region;
`ByteEncode₁₂` of the sum to `ek` (`enc12In_ok`); the epilogue.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open DecMul (in_c)
open EncMul (hiR sub_hi)

/-- `vg_mlkem*_kpke_keygen_row(ek = rdi, a = rsi, s = rdx, e = rcx, scratch = r8)` of rank `k`. -/
def kgRowK (k : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 512 * k⟩, ⟨s.gpr .rdx, 1024 * k⟩] ∧
    s.wr = [⟨s.gpr .rdi, 384⟩, ⟨s.gpr .rcx, 1024⟩, ⟨s.gpr .r8, 4096⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ ⟨s.gpr .rsi, 512 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ ⟨s.gpr .rdx, 1024 * k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ (⟨s.gpr .rcx, 1024⟩) ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ (⟨s.gpr .r8, 4096⟩) ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * k⟩ (⟨s.gpr .rcx, 1024⟩) ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * k⟩ (⟨s.gpr .r8, 4096⟩) ∧
    Region.Disjoint ⟨s.gpr .rdx, 1024 * k⟩ (⟨s.gpr .rcx, 1024⟩) ∧
    Region.Disjoint ⟨s.gpr .rdx, 1024 * k⟩ (⟨s.gpr .r8, 4096⟩) ∧
    Region.Disjoint (⟨s.gpr .rcx, 1024⟩) (⟨s.gpr .r8, 4096⟩) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 384⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 512 * k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 1024 * k⟩ ∧ (retR s).Disjoint (⟨s.gpr .rcx, 1024⟩) ∧
    (retR s).Disjoint (⟨s.gpr .r8, 4096⟩) ∧
    (s.gpr .rdi).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 512 * k ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 1024 * k ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 1024 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 4096 ≤ 2 ^ 64 ∧
    VecReducedW 16 s.mem (s.gpr .rsi) k ∧ VecReduced s.mem (s.gpr .rdx) k ∧ Reduced s.mem (s.gpr .rcx)
  post s s' :=
    bytesAt s'.mem (s.gpr .rdi) 384 =
      encode12 (add (dot (vecAtW 16 s.mem (s.gpr .rsi) k) (vecAt s.mem (s.gpr .rdx) k)) (polyAt s.mem (s.gpr .rcx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace KgRow

/-- The facts of the precondition, by name. -/
structure EP (k : Nat) (σ : State) : Prop where
  rd : σ.rd = [⟨σ.gpr .rsi, 512 * k⟩, ⟨σ.gpr .rdx, 1024 * k⟩]
  wr : σ.wr = [⟨σ.gpr .rdi, 384⟩, pR (σ.gpr .rcx), cR (σ.gpr .r8)]
  kA : Region.Disjoint ⟨σ.gpr .rdi, 384⟩ ⟨σ.gpr .rsi, 512 * k⟩
  kS : Region.Disjoint ⟨σ.gpr .rdi, 384⟩ ⟨σ.gpr .rdx, 1024 * k⟩
  kE : Region.Disjoint ⟨σ.gpr .rdi, 384⟩ (pR (σ.gpr .rcx))
  kC : Region.Disjoint ⟨σ.gpr .rdi, 384⟩ (cR (σ.gpr .r8))
  aE : Region.Disjoint ⟨σ.gpr .rsi, 512 * k⟩ (pR (σ.gpr .rcx))
  aC : Region.Disjoint ⟨σ.gpr .rsi, 512 * k⟩ (cR (σ.gpr .r8))
  sE : Region.Disjoint ⟨σ.gpr .rdx, 1024 * k⟩ (pR (σ.gpr .rcx))
  sC : Region.Disjoint ⟨σ.gpr .rdx, 1024 * k⟩ (cR (σ.gpr .r8))
  eC : Region.Disjoint (pR (σ.gpr .rcx)) (cR (σ.gpr .r8))
  xK : (retR σ).Disjoint ⟨σ.gpr .rdi, 384⟩
  xA : (retR σ).Disjoint ⟨σ.gpr .rsi, 512 * k⟩
  xS : (retR σ).Disjoint ⟨σ.gpr .rdx, 1024 * k⟩
  xE : (retR σ).Disjoint (pR (σ.gpr .rcx))
  xC : (retR σ).Disjoint (cR (σ.gpr .r8))
  nK : (σ.gpr .rdi).toNat + 384 ≤ 2 ^ 64
  nA : (σ.gpr .rsi).toNat + 512 * k ≤ 2 ^ 64
  nS : (σ.gpr .rdx).toNat + 1024 * k ≤ 2 ^ 64
  nE : (σ.gpr .rcx).toNat + 1024 ≤ 2 ^ 64
  nC : (σ.gpr .r8).toNat + 4096 ≤ 2 ^ 64
  redA : VecReducedW 16 σ.mem (σ.gpr .rsi) k
  redS : VecReduced σ.mem (σ.gpr .rdx) k
  redE : Reduced σ.mem (σ.gpr .rcx)

theorem ep {k : Nat} {σ : State} (hp : (kgRowK k).pre σ) : EP k σ :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23⟩ := hp
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩


section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

/-- The slots of the saved registers, the MXCSR slot and the table are apart. -/
theorem slots_in {p : Reg × Nat} (hp : p ∈ KpkeMul.slots) : InRegions σ.wr (Spill.slot (σ.gpr .r8) p.2) 8 :=
  ⟨cR (σ.gpr .r8), by rw [E.wr]; simp, in_c (by have := DecMul.slots_bound p hp; omega)⟩

/-- After the prologue. -/
structure P1 (k : Nat) (σ s : State) : Prop where
  rbx : s.gpr .rbx = σ.gpr .r8
  r12 : s.gpr .r12 = σ.gpr .rdi
  rbp : s.gpr .rbp = σ.gpr .rsi
  r15 : s.gpr .r15 = σ.gpr .rdx
  r13 : s.gpr .r13 = σ.gpr .rcx
  rsp : s.gpr .rsp = σ.gpr .rsp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = Spill.saveMem σ.mem (σ.gpr .r8) σ.gpr KpkeMul.slots

theorem pro_ok {Q : State → Prop} {rest : Prog isa} (h : ∀ s, P1 k σ s → WP isa rest s Q) :
    WP isa (.seq (.block KpkeKgRows.proR) rest) σ Q := by
  unfold KpkeKgRows.proR
  rw [EncMul.saveE_eq]
  refine WP.seq (Spill.save_then .r8 KpkeMul.slots (fun p hp => slots_in E hp) ?_)
  refine WP.mono (Q := P1 k σ) (by vrunm; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) h

end

/-- The inner code of the MXCSR region of the row. -/
abbrev rowIn (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .mov .rcx (.reg .rbx)]) (rowY16 k)

/-- After the row: the sum in `e`, the saved registers kept. -/
structure P2 (k : Nat) (σ s : State) : Prop where
  rbx : s.gpr .rbx = σ.gpr .r8
  r12 : s.gpr .r12 = σ.gpr .rdi
  r13 : s.gpr .r13 = σ.gpr .rcx
  rsp : s.gpr .rsp = σ.gpr .rsp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  saved : Spill.Saved s.mem (σ.gpr .r8) σ.gpr KpkeMul.slots
  frame : Frame [cR (σ.gpr .r8), pR (σ.gpr .rcx)] σ.mem s.mem
  sum : PolyIs s.mem (σ.gpr .rcx)
    (add (polyAt σ.mem (σ.gpr .rcx)) (dotP (vecAtW 16 σ.mem (σ.gpr .rsi) k) (vecAt σ.mem (σ.gpr .rdx) k) k))

section
variable {k : Nat} {σ : State} (E : EP k σ)
include E

theorem row_ok (hk : k = 3 ∨ k = 4) (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowIn k) = true)
    {s : State} (h : P1 k σ s) : WP isa (.seq (.block ([.mov .rcx (.reg .rbx)] ++ Bodies.avx2.tab))
      (withMxcsr .rbx oMx (rowIn k))) s (P2 k σ) := by
  have hk4 : k ≤ 4 := by omega
  have nC := E.nC
  have nA := E.nA
  have nS := E.nS
  have hcw : cR (σ.gpr .r8) ∈ σ.wr := by rw [E.wr]; simp
  have hew : pR (σ.gpr .rcx) ∈ σ.wr := by rw [E.wr]; simp
  -- the frame of the save
  have hf1 : Frame [cR (σ.gpr .r8)] σ.mem s.mem := by
    rw [h.mem]
    exact Spill.saveMem_frame_base σ.mem (σ.gpr .r8) σ.gpr KpkeMul.slots (L := 4096)
      (fun p hp' => by have := DecMul.slots_bound p hp'; omega) (by decide)
  have hsv : Spill.Saved s.mem (σ.gpr .r8) σ.gpr KpkeMul.slots := by
    rw [h.mem]; exact Spill.saveMem_saved _ _ _ _ (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .rcx = (σ.gpr .r8) ∧ s1.mem = s.mem ∧ Keep [.rcx] s s1)
    (by vrunm [h.rbx]; exact ⟨fun r hr => by
      simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl⟩)
    fun s1 ⟨h1cx, hm1, k1⟩ => ?_
  have hin : InRegions s1.wr (s1.gpr .rcx + BitVec.ofNat 64 3328) 256 := by
    rw [k1.2.2, h.wr, h1cx]; exact ⟨_, hcw, in_c (by decide)⟩
  refine WP.mono (BodiesOk.avx2.tab s1 hin) fun s2 ⟨hT2, hf2, k2⟩ => ?_
  rw [h1cx] at hT2 hf2
  rw [hm1] at hf2
  have k12 := k1.trans k2
  have h2bx : s2.gpr .rbx = (σ.gpr .r8) := by rw [k12.gpr (by decide), h.rbx]
  have hf12 : Frame [cR (σ.gpr .r8)] σ.mem s2.mem :=
    hf1.trans (hf2.sub fun r hr => ⟨cR (σ.gpr .r8), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact DecMul.sub_c (by decide)⟩)
  have hsv2 : Spill.Saved s2.mem (σ.gpr .r8) σ.gpr KpkeMul.slots :=
    hsv.frame hf2 fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (EncMul.hi_dis_tab _).sub_left (sub_hi (DecMul.slots_bound p hp').1 (by
        have := (DecMul.slots_bound p hp').2; omega))
  have h0 : InRegions s2.wr ((σ.gpr .r8) + BitVec.ofNat 64 768) 4 := by
    rw [k12.2.2, h.wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have h4 : InRegions s2.wr ((σ.gpr .r8) + BitVec.ofNat 64 772) 4 := by
    rw [k12.2.2, h.wr]; exact ⟨_, hcw, in_c (by decide)⟩
  have hfa : ∀ {o n : Nat}, o + n ≤ 512 * k → Region.Disjoint ⟨σ.gpr .rsi + BitVec.ofNat 64 o, n⟩ (cR (σ.gpr .r8)) :=
    fun h => E.aC.sub_left (Offset.sub_base _ h)
  have hfs : ∀ {o n : Nat}, o + n ≤ 1024 * k → Region.Disjoint ⟨σ.gpr .rdx + BitVec.ofNat 64 o, n⟩ (cR (σ.gpr .r8)) :=
    fun h => E.sC.sub_left (Offset.sub_base _ h)
  show WP isa (withMxcsr .rbx 768 (rowIn k)) s2 (P2 k σ)
  refine WP.mono (withMxcsr_ok' (r := .rbx) ⟨by decide, by decide⟩ [.rax, .rcx, .rdx, .rsi, .rdi, .r8]
    ⟨by decide, by decide⟩ h2bx h0 h4 hwo (Q := P2 k σ) (fun s3 k3 f3 => ?_)) fun s5 ⟨s4, hq4, hf5, k5⟩ => ?_
  · -- the row
    have hmx : Region.Sub (mxR (σ.gpr .r8)) (cR (σ.gpr .r8)) := DecMul.sub_c (by decide)
    have hf3 : Frame [cR (σ.gpr .r8)] σ.mem s3.mem :=
      hf12.trans (f3.sub fun r hr => ⟨cR (σ.gpr .r8), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact hmx⟩)
    have k23 := k12.trans k3
    refine WP.seq (WP.mono (Q := fun (s4 : State) => s4.gpr .rdi = σ.gpr .rcx ∧ s4.gpr .rsi = σ.gpr .rsi ∧
        s4.gpr .rdx = σ.gpr .rdx ∧ s4.gpr .rcx = σ.gpr .r8 ∧ s4.mem = s3.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] s3 s4)
      (by
        vrunm [k23.gpr (r := .r13) (by decide), k23.gpr (r := .rbp) (by decide), k23.gpr (r := .r15) (by decide),
          k23.gpr (r := .rbx) (by decide), h.r13, h.rbp, h.r15, h.rbx]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s4 ⟨h4di, h4si, h4dx, h4cx, hm4, k4⟩ => ?_)
    have hsr4 : s4.rd = [⟨σ.gpr .rsi, 512 * k⟩, ⟨σ.gpr .rdx, 1024 * k⟩] := by
      rw [k4.2.1, k3.2.1, k12.2.1, h.rd, E.rd]
    have hsw4 : s4.wr = [⟨σ.gpr .rdi, 384⟩, pR (σ.gpr .rcx), cR (σ.gpr .r8)] := by
      rw [k4.2.2, k3.2.2, k12.2.2, h.wr, E.wr]
    have hf4 : Frame [cR (σ.gpr .r8)] σ.mem s4.mem := by rw [hm4]; exact hf3
    have hx : RowY.CtxG (FRep.u16 512) k (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8)
        (vecAtW 16 σ.mem (σ.gpr .rsi) k) (vecAt σ.mem (σ.gpr .rdx) k) s4.mem s4.rd s4.wr :=
      { k1 := by omega
        k4 := hk4
        fl := by rw [vecAtW_length]
        gl := by rw [vecAt_length]
        F := fun j hj => by
          show PolyIsW 16 _ _ _
          rw [vecAtW16_get _ _ hj]
          refine polyIsW16_frame hf4 (fun r hr => ?_) ⟨?_, rfl⟩
          · simp only [List.mem_singleton] at hr; subst hr; exact hfa (by omega)
          · have := E.redA j hj
            rwa [show 32 * 16 * j = 512 * j by omega] at this
        G := fun j hj => by
          rw [vecAt_get _ _ hj]
          exact polyIs_frame hf4 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hfs (by omega))
            ⟨E.redS j hj, rfl⟩
        dF := fun j hj => (E.aE.sub_left (Offset.sub_base (n := 512) _ (by omega))).symm
        dG := fun j hj => (E.sE.sub_left (Offset.sub_base _ (by omega))).symm
        dT := E.eC.sub_right (DecMul.sub_c (by decide))
        inF := fun j hj => by
          rw [hsr4, hsw4]
          exact ⟨⟨σ.gpr .rsi, 512 * k⟩, by simp, Offset.contains_base (n := 512) _ (by omega) (by omega)⟩
        inG := fun j hj => by
          rw [hsr4, hsw4]
          exact ⟨⟨σ.gpr .rdx, 1024 * k⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
        inTab := by rw [hsr4, hsw4]; exact ⟨cR (σ.gpr .r8), by simp, in_c (by decide)⟩
        inT := by rw [hsw4]; exact ⟨pR (σ.gpr .rcx), by simp, Region.contains_self _ _⟩
        tab := by
          rw [hm4]
          exact tabY.frame f3 (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)) hT2
        red := (polyIs_frame hf4 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact E.eC)
          ⟨E.redE, rfl⟩).1 }
    refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8]
      (RowY.rowYg_ok (FRep.u16 512) hx h4si h4dx h4di h4cx) (rowY16_wo hk)) fun s5 ⟨⟨hP5, hf5, hrd5, hwr5⟩, k5⟩ => ?_
    have k35 := k4.trans k5
    have g : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp], s5.gpr r = s.gpr r := fun r hr => by
      rw [k35.gpr (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
        k23.gpr (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    have hfe : Frame [pR (σ.gpr .rcx)] s3.mem s5.mem := by rw [← hm4]; exact hf5
    refine ⟨by rw [g .rbx (by simp), h.rbx], by rw [g .r12 (by simp), h.r12], by rw [g .r13 (by simp), h.r13],
      by rw [g .rsp (by simp), h.rsp], by rw [hrd5, hsr4, E.rd], by rw [hwr5, hsw4, E.wr], ?_, ?_, ?_⟩
    · refine (hsv2.frame f3 fun p hp' r hr => ?_).frame hfe fun p hp' r hr => ?_
      · simp only [List.mem_singleton] at hr; subst hr
        have := DecMul.slots_bound p hp'
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact (E.eC.symm.sub_left (DecMul.sub_c (by have := DecMul.slots_bound p hp'; omega)))
    · exact (hf3.mono (by simp)).trans (hfe.mono (by simp))
    · rw [hm4] at hP5
      have he : polyAt s3.mem (σ.gpr .rcx) = polyAt σ.mem (σ.gpr .rcx) :=
        (polyIs_frame hf3 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact E.eC)
          ⟨E.redE, rfl⟩).2
      rw [he] at hP5
      exact hP5
  · refine ⟨by rw [k5.gpr (by simp), hq4.rbx], by rw [k5.gpr (by simp), hq4.r12], by rw [k5.gpr (by simp), hq4.r13],
      by rw [k5.gpr (by simp), hq4.rsp], by rw [k5.2.1, hq4.rd], by rw [k5.2.2, hq4.wr], ?_, ?_, ?_⟩
    · exact hq4.saved.frame hf5 fun p hp' r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := DecMul.slots_bound p hp'
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    · exact hq4.frame.trans (hf5.sub fun r hr => ⟨cR (σ.gpr .r8), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact DecMul.sub_c (by decide)⟩)
    · exact polyIs_frame hf5 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact E.eC.sub_right (DecMul.sub_c (by decide))) hq4.sum

end

theorem kgRow_wp {A : Prims} (hA : PrimsOk A) (hn : A.enc12.noCalls = true) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowIn L.k) = true) {σ : State} (hp : (kgRowK L.k).pre σ) :
    WP isa (KpkeKgRows.kgRow L A) σ fun s' => gprPreserved σ s' ∧ (kgRowK L.k).post σ s' := by
  have E := ep hp
  have nE := E.nE
  have nK := E.nK
  unfold KpkeKgRows.kgRow
  refine pro_ok E fun s1 h1 => ?_
  refine WP.seq (WP.mono (row_ok E hk hwo h1) fun s2 h2 => ?_)
  have e13 : pa s2 ((.r13, 0) : Ptr) = σ.gpr .rcx := by simp only [pa, h2.r13, add_ofNat_zero]
  have e12 : pa s2 ((.r12, 0) : Ptr) = σ.gpr .rdi := by simp only [pa, h2.r12, add_ofNat_zero]
  have hT : TwoHi (.r13, 0) (.r12, 0) 1024 384 s2 :=
    { off := ⟨by decide, by decide⟩
      d := by rw [e13, e12]; exact E.kE.symm
      rP := by rw [e13, show retR s2 = retR σ by simp only [retR, h2.rsp]]; exact E.xE
      rQ := by rw [e12, show retR s2 = retR σ by simp only [retR, h2.rsp]]; exact E.xK
      c := by
        rw [e13, e12, h2.rd, h2.wr, E.rd, E.wr]
        exact covers_append (covers_one ⟨pR (σ.gpr .rcx), by simp, Region.contains_self _ _⟩)
          (covers_one ⟨⟨σ.gpr .rdi, 384⟩, by simp, Region.contains_self _ _⟩)
      w := by
        rw [e12, h2.wr, E.wr]
        exact covers_one ⟨⟨σ.gpr .rdi, 384⟩, by simp, Region.contains_self _ _⟩ }
  refine WP.seq (WP.mono (enc12In_ok hA.enc12.ok hn (by decide) hT (by rw [e13]; exact h2.sum.1))
    fun s3 ⟨hP3, hb3⟩ => ?_)
  rw [e13, e12, h2.sum.2] at hb3
  rw [e12] at hP3
  have h3bx : s3.gpr .rbx = σ.gpr .r8 := by rw [hP3.cs .rbx (by decide), h2.rbx]
  have hsv3 : Spill.Saved s3.mem (s3.gpr .rbx) σ.gpr KpkeMul.slots := by
    rw [h3bx]
    exact h2.saved.frame hP3.frame fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.kC.symm.sub_left (DecMul.sub_c (by have := DecMul.slots_bound p hp'; omega))
  rw [DecMul.restore_eq]
  refine WP.mono (Spill.restore_ok .rbx KpkeMul.slots σ.gpr s3 (by decide) (fun p hp' => ?_) hsv3)
    fun s' ⟨g1, g2, hm', _, _⟩ => ⟨⟨Spill.calleeSaved_ok g1 g2 (by decide) (by
      rw [hP3.cs .rsp (by decide), h2.rsp]), ?_⟩, ?_⟩
  · rw [h3bx, hP3.rd, hP3.wr, h2.rd, h2.wr, E.rd, E.wr]
    exact ⟨cR (σ.gpr .r8), by simp, in_c (by have := DecMul.slots_bound p hp'; omega)⟩
  · rw [hm']
    have hf : Frame [cR (σ.gpr .r8), pR (σ.gpr .rcx), ⟨σ.gpr .rdi, 384⟩] σ.mem s3.mem :=
      (h2.frame.mono (by simp)).trans (hP3.frame.mono (by simp))
    refine hf.readW (r := retR σ) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [E.xC, E.xE, E.xK]
  · show bytesAt _ _ _ = _
    rw [hm', hb3, dotP_full (vecAtW_length _ _ _ _) (vecAt_length _ _ _), KgMul.add_comm_poly]

end KgRow

end VG.Proof.MlKem.X86_64
