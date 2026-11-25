module

-- separate module: the prepared callee's proof is independent of its AES-GCM caller, whose proofs it would pull in here
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Spec.Gcm.Bitsliced
import VerifiedGarbage.Proof.Gcm.RISCV64.Law
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH on RISC-V with the key's words computed before

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64
open VG.Impl.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghashOperand ghashClass)

/-- What `cachedHash` needs, for the hash subkey `H`. -/
structure CachedPre (H : Block) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 288⟩, ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a1, 16⟩, ⟨s.gpr .a4, 256⟩]
  al : (s.gpr .a0).toNat % 8 = 0
  sp : s.sp.toNat % 16 = 0
  table : (⟨s.sp - BitVec.ofNat 64 112, 112⟩ : Region).Disjoint ⟨s.gpr .a0, 288⟩
  y : (⟨s.sp - BitVec.ofNat 64 112, 112⟩ : Region).Disjoint ⟨s.gpr .a1, 16⟩
  data : (⟨s.sp - BitVec.ofNat 64 112, 112⟩ : Region).Disjoint ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
  fit : (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64
  small : 16 * (s.gpr .a3).toNat < 2 ^ 64
  key : ∀ i < 9, ∀ j < 4, s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8 * (4 * i + j))) 64 = ghashOperand H i &&& ghashClass j

/-- What it does. -/
def hashDone (H : Block) (s t : State) : Prop :=
  blockAt t.mem (s.gpr .a1) = ghashFrom H (blockAt s.mem (s.gpr .a1)) (blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)

theorem preparedHash_law {H : Block} (s₀ : State) (h : CachedPre H s₀) (hsp : 112 ≤ s₀.sp.toNat) :
    ∃ tr t, Exec isa cachedHash s₀ tr t ∧ abiPreserved s₀ t ∧ hashDone H s₀ t := by
  obtain ⟨hrd, hwr, hal, hsa, hft, hfy, hfd, hdf, hnlt, hkey⟩ := h
  obtain ⟨h1, h0, rfl⟩ : ∃ h1 h0, H = w2 h1 h0 := ⟨Spec.Gcm.ghashHi H, Spec.Gcm.ghashLo H, by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    show _ = ((Spec.Gcm.ghashHi H ++ Spec.Gcm.ghashLo H : BitVec (64 + 64))).getLsbD i
    rw [BitVec.getLsbD_append, Spec.Gcm.ghashHi, Spec.Gcm.ghashLo, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    by_cases h : i < 64
    · simp [h]
    · simp [h, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]⟩
  generalize hBd : s₀.sp - BitVec.ofNat 64 112 = B at hft hfy hfd
  have hBt : B.toNat = s₀.sp.toNat - 112 := by rw [← hBd]; exact toNat_sub_ofNat' hsp
  have hB : B.toNat % 16 = 0 := by omega
  have hfr : (⟨B, 112⟩ : Region) ∈ (allocd 112 s₀).wr := by rw [← hBd]; exact List.mem_cons_self ..
  refine frame_ok (F := 112) (by decide) hsp (yp := s₀.gpr .a1) (hBd ▸ hfy) ?_
  rw [hBd]
  refine WP.seq (WP.mono (Q := fun t => ∃ s₁, InvL s₁ h1 h0 (blockAt s₀.mem (s₀.gpr .a1)) (s₀.gpr .a2)
      (s₀.gpr .a3).toNat 0 t ∧ Words .a0 false s₁ ∧ s₁.gpr .a1 = s₀.gpr .a1 ∧ s₁.gpr .ra = s₀.gpr .ra ∧ s₁.sp = B ∧
    s₁.rd = s₀.rd ∧ s₁.wr = (allocd 112 s₀).wr ∧ Frame [⟨B, 112⟩] s₀.mem s₁.mem ∧
    Spill.Saved B s₀.gpr (savedAt 0) s₁.mem) ?_ ?_)
  · have hst : cachedStart = ([.addSp .t0 0] ++ saveAt 0 : List Instr) ++ (maskCode ++ loadY) := by
      simp only [cachedStart, List.append_assoc]
    rw [hst, WP.block_append_iff]
    refine WP.mono (saveAt_ok (B := B) (F := 112) (o := 0) hB hBd (by decide) (.inl rfl) (by decide) hfr)
      fun s₁ ⟨_, g₁, rd₁, wr₁, sp₁, f₁, sv₁⟩ => ?_
    have F₁ : Frame [⟨B, 112⟩] s₀.mem s₁.mem := f₁.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.sub_base B (by decide)⟩
    have a0₁ : s₁.gpr .a0 = s₀.gpr .a0 := g₁ .a0 (by decide)
    have hya : s₁.gpr .a1 = s₀.gpr .a1 := g₁ .a1 (by decide)
    have hc : ∀ k < 36, (⟨s₀.gpr .a0, 288⟩ : Region).Contains (s₀.gpr .a0 + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
      Offset.contains_base _ (by omega) (by omega)
    have r₀ : Rel .a0 false s₁ s₁ ⟨s₁.gpr, fun k => s₁.mem.readW (s₁.gpr .a0 + BitVec.ofNat 64 (8 * k)) 64⟩ :=
      ⟨rfl, Slots.init _ _ _, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    rw [WP.block_append_iff]
    refine WP.mono (maskCode_ok r₀ (by decide)) fun s₂ ⟨a₂, r₂, hM, k₂, m₂⟩ => ?_
    have mem₂ : s₂.mem = s₁.mem := r₂.ro rfl
    have hya₂ : s₂.gpr .a1 = s₀.gpr .a1 := by rw [r₂.g, k₂ _ (by decide)]; exact hya
    have hwr₁ : s₁.wr = (allocd 112 s₀).wr := wr₁
    refine WP.mono (loadY_ok r₂ (by decide) (by rw [hya₂, r₂.wr, hwr₁]; show _ ∈ _ :: s₀.wr; rw [hwr]; simp))
      fun t ⟨a, ra, hY, k, hm⟩ => ⟨s₁, ?_, ?_, hya, g₁ .ra (by decide), sp₁.trans hBd, rd₁, hwr₁, F₁, sv₁⟩
    · refine inv_start ra (hM.keep k) ?_ ?_ ?_ ?_ ((k _ (by decide)).trans (k₂ _ (by decide)))
        ((k _ (by decide)).trans (k₂ _ (by decide)))
      · intro i hi j hj
        rw [hm, m₂]
        show s₁.mem.readW (s₁.gpr .a0 + _) 64 = _
        rw [a0₁, F₁.readW (hc _ (by omega)) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hft.symm) (by decide)]
        exact hkey i hi j hj
      · rw [hY, hya₂, mem₂]
        refine blockAt_frame F₁ fun r hr => ?_
        rw [List.mem_singleton] at hr; subst hr; exact hfy.symm
      · rw [k _ (by decide), k₂ _ (by decide)]; exact g₁ .a2 (by decide)
      · rw [k _ (by decide), k₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact g₁ .a3 (by decide)
    · refine ⟨fun k hk => ?_, fun k hk => ⟨⟨s₀.gpr .a0, 288⟩, List.mem_append_left _ ?_, by rw [a0₁]; exact hc k hk⟩,
        fun h => absurd h (by decide)⟩
      · rw [a0₁]; exact Spill.al8 hal (by omega)
      · rw [rd₁]; show _ ∈ s₀.rd; rw [hrd]; exact List.mem_cons_self ..
  · intro t ⟨s₁, hI, hw, h1, hra, hsp₁, hrd₁, hwr₁, F₁, sv⟩
    refine WP.mono (rest_ok (F := 112) (o := 0) hw hnlt ?_ hB hsp₁ (by decide) (.inl rfl) (by decide) (by rw [hwr₁]; exact hfr)
      (by rw [h1, hwr₁]; show _ ∈ _ :: s₀.wr; rw [hwr]; simp) sv hI) fun u ⟨g, ra, sp, wr, rd, hb⟩ =>
        ⟨g, ra.trans hra, sp, wr.trans hwr₁, rd.trans hrd₁, ?_⟩
    · intro i hi
      refine ⟨⟨s₀.gpr .a2, 16 * (s₀.gpr .a3).toNat⟩, List.mem_append_left _ (by rw [hrd₁, hrd]; simp), ?_⟩
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [h1] at hb
      rw [hb, blocksAt_frame F₁ hnlt]
      intro r hr
      rw [List.mem_singleton] at hr; subst hr; exact hfd.symm

end VG.Proof.Gcm.RISCV64
