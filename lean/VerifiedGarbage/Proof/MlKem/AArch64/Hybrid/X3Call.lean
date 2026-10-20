module

public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Calls of `vg_keccak_f1600_x3_sha3` from ML-KEM's matrix

`x3call_ok`: the call (`Hybrid.x3call`) on the pair at `x19`, the third
state at `x28` and the working space at `x19 + 1536` (with `x30` kept in the
8 bytes after it, `X2.callR`) permutes the three states, changes memory only
in them, the working space and the function's 128-byte frame below the stack
pointer, keeps every register but `x0`–`x17` (`x30` is reloaded), from the
function's own proof (`X3.correct`, by `WP.callFV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR pair_contains)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR scrR pairAt_stateX2 stateX2_of_pairAt)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Spec.Sha3 (stateAt keccakF)

/-- The registers a call may change. -/
def clobbered : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem clobbered_preserved (r : Reg) (h : r ∉ clobbered) : r ∈ preserved := by
  cases r <;> first | exact absurd (by decide) h | decide

theorem depth : Impl.Sha3.AArch64.Hybrid.X3.code.aarch64Depth = 8 := by decide

/-- The function's frame. -/
abbrev frame (sp : Addr) : Region := below sp 128

/-- **A call** of `vg_keccak_f1600_x3_sha3` on the pair at `p` (`x19`) and
the state at `st` (`x28`). -/
theorem x3call_ok {s : State} {p q st : Addr} {A B S : Spec.Sha3.State}
    (hp : s.gpr .x19 = p) (hq : p + BitVec.ofNat 64 1536 = q) (hst : s.gpr .x28 = st)
    (hpair : PairAt s.mem p A B) (hS : stateAt s.mem st = S)
    (d01 : (pairR p).Disjoint (stR st)) (d02 : (pairR p).Disjoint (callR q))
    (d12 : (stR st).Disjoint (callR q))
    (hsp : 128 ≤ s.sp.toNat)
    (f0 : (frame s.sp).Disjoint (pairR p)) (f1 : (frame s.sp).Disjoint (stR st))
    (f2 : (frame s.sp).Disjoint (callR q))
    (hcov : Covers [pairR p, stR st, callR q] s.wr) :
    WP isa Impl.MlKem.AArch64.Hybrid.x3call s fun t =>
      Keep clobbered s t ∧
      Frame [pairR p, stR st, callR q, frame s.sp] s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧ stateAt t.mem st = keccakF S := by
  have hscr : Region.Sub (scrR q) (callR q) := Region.sub_prefix (by decide : 128 ≤ 136)
  have hslotS : Region.Sub ⟨q + BitVec.ofNat 64 128, 8⟩ (callR q) :=
    Offset.sub_base q (d := 128) (n := 8) (k := 136) (by decide)
  have hslotR : (callR q).Contains (q + BitVec.ofNat 64 128) 8 := Offset.contains_base q (by decide) (by decide)
  have hslot : InRegions s.wr (q + BitVec.ofNat 64 128) 8 :=
    hcov _ _ ⟨callR q, by simp, hslotR⟩
  have hsub : Covers [pairR p, stR st, scrR q] [pairR p, stR st, callR q] :=
    Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨pairR p, by simp, 0, (BitVec.add_zero p).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨stR st, by simp, 0, (BitVec.add_zero st).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨callR q, by simp, 0, (BitVec.add_zero q).symm, by simp only [scrR, callR]; decide⟩
  have hslot_sep : ∀ r ∈ [pairR p, stR st, scrR q] ++ [below s.sp (16 * 8)],
      (⟨q + BitVec.ofNat 64 128, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (d02.sub_right hslotS).symm
    · exact (d12.sub_right hslotS).symm
    · exact Offset.disjoint_base q (d := 128) (n := 8) (k := 128) (by decide) (by decide)
    · exact (f2.sub_right hslotS).symm
  unfold Impl.MlKem.AArch64.Hybrid.x3call
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₁ o₁ e₁ => ?_)
  have h2 : s₁.gpr .x2 = q := by rw [e₁, hp, hq]
  refine VG.Proof.Sha3.AArch64.wp_str ⟨by decide, by decide⟩ (by rw [h2]) (by rw [o₁.wr]; exact hslot)
    fun s₂ m₂ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ =>
      VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => WP.block_nil ?_
  have h0 : s₄.gpr .x0 = p := by
    rw [o₄.gpr _ (by decide), e₃, BitVec.add_zero, m₂.gpr, o₁.gpr _ (by decide), hp]
  have h1 : s₄.gpr .x1 = st := by
    rw [e₄, BitVec.add_zero, o₃.gpr _ (by decide), m₂.gpr, o₁.gpr _ (by decide), hst]
  have h2' : s₄.gpr .x2 = q := by
    rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), m₂.gpr, h2]
  have hlr : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s₄.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [o₄.gpr _ (by simpa using h1), o₃.gpr _ (by simpa using h0), m₂.gpr, o₁.gpr _ (by simpa using h2)]
  have hm : s₄.mem = s.mem.writeW (q + BitVec.ofNat 64 128) (s.gpr .x30) := by
    rw [o₄.mem, o₃.mem, m₂.mem, o₁.mem, o₁.gpr _ (by decide)]
  have hw : s₄.wr = s.wr := o₄.wr.trans (o₃.wr.trans (m₂.wr.trans o₁.wr))
  have hsp₄ : s₄.sp = s.sp := o₄.sp.trans (o₃.sp.trans (m₂.sp.trans o₁.sp))
  have ent : ∀ r, r = .x0 ∨ r = .x1 ∨ r = .x2 → (s₄.callEntry.withRegions [] [pairR p, stR st, scrR q]).gpr r = s₄.gpr r := by
    intro r hr
    simp only [State.withRegions_gpr]
    rcases hr with rfl | rfl | rfl <;> exact State.callEntry_gpr s₄ (by decide)
  refine WP.seq (WP.callFV (k := VG.Proof.Sha3.AArch64.Hybrid.X3.K) (rd := [])
    (wr := [pairR p, stR st, scrR q]) VG.Proof.Sha3.AArch64.Hybrid.X3.correct
    ⟨rfl, by simp only [State.withRegions_wr, ent .x0 (by simp), ent .x1 (by simp), ent .x2 (by simp), h0, h1, h2'],
      by simpa only [ent .x0 (by simp), ent .x1 (by simp), h0, h1] using d01,
      by simpa only [ent .x0 (by simp), ent .x2 (by simp), h0, h2'] using d02.sub_right hscr,
      by simpa only [ent .x1 (by simp), ent .x2 (by simp), h1, h2'] using d12.sub_right hscr,
      by simpa only [State.withRegions_sp, State.callEntry_sp, hsp₄] using hsp,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x0 (by simp), h0]; exact f0,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x1 (by simp), h1]; exact f1,
      by simp only [State.withRegions_sp, State.callEntry_sp, hsp₄, ent .x2 (by simp), h2']
         exact f2.sub_right hscr⟩
    (by rw [hw]; exact Covers.right (hsub.trans hcov)) (by rw [hw]; exact hsub.trans hcov) ?_
    (by rw [depth]; decide))
  intro t hr hwr hsp hf hk hv hpost
  rw [depth, hsp₄] at hf
  have hf₄ : Frame [callR q] s.mem s₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslotR
  have hpair₄ : PairAt s₄.mem p A B := fun i hi => by
    rw [hf₄.read (pair_contains p hi) (by simpa using d02) (by decide)]; exact hpair i hi
  have hS₄ : stateAt s₄.mem st = S := by
    rw [← hS]
    exact VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hf₄ (by simpa using d12)
  simp only [VG.Proof.Sha3.AArch64.Hybrid.X3.K, State.withRegions_mem, State.callEntry_mem,
    ent .x0 (by simp), ent .x1 (by simp), h0, h1] at hpost
  obtain ⟨hA, hB⟩ := stateX2_of_pairAt hpair₄
  rw [hA, hB, hS₄] at hpost
  have hval : t.mem.readW (q + BitVec.ofNat 64 128) 64 = s.gpr .x30 := by
    rw [hf.readW (r := ⟨q + BitVec.ofNat 64 128, 8⟩) (Region.contains_self _ _) hslot_sep (by decide),
      hm, Mem.readW_writeW_self64]
  have ht19 : t.gpr .x19 = p := by rw [hk .x19 (by decide) (by decide), hlr .x19 (by decide) (by decide) (by decide), hp]
  refine VG.Proof.Sha3.AArch64.wp_ldr (a := q + BitVec.ofNat 64 128) ⟨by decide, by decide⟩
    (by rw [ht19, ← hq, BitVec.add_assoc]; rfl)
    (by obtain ⟨R, hR, hc⟩ := hslot
        refine ⟨R, ?_, hc⟩
        rw [hwr, hw]
        exact List.mem_append_right _ hR)
    fun u hu => WP.block_nil ⟨⟨fun r hr' => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h30 : r = .x30
    · subst r; rw [hu.gpr, hval]
    · have hpres := clobbered_preserved r hr'
      rw [hu.other r h30, hk r hpres h30]
      have : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 := by
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        exact ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
      exact hlr r this.1 this.2.1 this.2.2
  · rw [hu.rd, hr, o₄.rd, o₃.rd, m₂.rd, o₁.rd]
  · rw [hu.wr, hwr, hw]
  · rw [hu.sp, hsp, hsp₄]
  · intro r hr
    rw [hu.vec, hv r hr, o₄.vcs r hr, o₃.vcs r hr, m₂.vec, o₁.vcs r hr]
  · rw [hu.mem]
    refine (hf₄.mono (fun r hr => by simp at hr; simp [hr])).trans (hf.sub fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨pairR p, by simp, fun _ h => h⟩
    · exact ⟨stR st, by simp, fun _ h => h⟩
    · exact ⟨callR q, by simp, hscr⟩
    · exact ⟨frame s.sp, by simp, fun _ h => h⟩
  · rw [hu.mem]
    have := pairAt_stateX2 t.mem p
    rwa [hpost.1, hpost.2.1] at this
  · rw [hu.mem]; exact hpost.2.2

end VG.Proof.MlKem.AArch64.Hybrid
