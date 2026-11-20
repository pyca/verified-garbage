module

public import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Poly1305.X86.Blocks
meta import VerifiedGarbage.Proof.Poly1305.X86.Lit
meta import VerifiedGarbage.Impl.Poly1305.X86
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Poly1305 on x86 (32-bit): `blocks`, the whole function

`vg_poly1305_blocks`, from its prologue, the step of its loop (`body_ok`) and
its epilogue (`Blocks.lean`): it is correct (`blocks_ok`) and constant time
(`blocks_ct`), for the functions that call it (ChaCha20-Poly1305's).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem blocks_eq : blocks = .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)),
    .mov .ecx (.mem (at_ .esp 12)), .alu .test .ecx (.reg .ecx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (reduce ++ restore))) := rfl

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
      .alu .test .ecx (.reg .ecx)] : List Instr))) s₀ fun s => ∃ F, SetupF s₀ F ∧
        BInv s₀ F 0 s ∧ s.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit
    (by rw [hp.wr]; exact List.mem_singleton_self _)) fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  obtain esp₁ := A₁.gpr .esp (by decide)
  obtain hF' := SetupF.of hF sv co
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine wp_test fun s₄ k₄ z₄ => WP.block_nil ⟨F, hF', ?_, ?_⟩
  · have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
    refine ⟨c₁.keep (by rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, ?_, ?_, ?_, ?_, fun k hk _ => ?_, fun hA => ?_⟩
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.gpr, hp.arg_same A₁.frame (i := 1) (by decide)]
      simp only [Nat.mul_zero, BitVec.add_zero]
    · rw [hm]; exact A₁.frame
    · rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd]
    · rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr]
    · rw [hm, words_eq A₁.words hk]
    · exact acc_entry hfit hF' (fun k hk => by rw [hm, words_eq A₁.words (by omega_using [hk])]) hA
  · rw [z₄, u₃.gpr, u₂.mem, hp.arg_same A₁.frame (i := 2) (by decide)]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  rw [blocks_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨F, hF, hL₀, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := BInv s₀ F (nb s₀)) ?_ fun s₂ hc₂ => blocks_epilogue_ok hp hF hc₂)
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp only [eval, hz, BitVec.and_self, BitVec.ofNat_eq_ofNat]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, BitVec.ofNat_eq_ofNat, beq_iff_eq] at h; simp only [nb, h, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ BInv s₀ F i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ BInv s₀ F (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hF hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public, and the word
holding `state` known to be the base address of the writable region. -/
def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128], argLen := 16, argBases := [(4, 0)] }

theorem blocks_wf₀ {s : State} (hp : BPre s) : VG.X86.Taint.Wf blocksτ₀ s := by
  obtain hst := hp.st_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp only [hp.wr, blocksτ₀, List.forall₂_cons, Std.le_refl, List.Forall₂.nil, and_self], by simp only [hp.wr, List.pairwise_cons, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega_using [hst]
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_st hp.arg_st
  · intro p hp'
    simp only [blocksτ₀, List.mem_singleton] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp only [addr, BitVec.add_zero, Taint.region, hp.wr, arg, argAddr, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.getD_some]

theorem blocks_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.blocksX86.pre s₁)
    (h₂ : Proof.Poly1305.blocksX86.pre s₂) (hpub : Proof.Poly1305.blocksX86.pub s₁ s₂) :
    VG.X86.Taint.Agree blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  obtain hp₁ := BPre.of _ h₁; have hp₂ := BPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, blocks_wf₀ hp₁, blocks_wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ?_) h4 hk⟩
  · simp only [blocksτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stp, a0]
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
    rcases this with rfl | rfl | rfl
    exacts [a0, a1, a2]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksX86.pre s) :
    ∃ t s', Exec isa blocks s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.blocksX86.post s s' :=
  blocks_correct (BPre.of s hs)

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksX86.pre Proof.Poly1305.blocksX86.pub
    blocks :=
  VG.Taint.constantTime (A := taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Poly1305.X86
