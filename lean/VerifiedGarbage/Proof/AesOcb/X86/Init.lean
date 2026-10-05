import VerifiedGarbage.Proof.AesOcb.X86.Calls

/-!
# AES-OCB on x86: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. The entry (our caller's
registers saved in `scratch`, the arguments into its slots), the key
schedule (`vg_aes_expand_key`), then `L_* = ENCIPHER(K, zeros(128))`
(`vg_aes_encrypt_blocks` on a zero block at byte 240 of the key context),
as one `Pc` (`init_pc`): correct (`init_correct`) and constant time
(`init_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem KeyRepr)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt restore)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok
  KeepEnv keeps_ok keepR runBlock_app_of in_off below_eq covers_left covers_off covers_cons covers_nil Pc pubOf
  pubOf_arg pubOf_esp pubOf_eq argIn_of arg0_ok ret_kept ret_below ofNat_lit ofNat_toNat32 toNat_add32
  toNat_ofNat32 exit_ok KeyCall KeyPost add_ofNat_assoc32 CT length_bytesAt)

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  kw : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  cw : (⟨w64 (p.2 2), 256⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  k_k : (below p.1 24).Disjoint ⟨w64 (p.2 0), (p.2 1).toNat⟩
  k_c : (below p.1 24).Disjoint ⟨w64 (p.2 2), 256⟩
  k_w : (below p.1 24).Disjoint ⟨w64 (p.2 3), 2560⟩
  fk : (p.2 0).toNat + (p.2 1).toNat ≤ 2 ^ 32
  fc : (p.2 2).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 3).toNat + 2560 ≤ 2 ^ 32
  sp : 24 ≤ p.1.toNat
  len : (p.2 1).toNat = 16 ∨ (p.2 1).toNat = 24 ∨ (p.2 1).toNat = 32

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : initPre s) (hp : pubOf 4 s = p) :
    InitPure p := by
  simp only [initPre] at h
  obtain ⟨-, -, d_kc, d_kw, -, d_cw, -, -, -, r_c, r_w, -, k_k, k_c, k_w, -, fk, fc, fw, sp, -, hl⟩ := h
  simp only [keyR, ictxR, scrR, retR, stackR] at d_kc d_kw d_cw r_c r_w k_k k_c k_w
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, below_eq sp] at k_k k_c k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide); have a3 := pubOf_arg hp (i := 3) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a2, a3, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp hl
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp, hl⟩

/-- The arguments the entry copies, and where. -/
abbrev initPs : List (Nat × Nat) := [(0, nO), (1, nlO), (2, ctxO)]

theorem initEntry_eq : (entry 3 (keep 0 nO ++ keep 1 nlO ++ keep 2 ctxO) : Prog isa) =
    entry 3 (initPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- After the entry. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 4 s₀ = p
  ebp : s.gpr .ebp = p.2 3
  esp : s.gpr .esp = p.1
  sK : slotv s.mem (p.2 3) nO = p.2 0
  sL : slotv s.mem (p.2 3) nlO = p.2 1
  sC : slotv s.mem (p.2 3) ctxO = p.2 2
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀)
      (entry 3 (keep 0 nO ++ keep 1 nlO ++ keep 2 ctxO)) (IEnt p) := by
  rw [initEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := initPure_of hpre hpub
    have hp := hpre
    simp only [initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have a : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have wW : Covers [⟨w64 (arg s₀ 3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 4).Disjoint ⟨w64 (arg s₀ 3), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    have fw : (arg s₀ 3).toNat + 2560 ≤ 2 ^ 32 := by rw [a 3 (by decide)]; exact hc.fw
    have fa' : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by omega
    generalize hSP : s₀.gpr .esp = SP at rA aw fa'
    have i₀ : InRegions (s₀.rd ++ s₀.wr) (argA SP 3) 4 :=
      rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa'⟩
    refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
    have hax : (s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32)).gpr .eax = arg s₀ 3 := by
      rw [gpr_setReg_self, ← hSP]; rfl
    set t₀ := s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32) with ht₀
    obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok t₀ hax (by rw [ht₀]; exact wW) fw
    have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), ht₀, gpr_setReg_of_ne _ _ (by decide), hSP]
    have hA₁ : ∀ i < 4, s₁.mem.readW (argA SP i) 32 = arg s₀ i := fun i hi => by
      rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (aw.sub_left (argA_sub hi fa')).sub_right (Lay.wSub (by decide))) (by decide)]
      rw [arg, argAddr, hSP]
      exact rfl
    have ke : KeepEnv (arg s₀ 3) SP 4 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa', fw⟩
    obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok initPs (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide) (by decide) ke
    refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
    have f₃' : Frame [⟨w64 (arg s₀ 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s₃.mem := by
      refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
      · simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have hsv : SavedAt s₃.mem (arg s₀ 3) s₀ := by
      have := sv₁.frame f₃ fun r hr => by
        simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      obtain ⟨a, b, c, d⟩ := this
      refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
        simp only [ht₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
    have sl : ∀ q ∈ initPs, slotv s₃.mem (arg s₀ 3) q.2 = p.2 q.1 := fun q hq => by
      have e := sl₃ q hq
      have hq1 : q.1 < 4 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> decide
      rw [hA₁ q.1 hq1, a q.1 hq1] at e
      exact e
    rw [a 3 (by decide)] at f₃' hsv sl
    exact ⟨hpre, hpub, by rw [g₃ _ (by decide), bp₁, a 3 (by decide)],
      by rw [g₃ _ (by decide), sp₁, ← hSP]; exact pubOf_esp hpub, sl (0, nO) (by simp), sl (1, nlO) (by simp),
      sl (2, ctxO) (by simp), hsv, f₃', by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl⟩
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 3 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

end VG.Proof.AesOcb.X86
