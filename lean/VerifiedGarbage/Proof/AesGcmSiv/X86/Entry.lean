import VerifiedGarbage.Proof.AesGcmSiv.X86.Run

/-!
# AES-GCM-SIV on x86: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). The entry saves our caller's registers in `W`
(AES-GCM's `save_ok`) and copies the stack arguments into their slots
(`keeps_ok`): after it, `Env` holds (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok
  keepR runBlock_app_of in_off below_eq covers_left)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := arg s 0
  W := arg s 7
  N := arg s 2
  A := arg s 3
  D := arg s 5
  SP := s.gpr .esp
  R := (arg s 1).toNat
  al := (arg s 4).toNat
  n := (arg s 6).toNat

/-- What the precondition says of the stack arguments. -/
structure ArgsOk (s : State) : Prop where
  rA : Covers [argsR (s.gpr .esp) 8] (s.rd ++ s.wr)
  aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 (arg s 7), 4096⟩
  fa : (s.gpr .esp).toNat + 4 + 4 * 8 ≤ 2 ^ 32

theorem lay_of {s : State} (h : onePre s) : Lay (prmOf s) := by
  obtain ⟨_, _, sd, sw, _, nd, nw, _, ad, aw, _, dw, _, _, _, _, _, rd, rw, _, bs, bn, ba, bd, bw, _, fK, fN, fA, fD,
    fW, sp28, _, hR⟩ := h
  simp only [stackR] at bs bn ba bd bw
  rw [show (28 : Addr) = BitVec.ofNat 64 28 from rfl, below_eq sp28] at bs bn ba bd bw
  exact ⟨fK, fW, fN, fA, fD, sp28, sw, sd, nw, nd, aw, ad, dw, bs, bn, ba, bd, bw, hR, BitVec.isLt _,
    BitVec.isLt _, rw, rd⟩

theorem perm_of {s : State} (h : onePre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, -⟩ := h
  have mrd : ∀ r ∈ [schR s, nonceR s, aadR s], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨mrd (schR s) (by simp), mrd (nonceR s) (by simp), mrd (aadR s) (by simp), mwr (dataR s) (by simp),
    mwr (workR s) (by simp)⟩

theorem argsOk_of {s : State} (h : onePre s) : ArgsOk s := by
  obtain ⟨_, hwr, -, -, -, -, -, -, -, -, -, -, -, wa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, spf, -⟩ := h
  refine ⟨?_, ?_, by omega⟩
  · rw [argsR_eq]; exact covers_left (covers_of_mem (by rw [hwr]; simp))
  · rw [argsR_eq]; exact wa.symm

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, nonceO), (3, aadO), (4, alenO), (5, dataO), (6, lenO)]

theorem sivEntry_eq : sivEntry = entry 7 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (p : Prm) (s' : State) : Prop where
  env : Env p s'
  saved : SavedAt s'.mem p.W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 128, 48⟩] s.mem s'.mem

/-- The entry. -/
theorem entry_ok {s : State} (h : onePre s) : WP isa sivEntry s (Entered s (prmOf s)) := by
  have L := lay_of h
  have P := perm_of h
  have Ao := argsOk_of h
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at Ao
  have rA := Ao.rA
  have aw := Ao.aw
  have fa := Ao.fa
  rw [hSP] at rA aw fa
  have fw : (arg s 7).toNat + 2560 ≤ 2 ^ 32 := by have := L.ww; simp only [prmOf] at this; omega
  have wW : Covers [⟨w64 (arg s 7), 2560⟩] s.wr := P.w2560
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 7) 32)).gpr .eax = arg s 7 := by
    rw [gpr_setReg_self, ← hSP]; rfl
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 7) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have argW : ∀ {i}, i < 8 → ∀ {d k : Nat}, d + k ≤ 4096 →
      ∀ r ∈ [(⟨w64 (arg s 7) + BitVec.ofNat 64 d, k⟩ : Region)], (⟨argA SP i, 4⟩ : Region).Disjoint r :=
    fun hi _ _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 8, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
    exact rfl
  have aw' : (argsR SP 8).Disjoint ⟨w64 (arg s 7), 2560⟩ := aw.sub_right (Region.sub_prefix (by decide))
  have ke : KeepEnv (arg s 7) SP 8 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw', fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = arg s 7 := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 (arg s 7) + BitVec.ofNat 64 128, 48⟩] s.mem s₃.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem (arg s 7) s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  have sl : ∀ q ∈ entryPs, slotv s₃.mem (arg s 7) q.2 = arg s q.1 := fun q hq => by
    have e := sl₃ q hq
    have hq1 : q.1 < 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hA₁ q.1 hq1] at e
    exact e
  have ofN : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  refine ⟨⟨bp₃, by rw [sp₃, ← hSP]; rfl, P.of_eq (by rw [rd₃, rd₁]; rfl) (by rw [wr₃, wr₁]; rfl),
    ⟨sl (0, ctxO) (by simp), by simp only [prmOf]; rw [sl (1, roundsO) (by simp)]; exact (ofN _).symm,
      sl (2, nonceO) (by simp), sl (3, aadO) (by simp),
      by simp only [prmOf]; rw [sl (4, alenO) (by simp)]; exact (ofN _).symm, sl (5, dataO) (by simp),
      by simp only [prmOf]; rw [sl (6, lenO) (by simp)]; exact (ofN _).symm⟩⟩, hsv, by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, f₃'⟩

end VG.Proof.AesGcmSiv.X86
