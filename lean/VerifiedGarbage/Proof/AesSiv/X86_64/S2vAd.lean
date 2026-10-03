import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf

/-!
# AES-SIV on x86-64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 dblMem dbl_ok dblMem_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem saved_le : ∀ p ∈ saved, p.2 + 8 ≤ 208 := by decide

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 := by decide

theorem saved_slots : Spill.Slots saved := by decide

theorem saved_all : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ saved.map Prod.fst := by decide

variable {D W : Addr}

theorem one_out' {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw


theorem xorD_ok {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr D 8) (w₁ : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (r₀ : InRegions (s.rd ++ s.wr) D 8) (r₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 8) 8)
    (q₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128) 8)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 136) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)),
        .store (at_ .r12 0) .rax, .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))),
        .store (at_ .r12 8) .rax] s = some s' ∧
      s'.mem = (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).writeW
        (D + BitVec.ofNat 64 8)
        ((s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (D + BitVec.ofNat 64 8) 64 ^^^
          (s.mem.writeW D (s.mem.readW D 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 128) 64)).readW
            (W + BitVec.ofNat 64 136) 64) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [stOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, k0, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ite_true, ite_false, h12, h15, w₀, w₁, r₀, r₁, q₀, q₁]
    rfl, ?_⟩
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem adTail_ok {s : State} (h15 : s.gpr .r15 = W) (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 120) 8) (w₂ : InRegions s.wr (W + BitVec.ofNat 64 120) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff)),
        .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16), .store (at_ .r15 adsOff) .rax,
        .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1), .store (at_ .r15 leftOff) .rax] s = some s' ∧
      s'.gpr .rbx = s.mem.readW (W + BitVec.ofNat 64 224) 64 ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).writeW
        (W + BitVec.ofNat 64 120)
        ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1) ∧
      s'.zf = some ((s.mem.writeW (W + BitVec.ofNat 64 112) (s.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
          (W + BitVec.ofNat 64 120) 64 - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [ctxOff, adsOff, leftOff, tOff, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h15, r₀, r₁, w₁, r₂, w₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false]
  · simp only [sx_ofNat (show 16 < 2 ^ 31 by decide),
      sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · simp only [sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide)]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it (the
context kept at `W + 224` while `rbx` holds `D`), then the descriptor pointer
at `W + 112` advanced by 16 and the count at `W + 120` decremented, ZF set
when it reaches 0. -/
theorem adStep_wp {s : State} (h12 : s.gpr .r12 = D) (h15 : s.gpr .r15 = W)
    (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, 2560⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩) (_wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + 2560 ≤ 2 ^ 64) :
    WP isa (.block adStep) s fun s' => s'.gpr .rbx = s.gpr .rbx ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 == 0) ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 + 16 ∧
      s'.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 - 1 ∧
      Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem := by
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base D hd (by omega)⟩
  have inW (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W hd (by omega)⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  have cD (d : Nat) (hd : d + 8 ≤ 16) : (⟨D, 16⟩ : Region).Contains (D + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base D hd (by omega)
  have dW {d n : Nat} (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨D, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W hd)
  -- The context saved, and `rbx` holding `D`.
  obtain ⟨s₁, run₁, m₁, b₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.store (at_ .r15 ctxOff) .rbx,
      .mov .rbx (.reg .r12)] s = some s₁ ∧ s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 224) (s.gpr .rbx) ∧
      s₁.gpr .rbx = D ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [ctxOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea,
        offset_nat, Option.map_some, h15, inW 224 (by decide), ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rw [gpr_setReg_self]; exact h12
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr]
    all_goals rfl
  -- The doubling.
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := dbl_ok s₁ b₁ (src := 0) (dst := 0)
    (by rw [rd₁, wr₁]; exact rr (inD 0 (by decide))) (by rw [rd₁, wr₁]; exact rr (inD (0 + 8) (by decide)))
    (by rw [wr₁]; exact inD 0 (by decide)) (by rw [wr₁]; exact inD (0 + 8) (by decide))
  have r12₂ : s₂.gpr .r12 = D := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h12]
  have r15₂ : s₂.gpr .r15 = W := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h15]
  have i₀ := inD 0 (by decide)
  rw [k0] at i₀
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := xorD_ok r12₂ r15₂ (by rw [wr₂, wr₁]; exact i₀)
    (by rw [wr₂, wr₁]; exact inD 8 (by decide)) (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr i₀)
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inD 8 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 128 (by decide)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact rr (inW 136 (by decide)))
  have r15₃ : s₃.gpr .r15 = W := by rw [g₃ _ (by decide), r15₂]
  have e₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  have ew : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain ⟨s₄, run₄, b₄, m₄, z₄, g₄, rd₄, wr₄⟩ := adTail_ok r15₃ (by rw [e₃]; exact rr (inW 224 (by decide)))
    (by rw [e₃]; exact rr (inW 112 (by decide))) (by rw [ew]; exact inW 112 (by decide))
    (by rw [e₃]; exact rr (inW 120 (by decide))) (by rw [ew]; exact inW 120 (by decide))
  -- What the doubling and the XOR write.
  have fd : Frame [⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂, dblMem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cD 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (cD (0 + 8) (by decide))
  have f₃ : Frame [⟨D, 16⟩] s₁.mem s₃.mem := by
    have c₀ := cD 0 (by decide)
    rw [k0] at c₀
    rw [m₃]
    exact (fd.writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ (cD 8 (by decide))
  have f₁ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 112) (e := 112) (n := 8)
      (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 120) (e := 112) (n := 8) (k := 16) (by decide)
        (by decide) (by decide))
  -- The slots at `W + 112` and `W + 120` before the tail.
  have sl {d : Nat} (hd : d + 8 ≤ 224) : s₃.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dW (by omega)) (by decide), f₁.readW (Region.contains_self _ _)
      (one_out' (Offset.disjoint W (by omega) (by omega) (by omega))) (by decide)]
  have sep : Mem.Sep (W + BitVec.ofNat 64 120) (64 / 8) (W + BitVec.ofNat 64 112) (64 / 8) :=
    Offset.sep W (d := 120) (n := 8) (e := 112) (k := 8) (by decide) (by decide) (by decide)
  have l₃ : (s₃.mem.writeW (W + BitVec.ofNat 64 112) (s₃.mem.readW (W + BitVec.ofNat 64 112) 64 + 16)).readW
      (W + BitVec.ofNat 64 120) 64 = s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 := by
    rw [Mem.readW_writeW_sep sep (by decide), sl (by decide)]; rfl
  rw [show adsOff = 112 from rfl, show leftOff = 120 from rfl]
  refine WP.of_runBlock ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show adStep = [.store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r12)] ++ Impl.CmacAes.X86_64.dbl 0 0 ++
      [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r15 stOff)), .store (at_ .r12 0) .rax,
       .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r15 (stOff + 8))), .store (at_ .r12 8) .rax] ++
      [.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 adsOff)), .alu .add .rax (imm 16),
       .store (at_ .r15 adsOff) .rax, .mov .rax (.mem (at_ .r15 leftOff)), .alu .sub .rax (imm 1),
       .store (at_ .r15 leftOff) .rax] from rfl, runBlock_append, runBlock_append, runBlock_append, run₁,
      Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄]
  · rw [b₄, f₃.readW (Region.contains_self _ _) (dW (by decide)) (by decide), m₁, Mem.readW_writeW_self64]
  · intro r h₁ h₂ h₃ h₄ h₅
    rw [g₄ r h₁ h₅, g₃ r h₁, g₂ r h₁ h₂ h₃ h₄, g₁ r h₅]
  · rw [rd₄, rd₃, rd₂, rd₁]
  · rw [wr₄, wr₃, wr₂, wr₁]
  · rw [z₄, l₃]; rfl
  · -- The XOR, a word at a time, of `dbl(D)` and the state.
    have sepD : Mem.Sep (D + BitVec.ofNat 64 8) (64 / 8) D (64 / 8) := by
      simpa using Offset.sep D (d := 8) (n := 8) (e := 0) (k := 8) (by decide) (by decide) (by decide)
    have fw : Frame [⟨D, 16⟩] s₂.mem (s₂.mem.writeW D (s₂.mem.readW D 64 ^^^
        s₂.mem.readW (W + BitVec.ofNat 64 128) 64)) := by
      have c₀ := cD 0 (by decide)
      rw [k0] at c₀
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀
    have e136 : W + BitVec.ofNat 64 136 = W + BitVec.ofNat 64 128 + BitVec.ofNat 64 8 := by
      rw [Offset.add_add]
    have d₄ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      one_out' (hDW.sub_right (Offset.sub_base W (by decide)))
    rw [bytesAt_frame f₄ d₄ (by decide), m₃, Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep sepD (by decide),
      fw.readW (Region.contains_self _ _) (fun r hr => dW (d := 136) (n := 8) (by decide) r hr) (by decide), e136,
      Proof.Cmac.xor_words]
    have hd := dblMem_bytes s₁.mem D 0 0
    rw [k0] at hd
    have dD : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      one_out' (hDW.sub_right (Offset.sub_base W (by decide)))
    have d128 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)],
        (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Disjoint r :=
      one_out' (Offset.disjoint W (by decide) (by omega) (by omega))
    rw [bytesAt_frame fd (fun r hr => dW (d := 128) (n := 16) (by decide) r hr) (by decide), m₂, hd,
      bytesAt_frame f₁ dD (by decide), bytesAt_frame f₁ d128 (by decide), Spec.Siv.dbl, Siv.xor_eq]
  · rw [m₄, Mem.readW_writeW_sep (Offset.sep W (d := 112) (n := 8) (e := 120) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, sl (by decide)]
  · rw [m₄, Mem.readW_writeW_self64, l₃]; rfl
  · refine ((f₁.mono ?_).trans (f₃.mono ?_)).trans (f₄.mono ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;> simp

end VG.Proof.AesSiv.X86_64
