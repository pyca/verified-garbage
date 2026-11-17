module

import VerifiedGarbage.Proof.AesSiv.X86_64.Crypt
public import VerifiedGarbage.Proof.AesSiv.X86_64.Ctr
public import VerifiedGarbage.Proof.AesSiv.X86_64.FinishShort
import VerifiedGarbage.Proof.AesSiv.X86_64.Finish
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Impl.AesSiv.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call

/-! ### `AesSiv.X86_64.S2vAd`, which this module and modules that import it used -/

section

/-!
# AES-SIV on x86-64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

@[expose] public section

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
    simp only [reduceCtorEq, stOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
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
    simp only [reduceCtorEq, ctxOff, adsOff, leftOff, tOff, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h15, r₀, r₁, w₁, r₂, w₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
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
    {nW : Nat} (hnW : 256 ≤ nW) (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, nW⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, nW⟩) (_wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + nW ≤ 2 ^ 64) :
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
    ⟨_, hDw, Offset.contains_base D hd (by omega_arith)⟩
  have inW (d : Nat) (hd : d + 8 ≤ 256) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W (by omega_using [hd, hnW]) (by omega_using [hd])⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  have cD (d : Nat) (hd : d + 8 ≤ 16) : (⟨D, 16⟩ : Region).Contains (D + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base D hd (by omega_arith)
  have dW {d n : Nat} (hd : d + n ≤ 256) (r : Region) (hr : r ∈ [(⟨D, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W (by omega_using [hd, hnW]))
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
    rw [f₃.readW (Region.contains_self _ _) (dW (by omega_arith)) (by decide), f₁.readW (Region.contains_self _ _)
      (one_out' (Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith))) (by decide)]
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
      one_out' (hDW.sub_right (Offset.sub_base W (by omega_using [hnW])))
    rw [bytesAt_frame f₄ d₄ (by decide), m₃, Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep sepD (by decide),
      fw.readW (Region.contains_self _ _) (fun r hr => dW (d := 136) (n := 8) (by decide) r hr) (by decide), e136,
      Proof.Cmac.xor_words]
    have hd := dblMem_bytes s₁.mem D 0 0
    rw [k0] at hd
    have dD : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)], (⟨D, 16⟩ : Region).Disjoint r :=
      one_out' (hDW.sub_right (Offset.sub_base W (by omega_using [hnW])))
    have d128 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 224, 8⟩ : Region)],
        (⟨W + BitVec.ofNat 64 128, 16⟩ : Region).Disjoint r :=
      one_out' (Offset.disjoint W (by decide) (by omega_arith) (by omega_arith))
    rw [bytesAt_frame fd (fun r hr => dW (d := 128) (n := 16) (by decide) r hr) (by decide), m₂, hd,
      bytesAt_frame f₁ dD (by decide), bytesAt_frame f₁ d128 (by decide), Spec.Siv.dbl, Siv.xor_eq]
  · rw [m₄, Mem.readW_writeW_sep (Offset.sep W (d := 112) (n := 8) (e := 120) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, sl (by decide)]
  · rw [m₄, Mem.readW_writeW_self64, l₃]; rfl
  · refine ((f₁.mono ?_).trans (f₃.mono ?_)).trans (f₄.mono ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;> simp

end VG.Proof.AesSiv.X86_64

end

end

/-!
# AES-SIV on x86-64: the end of `vg_aes_siv_encrypt`

From S2V's state of the associated data on, `encrypt` finishes S2V with the
plaintext into the first 16 bytes of the working space (`finish_wp`), sets
the counter from that IV (`counter_ok`), encrypts the data in place with CTR
(`ctr_wp`) and restores the registers: the working space then starts with
the IV and the data is the ciphertext (`sealTail_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {g : Lay} {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## What each step writes -/

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-! ## Ranges outside them -/

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (h : Env g s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h4 : d + n ≤ 224 ∨ 232 ≤ d) (h5 : d + n ≤ 256) :
    ∀ r ∈ finRegions g W out (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [hout])
  · exact Offset.disjoint W (by omega_using [h2]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h3]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h4]) (by omega_using [hd]) (by omega_using [])
  · exact h.dX h5
  · exact (h.stk_w.sub_right (h.sW h5)).symm

/-- A region outside the working space and the stack, outside what `finish` writes. -/
theorem fin_out (h : Env g s₀ C D P W R L) {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, g.n⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ finRegions g W out (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (h.sW hout)
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right h.sX
  · exact hs.symm

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : Env g s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega_using [hd]))
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact h.dX hd
  · exact (h.stk_w.sub_right (h.sW (by omega_using [hd]))).symm

/-- A region outside the data, the working space and the stack, outside what CTR writes. -/
theorem ctr_out (h : Env g s₀ C D P W R L) {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, g.n⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right h.sX
  · exact hs.symm

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])

/-- A region outside the working space, outside the counter. -/
theorem cnt_out (h : Env g s₀ C D P W R L) {X : Region} (hw : X.Disjoint ⟨W, g.n⟩) :
    ∀ r ∈ cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (h.sW (by decide))
  · exact hw.sub_right (h.sW (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-! ## From S2V's end to the restore -/

/-- The registers, and the data pointer and length in their slots. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- What `encrypt`'s and `decrypt`'s ends write: the data, the working space
and the stack. -/
abbrev endRegions (g : Lay) (W P : Addr) (L : Nat) (sp : Addr) : List Region := [⟨P, L⟩, ⟨W, g.n⟩, below sp 16]

theorem fin_sub (h : Env g s₀ C D P W R L) {out : Nat} (hout : out + 16 ≤ 256) :
    ∀ r ∈ finRegions g W out (s₀.gpr .rsp), ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega_using [hout])⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sX⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem cnt_sub (h : Env g s₀ C D P W R L) :
    ∀ r ∈ cntRegions W, ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem ctr_sub (h : Env g s₀ C D P W R L) :
    ∀ r ∈ ctrRegions g W P L (s₀.gpr .rsp), ∃ r' ∈ endRegions g W P L (s₀.gpr .rsp), Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sX⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

/-- `encrypt` from S2V's state of the associated data at `D` on: S2V's end
with the plaintext into the first 16 bytes of the working space
(`finish_wp`), the counter from that IV (`counter_ok`), CTR over the data in
place (`ctr_wp`) and the restore of the registers saved in the working space. -/
theorem sealTail_wp (v : UpdateImpl) (K : Calls v g) (h : Env g s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : SPre s₀ C D P W R L s) {gs : Reg → BitVec 64}
    (hsv : Spill.Saved s.mem W gs saved) :
    WP isa (.seq (finish g.x v.callee v.ctr.callee v.ctr.suffix 0) (.seq (.block (counter 0)) (.seq (ctr g.x v.ctr.callee) (.block restore)))) s
      fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = gs r) ∧ s'.gpr .rsp = s₀.gpr .rsp ∧
        Frame (endRegions g W P L (s₀.gpr .rsp)) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega_using [this]
  refine WP.seq (WP.mono (finish_wp v K h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := counter_ok h h₂.regs.r15 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (cntRegions W) s₂.mem s₃.mem := m₃ ▸ counter_frame _ _ _ _
  have hr₃ : Regs s₀ C D P W R L s₃ := h₂.regs.keep (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- The data pointer and its length, kept in their slots.
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (cnt_dis (by omega_using [hd']) (by omega_using [hd])) (by decide),
      f₂.readW (Region.contains_self _ _) (fin_dis h (by decide) (by omega_using [hd']) (by omega_using [hd]) (by omega_using [hd]) (by omega_using [hd])
        (by omega_using [hd']) (by omega_using [hd'])) (by decide)]
  have h208 : s₃.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), hs.d208]
  have h216 : s₃.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), hs.d216]
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact counter_cnt s₂.mem W
  refine WP.seq (WP.mono (ctr_wp v.ctr K.toCCalls h hcp hPw hr₃ (length_counter _) (counter_low _) hcnt h208 h216)
    fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hsv₄ : Spill.Saved s₄.mem W gs saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨saved_ge p hp, saved_le p hp⟩
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact cnt_dis (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact ctr_dis h (by omega_using [this]) (by omega_using [this])
  refine WP.mono (Spill.restore_ok .r15 saved gs s₄ (by decide) (fun p hp => by
      rw [h₄.regs.r15, h₄.regs.rd, h₄.regs.wr]; exact h.inRW rfl rfl (by have := saved_le p hp; omega_using [this]))
    (by rw [h₄.regs.r15]; exact hsv₄)) fun s₅ ⟨h₅a, h₅b, m₅, _, _⟩ => ?_
  have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₅.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [m₅, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₅.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₅.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [m₅, h₄.data, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h h.c_w) hRb, ctxCiph_frame f₂ (fin_out h (by decide) h.c_w h.stk_c) hRb,
      bytesAt_frame f₃ (cnt_out h h.p_w) hL, bytesAt_frame f₂ (fin_out h (by decide) h.p_w h.stk_p) hL]
  refine ⟨h₅a, by rw [h₅b _ (by decide), h₄.regs.rsp], ?_, by rw [hc, hv]; rfl⟩
  rw [m₅]
  exact ((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))

end VG.Proof.AesSiv.X86_64
