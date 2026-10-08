import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments and descriptors go through the same pieces: each load
of `work` from the stack, and of a descriptor's address from `work`, gives
both the same pointer (`rel_ld`), after which the taint analysis checks the
piece from it; every other value a piece branches on or addresses memory
with is the same in both runs by what correctness says of each (`pstep`):
the lengths, the slices done and the pointers, all functions of the public
arguments and the descriptors (`Pub`); and the calls get the same public
arguments.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (skip_rel)
open VG.Proof.Gcm (padA)

/-! ## Two runs, piece by piece -/

/-- A piece whose trace two runs share, with what correctness says of each run
after it. -/
theorem pstep {c : Prog isa} {F₁ F₂ G₁ G₂ : State → Prop}
    (hct : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp hct (fun _ _ h => h) hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A block whose first instruction `i₀` leads each run to a state related to
the one it started from by `F`. -/
theorem rel_ld {P Q : State → State → Prop} {i₀ : Instr} {l : List Instr} (F : State → State → Prop)
    (hld : ∀ s₁ s₂, P s₁ s₂ → WP isa (.block [i₀]) s₁ (F s₁) ∧ WP isa (.block [i₀]) s₂ (F s₂))
    (hct₀ : RelCT isa P (.block [i₀]) fun _ _ => True)
    (hrest : RelCT isa (fun t₁ t₂ => ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ t₁ ∧ F σ₂ t₂) (.block l) Q) :
    RelCT isa P (.block (i₀ :: l)) Q :=
  rel_block_split (l₁ := [i₀]) (RelCT.seq ((hct₀.wpDep hld).mono (fun _ _ h => h) fun _ _ h => h.2) hrest)

/-- A load of `d` from `[b + off]`. -/
def LdF (d b : Reg) (off : Nat) (σ t : State) : Prop :=
  t.gpr d = σ.mem.readW (σ.gpr b + BitVec.ofNat 64 off) 64 ∧ (∀ r, r ≠ d → t.gpr r = σ.gpr r) ∧
    t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr

/-- `work`, from the stack. -/
theorem ldW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 48) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 48))]) s (LdF .r11 .rsp 48 s) := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The descriptor of the next slice, from `work`. -/
theorem ldD_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 56) 8) :
    WP isa (.block [.mov .r10 (.mem (at_ .r11 gDesc))]) s (LdF .r10 .r11 56 s) := by
  refine WP.of_runBlock ⟨_, by simp only [gDesc]; xrun [hr], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

theorem ldW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 48))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem ldD_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r10 (.mem (at_ .r11 gDesc))]) hc).isSome =
    true := ⟨_, by simp only [gDesc]; taint_decide⟩

/-- The registers `rs` and the loaded one agree after a load from a register
of `rs`, of the same value in both runs. -/
theorem ld_agree {P : State → State → Prop} {d b : Reg} {off : Nat} {rs : List Reg}
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ →
      s₁.mem.readW (s₁.gpr b + BitVec.ofNat 64 off) 64 = s₂.mem.readW (s₂.gpr b + BitVec.ofNat 64 off) 64) :
    ∀ t₁ t₂, (∃ σ₁ σ₂, P σ₁ σ₂ ∧ LdF d b off σ₁ t₁ ∧ LdF d b off σ₂ t₂) → ∀ r ∈ d :: rs, t₁.gpr r = t₂.gpr r := by
  rintro t₁ t₂ ⟨σ₁, σ₂, hσ, ⟨a₁, b₁, -⟩, ⟨a₂, b₂, -⟩⟩ r hr
  by_cases hx : r = d
  · subst hx; rw [a₁, a₂]; exact hS _ _ hσ
  · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r (List.mem_of_ne_of_mem hx hr)

/-! ## What two runs share -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  rdi : s₀'.gpr .rdi = s₀.gpr .rdi
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  rdx : s₀'.gpr .rdx = s₀.gpr .rdx
  rcx : s₀'.gpr .rcx = s₀.gpr .rcx
  r8 : s₀'.gpr .r8 = s₀.gpr .r8
  r9 : s₀'.gpr .r9 = s₀.gpr .r9
  rsp : s₀'.gpr .rsp = s₀.gpr .rsp
  a : ∀ i, i < 6 → stackArg s₀' i = stackArg s₀ i
  desc : ∀ j < Cnt s₀ * 16, s₀'.mem (Src s₀ + BitVec.ofNat 64 j) = s₀.mem (Src s₀ + BitVec.ofNat 64 j)

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.sealGatherPub s₀ s₀') : Pub s₀ s₀' := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := h
  refine ⟨q₁.symm, q₂.symm, q₃.symm, q₄.symm, q₅.symm, q₆.symm, q₇.symm, fun i hi => ?_,
    fun j hj => (hd j hj).symm⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a₀.symm, a₁.symm, a₂.symm, a₃.symm, a₄.symm, a₅.symm]

section
variable {s₀ s₀' : State} (pb : Pub s₀ s₀')
include pb

theorem Pub.src : Src s₀' = Src s₀ := pb.a 0 (by decide)
theorem Pub.cnt : Cnt s₀' = Cnt s₀ := by simp only [Cnt, pb.a 1 (by decide)]
theorem Pub.dst : Dst s₀' = Dst s₀ := pb.a 2 (by decide)
theorem Pub.len : stackArg s₀' 3 = stackArg s₀ 3 := pb.a 3 (by decide)
theorem Pub.eL : L s₀' = L s₀ := by simp only [L, pb.len]
theorem Pub.tg : Tg s₀' = Tg s₀ := pb.a 4 (by decide)
theorem Pub.w : W s₀' = W s₀ := pb.a 5 (by decide)
theorem Pub.st : St s₀' = St s₀ := by simp only [St, pb.w]

/-- A word of the descriptors. -/
theorem Pub.descW {j : Nat} (hj : j + 8 ≤ Cnt s₀ * 16) :
    s₀'.mem.readW (Src s₀ + BitVec.ofNat 64 j) 64 = s₀.mem.readW (Src s₀ + BitVec.ofNat 64 j) 64 :=
  (Mem.readW_congr fun k hk => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; exact (pb.desc _ (by omega)).symm).symm

theorem Pub.sb {i : Nat} (hi : i < Cnt s₀) : sb s₀' i = sb s₀ i := by
  show s₀'.mem.readW (Src s₀' + BitVec.ofNat 64 (16 * i)) 64 = s₀.mem.readW (Src s₀ + BitVec.ofNat 64 (16 * i)) 64
  rw [pb.src]; exact pb.descW (by omega)

theorem Pub.sl {i : Nat} (hi : i < Cnt s₀) : sl s₀' i = sl s₀ i := by
  show (s₀'.mem.readW (Src s₀' + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat =
    (s₀.mem.readW (Src s₀ + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat
  rw [pb.src, BitVec.add_assoc, ofNat_add_ofNat, pb.descW (by omega)]

theorem Pub.gl {i : Nat} (hi : i ≤ Cnt s₀) : gl s₀' i = gl s₀ i := by
  induction i with
  | zero => rw [gl_zero, gl_zero]
  | succ i ih => rw [gl_succ, gl_succ, ih (by omega), pb.sl (by omega)]

end


/-- A block that first loads `work` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_w {P : State → State → Prop} {l : List Instr} (rs : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 48) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 48) 8)
    {Q : State → State → Prop}
    (hrest : RelCT isa (fun t₁ t₂ => ∃ σ₁ σ₂, P σ₁ σ₂ ∧ LdF .r11 .rsp 48 σ₁ t₁ ∧ LdF .r11 .rsp 48 σ₂ t₂) (.block l) Q) :
    RelCT isa P (.block (.mov .r11 (.mem (at_ .rsp 48)) :: l)) Q :=
  rel_ld (LdF .r11 .rsp 48) (fun _ _ h => ⟨ldW_ok (hS _ _ h).2.1, ldW_ok (hS _ _ h).2.2⟩)
    (rel_taint [.rsp] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) ldW_check) hrest

/-- `rel_w`, with the rest of the block checked by the taint analysis. -/
theorem rel_wt {P : State → State → Prop} {l : List Instr} (rs : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 48) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 48) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).isSome = true) :
    RelCT isa P (.block (.mov .r11 (.mem (at_ .rsp 48)) :: l)) fun _ _ => True :=
  rel_w rs hrs hag hS (rel_taint (.r11 :: rs) (ld_agree hag fun _ _ h => (hS _ _ h).1) hc)

/-- `rel_w`, then a load of the next descriptor's address from `work` into
`r10`, with the rest of the block checked by the taint analysis from `r10`,
`r11` and `rsp`. -/
theorem rel_wd {P : State → State → Prop} {l : List Instr}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 48) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 48) 8)
    (hD : ∀ s₁ s₂, P s₁ s₂ →
      s₁.mem.readW (s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 + BitVec.ofNat 64 56) 64 =
        s₂.mem.readW (s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 + BitVec.ofNat 64 56) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 + BitVec.ofNat 64 56) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 + BitVec.ofNat 64 56) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.r10, .r11, .rsp]) (.block l) hc).isSome = true) :
    RelCT isa P (.block (.mov .r11 (.mem (at_ .rsp 48)) :: .mov .r10 (.mem (at_ .r11 gDesc)) :: l))
      fun _ _ => True := by
  refine rel_w [.rsp] (by simp) (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hsp _ _ h) hS ?_
  have hag₁ := ld_agree (P := P) (d := .r11) (b := .rsp) (off := 48) (rs := [.rsp]) (fun _ _ h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hsp _ _ h) fun _ _ h => (hS _ _ h).1
  have hD' : ∀ t₁ t₂, (∃ σ₁ σ₂, P σ₁ σ₂ ∧ LdF .r11 .rsp 48 σ₁ t₁ ∧ LdF .r11 .rsp 48 σ₂ t₂) →
      t₁.mem.readW (t₁.gpr .r11 + BitVec.ofNat 64 56) 64 = t₂.mem.readW (t₂.gpr .r11 + BitVec.ofNat 64 56) 64 ∧
      InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .r11 + BitVec.ofNat 64 56) 8 ∧
      InRegions (t₂.rd ++ t₂.wr) (t₂.gpr .r11 + BitVec.ofNat 64 56) 8 := by
    rintro t₁ t₂ ⟨σ₁, σ₂, hσ, ⟨a₁, -, m₁, rd₁, wr₁⟩, ⟨a₂, -, m₂, rd₂, wr₂⟩⟩
    rw [a₁, a₂, m₁, m₂, rd₁, wr₁, rd₂, wr₂]
    exact hD _ _ hσ
  exact rel_ld (LdF .r10 .r11 56) (fun _ _ h => ⟨ldD_ok (hD' _ _ h).2.1, ldD_ok (hD' _ _ h).2.2⟩)
    (rel_taint [.r11] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag₁ _ _ h _ (by simp)) ldD_check)
    (rel_taint [.r10, .r11, .rsp] (ld_agree hag₁ fun _ _ h => (hD' _ _ h).1) hc)

/-! ## The checks of the taint analysis -/

theorem entry1_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block entry1.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem entry2_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block entry2) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem aadArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block aadArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem textLen_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block textLen.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem padLen_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block padLen) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem padArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block padArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem leftTest_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block leftTest.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sliceArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r10, .r11, .rsp]) (.block (sliceArgs.drop 2)) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sliceNext_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r10, .r11, .rsp]) (.block (sliceNext.drop 2)) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem finArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block finArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩


/-! ## The pieces, in two runs -/

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- `work` on the stack, in two runs between the calls. -/
theorem base_hW {ap ap' : BitVec 64} {i i' : Nat} {s₁ s₂ : State} (h₁ : Base s₀ ap i s₁) (h₂ : Base s₀' ap' i' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 48) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 48) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 48) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 48) 8 :=
  ⟨by rw [(h₁.w hp).2, (h₂.w hp').2, pb.w], (h₁.w hp).1, (h₂.w hp').1⟩

omit hp hp' in
theorem base_rsp {ap ap' : BitVec 64} {i i' : Nat} {s₁ s₂ : State} (h₁ : Base s₀ ap i s₁) (h₂ : Base s₀' ap' i' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp]; exact pb.rsp.symm

/-- A block of the code after the entry that starts by loading `work`, in two
runs between the calls. -/
theorem rel_base {F₁ F₂ : State → Prop} {l : List Instr}
    (hB : ∀ s₁ s₂, F₁ s₁ ∧ F₂ s₂ → ∃ ap ap' i i', Base s₀ ap i s₁ ∧ Base s₀' ap' i' s₂)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block l) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.block (.mov .r11 (.mem (at_ .rsp 48)) :: l)) fun _ _ => True :=
  rel_wt [.rsp] (by simp)
    (fun _ _ h => let ⟨_, _, _, _, b₁, b₂⟩ := hB _ _ h; base_rsp pb b₁ b₂)
    (fun _ _ h => let ⟨_, _, _, _, b₁, b₂⟩ := hB _ _ h; base_hW hp hp' pb b₁ b₂) hc

theorem entry1_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry1) fun s₁ s₂ =>
    E1 s₀ s₁ ∧ E1 s₀' s₂ := by
  refine pstep (F₁ := (· = s₀)) (F₂ := (· = s₀')) ?_ (fun _ h => by rw [h]; exact entry1_ok hp)
    (fun _ h => by rw [h]; exact entry1_ok hp')
  rw [show entry1 = .mov .r11 (.mem (at_ .rsp 48)) :: entry1.tail from rfl]
  refine rel_wt [.rsp] (by simp) (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact pb.rsp.symm)
    (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.w.symm, a_in hp (i := 5) (by decide), a_in hp' (i := 5) (by decide)⟩) entry1_check

theorem entry2_rel : RelCT isa (fun s₁ s₂ => E1 s₀ s₁ ∧ E1 s₀' s₂) (.block entry2) fun s₁ s₂ =>
    E2 s₀ s₁ ∧ E2 s₀' s₂ :=
  pstep (rel_taint [.r11, .rsp] (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1, pb.w]
      · rw [h.1.2.1 _ (by decide) (by decide) (by decide), h.2.2.1 _ (by decide) (by decide) (by decide), pb.rsp])
    entry2_check) (fun _ => w_entry2 hp) (fun _ => w_entry2 hp')

theorem init_rel (I : InitFn) : RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (.call I.fn.name I.fn.code)
    fun s₁ s₂ => Mid s₀ (AL s₀) 0 [] s₁ ∧ Mid s₀' (AL s₀') 0 [] s₂ := by
  refine pstep (RelCT.callEx (k := initK) I.ok I.ct fun s₁ s₂ h => ?_) (fun _ => w_init hp I) (fun _ => w_init hp' I)
  obtain ⟨⟨B₁, di₁, si₁, dx₁, cx₁⟩, ⟨B₂, di₂, si₂, dx₂, cx₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁⟩ := initEntry hp B₁ di₁ si₁ dx₁ cx₁
  obtain ⟨p₂, c₂, w₂⟩ := initEntry hp' B₂ di₂ si₂ dx₂ cx₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [B₁.rsp, B₂.rsp]; exact pb.rsp.symm⟩
  simp only [initK, initPub, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp), entry_rsp B₁.rsp,
    entry_rsp B₂.rsp, di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, K, Nn, pb.rdi, pb.rdx, pb.rcx, pb.st, pb.rsp, SP,
    and_self]

theorem aadArgs_rel : RelCT isa (fun s₁ s₂ => Mid s₀ (AL s₀) 0 [] s₁ ∧ Mid s₀' (AL s₀') 0 [] s₂) (.block aadArgs)
    fun s₁ s₂ => P4 s₀ s₁ ∧ P4 s₀' s₂ := by
  refine pstep ?_ (fun _ => w_aadArgs hp) (fun _ => w_aadArgs hp')
  rw [show aadArgs = .mov .r11 (.mem (at_ .rsp 48)) :: aadArgs.tail from rfl]
  exact rel_base hp hp' pb (fun _ _ h => ⟨_, _, _, _, h.1.toBase, h.2.toBase⟩) aadArgs_check

theorem aad_rel (A : AadFn) : RelCT isa (fun s₁ s₂ => P4 s₀ s₁ ∧ P4 s₀' s₂) (.call A.fn.name A.fn.code)
    fun s₁ s₂ => Mid s₀ (AL s₀) 0 (ad s₀) s₁ ∧ Mid s₀' (AL s₀') 0 (ad s₀') s₂ := by
  refine pstep (RelCT.callEx (k := aadK) A.ok A.ct fun s₁ s₂ h => ?_) (fun _ => w_aad hp A) (fun _ => w_aad hp' A)
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁⟩ := aadEntry hp M₁.toBase (hp.a_w.symm.sub_left stR_sub) hp.b_a
    (covers_of_mem (by rw [hp.rd]; simp)) hp.w_ad (AL s₀).isLt di₁ si₁ cx₁ (by rw [r8₁, ofNat_toNat])
  obtain ⟨p₂, c₂, w₂⟩ := aadEntry hp' M₂.toBase (hp'.a_w.symm.sub_left stR_sub) hp'.b_a
    (covers_of_mem (by rw [hp'.rd]; simp)) hp'.w_ad (AL s₀').isLt di₂ si₂ cx₂ (by rw [r8₂, ofNat_toNat])
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [M₁.rsp, M₂.rsp]; exact pb.rsp.symm⟩
  simp only [aadK, aadPub, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), entry_rsp M₁.rsp, entry_rsp M₂.rsp, di₁, di₂, si₁, si₂, dx₁, dx₂,
    cx₁, cx₂, r8₁, r8₂, K, Ad, AL, pb.rdi, pb.r8, pb.r9, pb.st, pb.rsp, SP, and_self]

theorem finArgs_rel : RelCT isa (fun s₁ s₂ => Fin s₀ s₁ ∧ Fin s₀' s₂) (.block finArgs)
    fun s₁ s₂ => P7 s₀ s₁ ∧ P7 s₀' s₂ := by
  refine pstep ?_ (fun _ => w_finArgs hp) (fun _ => w_finArgs hp')
  rw [show finArgs = .mov .r11 (.mem (at_ .rsp 48)) :: finArgs.tail from rfl]
  exact rel_base hp hp' pb (fun _ _ h => let ⟨_, _, b₁, _⟩ := h.1; let ⟨_, _, b₂, _⟩ := h.2;
    ⟨_, _, _, _, b₁, b₂⟩) finArgs_check

theorem fin_rel (F : FinFn) : RelCT isa (fun s₁ s₂ => P7 s₀ s₁ ∧ P7 s₀' s₂) (.call F.fn.name F.fn.code)
    fun _ _ => True := by
  refine RelCT.callEx (k := finK) F.ok F.ct fun s₁ s₂ h => ?_
  obtain ⟨⟨⟨_, _, B₁, -⟩, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩, ⟨⟨_, _, B₂, -⟩, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁⟩ := finEntry hp B₁ di₁ si₁ dx₁ r9₁
  obtain ⟨p₂, c₂, w₂⟩ := finEntry hp' B₂ di₂ si₂ dx₂ r9₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [B₁.rsp, B₂.rsp]; exact pb.rsp.symm⟩
  simp only [finK, finPub, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), entry_gpr _ _ (by decide : Reg.r9 ≠ .rsp), entry_rsp B₁.rsp,
    entry_rsp B₂.rsp, di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂, K, AL, pb.rdi, pb.rsi, pb.r9,
    pb.st, pb.len, pb.tg, pb.rsp, SP, and_self]

end


/-- The padding, as `vg_aes_gcm_stream_aad` reads it: apart from the state and
the stack, readable, and in the address space. -/
theorem pad_facts {M : CtxMode} {s : State} (hp : SG M s) :
    (stR s).Disjoint ⟨W s + BitVec.ofNat 64 88, pl s⟩ ∧ (tR s).Disjoint ⟨W s + BitVec.ofNat 64 88, pl s⟩ ∧
      Covers [⟨W s + BitVec.ofNat 64 88, pl s⟩] (s.rd ++ s.wr) ∧
      (W s + BitVec.ofNat 64 88).toNat + pl s ≤ 2 ^ 64 ∧ pl s < 2 ^ 64 := by
  have hw := hp.w_w
  have hpl : pl s = 16 - (AL s).toNat % 16 := rfl
  have wd : (W s + BitVec.ofNat 64 88).toNat = (W s).toNat + 88 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 88) (by decide)]; omega
  exact ⟨Offset.disjoint _ (.inr (by omega)) (by decide) (by omega), hp.b_w.sub_right (Offset.sub_base _ (by omega)),
    covers_left (by rw [hp.wr]; exact StreamTo.covers_off (k := 184) (d := 88) (by simp) (by omega) (by decide)),
    by rw [wd]; omega, by omega⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

theorem sliceArgs_ct {ap ap' : BitVec 64} {A A' : List Byte} {i : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ ap i A s₁ ∧ Mid s₀' ap' i A' s₂) (.block sliceArgs) fun _ _ => True := by
  rw [show sliceArgs = .mov .r11 (.mem (at_ .rsp 48)) :: .mov .r10 (.mem (at_ .r11 gDesc)) :: sliceArgs.drop 2
    from rfl]
  refine rel_wd (fun _ _ h => by rw [h.1.rsp, h.2.rsp]; exact pb.rsp.symm)
    (fun _ _ h => base_hW hp hp' pb h.1.toBase h.2.toBase) (fun _ _ h => ?_) sliceArgs_check
  rw [(h.1.toBase.w hp).2, (h.2.toBase.w hp').2]
  exact ⟨by rw [h.1.kept.desc, h.2.kept.desc, pb.src], h.1.toBase.slot hp (by decide),
    h.2.toBase.slot hp' (by decide)⟩

theorem sliceNext_ct {ap ap' : BitVec 64} {A A' : List Byte} {i : Nat} :
    RelCT isa (fun s₁ s₂ => S2 s₀ ap i A s₁ ∧ S2 s₀' ap' i A' s₂) (.block sliceNext) fun _ _ => True := by
  rw [show sliceNext = .mov .r11 (.mem (at_ .rsp 48)) :: .mov .r10 (.mem (at_ .r11 gDesc)) :: sliceNext.drop 2
    from rfl]
  refine rel_wd (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp]; exact pb.rsp.symm)
    (fun _ _ h => base_hW hp hp' pb h.1.1 h.2.1) (fun _ _ h => ?_) sliceNext_check
  rw [(h.1.1.w hp).2, (h.2.1.w hp').2]
  exact ⟨by rw [h.1.1.kept.desc, h.2.1.kept.desc, pb.src], h.1.1.slot hp (by decide), h.2.1.slot hp' (by decide)⟩

theorem sliceCall_ct (T : ToFn M) {ap ap' : BitVec 64} {A A' : List Byte} (hap : ap' = ap) {i : Nat}
    (hi : i < Cnt s₀) :
    RelCT isa (fun s₁ s₂ => S1 s₀ ap i A s₁ ∧ S1 s₀' ap' i A' s₂)
      (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hi' : i < Cnt s₀' := by rw [pb.cnt]; exact hi
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp]; exact pb.rsp.symm)
    (RelCT.callEx (k := toK M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, ax₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, ax₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₀₁, a₁₁, a₂₁⟩ := toEntry hp hi M₁.toBase di₁ si₁ dx₁ r9₁ r10₁ ax₁
  obtain ⟨p₂, c₂, w₂, a₀₂, a₁₂, a₂₂⟩ := toEntry hp' hi' M₂.toBase di₂ si₂ dx₂ r9₂ r10₂ ax₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by
    rw [pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, show SP s₀' = SP s₀ from pb.rsp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.rax, .r10, .rax] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [toK, toPub, Proof.AesGcm.arg, a₀₁, a₁₁, a₂₁, a₀₂, a₁₂, a₂₂, g _ _ (by decide : Reg.rdi ≠ .rsp),
    g _ _ (by decide : Reg.rsi ≠ .rsp), g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp),
    g _ _ (by decide : Reg.r8 ≠ .rsp), g _ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂,
    r8₁, r8₂, r9₁, r9₂, State.withRegions_gpr, State.callEntry_rsp, pushed_rsp, M₁.rsp, M₂.rsp, K, pb.rdi, pb.rsi,
    pb.st, pb.rsp, SP, pb.dst, pb.gl (Nat.le_of_lt hi), pb.sb hi, pb.sl hi, hap, and_self]

/-- Slice `i`, in two runs. -/
theorem slice_rel (T : ToFn M) {ap ap' : BitVec 64} {A A' : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    (hap' : ap' = BitVec.ofNat 64 A'.length) (hpp : ap' = ap) {i : Nat} (hi : i < Cnt s₀) :
    RelCT isa (fun s₁ s₂ => Mid s₀ ap i A s₁ ∧ Mid s₀' ap' i A' s₂)
      (.seq (.block sliceArgs) (.seq (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code) (.pop .rax 3))
        (.block sliceNext))) fun s₁ s₂ =>
      (Mid s₀ ap (i + 1) A s₁ ∧ s₁.zf = some (decide (Cnt s₀ - (i + 1) = 0))) ∧
        (Mid s₀' ap' (i + 1) A' s₂ ∧ s₂.zf = some (decide (Cnt s₀' - (i + 1) = 0))) := by
  have hi' : i < Cnt s₀' := by rw [pb.cnt]; exact hi
  exact RelCT.seq (pstep (sliceArgs_ct hp hp' pb) (fun _ => w_sliceArgs hp hi) (fun _ => w_sliceArgs hp' hi'))
    (RelCT.seq (pstep (sliceCall_ct hp hp' pb T hpp hi) (fun _ => w_sliceCall hp T hap hi)
      (fun _ => w_sliceCall hp' T hap' hi'))
      (pstep (sliceNext_ct hp hp' pb) (fun _ => w_sliceNext hp hi) (fun _ => w_sliceNext hp' hi')))

/-- The slices, in two runs. -/
theorem slices_rel (T : ToFn M) {ap ap' : BitVec 64} {A A' : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    (hap' : ap' = BitVec.ofNat 64 A'.length) (hpp : ap' = ap) :
    RelCT isa (fun s₁ s₂ => Mid s₀ ap 0 A s₁ ∧ Mid s₀' ap' 0 A' s₂) (slices T.fn) fun s₁ s₂ =>
      Mid s₀ ap (Cnt s₀) A s₁ ∧ Mid s₀' ap' (Cnt s₀') A' s₂ := by
  unfold slices
  refine RelCT.seq (pstep ?_ (fun _ => w_leftTest hp) (fun _ => w_leftTest hp')) ?_
  · rw [show leftTest = .mov .r11 (.mem (at_ .rsp 48)) :: leftTest.tail from rfl]
    exact rel_base hp hp' pb (fun _ _ h => ⟨_, _, _, _, h.1.toBase, h.2.toBase⟩) leftTest_check
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, pb.cnt]) ?_ ?_
  · refine skip_rel fun _ _ h => ?_
    have hC : Cnt s₀ = 0 := by have e := h.2; simp only [eval, h.1.1.2] at e; simpa using e
    have hC' : Cnt s₀' = 0 := by rw [pb.cnt]; exact hC
    exact ⟨hC ▸ h.1.1.1, hC' ▸ h.1.2.1⟩
  refine StreamTo.RelCT.of_imp (0 < Cnt s₀) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2] at e; simp at e; omega) fun hC => ?_
  refine (RelCT.loop (fun n s₁ s₂ => ∃ i, i < Cnt s₀ ∧ n = Cnt s₀ - i ∧ Mid s₀ ap i A s₁ ∧ Mid s₀' ap' i A' s₂)
    (fun n => RelCT.exists_ fun i => StreamTo.RelCT.of_imp (i < Cnt s₀ ∧ n = Cnt s₀ - i)
      (fun _ _ h => ⟨h.1, h.2.1⟩) fun ⟨hi, hn⟩ => ((slice_rel hp hp' pb T hap hap' hpp hi).mono
        (fun _ _ h => h.2.2) fun s₁ s₂ h => ?_)) (Cnt s₀)).mono (fun _ _ h => ⟨0, hC, rfl, h.1.1.1, h.1.2.1⟩)
    fun _ _ h => h
  obtain ⟨⟨M₁, z₁⟩, ⟨M₂, z₂⟩⟩ := h
  rw [pb.cnt] at z₂
  refine ⟨by simp only [eval, z₁, z₂], fun e => ?_, fun e => ?_⟩
  · have : Cnt s₀ - (i + 1) = 0 := by simp only [eval, z₁] at e; simpa using e
    have e₁ : i + 1 = Cnt s₀ := by omega
    exact ⟨e₁ ▸ M₁, by rw [pb.cnt]; exact e₁ ▸ M₂⟩
  · have : Cnt s₀ - (i + 1) ≠ 0 := by simp only [eval, z₁] at e; simpa using e
    exact ⟨Cnt s₀ - (i + 1), by omega, i + 1, by omega, rfl, M₁, M₂⟩

/-- The text, in two runs. -/
theorem text_rel (A : AadFn) (T : ToFn M) :
    RelCT isa (fun s₁ s₂ => Mid s₀ (AL s₀) 0 (ad s₀) s₁ ∧ Mid s₀' (AL s₀') 0 (ad s₀') s₂) (text A.fn T.fn)
      fun s₁ s₂ => Fin s₀ s₁ ∧ Fin s₀' s₂ := by
  unfold text
  refine RelCT.seq (pstep ?_ (fun _ => w_textLen hp) (fun _ => w_textLen hp')) ?_
  · rw [show textLen = .mov .r11 (.mem (at_ .rsp 48)) :: textLen.tail from rfl]
    exact rel_base hp hp' pb (fun _ _ h => ⟨_, _, _, _, h.1.toBase, h.2.toBase⟩) textLen_check
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL]) ?_ ?_
  · refine skip_rel fun _ _ h => ?_
    have hL : L s₀ = 0 := by have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e
    exact ⟨fin_none hp h.1.1 hL, fin_none hp' h.1.2 (by rw [pb.eL]; exact hL)⟩
  refine StreamTo.RelCT.of_imp (L s₀ ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hL => ?_
  have hL' : L s₀' ≠ 0 := by rw [pb.eL]; exact hL
  refine RelCT.seq ((pstep (rel_taint [.r11] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.w]) padLen_check)
    (fun _ => w_padLen hp) (fun _ => w_padLen hp')).mono (fun _ _ h => h.1) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun s₁ s₂ => Mid s₀ (apP s₀) 0 (padA (ad s₀)) s₁ ∧ Mid s₀' (apP s₀') 0 (padA (ad s₀')) s₂)
    ?_ ((slices_rel hp hp' pb T rfl rfl ?_).mono (fun _ _ h => h) fun _ _ h =>
      ⟨fin_slices hp h.1 hL, fin_slices hp' h.2 hL'⟩)
  rotate_left
  · simp only [apP, Proof.Gcm.padA, List.length_append, Proof.Gcm.length_zeros, length_ad, pb.r9, AL]
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2.2, h.2.2.2.2.2, AL, pb.r9]) ?_ ?_
  · refine skip_rel fun _ _ h => ?_
    have hr : (AL s₀).toNat % 16 = 0 := by have e := h.2; simp only [eval, h.1.1.2.2.2.2] at e; simpa using e
    exact ⟨pad_none h.1.1 hr, pad_none h.1.2 (by simp only [AL, pb.r9]; exact hr)⟩
  refine StreamTo.RelCT.of_imp ((AL s₀).toNat % 16 ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2.2] at e; simpa using e) fun hr => ?_
  have hr' : (AL s₀').toNat % 16 ≠ 0 := by simp only [AL, pb.r9]; exact hr
  refine RelCT.seq ((pstep (rel_taint [.r11] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.w]) padArgs_check)
    (fun _ => w_padArgs hp) (fun _ => w_padArgs hp')).mono (fun _ _ h => h.1) fun _ _ h => h) ?_
  refine pstep (RelCT.callEx (k := aadK) A.ok A.ct fun s₁ s₂ h => ?_) (fun _ h => w_padCall hp A h hr)
    (fun _ h => w_padCall hp' A h hr')
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂⟩⟩ := h
  obtain ⟨f₁, f₂, f₃, f₄, f₅⟩ := pad_facts hp
  obtain ⟨f₁', f₂', f₃', f₄', f₅'⟩ := pad_facts hp'
  obtain ⟨p₁, c₁, w₁⟩ := aadEntry hp M₁.toBase f₁ f₂ f₃ f₄ f₅ di₁ si₁ cx₁ r8₁
  obtain ⟨p₂, c₂, w₂⟩ := aadEntry hp' M₂.toBase f₁' f₂' f₃' f₄' f₅' di₂ si₂ cx₂ r8₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [M₁.rsp, M₂.rsp]; exact pb.rsp.symm⟩
  simp only [aadK, aadPub, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), entry_rsp M₁.rsp, entry_rsp M₂.rsp, di₁, di₂, si₁, si₂, dx₁, dx₂,
    cx₁, cx₂, r8₁, r8₂, K, AL, pl, pb.rdi, pb.r9, pb.st, pb.w, pb.rsp, SP, and_self]

end

/-- The streaming path, in two runs. -/
theorem stream_rel {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀') (I : InitFn)
    (A : AadFn) (T : ToFn M) (F : FinFn) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (stream I.fn A.fn T.fn F.fn) fun _ _ => True := by
  unfold stream
  exact RelCT.seq (init_rel hp hp' pb I) (RelCT.seq (aadArgs_rel hp hp' pb) (RelCT.seq (aad_rel hp hp' pb A)
    (RelCT.seq (text_rel hp hp' pb A T) (RelCT.seq (finArgs_rel hp hp' pb) (fin_rel hp hp' pb F)))))

end VG.Proof.AesGcm.X86_64.Gather
