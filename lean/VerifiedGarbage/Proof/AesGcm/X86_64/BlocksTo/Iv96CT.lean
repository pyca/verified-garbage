module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Iv96
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on whole blocks out of place, x86-64: constant time given the block index

Untrusted: everything here is checked by Lean. As `BlocksTo.encrypt_ct`, with
a loop given the block index (`EncCodeI`): its part is related step by step
(the comparison, taking all the blocks, the working space), then by the
loop's own relation, from the same index in both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- The registers public where the loops start. -/
abbrev regsT : List Reg := [.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem cmpT_check : ∃ hc, ((taint.check (Taint.ofRegs regsT) (.block [.alu .cmp .r9 (imm 16)]) hc).map
    fun τ' => (RegSet.ofList regsT).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nilT_check : ∃ hc, ((taint.check (Taint.ofRegs regsT) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem takeScratch_check (aligned : Bool) : ∃ hc, ((taint.check (Taint.ofRegs regsT)
    (.block (takeAllTo ++ Blocks.scratchSetup aligned)) hc).map fun τ' =>
      (RegSet.ofList regsT).subset τ'.regs && (!false || τ'.flags)) = some true := by
  cases aligned
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : BT M s₀) (hp' : BT M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- The part of a loop given the block index, in two runs with the same
index. -/
theorem stitchI_rel (aligned : Bool) (c : EncCodeI M) (hx : IdxArg 32 s₀) (hx' : IdxArg 32 s₀')
    (hi : s₀.mem.readW (SP s₀ + BitVec.ofNat 64 32) 32 = s₀'.mem.readW (SP s₀' + BitVec.ofNat 64 32) 32) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (stitchPart c.enc aligned true) fun _ _ => True := by
  have ag : ∀ s₁ s₂, ((∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂) →
      ∀ r ∈ regsT, s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ h r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [h.2.1.2.1, h.2.2.2.1, pb.dst]
    · exact h.1 r hr
  have post : ∀ {s : State}, BT M s → ∀ {s₁ : State}, EntryPost s s₁ →
      WP isa (.block [.alu .cmp .r9 (imm 16)]) s₁ fun s₂ => EntryPost s s₂ ∧ s₂.cf = some (decide (n s < 16)) :=
    fun {s} hp {s₁} ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ =>
      WP.mono (cmp16_ok (s := s) (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ =>
        ⟨⟨by rw [g₂]; exact h11, by rw [g₂]; exact h10, fun r a b => by rw [g₂]; exact hg r a b,
          by rw [m₂]; exact hk, by rw [m₂]; exact hf, rd₂.trans hrd, wr₂.trans hwr⟩, cf₂⟩
  have a := rel_wp (rel_regs regsT regsT false ag cmpT_check) (fun _ _ h => h.2)
    (fun _ h => post hp h) (fun _ h => post hp' h)
  refine RelCT.seq a (RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.2.1.2, h.2.2.2, pb.en]) ?_ ?_)
  · exact (rel_regs regsT [.rsp] false (fun _ _ h => h.1.1.1) nilT_check).mono (fun _ _ h => h) fun _ _ _ => trivial
  · have b := rel_wp (P := fun s₁ s₂ => (((∀ r ∈ regsT, s₁.gpr r = s₂.gpr r) ∧ (false = true → s₁.cf = s₂.cf ∧
        s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧ (EntryPost s₀ s₁ ∧
        s₁.cf = some (decide (n s₀ < 16))) ∧ EntryPost s₀' s₂ ∧ s₂.cf = some (decide (n s₀' < 16))) ∧
        isa.eval .b s₁ = some false)
      (rel_regs regsT regsT false (fun _ _ h => h.1.1.1) (takeScratch_check aligned))
      (F₁ := fun t => EntryPost s₀ t ∧ 16 ≤ n s₀) (F₂ := fun t => EntryPost s₀' t ∧ 16 ≤ n s₀')
      (fun _ _ h => by
        obtain ⟨⟨-, ⟨e₁, cf₁⟩, ⟨e₂, -⟩⟩, ht⟩ := h
        simp only [eval, cf₁, Option.some.injEq, decide_eq_false_iff_not] at ht
        exact ⟨⟨e₁, by omega⟩, e₂, by rw [pb.en]; omega⟩)
      (fun _ ⟨⟨h11, h10, hg, hk, hf, hrd, hwr⟩, h16⟩ => takeScratchI_ok (M := M) hp hx h16 h11 h10 hg hk hf hrd hwr)
      (fun _ ⟨⟨h11, h10, hg, hk, hf, hrd, hwr⟩, h16⟩ =>
        takeScratchI_ok (M := M) hp' hx' h16 h11 h10 hg hk hf hrd hwr)
    rw [show ((if true = true then takeAllTo else [.mov .rax (.reg .r9), .alu .and .rax (imm 15),
      .alu .sub .r9 (.reg .rax)]) ++ Blocks.scratchSetup aligned : List Instr) =
      takeAllTo ++ Blocks.scratchSetup aligned from rfl]
    refine RelCT.seq b (c.ct.mono (fun s₁ s₂ h => ?_) fun _ _ h => h)
    obtain ⟨⟨hr, -⟩, ⟨p₁, i₁, e₁⟩, ⟨p₂, i₂, e₂⟩⟩ := h
    exact ⟨hr, p₁, p₂, i₁, i₂, by rw [e₁, e₂]; exact hi⟩

end

/-- `vg_aes_gcm_encrypt_blocks_to` with a loop given the block index, for any
contract whose precondition gives `BT` and `IdxArg 32`, and whose public
arguments include those of `blocksToPub` and the index. -/
theorem encryptI_ct {M : CtxMode} (B : BlkFn M) (aligned : Bool) (c : EncCodeI M) {k : Contract isa}
    (hpre : ∀ s, k.pre s → BT M s ∧ IdxArg 32 s)
    (hpub : ∀ s s', k.pub s s' → Proof.AesGcm.blocksToPub s s' ∧
      s.mem.readW (SP s + BitVec.ofNat 64 32) 32 = s'.mem.readW (SP s' + BitVec.ofNat 64 32) 32) :
    ConstantTime isa k.pre k.pub (encrypt B.enc (some c.enc) aligned true) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  obtain ⟨hp, hx⟩ := hpre _ h
  obtain ⟨hp', hx'⟩ := hpre _ h'
  have pb := Pub.of (hpub _ _ hq).1
  have hi := (hpub _ _ hq).2
  have eq : qf s₀' = qf s₀ := by simp only [qf, pb.en]
  have hpiece : ∀ {s : State}, BT M s → IdxArg 32 s → ∀ s₁, EntryPost s s₁ →
      WP isa (stitchPart c.enc aligned true) s₁ (Mid s (qf s) (qf s)) :=
    fun hp hx _ ⟨h11, h10, hg, hk, hf, hrd, hwr⟩ => stitchFullTo_okG hp
      (fun s₄ h ga h9 h10₄ g11 hf₄ rd₄ => c.ok s₄ h (idxOk_of hp hx ga h9 h10₄ g11 hf₄ rd₄))
      h11 h10 hg hk hf hrd hwr
  have a := rel_wp (stitchI_rel hp hp' pb aligned c hx hx' hi) (fun _ _ h => h.2)
    (fun _ h => hpiece hp hx _ h) (fun _ h => hpiece hp' hx' _ h)
  have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
    (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
      Mid s₀ (qf s₀) (qf s₀) s₁ ∧ Mid s₀' (qf s₀') (qf s₀') s₂) [.rsp] [.rsp] (by simp)
    (fun _ _ h => h.1) (fun _ _ h => mid_hS hp hp' pb h.2.1 h.2.2) rest_check)
    (fun _ _ h => h.2) (fun _ h => restFullTo_ok hp h) (fun _ h => restFullTo_ok hp' h)
  have part : RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧
      EntryPost s₀' s₂) (head (some c.enc) aligned true) fun s₁ s₂ => ∃ q, Mid s₀ q q s₁ ∧ Mid s₀' q q s₂ :=
    (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨mid_rsp pb h.2.1 h.2.2, h.2.1, h.2.2⟩) b).mono
      (fun _ _ h => h) fun _ _ h => ⟨qf s₀, h.2.1, by rw [← eq]; exact h.2.2⟩
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq part ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb B _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.BlocksTo
