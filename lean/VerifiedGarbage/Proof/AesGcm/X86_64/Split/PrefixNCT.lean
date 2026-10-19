module

import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Lit
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bytes
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Layout
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
meta import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo
meta import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bytes
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Layout
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop

/-!
# AES-GCM `seal_split` on x86-64: `prefixN` in constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public values take the same branch of `nTest` (on the lengths); on the
path in one pass, each block is checked by the taint analysis from the
registers that hold the same values in both (`W`, then the copy's
arguments, then the loop's, as `NA`–`NC` give them), and the loop
(`StitchR.encN`, from its literal) addresses memory from its arguments
alone; the other path is `prefix`'s (`prefixNRel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn step)

theorem nTest_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.nTest) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem nCopyArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.nCopyArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem nArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15]) (.block SealSplit.nArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem nRest_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.nRest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The registers `StitchR.encN` addresses memory and counts from. -/
abbrev encNRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11, .rbx, .rbp, .rsp]

theorem encN_check :
    ∃ hc, (taint.check (Taint.ofRegs encNRegs) Impl.Gcm.X86_64.StitchR.encN hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP CtxMode.prepared Ctx W SP D S R n sl σ) (h' : PP CtxMode.prepared Ctx W SP D S R n sl σ')
include h h'

/-- After `nTest`. -/
abbrev NT (n sl : Nat) (σ t : State) : Prop :=
  t.cf = some (decide (1 ≤ sl / 256 ∧ sl / 256 < n / 256)) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = σ.gpr r) ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr

/-- The path in one pass, in two runs. -/
theorem nPath_rel (hS : Gcm.X86_64.StitchR.SetupFin) (hC : 1 ≤ sl / 256 ∧ sl / 256 < n / 256) {P : State → State → Prop}
    (hP : ∀ a b, P a b → NT n sl σ a ∧ NT n sl σ' b) :
    RelCT isa P (.seq (.block SealSplit.nCopyArgs) (.seq SealGather.copy (.seq (.block SealSplit.nArgs)
      (.seq Impl.Gcm.X86_64.StitchR.encN (.block SealSplit.nRest))))) fun _ _ => True := by
  have r15 : ∀ {t t' : State}, t.gpr .r15 = σ.gpr .r15 → t'.gpr .r15 = σ'.gpr .r15 → t.gpr .r15 = t'.gpr .r15 :=
    fun e e' => by rw [e, e', h.env.r15, h'.env.r15]
  refine RelCT.seq (step [.r15] nCopyArgs_check (F₁ := NT n sl σ) (F₂ := NT n sl σ')
    (G₁ := NA D S sl σ) (G₂ := NA D S sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨-, g₁, -⟩, ⟨-, g₂, -⟩⟩ := hP _ _ g
      exact r15 (g₁ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)))
    hP (fun _ ⟨_, g, m, rd, wr⟩ => nA_ok h g m rd wr) (fun _ ⟨_, g, m, rd, wr⟩ => nA_ok h' g m rd wr)) ?_
  refine RelCT.seq (step [.rsi, .rdi, .rcx] Gather.copy_check (F₁ := NA D S sl σ) (F₂ := NA D S sl σ')
    (G₁ := NB D S sl σ) (G₂ := NB D S sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g.1.rsi, g.2.rsi]
      · rw [g.1.rdi, g.2.rdi]
      · rw [g.1.rcx, g.2.rcx])
    (fun _ _ g => g) (fun _ g => nB_ok h g) (fun _ g => nB_ok h' g)) ?_
  refine RelCT.seq (step [.r13, .r14, .r15] nArgs_check (F₁ := NB D S sl σ) (F₂ := NB D S sl σ')
    (G₁ := NC Ctx W D S R n sl σ) (G₂ := NC Ctx W D S R n sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g.1.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          g.2.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.r13, h'.env.r13]
      · rw [g.1.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          g.2.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.r14, h'.env.r14]
      · rw [g.1.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          g.2.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ g => nC_ok h g) (fun _ g => nC_ok h' g)) ?_
  let G (σ : State) : State → Prop := fun u => ∃ t, NC Ctx W D S R n sl σ t ∧
    Gcm.X86_64.StitchR.NPost t (16 * (n / 256)) u
  refine RelCT.seq (step encNRegs encN_check (F₁ := NC Ctx W D S R n sl σ) (F₂ := NC Ctx W D S R n sl σ')
    (G₁ := G σ) (G₂ := G σ')
    (fun _ _ g r hr => by
      obtain ⟨g₁, g₂⟩ := g
      simp only [encNRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [g₁.rdi, g₂.rdi]
      · rw [g₁.rsi, g₂.rsi]
      · rw [g₁.rdx, g₂.rdx]
      · rw [g₁.rcx, g₂.rcx]
      · rw [g₁.r8, g₂.r8]
      · rw [g₁.r9, g₂.r9]
      · rw [g₁.r10, g₂.r10]
      · rw [g₁.r11, g₂.r11]
      · rw [g₁.rbx, g₂.rbx]
      · rw [g₁.rbp, g₂.rbp]
      · rw [g₁.keep _ (by simp), g₂.keep _ (by simp), h.env.rsp, h'.env.rsp])
    (fun _ _ g => g) (fun t g => WP.mono (nD_ok h hS hC g) fun u hu => ⟨t, g, hu⟩)
    (fun t g => WP.mono (nD_ok h' hS hC g) fun u hu => ⟨t, g, hu⟩)) ?_
  exact (step [.r15] nRest_check (F₁ := G σ) (F₂ := G σ') (G₁ := fun _ => True) (G₂ := fun _ => True)
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨t, hN, hu⟩, ⟨t', hN', hu'⟩⟩ := g
      rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hu'.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hN.keep _ (by simp),
        hN'.keep _ (by simp), h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ ⟨_, hN, hu⟩ => WP.mono (nE_ok h hC hN hu) fun _ _ => trivial)
    (fun _ ⟨_, hN, hu⟩ => WP.mono (nE_ok h' hC hN hu) fun _ _ => trivial)).mono (fun _ _ g => g) fun _ _ _ => trivial

end

/-- `prefixN` in two runs. -/
theorem prefixNRel (hS : Gcm.X86_64.StitchR.SetupFin) (T : BlkToFn CtxMode.prepared) : PreRel CtxMode.prepared (SealSplit.prefixN T.fn) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  unfold SealSplit.prefixN
  refine RelCT.seq (step [.r15] nTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := NT n sl σ) (G₂ := NT n sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact nTest_ok h.data.ok.lt h.sl_le h.env h.slen h.len)
    (fun _ hs => by rw [hs]; exact nTest_ok h'.data.ok.lt h'.sl_le h'.env h'.slen h'.len)) ?_
  refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.1, g.2.1]) ?_ ?_
  · refine StreamTo.RelCT.of_imp (1 ≤ sl / 256 ∧ sl / 256 < n / 256) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.1] at e; simpa using e) fun hC => ?_
    exact nPath_rel h h' hS hC fun _ _ g => g.1
  · refine rel_each fun t t' g => ?_
    obtain ⟨⟨⟨-, g₁, m₁, rd₁, wr₁⟩, ⟨-, g₂, m₂, rd₂, wr₂⟩⟩, -⟩ := g
    have he : ∀ {σ t : State} {M : CtxMode} {R : Nat}, PP M Ctx W SP D S R n sl σ →
        (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = σ.gpr r) → t.rd = σ.rd → t.wr = σ.wr →
        Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g rd wr => h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
      rd wr
    exact prefixRel T (h.of_eq (he h g₁ rd₁ wr₁) m₁ rd₁ wr₁) (h'.of_eq (he h' g₂ rd₂ wr₂) m₂ rd₂ wr₂)

/-! ## What every instruction of `prefixN` does not do -/

/-- The path in one pass. -/
abbrev nPart : Prog isa := .seq (.block SealSplit.nCopyArgs) (.seq SealGather.copy (.seq (.block SealSplit.nArgs)
  (.seq Impl.Gcm.X86_64.StitchR.encN (.block SealSplit.nRest))))

theorem nPart_mx : (nPart : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  lit_decide
theorem nPart_spSafe : (nPart : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)
theorem nPart_xdepth : (nPart : Prog isa).x86_64Depth = 0 := by decide +kernel

theorem prefixN_mx {fTo : Fn} (h : (SealSplit.prefix fTo).allInstrs (fun i => !loadsMxcsr i) = true) :
    (SealSplit.prefixN fTo).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := nPart_mx
  simp only [SealSplit.prefixN, Code.allInstrs] at e h ⊢
  rw [e, h]; decide

theorem prefixN_spSafe {fTo : Fn} (h : (SealSplit.prefix fTo).all (fun i => !X86_64.isa.writesSp i) = true) :
    (SealSplit.prefixN fTo).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := nPart_spSafe
  simp only [SealSplit.prefixN, Code.all] at e h ⊢
  rw [e, h]; decide

theorem prefixN_xdepth {fTo : Fn} {d : Nat} (h : (SealSplit.prefix fTo).x86_64Depth ≤ d) :
    (SealSplit.prefixN fTo).x86_64Depth ≤ d := by
  have e := nPart_xdepth
  simp only [SealSplit.prefixN, Code.x86_64Depth] at e h ⊢
  rw [e]; simp only [Nat.max_le] at h ⊢; omega

end VG.Proof.AesGcm.X86_64.Split
