module

public import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
public import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit

/-!
# SM4 ECB on x86-64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them. `ecb_framed` runs it with its
working space on the stack, zeroed on return: 3144 bytes, the 390 words of
the scratch buffer and 24 more.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Sm4 (specDir ecbX86_64)

/-- Resaving the values already in the save slots leaves memory unchanged. -/
private theorem saved_frame_eq {sRef : State} {b : Addr} {m m' : Mem}
    (h : Saved sRef b m) (h' : Saved sRef b m')
    (hf : Frame [⟨wordAddr b savedSlot, 48⟩] m m') : m' = m := by
  funext x
  by_cases hx : (⟨wordAddr b savedSlot, 48⟩ : Region).Contains x 1
  · let o := (x - wordAddr b savedSlot).toNat
    have ho : o < 48 := by simp only [Region.Contains] at hx; omega_using [hx]
    have hx' : x = wordAddr b savedSlot + BitVec.ofNat 64 o := by
      rw [show BitVec.ofNat 64 o = x - wordAddr b savedSlot from (BitVec.ofNat_toNat 64 _).trans (BitVec.setWidth_eq _)]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have ha : wordAddr b savedSlot + BitVec.ofNat 64 o =
        wordAddr b (savedSlot + o / 8) + BitVec.ofNat 64 (o % 8) := by
      simp only [wordAddr, VG.Offset.add_add]
      congr 2; omega_arith
    rw [hx', ha, byte_of_readW m' _ (by omega_arith), byte_of_readW m _ (by omega_arith),
      h _ (by omega_using [ho]), h' _ (by omega_using [ho])]
  · exact hf x (by simpa only [List.mem_singleton, forall_eq] using hx)

/-- The shared transform inlined, with the save slots carried by ECB. -/
private theorem cryptSharedInline_wp : CryptCorrect cryptShared.inline := by
  intro s sRef E hs hp hm hrdi
  let b := s.gpr sb
  have hw := hp.scr
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := restore_loads hw rfl hs
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .rdi sb
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movImm_ok s₂ .rsi (BitVec.ofNat 64 slots)
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ sb .rdi
  have b₄ : s₄.gpr sb = b := by rw [v₄, o₃ _ (by decide), v₂, o₁ sb (fun i _ => by exact (sreg_ne i).1.symm)]
  obtain ⟨s₅, e₅, sv₅, g₅, rd₅, wr₅, f₅⟩ := save_saved (b := b) (by rw [wr₄, wr₃, wr₂, wr₁]; exact hw) b₄
  have orig₄ : ∀ i < 6, s₄.gpr (sreg i) = sRef.gpr (sreg i) := fun i hi => by
    rw [o₄ _ (sreg_ne i).1, o₃ _ (by unfold sreg; split <;> decide),
      o₂ _ (by unfold sreg; split <;> decide), v₁ i hi]
  have mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have mem₅ : s₅.mem = s.mem := by
    apply saved_frame_eq hs
    · intro i hi; rw [← orig₄ i hi]; exact sv₅ i hi
    · rw [← mem₄]; exact f₅
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := slotAddr_ok s₅ .rdi tableEnd (by decide)
  have b₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), g₅, b₄]
  have mem₆ : s₆.mem = s.mem := m₆.trans mem₅
  have pre₆ : KeyCtx s₆ E :=
    { scr := by rw [b₆, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw
      fit := by rw [b₆]; exact hp.fit
      keys := fun i hi => by rw [mem₆, b₆]; exact hp.keys i hi }
  have mask₆ : MasksOk s₆ := by
    intro kv hkv; show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
    rw [mem₆, b₆]; exact hm kv hkv
  unfold cryptShared cryptCall Code.inline cryptPrepared
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₃, by
    rw [show ([VG.Impl.Aes.X86_64.movR .rdi sb, .movImm64 .rsi (BitVec.ofNat 64 slots)] : List Instr) =
      [VG.Impl.Aes.X86_64.movR .rdi sb] ++ [.movImm64 .rsi (BitVec.ofNat 64 slots)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩))
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_app, runBlock_app, e₄, Option.bind_some, e₅, Option.bind_some, e₆], ?_⟩)
  refine WP.seq (WP.mono (crypt16_wp pre₆ mask₆ (by rw [v₆, b₆, g₅, b₄])) fun s₇ ⟨c₇, out₇⟩ => ?_)
  have b₇ : s₇.gpr sb = b := c₇.base.trans b₆
  have sv₇ : Saved sRef b s₇.mem := fun i hi => by
    rw [← hs i hi, ← mem₆]
    refine c₇.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton] at hr; subst hr
    rw [b₆]; exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i))
      (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  obtain ⟨s₈, e₈, -, o₈, m₈, rd₈, wr₈⟩ := restore_loads (b := b)
    (by rw [c₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw) b₇ sv₇
  obtain ⟨s₉, e₉, v₉, o₉, m₉, rd₉, wr₉⟩ := slotAddr_ok s₈ .rdi tableEnd (by decide)
  have b₈ : s₈.gpr sb = b := (o₈ _ (fun i _ => (sreg_ne i).1.symm)).trans b₇
  have b₉ : s₉.gpr sb = b := (o₉ _ (by decide)).trans b₈
  have noSaved : ∀ r, r ∉ sboxWrites → ∀ i < 6, r ≠ sreg i := by
    intro r hr i _ he; subst r
    exact hr (by unfold sreg; split <;> decide)
  refine WP.of_runBlock ⟨s₈, e₈, WP.of_runBlock ⟨s₉, e₉, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩⟩
  · rw [rd₉, rd₈, c₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  · rw [wr₉, wr₈, c₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  · intro r hnot hkp
    by_cases hdi : r = .rdi
    · subst r; rw [v₉, b₈]; exact hrdi.symm
    · by_cases hsb : r = sb
      · subst r; exact b₉
      · rw [o₉ _ hdi, o₈ _ (noSaved r hnot), c₇.keep r hnot hkp, o₆ _ hdi, g₅,
          o₄ _ hsb, o₃ _ hkp, o₂ _ hdi, o₁ _ (noSaved r hnot)]
  · rw [m₉, m₈, ← mem₆]
    change Frame [⟨b, 8 * tableSlot⟩] s₆.mem s₇.mem
    rw [← b₆]; exact c₇.frame
  · intro kv hkv
    show s₉.mem.readW (wordAddr (s₉.gpr sb) kv.1) 64 = kv.2
    rw [m₉, m₈, b₉, ← b₇]; exact c₇.masks kv hkv
  · intro j hj
    have := out₇ j hj
    simp only [tailBlock] at this ⊢
    rw [m₉, m₈, b₉, ← b₇, this, mem₆, b₆]

/-- The initial taint: the registers of the arguments and the stack pointer are
public. It knows nothing of the writable regions: the code never reads a public
value back from them, and tracking them would cost the kernel at every store. -/
def ecbTaint : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbTaint_agree (dir : Dir) (s t : State) (_ : (ecbX86_64 dir).pre s) (_ : (ecbX86_64 dir).pre t)
    (hp : (ecbX86_64 dir).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86_64 dir).pre (ecbX86_64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86_64 dir).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ecb_wp dir hs
  refine ⟨t, s', he, abiPreserved_of_exec (c := ecb dir) ?_ he hg, hpost⟩
  cases dir <;> lit_decide

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 1 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 390⟩]

theorem ecb_verified (dir : Dir) :
    Verified X86_64.target (ecb dir) (Proof.Sm4.ecbScratchContract X86_64.abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbX86_64, specDir,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 390 (ecb dir))
      (Spec.Sm4.ecbContract X86_64.abi (specDir dir) 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 390) (post := Spec.Sm4.ecbPost (specDir dir) X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3144) (ecb_verified dir) (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by cases dir <;> lit_decide)) (by cases dir <;> lit_decide) (by decide)
    (Proof.Sm4.ecbPostOut_local _ _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- Inlining changes only the prepared transform, leaving ECB's structure. -/
private theorem ecbShared_inline (dir : Dir) :
    (ecbShared dir).inline = ecbWith cryptShared.inline dir := by
  cases dir <;> kernel_rfl

private theorem ecbShared_inline_correct (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) :
    ∃ t s', Exec isa (ecbShared dir).inline s t s' ∧ abiPreserved s s' ∧ (ecbX86_64 dir).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := ecbWith_wp cryptShared.inline cryptSharedInline_wp dir hs
  rw [← ecbShared_inline] at he
  exact ⟨t, s', he, abiPreserved_of_exec (by cases dir <;> lit_decide) he hg, hp⟩

private theorem ecbShared_inline_ct (dir : Dir) :
    ConstantTime isa (ecbX86_64 dir).pre (ecbX86_64 dir).pub (ecbShared dir).inline := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide)

private theorem ecbShared_implies (dir : Dir) :
    (ecbX86_64 dir).Implies (Proof.Sm4.ecbScratchContract X86_64.abi (specDir dir) slots 8) := by
  cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbX86_64, specDir,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat

/-- ECB's buffers stay clear of the shared call's return-address slot. -/
theorem ecbShared_verified (dir : Dir) :
    Verified X86_64.target (ecbShared dir) (Proof.Sm4.ecbScratchContract X86_64.abi (specDir dir) slots 8) := by
  refine Verified.of_inline (by cases dir <;> lit_decide) (ecbShared_inline_correct dir)
    (ecbShared_inline_ct dir) (ecbShared_implies dir) (fun _ h => Sig.clear_of_pre h) ?_
    (fun _ _ _ _ h => Sig.rsp_of_pub h)
  intro s b hv u hs hp
  have hs' := (ecbShared_implies dir).pre s hs
  have hc := Sig.clear_of_pre hs
  obtain ⟨-, hw, -, -, -, -, -, -, fitD, -⟩ := hs'
  have hf : Frame [hole (s.gpr .rsp)] b.mem (b.patch (hole (s.gpr .rsp)) hv u).mem := by
    intro x hx; exact State.patch_mem (hx _ (List.mem_singleton_self _))
  change Spec.Sm4.blocksAt _ _ _ = _
  rw [Proof.Sm4.blocksAt_frame hf (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    rw [Nat.mul_comm]
    exact hc _ (List.mem_append_right _ (by rw [hw]; exact List.mem_cons_self)))
    (by omega_using [fitD])]
  exact hp

/-- The smaller frame leaves room for the return address within the existing
3144-byte public stack contract. -/
theorem ecbShared_framed (dir : Dir) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3128 .rcx 390 (ecbShared dir))
      (Spec.Sm4.ecbContract X86_64.abi (specDir dir) 3144) := by
  apply X86_64.Verified.stack_mono (n := 3136) (by decide)
  · exact X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
      (n := 390) (post := Spec.Sm4.ecbPost (specDir dir) X86_64.abi.ptrBits) (wa := true) (stack := 8)
      (bytes := 3128) (ecbShared_verified dir) (by decide) (by decide) (by decide)
      (Code.all_of_spTest (by cases dir <;> lit_decide)) (by cases dir <;> lit_decide) (by decide)
      (Proof.Sm4.ecbPostOut_local _ _)
      (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
  · exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

end VG.Proof.Sm4.X86_64
