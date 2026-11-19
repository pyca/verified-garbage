module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.X86_64.Verified
public import VerifiedGarbage.Proof.Idea.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
public import VerifiedGarbage.Proof.Idea.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Idea.X86_64.Lit
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Spec.Idea.Ofb
meta import VerifiedGarbage.Spec.Idea.OfbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Idea.X86_64.Verified
meta import VerifiedGarbage.Proof.Idea.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Idea.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Idea.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Idea.ScrubLocal
meta import VerifiedGarbage.Proof.Idea.ScrubLocal
public import VerifiedGarbage.Proof.Idea.Inverse
public import VerifiedGarbage.Proof.Idea.X86_64.ConstantTime
public import VerifiedGarbage.Proof.Idea.X86_64.Block
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Idea.Inverse
meta import VerifiedGarbage.Proof.Idea.X86_64.ConstantTime
meta import VerifiedGarbage.Proof.Idea.X86_64.Block
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Idea.KeyLit
import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Linear
meta import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-! ### `Idea.X86_64.Key`, which only this module used -/

section

/-!
# IDEA key expansion on x86-64

Each schedule quadword (`expandWord q`) is a fixed bit permutation of the
key's two quadwords, checked by evaluation over the lane domain
(`expand_check`, `Straight.linear_ok`): bit `p` of `rax` is the key bit
`expandSrc q p`. The quadwords are stored in turn (`words_run`), and every
subkey bit is then the key bit `Spec.Idea.expandKey` takes
(`expandKey_getLsbD`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Idea.X86_64 VG.Impl.Idea

/-- The key's two quadwords at `rdi`, no slots. -/
def eCfg : Cfg := { base := .rsi, slots := 0, ext := .rdi, exts := 2 }

/-- Bit `p` of quadword `q`: atom `64 j + t`, bit `t` of key quadword `j`. -/
def eG (q p : Nat) : List Nat := [64 * (expandSrc q p).1 + (expandSrc q p).2]

theorem expand_check : ∀ q < 13,
    check (lanes 64 7) eCfg (linExt 0) (expandWord q) (linEnv []) (linPost 7 [(.rax, eG q)]) = true := by
  lit_decide

/-- The registers `expandWord` keeps. -/
theorem expand_kept : ∀ q < 13, ∀ r ∈ [Reg.rdi, .rsi, .rsp, .rbx, .rbp, .r12, .r13, .r14, .r15],
    ((expandWord q).all fun i => i.dst != some r) = true := by
  lit_decide

theorem expandWord_run (q : Nat) (hq : q < 13) (s : State)
    (hk : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (expandWord q) s = some s' ∧
      (∀ p < 64, (s'.gpr .rax).getLsbD p =
        (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * (expandSrc q p).1)) 64).getLsbD
          (expandSrc q p).2) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s.gpr r) := by
  have hok : Ok eCfg s := ⟨fun k hk' => absurd hk' (by simp [eCfg]), fun k hk' => hk k hk',
    by decide, fun k hk' => absurd hk' (by simp [eCfg])⟩
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok (expand_check q hq) hok
    (fun i => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 64)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 2 := hj
      refine ⟨by omega_using [hj'], ?_⟩
      simp only [Nat.zero_add, wordAddr]
      rfl)
  refine ⟨s', hs', fun p hp => ?_, hrd, hwr, ?_, fun r hr => hoth r (expand_kept q hq r hr)⟩
  · have src := keyLoc_spec (keyBit_lt (4 * q + p / 16) (p % 16))
    rw [hout .rax (eG q) (by simp) p hp]
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc] using src.2.1)]
  · funext a
    exact hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, eCfg, Region.Contains]

/-- After `q` quadwords: the schedule's first `q` quadwords hold their key bits,
nothing else is written, and the pointers and other registers are kept. -/
structure ExpInv (s₀ : State) (q : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = s₀.gpr .rdi
  rsi : t.gpr .rsi = s₀.gpr .rsi
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  regs : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .rsi, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .rdi))).getLsbD (keyBit (4 * i + p / 16) (p % 16))

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `rdi`)
readable, the schedule (104 bytes at `rsi`) writable, apart. -/
structure ExpPre (s : State) : Prop where
  key : ⟨s.gpr .rdi, 16⟩ ∈ s.rd ++ s.wr
  sched : ⟨s.gpr .rsi, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .rdi, 16⟩ : Region).Disjoint ⟨s.gpr .rsi, 104⟩

theorem words_run (s₀ : State) (hp : ExpPre s₀) : ∀ q ≤ 13, ∃ t,
    runBlock isa ((List.range q).flatMap fun q => expandWord q ++ ([.store (at_ .rsi (8 * q)) .rax] : List Instr)) s₀ =
      some t ∧ ExpInv s₀ q t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _,
      fun i hi => absurd hi (by omega_using [])⟩⟩
  | q + 1, hq => by
    obtain ⟨t, ht, hi⟩ := words_run s₀ hp q (by omega_using [hq])
    obtain ⟨t₁, h₁, bits₁, rd₁, wr₁, mem₁, regs₁⟩ := expandWord_run q (by omega_using [hq]) t (fun j hj => by
      rw [hi.rd, hi.wr, hi.rdi]
      exact ⟨_, hp.key, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
    have hw : InRegions t₁.wr (t₁.ea (at_ .rsi (8 * q))) 8 := by
      rw [ea_at, regs₁ .rsi (by simp), wr₁, hi.wr, hi.rsi]
      exact ⟨_, hp.sched, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
    have h₂ : runBlock isa [.store (at_ .rsi (8 * q)) .rax] t₁ =
        some { t₁ with mem := t₁.mem.writeW (t₁.ea (at_ .rsi (8 * q))) (t₁.gpr .rax) } := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, isa, hw, ↓reduceIte]
    have ea₁ : t₁.ea (at_ .rsi (8 * q)) = s₀.gpr .rsi + BitVec.ofNat 64 (8 * q) := by
      rw [ea_at, regs₁ .rsi (by simp), hi.rsi]
    have sub : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15],
        r ∈ [Reg.rdi, .rsi, .rsp, .rbx, .rbp, .r12, .r13, .r14, .r15] := by decide
    refine ⟨{ t₁ with mem := t₁.mem.writeW (t₁.ea (at_ .rsi (8 * q))) (t₁.gpr .rax) }, ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append h₁ h₂)
    · refine ⟨(regs₁ .rdi (by simp)).trans hi.rdi, (regs₁ .rsi (by simp)).trans hi.rsi,
        rd₁.trans hi.rd, wr₁.trans hi.wr,
        fun r hr => (regs₁ r (sub r hr)).trans (hi.regs r hr), ?_, ?_⟩
      · show Frame _ s₀.mem (t₁.mem.writeW _ _)
        rw [mem₁, ea₁]
        refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
          (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hq]))
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_using [])
      · intro i hiq p hp64
        show ((t₁.mem.writeW _ _).readW _ 64).getLsbD p = _
        rw [mem₁, ea₁]
        by_cases he : i = q
        · subst he
          rw [Mem.readW_writeW_self64, bits₁ p hp64]
          have src := keyLoc_spec (keyBit_lt (4 * i + p / 16) (p % 16))
          rw [readW_getLsbD _ _ (by simpa [expandSrc] using src.2.1), Offset.add_ofNat_add_ofNat,
            hi.rdi]
          simp only [expandSrc] at src ⊢
          rw [src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega_using [])]
          refine congrArg (fun b => BitVec.getLsbD b _) (hi.frame _ fun r hr hc => ?_)
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.sep _ (Offset.contains_base _ (by omega_using []) (by omega_using []))
            (Region.sub_prefix (by omega_using [hq]) _ hc)
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he]) (by omega_using [hq, hiq]) (by omega_using [hq])) (by decide)]
          exact hi.words i (by omega_using [hiq, he]) p hp64

theorem schedule_eq (s₀ t : State) (hi : ExpInv s₀ 13 t) :
    Spec.Idea.scheduleAt t.mem (s₀.gpr .rsi) = Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (s₀.gpr .rdi)) := by
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega_using [hn]) _ (by omega_using [hb]), expandKey_getLsbD _ hn hb,
    show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega_using [hb], show (16 * (n % 4) + b) % 16 = b by omega_using [hb]]

/-- `vg_idea_expand_key` on x86-64. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 16⟩
    let sched : Region := ⟨s.gpr .rsi, 104⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched] ∧ key.Disjoint sched ∧ ret.Disjoint sched
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .rsi) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (s.gpr .rdi))
  pub := PublicRegs [.rdi, .rsi]

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨hrd, hwr, hsep, hret⟩ := hs
  obtain ⟨t, ht, hi⟩ := words_run s ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩ 13 (by decide)
  obtain ⟨tr, s', he, hi⟩ : WP isa expandKey s (ExpInv s 13) := WP.of_runBlock ⟨t, ht, hi⟩
  refine ⟨tr, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, schedule_eq s s' hi⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hi.regs _ (by decide)
  · exact hi.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hret) (by decide)

def expandSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem publicRegs_two (s₁ s₂ : State) : PublicRegs [.rdi, .rsi] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi := by
  simp [PublicRegs]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) := by
  refine Verified.of_correct expand_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi,
    argRegs, expandContract, publicRegs_two] [expandSat] using expandSat

end VG.Proof.Idea.X86_64

end

end

/-! ### `Idea.X86_64.Invert`, which only this module used -/

section

/-!
# IDEA decryption subkeys on x86-64

Each decryption subkey is a copy, the negation or the inverse of an
encryption subkey (`invertKey_getD`, `Impl.Idea.invOp`), computed into
`rdx` (`invWord_ok`; the inverse by a loop of fifteen steps of
`t := (t ⊙ t) ⊙ a`, `invLoop_ok`), placed in its 16 bits of `r10`
(`invPlace`), and stored a quadword at a time (`invQuad_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64 VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.rax, .rcx, .rdx, .r8, .r9, .r11]

theorem loadKey_run (z : Spec.Idea.Schedule) (r : Reg) {k : Nat} (hk : k < 52) (t : State)
    (hz : KeyOk z t) :
    ∃ t', runBlock isa (loadKey r k) t = some t' ∧ (t'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] t t' := by
  unfold loadKey
  split
  · rename_i h
    have k₁ := hz.low k h
    refine ⟨t.setReg r (t.mem.readW (t.ea (at_ .rdi (2 * k))) 64), ?_, ?_, ?_⟩
    · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, isa, k₁.1,
        ↓reduceIte, Option.map_some]
    · rw [RegUpd.gpr_setReg_self, k₁.2]
    · refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
      simp only [List.mem_singleton] at hq
      exact RegUpd.gpr_setReg_of_ne _ _ hq
  · rename_i h
    have k₁ := hz.low 48 (by decide)
    simp only [Nat.reduceMul] at k₁
    have l := hz.last (k - 48) (by omega_using [hk])
    rw [show 48 + (k - 48) = k by omega_using [h]] at l
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc, State.load64, isa,
      k₁.1, ↓reduceIte, Option.map_some, RegUpd.gpr_setReg_self, show 1 ≤ 16 * (k - 48) by omega_using [h],
      show 16 * (k - 48) ≤ 63 by omega_using [hk], and_self,
      Option.some.injEq, exists_eq_left', l, true_and]
    refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
    simp only [List.mem_singleton] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq, ite_false]

theorem invStep_run (t : State) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .r9 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .r9).setWidth 16) ((t.gpr .r9).setWidth 16))
        ((t.gpr .r8).setWidth 16)).setWidth 64 ∧
      t'.gpr .rcx = t.gpr .rcx - 1 ∧ t'.zf = some (t.gpr .rcx - 1 == 0) ∧
      Keep [.rax, .rcx, .rdx, .r9] t t' := by
  have h₁ : runBlock isa [.mov .rax (.reg .r9), .mov .rdx (.reg .r9)] t =
      some ((t.setReg .rax (t.gpr .r9)).setReg .rdx (t.gpr .r9)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run ((t.setReg .rax (t.gpr .r9)).setReg .rdx (t.gpr .r9))
  have h₃ : runBlock isa [.mov .rax (.reg .rdx), .mov .rdx (.reg .r8)] t₂ =
      some ((t₂.setReg .rax (t₂.gpr .rdx)).setReg .rdx (t₂.gpr .r8)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
  obtain ⟨t₄, h₄, v₄, e₄⟩ := mul_run ((t₂.setReg .rax (t₂.gpr .rdx)).setReg .rdx (t₂.gpr .r8))
  obtain ⟨t₅, h₅, r9₅, rcx₅, zf₅, e₅⟩ : ∃ t₅, runBlock isa [.mov .r9 (.reg .rdx), .alu .sub .rcx (.imm 1)] t₄ =
      some t₅ ∧ t₅.gpr .r9 = t₄.gpr .rdx ∧ t₅.gpr .rcx = t₄.gpr .rcx - 1 ∧
      t₅.zf = some (t₄.gpr .rcx - 1 == 0) ∧ Keep [.rcx, .r9] t₄ t₅ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
      Option.map_some, Option.bind_some, signExtend_one, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.zf_setReg, RegUpd.zf_arithFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq,
      exists_eq_left', true_and]
    refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]
  have r8₂ : t₂.gpr .r8 = t.gpr .r8 := by
    rw [e₂.reg .r8 (by decide)]; rfl
  have rcx₄ : t₄.gpr .rcx = t.gpr .rcx := by
    rw [e₄.reg .rcx (by decide)]
    show t₂.gpr .rcx = _
    rw [e₂.reg .rcx (by decide)]; rfl
  refine ⟨t₅, run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅, ?_, ?_, ?_, ?_⟩
  · rw [r9₅, v₄, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_self, v₂, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_self, setWidth_setWidth16, r8₂]
  · rw [rcx₅, rcx₄]
  · rw [zf₅, rcx₄]
  · refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [e₅.reg q (by simp [hq.2.1, hq.2.2.2]), e₄.reg q (by simp [hq.1, hq.2.2.1]),
        RegUpd.gpr_setReg_of_ne _ _ hq.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hq.1,
        e₂.reg q (by simp [hq.1, hq.2.2.1]), RegUpd.gpr_setReg_of_ne _ _ hq.2.2.1,
        RegUpd.gpr_setReg_of_ne _ _ hq.1]
    · rw [e₅.mem, e₄.mem]; exact e₂.mem
    · rw [e₅.rd, e₄.rd]; exact e₂.rd
    · rw [e₅.wr, e₄.wr]; exact e₂.wr

/-- `c` steps remain: `r9` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  rcx : t.gpr .rcx = BitVec.ofNat 64 c
  r8 : (t.gpr .r8).setWidth 16 = a
  r9 : (t.gpr .r9).setWidth 16 = chain a (15 - c)
  keep : Keep [.rax, .rcx, .rdx, .r9] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .r9 = (Spec.Idea.inv a).setWidth 64 ∧ Keep [.rax, .rcx, .rdx, .r9] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', r9', rcx', zf', e'⟩ := invStep_run t
  refine WP.of_runBlock ⟨t', h', ?_⟩
  have hv : t'.gpr .r9 = (chain a (15 - c + 1)).setWidth 64 := by
    rw [r9', hi.r9, hi.r8]; rfl
  have hc : t.gpr .rcx - 1 = BitVec.ofNat 64 (c - 1) := by
    rw [hi.rcx]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_arith
  have keep' : Keep [.rax, .rcx, .rdx, .r9] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨?_, ?_, keep'⟩
    · simp only [eval, zf', hc]; rfl
    · rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨?_, c - 1, by omega_arith, by omega_arith, by omega_using [this], rcx'.trans hc, ?_, ?_, keep'⟩
    · simp only [eval, zf', hc, Option.map_some, Option.some.injEq]
      have h : (BitVec.ofNat 64 (c - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega_arith
      rw [h]; rfl
    · rw [e'.reg .r8 (by decide)]; exact hi.r8
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega_arith]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .rdx = ((Spec.Idea.invertKey z).getD n 0).setWidth 64 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .rdx hk t hz
    refine WP.of_runBlock ⟨(arithFlags t₁ (t₁.gpr .rdx &&& 65535) false false).setReg .rdx
      (t₁.gpr .rdx &&& 65535), run_append h₁ (by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
          Option.bind_some, signExtend_mask]), ?_, ?_⟩
    · rw [RegUpd.gpr_setReg_self, mask_setWidth, v₁]; rfl
    · refine (e₁.mono (by decide)).trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩
      rw [RegUpd.gpr_setReg_of_ne _ _ (by intro h; subst h; exact hq (by decide))]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .r11 hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ : ∃ t₂, runBlock isa [.mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .r11),
        .alu .and .rdx (.imm 0xffff)] t₁ = some t₂ ∧
        t₂.gpr .rdx = (0 - t₁.gpr .r11) &&& 65535 ∧ Keep [.rdx] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, isa,
        Option.map_some, Option.bind_some, signExtend_mask, State.setReg32, RegUpd.gpr_setReg,
        reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
      refine ⟨by rfl, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
      simp only [List.mem_singleton] at hq
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, ?_⟩
    · rw [v₂, neg_mask, v₁]; rfl
    · exact (e₁.mono (by decide)).trans (e₂.mono (by decide))
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .r8 hk t hz
    obtain ⟨t₂, h₂, r8₂, r9₂, rcx₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r9 (.reg .r8), .mov32 .rcx (.imm 15)] t₁ =
        some t₂ ∧ t₂.gpr .r8 = t₁.gpr .r8 ∧ t₂.gpr .r9 = t₁.gpr .r8 ∧ t₂.gpr .rcx = 15 ∧
        Keep [.r9, .rcx] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, isa,
        Option.map_some, State.setReg32, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte,
        Option.some.injEq, exists_eq_left', true_and]
      refine ⟨by rfl, keep_reg_of (fun q hq => ?_) rfl rfl rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [RegUpd.gpr_setReg, hq.1, hq.2, ite_false]
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ 15 t₂ ⟨by decide, by decide, rcx₂, by rw [r8₂, v₁],
      by rw [r9₂, v₁]; rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩) fun t₃ ⟨r9₃, e₃⟩ => ?_
    refine WP.of_runBlock ⟨t₃.setReg .rdx (t₃.gpr .r9), by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some], ?_, ?_⟩
    · rw [RegUpd.gpr_setReg_self, r9₃]; rfl
    · refine (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
        ⟨fun q hq => ?_, rfl, rfl, rfl⟩))
      exact RegUpd.gpr_setReg_of_ne _ _ (by intro h; subst h; exact hq (by decide))

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `r10` holds the first `i` decryption subkeys of quadword `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 64, (t.gpr .r10).getLsbD p =
    if p < 16 * i then (dk z (4 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_run (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 4) (t : State)
    (hrdx : t.gpr .rdx = (dk z (4 * q + i)).setWidth 64) (hacc : i = 0 ∨ Acc z q i t) :
    ∃ t', runBlock isa (invPlace (4 * q + i)) t = some t' ∧ Acc z q (i + 1) t' ∧
      Keep [.rdx, .r10] t t' := by
  unfold invPlace
  split
  · rename_i h
    have hi0 : i = 0 := by omega_using [hi, h]
    subst hi0
    refine ⟨t.setReg .r10 (t.gpr .rdx), by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some], ?_, ?_⟩
    · intro p hp
      rw [RegUpd.gpr_setReg_self, hrdx, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and,
        Nat.add_zero]
      by_cases hp16 : p < 16
      · rw [ite_eq_left (by omega_using [hp16]), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
      · rw [ite_eq_right (by omega_using [hp16])]; exact BitVec.getLsbD_of_ge _ _ (by omega_using [hp16])
    · refine keep_reg_of (fun r hr => ?_) rfl rfl rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact RegUpd.gpr_setReg_of_ne _ _ hr.2
  · rename_i h
    have hi0 : i ≠ 0 := by omega_using [h]
    have hacc' := hacc.resolve_left hi0
    have hm : (4 * q + i) % 4 = i := by omega_using [hi]
    rw [hm]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, isa,
      Option.bind_some, show 1 ≤ 16 * i by omega_using [h], show 16 * i ≤ 63 by omega_using [hi], and_self, ↓reduceIte,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, keep_reg_of (fun r hr => ?_) rfl rfl rfl⟩
    · rw [RegUpd.gpr_setReg_self, BitVec.getLsbD_or, hacc' p hp, hrdx, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth]
      by_cases h1 : p < 16 * i
      · simp [h1, show p < 16 * (i + 1) by omega_using [h1]]
      · by_cases h2 : p < 16 * (i + 1)
        · simp [h1, h2, hp, show p - 16 * i < 64 by omega_using [hp], show 4 * q + p / 16 = 4 * q + i by omega_using [h1, h2],
            show p % 16 = p - 16 * i by omega_using [h1, h2]]
        · simp only [h1, h2, ↓reduceIte, Bool.false_or]
          rw [BitVec.getLsbD_of_ge (dk z (4 * q + i)) _ (by omega_using [h2])]
          simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- The registers computing a quadword of decryption subkeys writes. -/
abbrev quadWrites : List Reg := [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11]

theorem quadWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 13) (hi : i < 4) (t : State)
    (hz : KeyOk z t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → Keep quadWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega_using [hq, hi]) t hz) fun t₁ ⟨v₁, e₁⟩ => ?_
  apply WP.seq
  have hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.reg .r10 (by decide)]; exact h p hp
  obtain ⟨t₂, h₂, a₂, e₂⟩ := invPlace_run z q i hi t₁ v₁ hacc₁
  exact WP.of_runBlock ⟨t₂, h₂, hrest t₂ a₂ ((e₁.mono (by decide)).trans (e₂.mono (by decide)))⟩

/-- What `vg_idea_invert_key` needs of its state: the encryption subkeys (104
bytes at `rdi`) readable, the decryption subkeys (104 bytes at `rsi`)
writable, apart. -/
structure InvPre (s : State) : Prop where
  sched : ⟨s.gpr .rdi, 104⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .rsi, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .rdi, 104⟩ : Region).Disjoint ⟨s.gpr .rsi, 104⟩

/-- After `q` quadwords of decryption subkeys. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = s₀.gpr .rdi
  rsi : t.gpr .rsi = s₀.gpr .rsi
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  regs : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .rsi, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (dk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) (4 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (hi : QInv s₀ q t) (hq : q ≤ 13) :
    KeyOk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) t := by
  have h := keyOk_of t (by rw [hi.rdi, hi.rd, hi.wr]; exact hp.sched)
  rwa [hi.rdi, scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega_using [hq]))) (by decide))] at h

theorem invQuad_ok (s₀ : State) (hp : InvPre s₀) (q : Nat) (hq : q < 13) (t : State)
    (hi : QInv s₀ q t) : WP isa (invQuad q) t (QInv s₀ (q + 1)) := by
  have hz := hi.keyOk hp (by omega_using [hq])
  simp only [invQuad, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons, List.foldr_nil]
  refine quadWord_ok _ q 0 hq (by decide) t hz (Or.inl rfl) fun t₁ a₁ e₁ => ?_
  refine quadWord_ok _ q 1 hq (by decide) t₁ (hz.keep e₁ (by decide)) (Or.inr a₁) fun t₂ a₂ e₂ => ?_
  refine quadWord_ok _ q 2 hq (by decide) t₂ ((hz.keep e₁ (by decide)).keep e₂ (by decide)) (Or.inr a₂)
    fun t₃ a₃ e₃ => ?_
  refine quadWord_ok _ q 3 hq (by decide) t₃
    (((hz.keep e₁ (by decide)).keep e₂ (by decide)).keep e₃ (by decide)) (Or.inr a₃)
    fun t₄ a₄ e₄ => ?_
  have e := e₁.trans (e₂.trans (e₃.trans e₄))
  have hw : InRegions t₄.wr (t₄.ea (at_ .rsi (8 * q))) 8 := by
    rw [ea_at, e.reg .rsi (by decide), e.wr, hi.wr, hi.rsi]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  have ea₄ : t₄.ea (at_ .rsi (8 * q)) = s₀.gpr .rsi + BitVec.ofNat 64 (8 * q) := by
    rw [ea_at, e.reg .rsi (by decide), hi.rsi]
  refine WP.of_runBlock ⟨{ t₄ with mem := t₄.mem.writeW (t₄.ea (at_ .rsi (8 * q))) (t₄.gpr .r10) },
    by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, isa, hw, ↓reduceIte],
    ?_⟩
  have sub : ∀ r ∈ [Reg.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15], r ∉ quadWrites := by decide
  refine ⟨(e.reg .rdi (by decide)).trans hi.rdi, (e.reg .rsi (by decide)).trans hi.rsi,
    e.rd.trans hi.rd, e.wr.trans hi.wr, fun r hr => (e.reg r (sub r hr)).trans (hi.regs r hr), ?_, ?_⟩
  · show Frame _ s₀.mem (t₄.mem.writeW _ _)
    rw [e.mem, ea₄]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hq]))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_using [])
  · intro i hiq p hp64
    show ((t₄.mem.writeW _ _).readW _ 64).getLsbD p = _
    rw [e.mem, ea₄]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self64, a₄ p hp64, ite_eq_left (by omega_using [hp64])]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he]) (by omega_using [hq, hiq]) (by omega_using [hq])) (by decide)]
      exact hi.words i (by omega_using [hiq, he]) p hp64

/-- Quadwords `q … q + n - 1`. -/
def quads (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invQuad q) rest) (.block [])

theorem quads_ok (s₀ : State) (hp : InvPre s₀) :
    ∀ n q, q + n = 13 → ∀ t, QInv s₀ q t → WP isa (quads q n) t (QInv s₀ 13)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [quads, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invQuad_ok s₀ hp q (by omega_using [h]) t hi) fun t₁ h₁ =>
      quads_ok s₀ hp n (q + 1) (by omega_using [h]) t₁ h₁

theorem invertKey_eq : invertKey = quads 0 13 := rfl

/-- `vg_idea_invert_key` on x86-64. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 104⟩
    let out : Region := ⟨s.gpr .rsi, 104⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [out] ∧ sched.Disjoint out ∧ ret.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .rsi) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (s.gpr .rdi))
  pub := PublicRegs [.rdi, .rsi]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨hrd, hwr, hsep, hret⟩ := hs
  have hp : InvPre s := ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩
  obtain ⟨tr, s', he, hi⟩ := quads_ok s hp 13 0 rfl s ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl,
    Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩
  rw [← invertKey_eq] at he
  refine ⟨tr, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hi.regs _ (by decide)
  · exact hi.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hret) (by decide)
  · show Spec.Idea.scheduleAt s'.mem (s.gpr .rsi) = _
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega_using [hn]) _ (by omega_using [hb]),
      show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega_using [hb],
      show (16 * (n % 4) + b) % 16 = b by omega_using [hb]]

def invertSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩]

theorem invertKey_verified : Verified target invertKey (Spec.Idea.invertKeyContract abi) := by
  refine Verified.of_correct invert_correct (invertKey_constantTime _) ?_
  sig_implies [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, abi,
    argRegs, invertContract, publicRegs_two] [invertSat] using invertSat

end VG.Proof.Idea.X86_64

end

end

/-!
# IDEA on x86-64, without secret residue

Key expansion and inversion and the ECB, CBC, CFB64 and OFB functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
schedule (`scheduleAt_congr`), the blocks or bytes of the data and the
chaining value.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64.Scrub

open VG.Spec.Idea VG.X86_64 VG.X86_64.Scrub VG.Proof.Idea.ScrubLocal

/-! ## Postconditions -/
theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.le_refl _

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm


theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract X86_64.abi stack) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ sc = _
    rw [scheduleAt_of hb.2]
    exact h

theorem invertKeyOut (stack : Nat) : PostOut (invertKeyContract X86_64.abi stack) (invertKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [invertKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ inv = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (stack : Nat) : PostOut (ecbContract X86_64.abi stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show blocksAt m₂ dt _ = _
    rw [blocksAt_of hb.2 (len_le ln 8)]
    exact h

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86_64.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86_64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

/-! ## The registrations -/

/-- `vg_idea_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.Idea.X86_64.expandKey

def expandKeyKs : List Nat := keep_for% Spec.Idea.expandKeyApi.sig 0 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.expandKeyApi.sig 0 []) expandKeyCode
      h).any (RScrub.resOkB · 0 expandKeyKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_expand_key`. -/
def expandKeyReg : Registration Spec.Idea.expandKeyApi X86_64.target :=
  scrubOf {
    code := expandKeyCode
    stack := 0
    verified := Proof.Idea.X86_64.expandKey_verified } .sse false [.rcx, .rdx] (expandKeyOut _) [] (pubOk_nil _) ⟨expandKeyKs, expandKeyOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_invert_key`'s code. -/
abbrev invertKeyCode : Prog isa :=
  Impl.Idea.X86_64.invertKey

def invertKeyKs : List Nat := keep_for% Spec.Idea.invertKeyApi.sig 0 invertKeyCode []

theorem invertKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.invertKeyApi.sig 0 []) invertKeyCode
      h).any (RScrub.resOkB · 0 invertKeyKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of invertKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_invert_key`. -/
def invertKeyReg : Registration Spec.Idea.invertKeyApi X86_64.target :=
  scrubOf {
    code := invertKeyCode
    stack := 0
    verified := Proof.Idea.X86_64.invertKey_verified } .sse false [.rcx, .rdx, .r8, .r9, .r10, .r11] (invertKeyOut _) [] (pubOk_nil _) ⟨invertKeyKs, invertKeyOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_ecb`'s code. -/
abbrev ecbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 24 .rcx Impl.Idea.X86_64.ecb

def ecbKs : List Nat := keep_for% Spec.Idea.ecbApi.sig 24 ecbCode []

theorem ecbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.ecbApi.sig 24 []) ecbCode
      h).any (RScrub.resOkB · 24 ecbKs (Impl.Scrub.X86_64.chunks 24)) = true :=
  RScrub.Analysed.ok_of ecbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_ecb`. -/
def ecbReg : Registration Spec.Idea.ecbApi X86_64.target :=
  scrubOf {
    code := ecbCode
    stack := 24
    verified := Proof.Idea.X86_64.ecb_framed } .sse false [.rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] (ecbOut _) [] (pubOk_nil _) ⟨ecbKs, ecbOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.Idea.cbcEncryptChainedApi.sig 184 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cbcEncryptChainedApi.sig 184 []) cbcEncryptCode
      h).any (RScrub.resOkB · 184 cbcEncryptKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.Idea.cbcEncryptChainedApi X86_64.target :=
  scrubOf {
    code := cbcEncryptCode
    stack := 184
    verified := Proof.Idea.X86_64.cbcEncryptChained_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cbcEncryptOut _) [] (pubOk_nil _) ⟨cbcEncryptKs, cbcEncryptOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcDecryptChained

def cbcDecryptKs : List Nat := keep_for% Spec.Idea.cbcDecryptChainedApi.sig 184 cbcDecryptCode []

theorem cbcDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cbcDecryptChainedApi.sig 184 []) cbcDecryptCode
      h).any (RScrub.resOkB · 184 cbcDecryptKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cbcDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptReg : Registration Spec.Idea.cbcDecryptChainedApi X86_64.target :=
  scrubOf {
    code := cbcDecryptCode
    stack := 184
    verified := Proof.Idea.X86_64.cbcDecryptChained_framed } .sse false [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cbcDecryptOut _) [] (pubOk_nil _) ⟨cbcDecryptKs, cbcDecryptOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cfb64_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.Idea.cfbEncryptApi.sig 184 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cfbEncryptApi.sig 184 []) cfbEncryptCode
      h).any (RScrub.resOkB · 184 cfbEncryptKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncryptReg : Registration Spec.Idea.cfbEncryptApi X86_64.target :=
  scrubOf {
    code := cfbEncryptCode
    stack := 184
    verified := Proof.Idea.X86_64.cfbEncrypt_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cfbEncryptOut _) [] (pubOk_nil _) ⟨cfbEncryptKs, cfbEncryptOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cfb64_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecrypt

def cfbDecryptKs : List Nat := keep_for% Spec.Idea.cfbDecryptApi.sig 184 cfbDecryptCode []

theorem cfbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cfbDecryptApi.sig 184 []) cfbDecryptCode
      h).any (RScrub.resOkB · 184 cfbDecryptKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cfbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecryptReg : Registration Spec.Idea.cfbDecryptApi X86_64.target :=
  scrubOf {
    code := cfbDecryptCode
    stack := 184
    verified := Proof.Idea.X86_64.cfbDecrypt_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cfbDecryptOut _) [] (pubOk_nil _) ⟨cfbDecryptKs, cfbDecryptOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cfb64_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.Idea.cfbEncryptFinalApi.sig 184 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cfbEncryptFinalApi.sig 184 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 184 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Idea.cfbEncryptFinalApi X86_64.target :=
  scrubOf {
    code := cfbEncryptFinalCode
    stack := 184
    verified := Proof.Idea.X86_64.cfbEncryptFinal_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cfbEncryptFinalOut _) [] (pubOk_nil _) ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_cfb64_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.Idea.cfbDecryptFinalApi.sig 184 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.cfbDecryptFinalApi.sig 184 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 184 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Idea.cfbDecryptFinalApi X86_64.target :=
  scrubOf {
    code := cfbDecryptFinalCode
    stack := 184
    verified := Proof.Idea.X86_64.cfbDecryptFinal_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (cfbDecryptFinalOut _) [] (pubOk_nil _) ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.Idea.ofbApi.sig 184 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.ofbApi.sig 184 []) ofbCode
      h).any (RScrub.resOkB · 184 ofbKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_ofb`. -/
def ofbReg : Registration Spec.Idea.ofbApi X86_64.target :=
  scrubOf {
    code := ofbCode
    stack := 184
    verified := Proof.Idea.X86_64.ofb_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (ofbOut _) [] (pubOk_nil _) ⟨ofbKs, ofbOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

/-- `vg_idea_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.Idea.ofbFinalApi.sig 184 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Idea.ofbFinalApi.sig 184 []) ofbFinalCode
      h).any (RScrub.resOkB · 184 ofbFinalKs (Impl.Scrub.X86_64.chunks 184)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_idea_ofb_final`. -/
def ofbFinalReg : Registration Spec.Idea.ofbFinalApi X86_64.target :=
  scrubOf {
    code := ofbFinalCode
    stack := 184
    verified := Proof.Idea.X86_64.ofbFinal_framed } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (ofbFinalOut _) [] (pubOk_nil _) ⟨ofbFinalKs, ofbFinalOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

end VG.Proof.Idea.X86_64.Scrub
