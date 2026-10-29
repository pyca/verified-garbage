module

import VerifiedGarbage.Proof.Idea.KeyBits
public import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Idea.KeyLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Idea.PPC64LE
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-!
# IDEA key expansion on PPC64LE

Each schedule doubleword (`expandWord q`) is a fixed bit permutation of the
key's two doublewords, checked by evaluation over the lane domain
(`expand_check`, `StraightK.linear_ok`): bit `p` of `r10` is the key bit
`expandSrc q p`. The doublewords are stored in turn (`words_run`), and every
subkey bit is then the key bit `Spec.Idea.expandKey` takes
(`expandKey_getLsbD`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Idea.PPC64LE VG.Impl.Idea

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- Composing two runs. -/
theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

/-- The key's two doublewords at `r3`, no slots. -/
def eCfg : Cfg := { base := .r4, slots := 0, ext := .r3, exts := 2 }

/-- Bit `p` of doubleword `q`: atom `64 j + t`, bit `t` of key doubleword `j`. -/
def eG (q p : Nat) : List Nat := [64 * (expandSrc q p).1 + (expandSrc q p).2]

theorem expand_check : ∀ q < 13,
    check (lanes 64 7) eCfg (linExt 0) (expandWord q) (linEnv []) (linPost 7 [(.r10, eG q)]) = true := by
  lit_decide

/-- `expandWord` keeps the pointers. -/
theorem expand_kept : ∀ q < 13, ∀ r ∈ [Reg.r3, .r4],
    ((expandWord q).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem expandWord_run (q : Nat) (hq : q < 13) (s : State)
    (hk : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (expandWord q) s = some s' ∧
      (∀ p < 64, (s'.gpr .r10).getLsbD p =
        (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * (expandSrc q p).1)) 64).getLsbD
          (expandSrc q p).2) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r ∈ [Reg.r3, .r4], s'.gpr r = s.gpr r) := by
  have hok : Ok eCfg s := ⟨fun k hk' => absurd hk' (by simp [eCfg]), fun k hk' => hk k hk',
    by decide, fun k hk' => absurd hk' (by simp [eCfg])⟩
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok (expand_check q hq) hok
    (fun i => s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * i)) 64)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 2 := hj
      refine ⟨by omega_arith, ?_⟩
      simp only [Nat.zero_add, wordAddr]
      rfl)
  refine ⟨s', hs', fun p hp => ?_, hrd, hwr, ?_, fun r hr => hoth r (expand_kept q hq r hr)⟩
  · have src := keyLoc_spec (keyBit_lt (4 * q + p / 16) (p % 16))
    rw [hout .r10 (eG q) (by simp) p hp]
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc] using src.2.1)]
  · funext a
    exact hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, eCfg, Region.Contains]

/-- After `q` doublewords: the schedule's first `q` doublewords hold their key
bits, nothing else is written, and the pointers are kept. -/
structure ExpInv (s₀ : State) (q : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = s₀.gpr .r3
  r4 : t.gpr .r4 = s₀.gpr .r4
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .r4, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .r4 + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .r3))).getLsbD (keyBit (4 * i + p / 16) (p % 16))

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `r3`)
readable, the schedule (104 bytes at `r4`) writable, apart. -/
structure ExpPre (s : State) : Prop where
  key : ⟨s.gpr .r3, 16⟩ ∈ s.rd ++ s.wr
  sched : ⟨s.gpr .r4, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r4, 104⟩

theorem words_run (s₀ : State) (hp : ExpPre s₀) : ∀ q ≤ 13, ∃ t,
    runBlock isa ((List.range q).flatMap fun q => expandWord q ++ ([.store .d .r10 .r4 (8 * q)] : List Instr)) s₀ =
      some t ∧ ExpInv s₀ q t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun i hi => absurd hi (by omega_arith)⟩⟩
  | q + 1, hq => by
    obtain ⟨t, ht, hi⟩ := words_run s₀ hp q (by omega_arith)
    obtain ⟨t₁, h₁, bits₁, rd₁, wr₁, mem₁, regs₁⟩ := expandWord_run q (by omega_arith) t (fun j hj => by
      rw [hi.rd, hi.wr, hi.r3]
      exact ⟨_, hp.key, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    have hw : InRegions t₁.wr (t₁.gpr .r4 + BitVec.ofNat 64 (8 * q)) 8 := by
      rw [regs₁ .r4 (by simp), wr₁, hi.wr, hi.r4]
      exact ⟨_, hp.sched, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    have h₂ : runBlock isa [.store .d .r10 .r4 (8 * q)] t₁ =
        some { t₁ with mem := t₁.mem.writeW (t₁.gpr .r4 + BitVec.ofNat 64 (8 * q)) (t₁.gpr .r10) } := by
      rw [runBlock_cons, exec_store_d (by decide) ⟨by omega_arith, by omega_arith⟩ hw, runStep_some, runBlock_nil]
    have ea₁ : t₁.gpr .r4 + BitVec.ofNat 64 (8 * q) = s₀.gpr .r4 + BitVec.ofNat 64 (8 * q) := by
      rw [regs₁ .r4 (by simp), hi.r4]
    refine ⟨{ t₁ with mem := t₁.mem.writeW (t₁.gpr .r4 + BitVec.ofNat 64 (8 * q)) (t₁.gpr .r10) }, ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append h₁ h₂)
    · refine ⟨(regs₁ .r3 (by simp)).trans hi.r3, (regs₁ .r4 (by simp)).trans hi.r4,
        rd₁.trans hi.rd, wr₁.trans hi.wr, ?_, ?_⟩
      · show Frame _ s₀.mem (t₁.mem.writeW _ _)
        rw [mem₁, ea₁]
        refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
          (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_arith)
      · intro i hiq p hp64
        show ((t₁.mem.writeW _ _).readW _ 64).getLsbD p = _
        rw [mem₁, ea₁]
        by_cases he : i = q
        · subst he
          rw [Mem.readW_writeW_self64, bits₁ p hp64]
          have src := keyLoc_spec (keyBit_lt (4 * i + p / 16) (p % 16))
          rw [readW_getLsbD _ _ (by simpa [expandSrc] using src.2.1), Offset.add_ofNat_add_ofNat,
            hi.r3]
          simp only [expandSrc] at src ⊢
          rw [src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega_arith)]
          refine congrArg (fun b => BitVec.getLsbD b _) (hi.frame _ fun r hr hc => ?_)
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.sep _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
            (Region.sub_prefix (by omega_arith) _ hc)
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
          exact hi.words i (by omega_arith) p hp64

theorem schedule_eq (s₀ t : State) (hi : ExpInv s₀ 13 t) :
    Spec.Idea.scheduleAt t.mem (s₀.gpr .r4) = Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (s₀.gpr .r3)) := by
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega_arith) _ (by omega_arith), expandKey_getLsbD _ hn hb,
    show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega_arith, show (16 * (n % 4) + b) % 16 = b by omega_arith]

/-- `vg_idea_expand_key` on PPC64LE. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let sched : Region := ⟨s.gpr .r4, 104⟩
    s.rd = [key] ∧ s.wr = [sched] ∧ key.Disjoint sched
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .r4) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨hrd, hwr, hsep⟩ := hs
  obtain ⟨t, ht, hi⟩ := words_run s ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩ 13 (by decide)
  obtain ⟨tr, s', he, hi, hk⟩ : WP isa expandKey s fun s' => ExpInv s 13 s' ∧ Keep [.r10, .r11, .r12] s s' :=
    WP.keep _ (WP.of_runBlock ⟨t, ht, hi⟩) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), schedule_eq s s' hi⟩

theorem expand_ct : ConstantTime isa expandContract.pre expandContract.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

def expandSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) :=
  Verified.of_correct expand_correct expand_ct (by
    sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi,
      argRegs, expandContract] [expandSat] using expandSat)

end VG.Proof.Idea.PPC64LE
