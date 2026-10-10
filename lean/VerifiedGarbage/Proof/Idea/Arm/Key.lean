import VerifiedGarbage.Proof.Idea.Arm.ConstantTime
import VerifiedGarbage.Proof.Idea.Arm.Mul
import VerifiedGarbage.Proof.Idea.KeyBits32
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA key expansion on ARMv7

Each schedule word (`expandWord w`, two subkeys) is a fixed bit permutation
of the key's four 32-bit words, checked by evaluation over the lane domain
(`expand_check`, `Straight.linear_ok`): bit `p` of `r12` is the key bit
`expandSrc32 w p`. The words are stored in turn (`words_run`), and every
subkey bit is then the key bit `Spec.Idea.expandKey` takes
(`expandKey_getLsbD`).
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Idea.Arm VG.Impl.Idea

/-- The key's four words at `r0`, no slots. -/
def eCfg : Cfg := { base := .r1, slots := 0, ext := .r0, exts := 4 }

/-- Bit `p` of word `w`: atom `32 j + t`, bit `t` of key word `j`. -/
def eG (w p : Nat) : List Nat := [32 * (expandSrc32 w p).1 + (expandSrc32 w p).2]

theorem expand_check : ∀ w < 26,
    check (lanes 32 7) eCfg (linExt 0) (expandWord w) (linEnv []) (linPost 7 [(.r12, eG w)]) = true := by
  lit_decide

/-- The registers `expandWord` keeps. -/
abbrev expandKept : List Reg :=
  [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem expand_kept : ∀ w < 26, ∀ r ∈ expandKept,
    ((expandWord w).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem expandWord_run (w : Nat) (hw : w < 26) (s : State)
    (hk : ∀ j < 4, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (expandWord w) s = some s' ∧
      (∀ p < 32, (s'.gpr .r12).getLsbD p =
        (s.mem.readW (wordAddr (s.gpr .r0) (expandSrc32 w p).1) 32).getLsbD (expandSrc32 w p).2) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r ∈ expandKept, s'.gpr r = s.gpr r) := by
  have hok : Ok eCfg s := ⟨fun k hk' => absurd hk' (by simp [eCfg]), fun k hk' => hk k hk',
    by simp only [eCfg, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (s.gpr .r1).isLt,
    fun k hk' => absurd hk' (by simp [eCfg])⟩
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok (expand_check w hw) hok
    (fun i => s.mem.readW (wordAddr (s.gpr .r0) i) 32)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 4 := hj
      refine ⟨by omega, ?_⟩
      simp only [Nat.zero_add]
      rfl)
  refine ⟨s', hs', fun p hp => ?_, hrd, hwr, hsp, ?_, fun r hr => hoth r (expand_kept w hw r hr)⟩
  · have src := keyLoc32_spec (keyBit_lt (2 * w + p / 16) (p % 16))
    rw [hout .r12 (eG w) (by simp) p hp]
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc32] using src.2.1)]
  · funext a
    exact hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, eCfg, Region.Contains]

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `r0`)
readable, the schedule (104 bytes at `r1`) writable, apart, neither
wrapping around. -/
structure ExpPre (s : State) : Prop where
  key : ⟨State.addr (s.gpr .r0), 16⟩ ∈ s.rd ++ s.wr
  sched : ⟨State.addr (s.gpr .r1), 104⟩ ∈ s.wr
  sep : (⟨State.addr (s.gpr .r0), 16⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 104⟩
  fit0 : (s.gpr .r0).toNat + 16 ≤ 2 ^ 32
  fit1 : (s.gpr .r1).toNat + 104 ≤ 2 ^ 32

/-- After `q` words: the schedule's first `q` words hold their key bits,
nothing else is written, and the pointers and other registers are kept. -/
structure ExpInv (s₀ : State) (q : Nat) (t : State) : Prop where
  r0 : t.gpr .r0 = s₀.gpr .r0
  r1 : t.gpr .r1 = s₀.gpr .r1
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  regs : ∀ r ∈ expandKept, t.gpr r = s₀.gpr r
  frame : Frame [⟨State.addr (s₀.gpr .r1), 4 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 32,
    (t.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i)) 32).getLsbD p =
      (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (State.addr (s₀.gpr .r0)))).getLsbD
        (keyBit (2 * i + p / 16) (p % 16))

theorem words_run (s₀ : State) (hp : ExpPre s₀) : ∀ q ≤ 26, ∃ t,
    runBlock isa ((List.range q).flatMap fun w => expandWord w ++ ([.str .r12 .r1 (4 * w)] : List Instr)) s₀ =
      some t ∧ ExpInv s₀ q t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _,
      fun i hi => absurd hi (by omega)⟩⟩
  | q + 1, hq => by
    obtain ⟨t, ht, hi⟩ := words_run s₀ hp q (by omega)
    obtain ⟨t₁, h₁, bits₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := expandWord_run q (by omega) t (fun j hj => by
      rw [hi.rd, hi.wr, hi.r0, wordAddr, addr_add (by have := hp.fit0; omega)]
      exact ⟨_, hp.key, Offset.contains_base _ (by omega) (by omega)⟩)
    have r1₁ : t₁.gpr .r1 = s₀.gpr .r1 := (regs₁ .r1 (by simp)).trans hi.r1
    have hfit : (t₁.gpr .r1).toNat + 4 * q < 2 ^ 32 := by rw [r1₁]; have := hp.fit1; omega
    have hw : InRegions t₁.wr (State.addr (t₁.gpr .r1 + BitVec.ofNat 32 (4 * q))) 4 := by
      rw [addr_add hfit, r1₁, wr₁, hi.wr]
      exact ⟨_, hp.sched, Offset.contains_base _ (by omega) (by omega)⟩
    have h₂ : runBlock isa [.str .r12 .r1 (4 * q)] t₁ =
        some { t₁ with mem := t₁.mem.writeW (State.addr (t₁.gpr .r1 + BitVec.ofNat 32 (4 * q))) (t₁.gpr .r12) } := by
      rw [runBlock_cons, exec_str (by omega) hw, runStep_some, runBlock_nil]
    rw [addr_add hfit, r1₁] at h₂
    refine ⟨{ t₁ with mem := t₁.mem.writeW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * q)) (t₁.gpr .r12) }, ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append h₁ h₂)
    · refine ⟨(regs₁ .r0 (by simp)).trans hi.r0, r1₁, rd₁.trans hi.rd, wr₁.trans hi.wr,
        sp₁.trans hi.sp, fun r hr => (regs₁ r hr).trans (hi.regs r hr), ?_, ?_⟩
      · show Frame _ s₀.mem (t₁.mem.writeW _ _)
        rw [mem₁]
        refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
          (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega)
      · intro i hiq p hp32
        show ((t₁.mem.writeW _ _).readW _ 32).getLsbD p = _
        rw [mem₁]
        by_cases he : i = q
        · subst he
          rw [Mem.readW_writeW_self32, bits₁ p hp32]
          have src := keyLoc32_spec (keyBit_lt (2 * i + p / 16) (p % 16))
          rw [hi.r0, wordAddr, addr_add (by have := hp.fit0; simp only [expandSrc32] at src ⊢; omega),
            readW32_getLsbD _ _ (by simpa [expandSrc32] using src.2.1), Offset.add_ofNat_add_ofNat]
          simp only [expandSrc32] at src ⊢
          rw [src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega)]
          refine congrArg (fun b => BitVec.getLsbD b _) (hi.frame _ fun r hr hc => ?_)
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.sep _ (Offset.contains_base _ (by omega) (by omega))
            (Region.sub_prefix (by omega) _ hc)
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact hi.words i (by omega) p hp32

theorem schedule_eq (s₀ t : State) (hi : ExpInv s₀ 26 t) :
    Spec.Idea.scheduleAt t.mem (State.addr (s₀.gpr .r1)) =
      Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (State.addr (s₀.gpr .r0))) := by
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD32 _ _ hn hb, hi.words (n / 2) (by omega) _ (by omega), expandKey_getLsbD _ hn hb,
    show 2 * (n / 2) + (16 * (n % 2) + b) / 16 = n by omega, show (16 * (n % 2) + b) % 16 = b by omega]

/-- `vg_idea_expand_key` on ARMv7. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sched : Region := ⟨State.addr (s.gpr .r1), 104⟩
    s.rd = [key] ∧ s.wr = [sched] ∧ key.Disjoint sched ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 104 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (State.addr (s.gpr .r0)))
  pub := PublicRegs [.r0, .r1]

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨hrd, hwr, hsep, fit0, fit1⟩ := hs
  obtain ⟨t, ht, hi⟩ := words_run s ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep, fit0, fit1⟩ 26
    (by decide)
  obtain ⟨tr, s', he, hi⟩ : WP isa expandKey s (ExpInv s 26) := WP.of_runBlock ⟨t, ht, hi⟩
  refine ⟨tr, s', he, ⟨fun r hr => hi.regs r ?_, hi.sp⟩, schedule_eq s s' hi⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def expandSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem publicRegs_two (s₁ s₂ : State) : PublicRegs [.r0, .r1] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 := by
  simp [PublicRegs]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) := by
  refine Verified.of_correct expand_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi,
    argRegs, reduceClassify, Loc.val, State.addr, expandContract, publicRegs_two] [expandSat] using expandSat

end VG.Proof.Idea.Arm
