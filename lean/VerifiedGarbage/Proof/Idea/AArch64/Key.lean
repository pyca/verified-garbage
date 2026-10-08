import VerifiedGarbage.Proof.Idea.AArch64.Ecb
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Framework.AArch64.Linear

/-!
# IDEA key expansion on AArch64

Each schedule quadword (`expandWord q`) is a fixed bit permutation of the
key's two quadwords, checked by evaluation over the lane domain
(`expand_check`, `Straight.linear_ok`): bit `p` of `x11` is the key bit
`expandSrc q p`. The quadwords are stored in turn (`words_run`), and every
subkey bit is then the key bit `Spec.Idea.expandKey` takes
(`expandKey_getLsbD`).
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Idea.AArch64 VG.Impl.Idea

/-- The key's two quadwords at `x0`, no slots. -/
def eCfg : Cfg := { base := .x1, slots := 0, ext := .x0, exts := 2 }

/-- Bit `p` of quadword `q`: atom `64 j + t`, bit `t` of key quadword `j`. -/
def eG (q p : Nat) : List Nat := [64 * (expandSrc q p).1 + (expandSrc q p).2]

theorem expand_check : ∀ q < 13,
    check (lanes 64 7) eCfg (linExt 0) (expandWord q) (linEnv []) (linPost 7 [(.x11, eG q)]) = true := by
  decide +kernel

/-- The registers `expandWord` keeps. -/
abbrev expandKept : List Reg :=
  [.x0, .x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem expand_kept : ∀ q < 13, ∀ r ∈ expandKept,
    ((expandWord q).all fun i => dstOf i != some r) = true := by
  decide +kernel

theorem expandWord_run (q : Nat) (hq : q < 13) (s : State)
    (hk : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (expandWord q) s = some s' ∧
      (∀ p < 64, (s'.gpr .x11).getLsbD p =
        (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (8 * (expandSrc q p).1)) 64).getLsbD
          (expandSrc q p).2) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r ∈ expandKept, s'.gpr r = s.gpr r) := by
  have hok : Ok eCfg s := ⟨fun k hk' => absurd hk' (by simp [eCfg]), fun k hk' => hk k hk',
    by decide, fun k hk' => absurd hk' (by simp [eCfg])⟩
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok (expand_check q hq) hok
    (fun i => s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 64)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 2 := hj
      refine ⟨by omega, ?_⟩
      simp only [Nat.zero_add, wordAddr]
      rfl)
  refine ⟨s', hs', fun p hp => ?_, hrd, hwr, hsp, ?_, fun r hr => hoth r (expand_kept q hq r hr)⟩
  · have src := keyLoc_spec (keyBit_lt (4 * q + p / 16) (p % 16))
    rw [hout .x11 (eG q) (by simp) p hp]
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc] using src.2.1)]
  · funext a
    exact hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, eCfg, Region.Contains]

/-- After `q` quadwords: the schedule's first `q` quadwords hold their key bits,
nothing else is written, and the pointers and other registers are kept. -/
structure ExpInv (s₀ : State) (q : Nat) (t : State) : Prop where
  x0 : t.gpr .x0 = s₀.gpr .x0
  x1 : t.gpr .x1 = s₀.gpr .x1
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  regs : ∀ r ∈ expandKept, t.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .x1, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .x1 + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .x0))).getLsbD (keyBit (4 * i + p / 16) (p % 16))

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `x0`)
readable, the schedule (104 bytes at `x1`) writable, apart. -/
structure ExpPre (s : State) : Prop where
  key : ⟨s.gpr .x0, 16⟩ ∈ s.rd ++ s.wr
  sched : ⟨s.gpr .x1, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .x0, 16⟩ : Region).Disjoint ⟨s.gpr .x1, 104⟩

theorem words_run (s₀ : State) (hp : ExpPre s₀) : ∀ q ≤ 13, ∃ t,
    runBlock isa ((List.range q).flatMap fun q => expandWord q ++ ([.str .x .x11 .x1 (8 * q)] : List Instr)) s₀ =
      some t ∧ ExpInv s₀ q t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _,
      fun i hi => absurd hi (by omega)⟩⟩
  | q + 1, hq => by
    obtain ⟨t, ht, hi⟩ := words_run s₀ hp q (by omega)
    obtain ⟨t₁, h₁, bits₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := expandWord_run q (by omega) t (fun j hj => by
      rw [hi.rd, hi.wr, hi.x0]
      exact ⟨_, hp.key, Offset.contains_base _ (by omega) (by omega)⟩)
    have x1₁ : t₁.gpr .x1 = s₀.gpr .x1 := (regs₁ .x1 (by simp)).trans hi.x1
    have hw : InRegions t₁.wr (t₁.gpr .x1 + BitVec.ofNat 64 (8 * q)) 8 := by
      rw [x1₁, wr₁, hi.wr]
      exact ⟨_, hp.sched, Offset.contains_base _ (by omega) (by omega)⟩
    have h₂ : runBlock isa [.str .x .x11 .x1 (8 * q)] t₁ =
        some { t₁ with mem := t₁.mem.writeW (t₁.gpr .x1 + BitVec.ofNat 64 (8 * q)) (t₁.gpr .x11) } := by
      rw [runBlock_cons, exec_str_x ⟨by omega, by omega⟩ hw, runStep_some, runBlock_nil]
    refine ⟨{ t₁ with mem := t₁.mem.writeW (t₁.gpr .x1 + BitVec.ofNat 64 (8 * q)) (t₁.gpr .x11) }, ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append h₁ h₂)
    · refine ⟨(regs₁ .x0 (by simp)).trans hi.x0, x1₁, rd₁.trans hi.rd, wr₁.trans hi.wr,
        sp₁.trans hi.sp, fun r hr => (regs₁ r hr).trans (hi.regs r hr), ?_, ?_⟩
      · show Frame _ s₀.mem (t₁.mem.writeW _ _)
        rw [mem₁, x1₁]
        refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
          (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega)
      · intro i hiq p hp64
        show ((t₁.mem.writeW _ _).readW _ 64).getLsbD p = _
        rw [mem₁, x1₁]
        by_cases he : i = q
        · subst he
          rw [Mem.readW_writeW_self64, bits₁ p hp64]
          have src := keyLoc_spec (keyBit_lt (4 * i + p / 16) (p % 16))
          rw [readW_getLsbD _ _ (by simpa [expandSrc] using src.2.1), Offset.add_ofNat_add_ofNat,
            hi.x0]
          simp only [expandSrc] at src ⊢
          rw [src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega)]
          refine congrArg (fun b => BitVec.getLsbD b _) (hi.frame _ fun r hr hc => ?_)
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.sep _ (Offset.contains_base _ (by omega) (by omega))
            (Region.sub_prefix (by omega) _ hc)
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact hi.words i (by omega) p hp64

theorem schedule_eq (s₀ t : State) (hi : ExpInv s₀ 13 t) :
    Spec.Idea.scheduleAt t.mem (s₀.gpr .x1) = Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (s₀.gpr .x0)) := by
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega) _ (by omega), expandKey_getLsbD _ hn hb,
    show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega, show (16 * (n % 4) + b) % 16 = b by omega]

/-- `vg_idea_expand_key` on AArch64. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let sched : Region := ⟨s.gpr .x1, 104⟩
    s.rd = [key] ∧ s.wr = [sched] ∧ key.Disjoint sched
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .x1) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (s.gpr .x0))
  pub := PublicRegs [.x0, .x1]

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨hrd, hwr, hsep⟩ := hs
  obtain ⟨t, ht, hi⟩ := words_run s ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩ 13 (by decide)
  obtain ⟨tr, s', he, hi⟩ : WP isa expandKey s (ExpInv s 13) := WP.of_runBlock ⟨t, ht, hi⟩
  refine ⟨tr, s', he, ⟨fun r hr => hi.regs r ?_, hi.sp, Exec.preservedV he (by lit_decide)⟩,
    schedule_eq s s' hi⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def expandSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem publicRegs_two (s₁ s₂ : State) : PublicRegs [.x0, .x1] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 := by
  simp [PublicRegs]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) := by
  refine Verified.of_correct expand_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi,
    argRegs, expandContract, publicRegs_two] [expandSat] using expandSat

end VG.Proof.Idea.AArch64
