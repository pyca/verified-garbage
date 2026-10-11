import VerifiedGarbage.Proof.Idea.X86.Lit
import VerifiedGarbage.Proof.Idea.X86.Round
import VerifiedGarbage.Proof.Idea.KeyBits32
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA key expansion on x86 (32-bit)

The schedule's 26 words (two subkeys each) are fixed bit permutations of the
key's four 32-bit words, built in place: the whole of `expandBody` is
checked by one evaluation over the lane domain (`expand_check`,
`Straight.linear_ok`), with the key's words (at `eax`) as external words and
the schedule's (at `ecx`) as slots: bit `p` of schedule word `w` is the key
bit `expandSrc32 w p`, and every subkey bit is then the key bit
`Spec.Idea.expandKey` takes (`expandKey_getLsbD`).
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Idea.X86 VG.Impl.Idea

/-- The key's four words at `eax`, the schedule's 26 at `ecx`. -/
def eCfg : Cfg := { base := .ecx, slots := 26, ext := .eax, exts := 4 }

/-- Bit `p` of word `w`: atom `32 j + t`, bit `t` of key word `j`. -/
def eG (w p : Nat) : List Nat := [32 * (expandSrc32 w p).1 + (expandSrc32 w p).2]

theorem expand_check :
    check (lanes 32 7) eCfg (linExt 0) expandBody (linEnv [])
      (linPost 26 7 ((List.range 26).map fun w => (w, eG w))) = true := by
  lit_decide

/-- `vg_idea_expand_key` on x86: the key (16 bytes) readable, the schedule
(104 bytes) writable, apart from each other, the arguments and the return
address, none wrapping around. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 104⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched] ∧ key.Disjoint sched ∧ args.Disjoint sched ∧
      ret.Disjoint sched ∧ (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 104 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem ((arg s 1).setWidth 64) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

theorem arg_src {s : State} {i n : Nat} (hi : 4 * i + 4 ≤ n) (h : ⟨argAddr s 0, n⟩ ∈ s.rd)
    (hf : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) :
    readSrc s (.mem (argOp i)) = some (arg s i) := by
  simp only [readSrc, State.load32, arg]
  refine ite_eq_left ⟨_, List.mem_append_left _ h, ?_⟩
  show Region.Contains _ (addr (s.gpr .esp) (4 + 4 * i)) 4
  simp only [argAddr]
  rw [show ((s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 : Addr) = addr (s.gpr .esp) 4 from rfl,
    addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem arg_eq (s : State) (i : Nat) : s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := rfl

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    WP isa expandKey s (fun s' => abiPreserved s s' ∧ expandContract.post s s') := by
  obtain ⟨hrd, hwr, dKS, dAS, dRS, fitK, fitS, fitSp⟩ := hs
  have hargs : ⟨argAddr s 0, 8⟩ ∈ s.rd := by rw [hrd]; simp
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 0) (by decide) hargs (by omega))
  have hargs₁ : ⟨argAddr s₁ 0, 8⟩ ∈ s₁.rd := by
    rw [e₁.rd]; simp only [argAddr, e₁.reg .esp (by decide)]; exact hargs
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .ecx _ _ s₁ (arg_src (i := 1) (by decide) hargs₁
    (by rw [e₁.reg .esp (by decide)]; omega))
  have a1 : arg s₁ 1 = arg s 1 := by simp only [arg, argAddr, e₁.mem, e₁.reg .esp (by decide)]
  have ecx₂ : s₂.gpr .ecx = arg s 1 := v₂.trans a1
  have eax₂ : s₂.gpr .eax = arg s 0 := (e₂.reg .eax (by decide)).trans v₁
  have e₀₂ : Keep [.eax, .ecx] s s₂ := (e₁.weaken (by decide)).trans (e₂.weaken (by decide))
  have hok : Ok eCfg s₂ := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
    · show InRegions s₂.wr (addr (s₂.gpr .ecx) (4 * k)) 4
      rw [e₀₂.wr, hwr, ecx₂, addr_eq (by simp only [eCfg] at hk; omega)]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by simp only [eCfg] at hk; omega)
        (by simp only [eCfg] at hk; omega)⟩
    · show InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) (4 * k)) 4
      simp only [eCfg] at hk
      rw [e₀₂.rd, hrd, eax₂, addr_eq (by omega)]
      exact ⟨⟨(arg s 0).setWidth 64, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · show (s₂.gpr .ecx).toNat + 4 * 26 ≤ 2 ^ 32
      rw [ecx₂]; omega
    · simp only [eCfg] at hk hj
      show Mem.Sep (addr (s₂.gpr .ecx) (4 * k)) 4 (addr (s₂.gpr .eax) (4 * j)) 4
      rw [ecx₂, eax₂, addr_eq (by omega), addr_eq (by omega)]
      exact fun x h₁ h₂ => dKS x (Region.Contains.byte (Offset.contains_base _ (by omega) (by omega)) h₂)
        (Region.Contains.byte (Offset.contains_base _ (by omega) (by omega)) h₁)
  obtain ⟨s', hs', hout, hrd', hwr', hoth, hfr⟩ := linear_ok expand_check hok
    (fun i => s₂.mem.readW (wordAddr (s₂.gpr .eax) i) 32)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 4 := hj
      refine ⟨by omega, ?_⟩
      simp only [Nat.zero_add]
      rfl)
  refine WP.of_runBlock ⟨s', ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact run_append (a := [_, _]) (run_append h₁ h₂) hs'
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hk : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], (expandBody.all fun i => i.dst != some r) = true := by
      lit_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hoth _ (hk _ (by simp))).trans (e₀₂.reg _ (by decide))
  · rw [← e₀₂.mem]
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, eCfg, ecx₂]
    exact dRS
  · show Spec.Idea.scheduleAt s'.mem _ = _
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hw := hout (n / 2) (eG (n / 2)) (List.mem_map.mpr ⟨n / 2, List.mem_range.mpr (by omega), rfl⟩)
      (16 * (n % 2) + b) (by omega)
    rw [scheduleAt_getLsbD32 _ _ hn hb, ← addr_eq (by omega), ← ecx₂]
    show (s'.mem.readW (wordAddr (s₂.gpr eCfg.base) (n / 2)) 32).getLsbD _ = _
    rw [hw]
    have src := keyLoc32_spec (keyBit_lt (2 * (n / 2) + (16 * (n % 2) + b) / 16) ((16 * (n % 2) + b) % 16))
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc32] using src.2.1), expandKey_getLsbD _ hn hb]
    simp only [expandSrc32] at src ⊢
    rw [show 2 * (n / 2) + (16 * (n % 2) + b) / 16 = n by omega, show (16 * (n % 2) + b) % 16 = b by omega]
      at src ⊢
    rw [wordAddr, eax₂, addr_eq (by omega), readW32_getLsbD _ _ src.2.1, Offset.add_ofNat_add_ofNat,
      src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega), e₀₂.mem]

def keyTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem keyTaint_wf {s : State} (h : expandContract.pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, ao, ro, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [keyTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact Taint.frame_disjoint (n := 8) (by omega) ro ao

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : expandContract.pre s₁) (h₂ : expandContract.pre s₂)
    (hp : expandContract.pub s₁ s₂) : VG.X86.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, expandContract.pre s → (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [keyTaint] at hk
    rw [show Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem expandKey_constantTime : ConstantTime isa expandContract.pre expandContract.pub expandKey :=
  VG.Taint.constantTime (A := taint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def keySatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 104⟩]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) := by
  refine Verified.of_correct expand_correct expandKey_constantTime ?_
  sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi, argSlots,
    argVal, argBytes, expandContract] [keySatState, arg, argAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Idea.X86
