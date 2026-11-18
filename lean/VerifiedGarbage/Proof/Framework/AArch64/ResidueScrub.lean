module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueFrame
public import VerifiedGarbage.Proof.Framework.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Returning without secret residue, through calls and frames (AArch64)

`RTaintF.noResidue_withScrub`: code verified against its contract, whose
frames stay within `W` bytes below the stack pointer and whose analysis
through calls and frames (`rtaintF W`) from everything public ends with the
registers the calling convention does not preserve public (but `x9` and
`v31`, which the clearing writes), the flags public and the result public
above bit `r` (`doneF r`), followed by the clearing of those `W` bytes
(`withScrub W`), returns without secret residue with an `r`-bit result.

After the code, the two runs agree on their memory outside the regions but
in the window (`RTaintF.AgreeD`); the clearing then zeroes the window and
releases it, which the shared unknowns turn into the same bytes in both
(`Scrub.tail_run`). The registers the calling convention preserves are what
they were on entry (`abiPreserved`), and the clearing writes `x9` from the
stack pointer and `v31` with zero.

`Verified.withScrub`: the clearing keeps code verified against a contract
whose arguments are all in registers, if the `W` bytes are within the stack
the contract reserves, which no buffer overlaps, and its postcondition reads
the memory on return only within the buffers (`hpost`). Its trace is the
stack pointer's, which the two runs share.
-/

@[expose] public section

namespace VG.AArch64.RTaintF

open VG.AArch64 VG.AArch64.Residue VG.AArch64.Scrub VG.Impl.Residue.AArch64

/-- The registers the calling convention does not preserve, but `x0` and `x9`. -/
def scratchNo9 : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem mem_scratchNo9 {q : Reg} (hq : q ≠ .x0) (h9 : q ≠ .x9) (hp : q ∉ preserved) :
    q ∈ scratchNo9 := by
  cases q <;> simp_all [scratchNo9, preserved]

/-- The analysis ends at the depth it started from, with the registers the
calling convention does not preserve public but `x9`, `v31` and what it
preserves of `v8`–`v15` (their low halves), the flags public, and the result
public above bit `r`. -/
def doneF (r : Nat) (τ : T) : Bool :=
  τ.2 == some 0 &&
    scratchNo9.all (fun q => τ.1.1.1.1.1.mem q) &&
    RTaintL.vregs.all (fun v => v == .v31 || (if preservedV.contains v then
      τ.1.1.1.1.2.mem v || τ.1.1.2.2.mem v else RTaintL.vpub τ.1.1 v)) &&
    τ.1.1.1.2.1 &&
    (Nat.ble τ.1.1.1.2.2 r || Nat.ble (RTaintB.wget τ.1.2 .x0) r)

theorem outside0_ghost {s₁ s₂ : State} (h : Outside 0 s₁ s₂) : Outside 0 s₁ (ghost s₁ s₂) := by
  obtain ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hv, hd, hvr, hm⟩ := h
  refine ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hv, hd, hvr, fun x hx => ?_⟩
  exact ghost_off hrd hwr x hx

theorem agree_init {W : Nat} (hW : W < 2 ^ 64) {s₁ s₂ : State} (h : Outside 0 s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) : Agree W (RTaintB.init, some 0) s₁ s₂ :=
  ⟨0, Or.inl rfl, ⟨RTaintL.agree_init (outside0_ghost h) hu, (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩, Nat.zero_le _, hW,
    fun x hx _ => h.2.2.2.2.2.2.2.2.2.2.2 x (by rw [h.1, h.2.1]; exact hx)⟩

/-- Code verified against its contract, whose analysis (`rtaintF W`) ends in
`doneF r`, followed by the clearing of the `W` bytes below the stack
pointer, returns without secret residue, with an `r`-bit result. -/
theorem noResidue_withScrub {c : Prog isa} {k : Contract isa} {r W : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hsp : ∀ s, k.pre s → W ≤ s.sp.toNat)
    (h : ∃ hc, ((rtaintF W).check (RTaintB.init, some 0) c hc).any (doneF r) = true) :
    NoResidue (withScrub W c) k r := by
  intro s₁ s₂ t₁ t₂ s₁'' s₂'' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : (rtaintF W).check (RTaintB.init, some 0) c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
  rw [hτ] at h
  have hd : doneF r τ' = true := h
  simp only [doneF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hd
  obtain ⟨⟨⟨⟨hd0, hg⟩, hvv⟩, hfl⟩, hx⟩ := hd
  cases e₁ with
  | seq ea₁ eb₁ =>
  cases e₂ with
  | seq ea₂ eb₂ =>
  rename_i s₁' _ _ s₂' _ _
  obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
  obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det ea₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det ea₂ f₂
  obtain ⟨d, hdd, hb, -, hW64, hout⟩ := TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp
    (agree_init (by omega) ho hu) ea₁ ea₂
  have hd00 : d = 0 := by
    rw [hd0] at hdd
    rcases hdd with h | h
    · exact (Option.some.inj h).symm
    · cases h
  subst hd00
  obtain ⟨hsp', hrd', hwr', hdi', hu'⟩ := AgreeD.rest ⟨hb, Nat.zero_le _, hW64, hout⟩
  obtain ⟨v₁, x₁, tr₁⟩ := tail_run hW s₁' (by rw [hp₁.2.1]; exact hsp s₁ h₁)
  obtain ⟨v₂, x₂, tr₂⟩ := tail_run hW s₂' (by rw [hp₂.2.1]; exact hsp s₂ h₂)
  obtain ⟨-, rfl⟩ := Exec.det eb₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det eb₂ x₂
  obtain ⟨⟨⟨⟨⟨-, hgr⟩, hvr⟩, hflags, hx0, -⟩, hq⟩, hb₁, hb₂⟩ := hb
  refine ⟨by rw [tr₁.rd, tr₂.rd, hrd'], by rw [tr₁.wr, tr₂.wr, hwr'], fun q hq0 => ?_, ?_,
    by rw [tr₁.sp, tr₂.sp, hsp'], ?_, ?_, ?_, ?_, by rw [tr₁.dit, tr₂.dit, hdi'], ?_, ?_⟩
  · rw [tr₁.gpr, tr₂.gpr]
    by_cases h9 : q = .x9
    · simp only [h9, ↓reduceIte, hsp']
    · simp only [h9, ↓reduceIte]
      by_cases hpq : q ∈ preserved
      · rw [hp₁.1 q hpq, hp₂.1 q hpq]; exact ho.2.2.1 q hq0
      · exact hgr q (Taint.pub_iff.mp (hg q (mem_scratchNo9 hq0 h9 hpq)))
  · rw [tr₁.gpr, tr₂.gpr]
    simp only [reduceCtorEq, ↓reduceIte]
    rcases hx with hx | hx
    · exact RTaint.shr_mono hx0 (Nat.le_of_ble_eq_true hx)
    · rw [RTaintB.shr_eq_zero (RTaintB.wget_bound hb₁ .x0) (Nat.le_of_ble_eq_true hx),
        RTaintB.shr_eq_zero (x := s₂'.gpr .x0) (RTaintB.wget_bound hb₂ .x0)
          (Nat.le_of_ble_eq_true hx)]
  · rw [tr₁.c, tr₂.c]; exact (hflags hfl).1
  · rw [tr₁.nf, tr₂.nf]; exact (hflags hfl).2.1
  · rw [tr₁.zf, tr₂.zf]; exact (hflags hfl).2.2.1
  · rw [tr₁.vf, tr₂.vf]; exact (hflags hfl).2.2.2
  · rw [tr₁.v, tr₂.v]
    funext w
    by_cases h31 : w = .v31
    · simp only [h31, ↓reduceIte]
    · simp only [h31, ↓reduceIte]
      have hw := (hvv w (RTaintL.mem_vregs w)).resolve_left h31
      by_cases hpv : w ∈ preservedV
      · simp only [List.contains_iff_mem.mpr hpv, ↓reduceIte, Bool.or_eq_true] at hw
        rcases hw with hw | hw
        · exact hvr w hw
        · refine RTaintL.eq_of_halves ?_ (hq true w hw)
          rw [hp₁.2.2 w hpv, hp₂.2.2 w hpv, ho.2.2.2.2.2.2.2.2.2.2.1]
      · have : preservedV.contains w = false := by simpa using hpv
        simp only [this, Bool.false_eq_true, ↓reduceIte, RTaintL.vpub, Bool.or_eq_true,
          Bool.and_eq_true] at hw
        rcases hw with hw | ⟨h₀, h₁'⟩
        · exact hvr w hw
        · exact RTaintL.eq_of_halves (hq false w h₀) (hq true w h₁')
  · intro x hx
    rw [tr₁.rd, tr₁.wr] at hx
    rw [tr₁.mem, tr₂.mem, hsp']
    by_cases hin : (x - (s₂'.sp - BitVec.ofNat 64 W)).toNat < W
    · simp only [lose, hin, ↓reduceIte, hu', zeroTo]
    · rw [lose_out hin, lose_out hin]
      simp only [zeroTo, hin, ↓reduceIte]
      refine hout x (by rw [← hrd', ← hwr']; exact hx) fun hc => hin ?_
      unfold window Region.Contains at hc
      simp only [BitVec.add_zero] at hc
      omega

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The `W ≤ stack` bytes below the stack pointer on entry are apart from the buffers. -/
theorem scrub_disjoint (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W)
    (hWs : W ≤ stack) {s : State} (hs : (sig.contract abi pre post wa stack leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 W, W⟩ := by
  intro b hb
  rw [pre_regs hk] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hst : stackBelow s.sp stack = [⟨s.sp - BitVec.ofNat 64 stack, stack⟩] := by
    cases stack with
    | zero => omega
    | succ n => rfl
  have hr := hres ⟨s.sp - BitVec.ofNat 64 stack, stack⟩ (by rw [hst]; exact List.mem_singleton_self _)
    b (List.mem_append_left _ hb)
  exact hr.symm.sub_right (Offset.sub_below _ hWs (by omega))

theorem Verified.withScrub {c : Prog isa} {W : Nat}
    (h : Verified target c (sig.contract abi pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    Verified target (withScrub W c) (sig.contract abi pre post wa stack leak) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have hsb : ∀ s, (sig.contract abi pre post wa stack leak).pre s → W ≤ s.sp.toNat := by
    intro s hs
    rw [pre_regs hk] at hs
    rcases hs.1 with h0 | h0 <;> omega
  have hrun : ∀ s, (sig.contract abi pre post wa stack leak).pre s → ∃ t s₃ u,
      Exec isa c s t s₃ ∧ abiPreserved s s₃ ∧ (sig.contract abi pre post wa stack leak).post s s₃ ∧
      Exec isa (scrubTail W) s₃ (tailTrace s₃.sp W) u ∧ TailRun W s₃ u := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor s hs
    obtain ⟨u, ex, tr⟩ := tail_run hW s₃ (by rw [ha.2.1]; exact hsb s hs)
    exact ⟨t, s₃, u, he, ha, hq, ex, tr⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, u, he, ha, hq, ex, tr⟩ := hrun s hs
    refine ⟨_, u, Exec.seq he ex, ⟨fun q hq' => ?_, by rw [tr.sp]; exact ha.2.1, fun w hw => ?_⟩, ?_⟩
    · have h9 : q ≠ .x9 := by rintro rfl; simp [preserved] at hq'
      rw [tr.gpr]; simp only [h9, ↓reduceIte]; exact ha.1 q hq'
    · have h31 : w ≠ .v31 := by rintro rfl; simp [preservedV] at hw
      rw [tr.v]; simp only [h31, ↓reduceIte]; exact ha.2.2 w hw
    · rw [post_regs hk] at hq ⊢
      have hx0 : u.gpr .x0 = s₃.gpr .x0 := by rw [tr.gpr]; simp
      rw [hx0]
      refine hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb a ha' => ?_) hq
      have hd := scrub_disjoint hk hW.1 hWs hs b hb a ha'
      rw [tr.mem, ha.2.1]
      have hnot : ¬ (a - (s.sp - BitVec.ofNat 64 W)).toNat < W := fun hlt =>
        hd (show (a - (s.sp - BitVec.ofNat 64 W)).toNat + 1 ≤ W by omega)
      rw [lose_out hnot]
      simp only [zeroTo, hnot, ↓reduceIte]
  · cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    obtain ⟨_, _, _, f₁, p₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨_, _, _, f₂, p₂, -, x₂, -⟩ := hrun s₂ h₂
    obtain ⟨rfl, rfl⟩ := Exec.det a₁ f₁
    obtain ⟨rfl, rfl⟩ := Exec.det a₂ f₂
    rw [(Exec.det b₁ x₁).1, (Exec.det b₂ x₂).1, p₁.2.1, p₂.2.1,
      hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, ((pub_regs hk).mp hp).1.1.1]

end

/-! ## The result's upper bits -/

theorem retFix_run (rb : Nat) (s : State) : ∃ g, execBlock isa (retFix rb) s =
    some ({ s with gpr := g }, []) ∧ (∀ q, q ≠ .x0 → g q = s.gpr q) ∧
    (g .x0).setWidth rb = (s.gpr .x0).setWidth rb := by
  by_cases h0 : rb = 0
  · subst h0
    refine ⟨fun q => if q = .x0 then 0 else s.gpr q, ?_, fun q hq => by simp [hq], ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write]
    · apply BitVec.eq_of_toNat_eq
      have h1 := ((((fun q => if q = .x0 then (0 : BitVec 64) else s.gpr q) .x0)).setWidth 0).isLt
      have h2 := ((s.gpr .x0).setWidth 0).isLt
      simp only [Nat.pow_zero] at h1 h2
      omega
  by_cases h32 : rb = 32
  · subst h32
    refine ⟨fun q => if q = .x0 then ((s.gpr .x0).setWidth 32 + 0).setWidth 64 else s.gpr q, ?_,
      fun q hq => by simp [hq], ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write, State.read]
    · simp
  · have : retFix rb = [] := by
      unfold retFix; split <;> simp_all
    exact ⟨s.gpr, by rw [this]; rfl, fun _ _ => rfl, rfl⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Clearing what `x0` holds beyond the result keeps code verified. -/
theorem Verified.withRet {c : Prog isa}
    (h : Verified target c (sig.contract abi pre post wa stack leak)) :
    Verified target (withRet (sig.retBits abi.ptrBits) c) (sig.contract abi pre post wa stack leak) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hcor s hs
    obtain ⟨g, hb, hg, hx⟩ := retFix_run (sig.retBits abi.ptrBits) s'
    refine ⟨_, _, Exec.seq he (Exec.block hb), ⟨fun q hq' => ?_, ha.2.1, ha.2.2⟩, ?_⟩
    · have : q ≠ .x0 := by rintro rfl; simp [preserved] at hq'
      show g q = s.gpr q
      rw [hg q this]; exact ha.1 q hq'
    · revert hq
      simp only [Sig.contract]
      split
      · exact id
      · intro hq
        have hr : (abi.ret { s' with gpr := g }).setWidth (sig.retBits abi.ptrBits) =
            (abi.ret s').setWidth (sig.retBits abi.ptrBits) := hx
        have hm : abi.mem { s' with gpr := g } = abi.mem s' := rfl
        rw [hm, hr]; exact hq
  · cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    cases b₁ with
    | block hb₁ =>
    cases b₂ with
    | block hb₂ =>
    obtain ⟨_, hr₁, -, -⟩ := retFix_run (sig.retBits abi.ptrBits) _
    obtain ⟨_, hr₂, -, -⟩ := retFix_run (sig.retBits abi.ptrBits) _
    rw [hr₁] at hb₁; rw [hr₂] at hb₂
    cases hb₁; cases hb₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂]

end

end VG.AArch64.RTaintF
