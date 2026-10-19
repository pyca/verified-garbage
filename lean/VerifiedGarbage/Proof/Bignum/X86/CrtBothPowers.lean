module

public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorFrame
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.X86.CopyArray

/-! # Both CRT factor residues, by one exponentiation run twice

`powers` raises the factor in `p`'s slot into `mp`'s and then exchanges the
factors (`p` with `q`, `dp` with `dq`, `mp` with `mq`), twice: the second
iteration raises `q`, and its exchange puts every component back in its slot
and each residue in its own. A counter in the header picks each iteration's
length argument and ends the loop. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt

def powersRanges (n : Nat) : List (Nat × Nat) :=
  arithmeticRanges n ++ [(slot n pSlot, 4 * stride n), (slot n mpSlot, 2 * stride n), tableRange n,
    (counterOffset, 4)]

/-- What the factors' exponentiations at `half n` words need: each factor's
length (a public argument) and, when it fits `half n` words, the factor and
its exponent below `2 ^ (64 half n)`. -/
structure PowerArgs (base : Addr) (bytes n : Nat) (s : State) : Prop where
  pLen : ∃ v, CallArgument s base bytes 7 v ∧ (v.toNat ≤ 8 * half n →
    wordsVal s.mem base (slot n pSlot) n < 2 ^ (64 * half n) ∧
      wordsVal s.mem base (slot n dpSlot) n < 2 ^ (64 * half n))
  qLen : ∃ v, CallArgument s base bytes 9 v ∧ (v.toNat ≤ 8 * half n →
    wordsVal s.mem base (slot n qSlot) n < 2 ^ (64 * half n) ∧
      wordsVal s.mem base (slot n dqSlot) n < 2 ^ (64 * half n))

theorem PowerArgs.keep {base : Addr} {bytes n : Nat} {s t : State} (h : PowerArgs base bytes n s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem)
    (P : wordsVal t.mem base (slot n pSlot) n = wordsVal s.mem base (slot n pSlot) n)
    (DP : wordsVal t.mem base (slot n dpSlot) n = wordsVal s.mem base (slot n dpSlot) n)
    (Q : wordsVal t.mem base (slot n qSlot) n = wordsVal s.mem base (slot n qSlot) n)
    (DQ : wordsVal t.mem base (slot n dqSlot) n = wordsVal s.mem base (slot n dqSlot) n) :
    PowerArgs base bytes n t := by
  obtain ⟨vp, AP, BP⟩ := h.pLen
  obtain ⟨vq, AQ, BQ⟩ := h.qLen
  exact ⟨⟨vp, AP.keep K sp O, by rw [P, DP]; exact BP⟩, ⟨vq, AQ.keep K sp O, by rw [Q, DQ]; exact BQ⟩⟩


/-- Numbers apart from every range that changed. -/
theorem Outs.words {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (fit : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact O.val32 (fun r hr => by have := hd r hr; omega) (by omega)

/-- The counter, apart from every range that changed. -/
theorem Outs.counter {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (hd : ∀ r ∈ rs, counterOffset + 4 ≤ r.1 ∨ r.1 + r.2 ≤ counterOffset) :
    w32 m' base counterOffset = w32 m base counterOffset := by
  have V := O.val32 (d := counterOffset) (k := 1) (fun r hr => by have := hd r hr; omega)
    (by unfold counterOffset multiplierOffset; omega)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using V

/-- The `k` words at `A` and `B` exchanged through `T`. -/
theorem swap_ok {s : State} {base : Addr} {bytes k A B T : Nat} (hs : Scr s base bytes) (hk : 0 < k)
    (AB : A + 8 * k ≤ B) (BT : B + 8 * k ≤ T) (hT : T + 8 * k ≤ bytes) :
    WP isa (.seq (copyArray k A T) (.seq (copyArray k B A) (copyArray k T B))) s fun t =>
      wordsVal t.mem base A k = wordsVal s.mem base B k ∧ wordsVal t.mem base B k = wordsVal s.mem base A k ∧
      Outs base [(A, 8 * k), (B, 8 * k), (T, 8 * k)] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nw := hs.nowrap
  refine WP.seq (WP.mono (copyArray_ok hs hk (by omega) (by omega) (.inr (.inr (by omega))))
    fun u ⟨U, Ou, Ku⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine WP.seq (WP.mono (copyArray_ok hu hk (by omega) (by omega) (.inr (.inl (by omega))))
    fun v ⟨V, Ov, Kv⟩ => ?_)
  have hv := hu.of_keeps Kv (by decide)
  refine WP.mono (copyArray_ok hv hk (by omega) (by omega) (.inr (.inl (by omega))))
    fun t ⟨W, Ot, Kt⟩ => ⟨?_, ?_, ?_, Ku.trans (Kv.trans Kt)⟩
  · rw [Ot.wordsVal (.inl (by omega)) (by omega), V, Ou.wordsVal (.inl (by omega)) (by omega)]
  · rw [W, Ov.wordsVal (.inr (by omega)) (by omega), U]
  · exact ((Outside.within Ou (r := (T, 8 * k)) (by simp) (Nat.le_refl _) (Nat.le_refl _)).trans
      (Outside.within Ov (r := (A, 8 * k)) (by simp) (Nat.le_refl _) (Nat.le_refl _))).trans
      (Outside.within Ot (r := (B, 8 * k)) (by simp) (Nat.le_refl _) (Nat.le_refl _))

/-- The test of the counter, into ZF. -/
theorem counterTest_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes) (hb : 64 ≤ bytes) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc counterOffset)), .alu .cmp .eax (.imm 0)]) s fun u =>
      u.mem = s.mem ∧ Keeps [.eax] s u ∧ u.zf = some (decide (w32 s.mem base counterOffset = 0)) := by
  refine wp_movS (readSrc_sc hs (d := counterOffset) (by unfold counterOffset multiplierOffset; omega))
    fun u U _ => wp_cmpS rfl fun w F Z => WP.block_nil ⟨F.mem.trans U.mem, U.keeps.trans (F.keeps _), ?_⟩
  rw [Z, U.gpr]
  refine congrArg some (Bool.eq_iff_iff.mpr ?_)
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have e : s.mem.readW (off base counterOffset) 32 = 0 := by simpa using h
    change (s.mem.readW (off base counterOffset) 32).toNat = 0
    rw [e]; rfl
  · intro h
    have e : s.mem.readW (off base counterOffset) 32 = 0 := BitVec.eq_of_toNat_eq h
    rw [e]; rfl

/-- The counter's start. -/
theorem powersInit_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes) (hb : 64 ≤ bytes) :
    WP isa (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc counterOffset) .eax]) s fun u =>
      Outside base counterOffset 4 s.mem u.mem ∧ Keeps [.eax] s u ∧ w32 u.mem base counterOffset = 0 := by
  have nw := hs.nowrap
  have hc : counterOffset + 4 ≤ bytes := by unfold counterOffset multiplierOffset; omega
  refine wp_movS rfl fun s₁ U₁ _ => wp_storeS (hs.of_keeps U₁.keeps (by decide) |>.ea (d := counterOffset)
    (by omega)) (hs.of_keeps U₁.keeps (by decide) |>.write hc) fun u M =>
      WP.block_nil ⟨?_, U₁.keeps.trans (M.keeps _), ?_⟩
  · rw [M.mem, U₁.mem]; exact writeW32_outside _ _ _ (by omega)
  · rw [M.mem]
    change (Mem.readW _ _ 32).toNat = _
    rw [Mem.readW_writeW_self32, U₁.gpr]; rfl

/-- The length of the factor the counter `k` names, compared with `8 half n`. -/
theorem selectLength_ok {s : State} {base : Addr} {bytes n k arg : Nat} {v : BitVec 32}
    (hs : Scr s base bytes) (hn32 : 128 * n < 2 ^ 32) (hb : 64 ≤ bytes) (hk : k < 2)
    (C : w32 s.mem base counterOffset = k) (harg : arg = if k = 0 then 7 else 9)
    (A : CallArgument s base bytes arg v) :
    WP isa (selectLength n) s fun w =>
      w.mem = s.mem ∧ Keeps [.eax] s w ∧ w.cf = some (decide (v.toNat < 8 * half n + 1)) := by
  unfold selectLength
  refine WP.seq (wp_movS (readSrc_sc hs (d := counterOffset) (by unfold counterOffset multiplierOffset; omega))
    fun u U _ => wp_cmpS rfl fun w F Z => WP.block_nil ?_)
  have Mw : w.mem = s.mem := F.mem.trans U.mem
  have Kw : Keeps [.eax] s w := U.keeps.trans (F.keeps _)
  have Aw : CallArgument w base bytes arg v :=
    A.keep Kw (by decide) (by rw [Mw]; exact VG.Proof.Mont.Outside.refl _ _ _ _)
  have value : (u.gpr .eax).toNat = k := by rw [U.gpr]; exact C
  refine WP.ite _ Z (fun z => ?_) (fun z => ?_)
  · have k0 : k = 0 := by
      have z' : u.gpr .eax = 0 := by simpa using z
      rw [z'] at value; rw [← value]; rfl
    subst k0
    simp only [ite_true] at harg
    subst harg
    refine WP.mono (lengthFits_ok hn32 Aw) fun t ⟨M, K, cf⟩ => ⟨M.trans Mw, Kw.trans K, cf⟩
  · have k1 : k ≠ 0 := by
      intro k0
      have z' : u.gpr .eax ≠ 0 := by simpa using z
      exact z' (BitVec.eq_of_toNat_eq (by rw [value, k0]; rfl))
    rw [ite_eq_right_iff.mpr (fun h => absurd h k1)] at harg
    subst harg
    refine WP.mono (lengthFits_ok hn32 Aw) fun t ⟨M, K, cf⟩ => ⟨M.trans Mw, Kw.trans K, cf⟩

theorem counter_next {x : BitVec 32} {k : Nat} (hk : k < 2) (h : x.toNat = k) :
    (x + 1).toNat = k + 1 ∧ (x + 1 - 2 == 0) = decide (k + 1 = 2) := by
  obtain rfl : x = BitVec.ofNat 32 k := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat]; omega)
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- Changes within `powers`'s ranges. -/
theorem powers_within {base : Addr} {n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ q ∈ rs, q = (0, 8) ∨ q = (64, contextBytes n - 64) ∨ q = (counterOffset, 4) ∨
      (slot n pSlot ≤ q.1 ∧ q.1 + q.2 ≤ slot n pSlot + 4 * stride n) ∨
      (slot n mpSlot ≤ q.1 ∧ q.1 + q.2 ≤ slot n mpSlot + 2 * stride n) ∨
      (slot n 20 ≤ q.1 ∧ q.1 + q.2 ≤ slot n 20 + 8 * stride n)) :
    Outs base (powersRanges n) m m' := by
  refine Outs.within O fun q hq => ?_
  rcases h q hq with rfl | rfl | rfl | h | h | h
  · exact ⟨_, by simp [powersRanges, arithmeticRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [powersRanges, arithmeticRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [powersRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(slot n pSlot, 4 * stride n), by simp [powersRanges], h⟩
  · exact ⟨(slot n mpSlot, 2 * stride n), by simp [powersRanges], h⟩
  · exact ⟨tableRange n, by simp [powersRanges], h⟩

/-- One iteration: the power of the factor in `p`'s slot into `mq`'s, the
factors exchanged, and the counter advanced. -/
theorem factorStep_ok {s : State} {base : Addr} {bytes n k arg : Nat} {v : BitVec 32}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (hk : k < 2) (C : w32 s.mem base counterOffset = k) (harg : arg = if k = 0 then 7 else 9)
    (A : CallArgument s base bytes arg v) :
    WP isa (factorStep n) s fun t =>
      ((v.toNat ≤ 8 * half n → wordsVal s.mem base (slot n pSlot) n < 2 ^ (64 * half n) ∧
          wordsVal s.mem base (slot n dpSlot) n < 2 ^ (64 * half n)) →
        let result := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dpSlot) n %
          safePrime (wordsVal s.mem base (slot n pSlot) n)
        wordsVal t.mem base (slot n mqSlot) n = result ∧ wordsVal t.mem base (slot n mqSlot) (2 * n) = result) ∧
      wordsVal t.mem base (slot n pSlot) n = wordsVal s.mem base (slot n qSlot) n ∧
      wordsVal t.mem base (slot n qSlot) n = wordsVal s.mem base (slot n pSlot) n ∧
      wordsVal t.mem base (slot n dpSlot) n = wordsVal s.mem base (slot n dqSlot) n ∧
      wordsVal t.mem base (slot n dqSlot) n = wordsVal s.mem base (slot n dpSlot) n ∧
      wordsVal t.mem base (slot n mpSlot) n = wordsVal s.mem base (slot n mqSlot) n ∧
      wordsVal t.mem base (slot n mpSlot) (2 * n) = wordsVal s.mem base (slot n mqSlot) (2 * n) ∧
      w32 t.mem base counterOffset = k + 1 ∧ t.zf = some (decide (k + 1 = 2)) ∧
      Outs base (powersRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have top : slot n 20 + 8 * stride n = size n := by unfold size slot; omega
  have st : stride n = 16 * n + 8 := rfl
  have fit : size n ≤ 2 ^ 64 := by omega
  have sz : slot n 28 = size n := rfl
  have hb : 64 ≤ bytes := by unfold size slot at hz; omega
  have b (i : Nat) : slot n i = 64 + i * (16 * n + 8) := rfl
  have hz' : 64 + 28 * (16 * n + 8) ≤ bytes := hz
  have s9 : contextBytes n = 64 + 9 * (16 * n + 8) := rfl
  have sP : slot n pSlot = 64 + 10 * (16 * n + 8) := rfl
  have sQ : slot n qSlot = 64 + 11 * (16 * n + 8) := rfl
  have sDP : slot n dpSlot = 64 + 12 * (16 * n + 8) := rfl
  have sDQ : slot n dqSlot = 64 + 13 * (16 * n + 8) := rfl
  have s12 : slot n 12 = 64 + 12 * (16 * n + 8) := rfl
  have s14 : slot n 14 = 64 + 14 * (16 * n + 8) := rfl
  have sMP : slot n mpSlot = 64 + 16 * (16 * n + 8) := rfl
  have sMQ : slot n mqSlot = 64 + 17 * (16 * n + 8) := rfl
  have s20 : slot n 20 = 64 + 20 * (16 * n + 8) := rfl
  have sc : counterOffset = 48 := rfl
  have sS : size n = 64 + 28 * (16 * n + 8) := rfl
  unfold factorStep
  refine WP.seq (WP.mono (selectLength_ok hs hn32 hb hk C harg A) fun w ⟨Mw, Kw, cf⟩ => ?_)
  have hw := hs.of_keeps Kw (by decide)
  refine WP.seq (WP.mono (fitPower_ok hw hn hn32 hz (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) cf) fun u ⟨PV, O, K⟩ => ?_)
  rw [Mw] at PV O
  have hu := hw.of_keeps K (by decide)
  have Pu := factor_value O (i := pSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have Qu := factor_value O (i := qSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have DPu := factor_value O (i := dpSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have DQu := factor_value O (i := dqSlot) (k := n) (by decide) (by decide) (by decide) (by omega) fit
  have MQu := factor_value O (i := mqSlot) (k := 2 * n) (by decide) (by decide) (by decide) (by omega) fit
  have Cu : w32 u.mem base counterOffset = k := by
    rw [Outs.counter O (by
      simp only [factorRanges, arithmeticRanges, tableRange, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      omega), C]
  unfold swapFactors swapSlots
  refine WP.seq (WP.seq (WP.mono (swap_ok hu hn (A := slot n pSlot) (B := slot n qSlot) (T := slot n 20)
    (by omega) (by omega)
    (by omega)) fun u₁ ⟨P₁, Q₁, O₁, K₁⟩ => ?_))
  have hu₁ := hu.of_keeps K₁ (by decide)
  refine WP.seq (WP.mono (swap_ok hu₁ hn (A := slot n dpSlot) (B := slot n dqSlot) (T := slot n 20)
    (by omega) (by omega)
    (by omega)) fun u₂ ⟨P₂, Q₂, O₂, K₂⟩ => ?_)
  have hu₂ := hu₁.of_keeps K₂ (by decide)
  refine WP.mono (swap_ok hu₂ (k := 2 * n) (by omega) (A := slot n mpSlot) (B := slot n mqSlot) (T := slot n 20)
    (by omega) (by omega)
    (by omega)) fun u₃ ⟨P₃, Q₃, O₃, K₃⟩ => ?_
  have hu₃ := hu₂.of_keeps K₃ (by decide)
  have sep₁ {d j : Nat} {m m' : Mem} (O' : Outs base [(slot n pSlot, 8 * n), (slot n qSlot, 8 * n),
      (slot n 20, 8 * n)] m m') (hd : d + 8 * j ≤ slot n pSlot ∨ slot n 12 ≤ d ∧ d + 8 * j ≤ slot n 20)
      (hj : j ≤ 2 * n) : wordsVal m' base d j = wordsVal m base d j :=
    Outs.words O' (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at hd ⊢; omega) (by omega)
  have sep₂ {d j : Nat} {m m' : Mem} (O' : Outs base [(slot n dpSlot, 8 * n), (slot n dqSlot, 8 * n),
      (slot n 20, 8 * n)] m m') (hd : d + 8 * j ≤ slot n dpSlot ∨ slot n 14 ≤ d ∧ d + 8 * j ≤ slot n 20)
      (hj : j ≤ 2 * n) : wordsVal m' base d j = wordsVal m base d j :=
    Outs.words O' (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at hd ⊢; omega) (by omega)
  have sep₃ {d j : Nat} {m m' : Mem} (O' : Outs base [(slot n mpSlot, 8 * (2 * n)),
      (slot n mqSlot, 8 * (2 * n)), (slot n 20, 8 * (2 * n))] m m')
      (hd : d + 8 * j ≤ slot n mpSlot) : wordsVal m' base d j = wordsVal m base d j :=
    Outs.words O' (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at hd ⊢; omega) (by omega)
  have Pt : wordsVal u₃.mem base (slot n pSlot) n = wordsVal s.mem base (slot n qSlot) n := by
    rw [sep₃ O₃ (by omega), sep₂ O₂ (by omega)
      (by omega), P₁, Qu]
  have Qt : wordsVal u₃.mem base (slot n qSlot) n = wordsVal s.mem base (slot n pSlot) n := by
    rw [sep₃ O₃ (by omega), sep₂ O₂ (by omega)
      (by omega), Q₁, Pu]
  have DPt : wordsVal u₃.mem base (slot n dpSlot) n = wordsVal s.mem base (slot n dqSlot) n := by
    rw [sep₃ O₃ (by omega), P₂,
      sep₁ O₁ (by omega) (by omega), DQu]
  have DQt : wordsVal u₃.mem base (slot n dqSlot) n = wordsVal s.mem base (slot n dpSlot) n := by
    rw [sep₃ O₃ (by omega), Q₂,
      sep₁ O₁ (by omega) (by omega), DPu]
  have MPt : wordsVal u₃.mem base (slot n mpSlot) (2 * n) = wordsVal s.mem base (slot n mqSlot) (2 * n) := by
    rw [P₃, sep₂ O₂ (by omega) (by omega),
      sep₁ O₁ (by omega) (by omega), MQu]
  have MQt : wordsVal u₃.mem base (slot n mqSlot) (2 * n) = wordsVal u.mem base (slot n mpSlot) (2 * n) := by
    rw [Q₃, sep₂ O₂ (by omega) (by omega),
      sep₁ O₁ (by omega) (by omega)]
  have Ct : w32 u₃.mem base counterOffset = k := by
    have h₁ := Outs.counter O₁ (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]; omega)
    have h₂ := Outs.counter O₂ (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]; omega)
    have h₃ := Outs.counter O₃ (by simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]; omega)
    rw [h₃, h₂, h₁, Cu]
  have hc : counterOffset + 4 ≤ bytes := by unfold counterOffset multiplierOffset; omega
  refine wp_movS (readSrc_sc hu₃ hc) fun a₁ U₁ _ => wp_addS rfl fun a₂ U₂ _ => ?_
  have K₁₂ : Keeps [.eax] u₃ a₂ := U₁.keeps.trans U₂.keeps
  have ha₂ := hu₃.of_keeps K₁₂ (by decide)
  refine wp_storeS (ha₂.ea (by omega)) (ha₂.write hc) fun a₃ M₃ => wp_cmpS rfl fun t F Z => WP.block_nil ?_
  have mem₂ : a₂.mem = u₃.mem := by rw [U₂.mem, U₁.mem]
  have value : (a₂.gpr .eax).toNat = k + 1 ∧ (a₂.gpr .eax - 2 == 0) = decide (k + 1 = 2) := by
    rw [U₂.gpr, U₁.gpr]
    exact counter_next hk Ct
  have Ot : Outside base counterOffset 4 u₃.mem t.mem := by
    rw [F.mem, M₃.mem, mem₂]; exact writeW32_outside _ _ _ (by omega)
  have keep {d j : Nat} (hd : counterOffset + 4 ≤ d) (hj : d + 8 * j ≤ size n) :
      wordsVal t.mem base d j = wordsVal u₃.mem base d j :=
    Ot.wordsVal (.inr hd) (by omega)
  have hi (i : Nat) : counterOffset + 4 ≤ slot n i := by
    have := slot_header n i; omega
  refine ⟨fun B => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨V, W⟩ := PV B
    refine ⟨?_, ?_⟩
    · rw [keep (hi _) (by omega),
        wordsVal_prefix _ _ _ (Nat.le_mul_of_pos_left n (by decide) : n ≤ 2 * n), MQt,
        ← wordsVal_prefix _ _ _ (Nat.le_mul_of_pos_left n (by decide) : n ≤ 2 * n), V]
    · rw [keep (hi _) (by omega), MQt, W]
  · rw [keep (hi _) (by omega), Pt]
  · rw [keep (hi _) (by omega), Qt]
  · rw [keep (hi _) (by omega), DPt]
  · rw [keep (hi _) (by omega), DQt]
  · rw [keep (hi _) (by omega),
      wordsVal_prefix _ _ _ (Nat.le_mul_of_pos_left n (by decide) : n ≤ 2 * n), MPt,
      ← wordsVal_prefix _ _ _ (Nat.le_mul_of_pos_left n (by decide) : n ≤ 2 * n)]
  · rw [keep (hi _) (by omega), MPt]
  · rw [F.mem, M₃.mem]
    change (Mem.readW _ _ 32).toNat = _
    rw [Mem.readW_writeW_self32 _ _ _]
    exact value.1
  · rw [Z, M₃.gpr, value.2]
  · refine powers_within (n := n) O ?_ |>.trans (powers_within (n := n) O₁ ?_ |>.trans
      (powers_within (n := n) O₂ ?_ |>.trans (powers_within (n := n) O₃ ?_ |>.trans
      (powers_within (n := n) (Outs.of_outside Ot (rs := [(counterOffset, 4)]) (by simp)) ?_))))
    all_goals
      simp only [factorRanges, arithmeticRanges, tableRange, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, Prod.mk.injEq, true_or, or_true, true_and] <;> omega
  · exact (Kw.mono (by decide)).trans (K.trans ((K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans
      ((K₃.mono (by decide)).trans ((K₁₂.mono (by decide)).trans ((M₃.keeps _).trans (F.keeps _)))))))

/-- The modulus, the coefficient and the input, which `powers` leaves. -/
theorem powers_value {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (powersRanges n) m m') (hi : i = 9 ∨ i = 14 ∨ i = 15) (hk : k ≤ 2 * n)
    (fit : size n ≤ 2 ^ 64) : wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have sS : size n = 64 + 28 * (16 * n + 8) := rfl
  have s9 : contextBytes n = 64 + 9 * (16 * n + 8) := rfl
  have sP : slot n pSlot = 64 + 10 * (16 * n + 8) := rfl
  have sMP : slot n mpSlot = 64 + 16 * (16 * n + 8) := rfl
  have s20 : slot n 20 = 64 + 20 * (16 * n + 8) := rfl
  have st : stride n = 16 * n + 8 := rfl
  have sc : counterOffset = 48 := rfl
  have h : slot n i = 64 + i * (16 * n + 8) := rfl
  refine Outs.words O ?_ (by rcases hi with rfl | rfl | rfl <;> omega)
  simp only [powersRanges, arithmeticRanges, tableRange, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  rcases hi with rfl | rfl | rfl <;> omega

/-- `powers` writes only within the working space. -/
theorem powers_outside {n bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (powersRanges n) m m') (hz : size n ≤ bytes) : Outside base 0 bytes m m' := by
  have sS : size n = 64 + 28 * (16 * n + 8) := rfl
  have s9 : contextBytes n = 64 + 9 * (16 * n + 8) := rfl
  have sP : slot n pSlot = 64 + 10 * (16 * n + 8) := rfl
  have sMP : slot n mpSlot = 64 + 16 * (16 * n + 8) := rfl
  have s20 : slot n 20 = 64 + 20 * (16 * n + 8) := rfl
  have st : stride n = 16 * n + 8 := rfl
  have sc : counterOffset = 48 := rfl
  refine Outs.outside O ?_
  simp only [powersRanges, arithmeticRanges, tableRange, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  omega

theorem powers_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (args : PowerArgs base bytes n s) :
    WP isa (powers n) s fun t =>
      let xp := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dpSlot) n %
        safePrime (wordsVal s.mem base (slot n pSlot) n)
      let xq := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n dqSlot) n %
        safePrime (wordsVal s.mem base (slot n qSlot) n)
      wordsVal t.mem base (slot n mpSlot) n = xp ∧ wordsVal t.mem base (slot n mpSlot) (2 * n) = xp ∧
      wordsVal t.mem base (slot n mqSlot) n = xq ∧ wordsVal t.mem base (slot n mqSlot) (2 * n) = xq ∧
      wordsVal t.mem base (slot n pSlot) n = wordsVal s.mem base (slot n pSlot) n ∧
      wordsVal t.mem base (slot n qSlot) n = wordsVal s.mem base (slot n qSlot) n ∧
      Outs base (powersRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have fit : size n ≤ 2 ^ 64 := by omega
  have sS : size n = 64 + 28 * (16 * n + 8) := rfl
  have sc : counterOffset = 48 := rfl
  obtain ⟨vp, AP, BP⟩ := args.pLen
  obtain ⟨vq, AQ, BQ⟩ := args.qLen
  have hc : counterOffset + 4 ≤ bytes := by omega
  unfold powers
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => wp_storeS (hs.of_keeps U₁.keeps (by decide) |>.ea (by omega))
    (hs.of_keeps U₁.keeps (by decide) |>.write hc) fun s₀ M₀ => WP.block_nil ?_)
  have O₀ : Outs base (powersRanges n) s.mem s₀.mem := by
    rw [M₀.mem, U₁.mem]
    exact Outs.of_outside (writeW32_outside _ _ _ (by omega)) (by simp [powersRanges])
  have K₀ : Keeps powerClob s s₀ := (U₁.keeps.mono (by decide)).trans (M₀.keeps _)
  have C₀ : w32 s₀.mem base counterOffset = 0 := by
    rw [M₀.mem]
    change (Mem.readW _ _ 32).toNat = _
    rw [Mem.readW_writeW_self32, U₁.gpr]; rfl
  let P := wordsVal s.mem base (slot n pSlot) n
  let Q := wordsVal s.mem base (slot n qSlot) n
  let DP := wordsVal s.mem base (slot n dpSlot) n
  let DQ := wordsVal s.mem base (slot n dqSlot) n
  let X := wordsVal s.mem base (slot n inputSlot) n
  have keep₀ {i : Nat} (hi : 9 ≤ i) (hi' : i < 20) :
      wordsVal s₀.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    rw [M₀.mem, U₁.mem]
    exact (writeW32_outside _ _ _ (by omega)).wordsVal (.inr (by have := slot_header n i; omega)) (by
      have := slot_bound (n := n) hi'; unfold stride at this; omega)
  refine WP.loop (M := isa) (fun m u => ∃ k, m = 2 - k ∧ k < 2 ∧ w32 u.mem base counterOffset = k ∧
      Outs base (powersRanges n) s.mem u.mem ∧ Keeps powerClob s u ∧
      (k = 0 → wordsVal u.mem base (slot n pSlot) n = P ∧ wordsVal u.mem base (slot n qSlot) n = Q ∧
        wordsVal u.mem base (slot n dpSlot) n = DP ∧ wordsVal u.mem base (slot n dqSlot) n = DQ) ∧
      (k = 1 → wordsVal u.mem base (slot n pSlot) n = Q ∧ wordsVal u.mem base (slot n qSlot) n = P ∧
        wordsVal u.mem base (slot n dpSlot) n = DQ ∧ wordsVal u.mem base (slot n dqSlot) n = DP ∧
        wordsVal u.mem base (slot n mqSlot) n = X ^ DP % safePrime P ∧
        wordsVal u.mem base (slot n mqSlot) (2 * n) = X ^ DP % safePrime P))
    ?_ 2 s₀ ⟨0, rfl, by decide, C₀, O₀, K₀,
      fun _ => ⟨keep₀ (by decide) (by decide), keep₀ (by decide) (by decide), keep₀ (by decide) (by decide),
        keep₀ (by decide) (by decide)⟩, fun h => absurd h (by decide)⟩
  rintro m u ⟨k, rfl, hk, Cu, Ou, Ku, I₀, I₁⟩
  have hu := hs.of_keeps Ku (by decide)
  have Out := powers_outside Ou hz
  have Xu : wordsVal u.mem base (slot n inputSlot) n = X :=
    powers_value Ou (i := inputSlot) (by decide) (by omega) fit
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · obtain ⟨Pu, Qu, DPu, DQu⟩ := I₀ rfl
    refine WP.mono (factorStep_ok hu hn hn32 hz (by decide) Cu rfl (AP.keep Ku (by decide) Out))
      fun t ⟨V, Pt, Qt, DPt, DQt, _, _, Ct, Zt, Ot, Kt⟩ => .inr ⟨by simp [eval, Zt], 1, by decide,
        1, rfl, by decide, Ct, Ou.trans Ot, Ku.trans Kt, fun h => absurd h (by decide), fun _ => ?_⟩
    obtain ⟨Vn, Vw⟩ := V (by rw [Pu, DPu]; exact BP)
    rw [Xu, Pu, DPu] at Vn Vw
    exact ⟨Pt.trans Qu, Qt.trans Pu, DPt.trans DQu, DQt.trans DPu, Vn, Vw⟩
  · obtain ⟨Pu, Qu, DPu, DQu, MQn, MQw⟩ := I₁ rfl
    refine WP.mono (factorStep_ok hu hn hn32 hz (by decide) Cu rfl (AQ.keep Ku (by decide) Out))
      fun t ⟨V, Pt, Qt, DPt, DQt, MPt, MPwt, Ct, Zt, Ot, Kt⟩ => .inl ⟨by simp [eval, Zt], ?_⟩
    obtain ⟨Vn, Vw⟩ := V (by rw [Pu, DPu]; exact BQ)
    rw [Xu, Pu, DPu] at Vn Vw
    exact ⟨MPt.trans MQn, MPwt.trans MQw, Vn, Vw, Pt.trans Qu, Qt.trans Pu, Ou.trans Ot, Ku.trans Kt⟩

end VG.Proof.Bignum.X86.Crt
