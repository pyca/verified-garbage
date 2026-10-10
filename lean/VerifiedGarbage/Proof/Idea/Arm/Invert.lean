import VerifiedGarbage.Proof.Idea.Arm.Key
import VerifiedGarbage.Proof.Idea.Arm.Block
import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Idea.Scratch32
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# IDEA decryption subkeys on ARMv7

With the scratch buffer as an argument (at `r2`, 24 bytes), `invertKey`
saves `r4`–`r9` in it and restores them at the end. Each decryption subkey
is a copy, the negation or the inverse of an encryption subkey
(`invertKey_getD`, `Impl.Idea.invOp`), computed into `r3` (`invWord_ok`;
the inverse by a loop of fifteen steps of `t := (t ⊙ t) ⊙ a`,
`invLoop_ok`), placed in its 16 bits of `r7` (`invPlace`), and stored two
at a time (`invPair_ok`).
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.r3, .r4, .r5, .r6, .r8, .r9]

theorem invStep_run (t : State) (hm : MaskOk t) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .r5 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .r5).setWidth 16) ((t.gpr .r5).setWidth 16))
        ((t.gpr .r4).setWidth 16)).setWidth 32 ∧
      t'.gpr .r6 = t.gpr .r6 - 1 ∧ t'.z = (t.gpr .r6 - 1 == 0) ∧ Keep [.r5, .r6, .r8, .r9] t t' := by
  obtain ⟨t₁, h₁, v₁, e₁⟩ := mul_run .r5 .r5 .r5 (by decide) t hm
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run .r5 .r5 .r4 (by decide) t₁ ((e₁.reg .r12 (by decide)).trans hm)
  refine ⟨(subFlags t₂ (t₂.gpr .r6) 1).setReg .r6 (t₂.gpr .r6 - 1), ?_, ?_, ?_, ?_, ?_⟩
  · refine run_append (run_append h₁ h₂) ?_
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, enc_one, ↓reduceIte,
      Option.map_some]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]
    show t₂.gpr .r5 = _
    rw [v₂, v₁, setWidth_setWidth16_32, e₁.reg .r4 (by decide)]
  · rw [RegUpd.gpr_setReg_self, e₂.reg .r6 (by decide), e₁.reg .r6 (by decide)]
  · show (t₂.gpr .r6 - 1 == 0) = _
    rw [e₂.reg .r6 (by decide), e₁.reg .r6 (by decide)]
  · refine (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans
      ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hq.2.1]
    rfl

/-- `c` steps remain: `r5` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  r6 : t.gpr .r6 = BitVec.ofNat 32 c
  r4 : (t.gpr .r4).setWidth 16 = a
  r5 : (t.gpr .r5).setWidth 16 = chain a (15 - c)
  keep : Keep [.r5, .r6, .r8, .r9] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (hm : MaskOk t₀) (c : Nat) (t : State)
    (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) .ne) t (fun t' =>
      t'.gpr .r5 = (Spec.Idea.inv a).setWidth 32 ∧ Keep [.r5, .r6, .r8, .r9] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', r5', r6', z', e'⟩ := invStep_run t ((hi.keep.reg .r12 (by decide)).trans hm)
  refine WP.of_runBlock ⟨t', h', ?_⟩
  have hv : t'.gpr .r5 = (chain a (15 - c + 1)).setWidth 32 := by
    rw [r5', hi.r5, hi.r4]; rfl
  have hc : t'.gpr .r6 = BitVec.ofNat 32 (c - 1) := by
    rw [r6', hi.r6]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have hev : isa.eval .ne t' = some (decide (c - 1 ≠ 0)) := by
    show some (!t'.z) = _
    rw [z', ← r6', hc]
    congr 1
    have := hi.le
    by_cases h0 : c - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (c - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (c - 1) == 0) = false from by simpa using hne]
      simp [h0]
  have keep' : Keep [.r5, .r6, .r8, .r9] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨hev, ?_, keep'⟩
    rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      c - 1, by omega, by omega, by omega, hc, ?_, ?_, keep'⟩
    · rw [e'.reg .r4 (by decide)]; exact hi.r4
    · rw [hv, setWidth_setWidth16_32, show 15 - c + 1 = 15 - (c - 1) by omega]

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t)
    (hm : MaskOk t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .r3 = ((Spec.Idea.invertKey z).getD n 0).setWidth 32 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r3 k hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := dp_run .and .r3 .r3 .r12 t₁
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    simp only at v₂
    rw [v₂, e₁.reg .r12 (by decide), hm, mask32_setWidth, v₁]; rfl
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r3 k hk t hz
    have m₁ : MaskOk t₁ := (e₁.reg .r12 (by decide)).trans hm
    obtain ⟨t₂, h₂, v₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r9 (.imm 0), .dp .sub .r3 .r9 (.reg .r3),
        .dp .and .r3 .r3 (.reg .r12)] t₁ = some t₂ ∧
        t₂.gpr .r3 = (0 - t₁.gpr .r3) &&& 65535 ∧ Keep [.r3, .r9] t₁ t₂ := by
      have e0 : encodable 0 = true := by decide
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e0, ↓reduceIte,
        Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, m₁, Option.some.injEq, exists_eq_left']
      exact ⟨trivial, by keep_tac⟩
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, (e₁.weaken (by decide)).trans (e₂.weaken (by decide))⟩
    rw [v₂, neg_mask32, v₁]; rfl
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run .r4 k hk t hz
    obtain ⟨t₂, h₂, r4₂, r5₂, r6₂, e₂⟩ : ∃ t₂, runBlock isa [.mov .r5 (.reg .r4), .mov .r6 (.imm 15)] t₁ =
        some t₂ ∧ t₂.gpr .r4 = t₁.gpr .r4 ∧ t₂.gpr .r5 = t₁.gpr .r4 ∧ t₂.gpr .r6 = 15 ∧
        Keep [.r5, .r6] t₁ t₂ := by
      have e15 : encodable 15 = true := by decide
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e15, ↓reduceIte,
        Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, Option.some.injEq, exists_eq_left']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | keep_tac
    have m₂ : MaskOk t₂ := (e₂.reg .r12 (by decide)).trans ((e₁.reg .r12 (by decide)).trans hm)
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ m₂ 15 t₂ ⟨by decide, by decide, r6₂, by rw [r4₂, v₁],
      by rw [r5₂, v₁]; rfl, Keep.refl _ _⟩) fun t₃ h₃ => ?_
    obtain ⟨r5₃, e₃⟩ := h₃
    obtain ⟨t₄, h₄, r3₄, e₄⟩ : ∃ t₄, runBlock isa [.mov .r3 (.reg .r5)] t₃ = some t₄ ∧
        t₄.gpr .r3 = t₃.gpr .r5 ∧ Keep [.r3] t₃ t₄ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
        RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left', true_and]
      keep_tac
    refine WP.of_runBlock ⟨t₄, h₄, ?_, ?_⟩
    · rw [r3₄, r5₃]; rfl
    · exact (e₁.weaken (by decide)).trans ((e₂.weaken (by decide)).trans ((e₃.weaken (by decide)).trans
        (e₄.weaken (by decide))))

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `r7` holds the first `i` decryption subkeys of pair `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 32, (t.gpr .r7).getLsbD p =
    if p < 16 * i then (dk z (2 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_run (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 2) (t : State)
    (hr3 : t.gpr .r3 = (dk z (2 * q + i)).setWidth 32) (hacc : i = 0 ∨ Acc z q i t) :
    ∃ t', runBlock isa (invPlace (2 * q + i)) t = some t' ∧ Acc z q (i + 1) t' ∧
      Keep [.r7] t t' := by
  unfold invPlace
  split
  · rename_i h
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_setReg_self, hr3, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and,
      Nat.add_zero]
    by_cases hp16 : p < 16
    · rw [ite_eq_left (by omega), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
    · rw [ite_eq_right (by omega)]; exact BitVec.getLsbD_of_ge _ _ (by omega)
  · rename_i h
    have hi1 : i = 1 := by omega
    subst hi1
    have hacc' := hacc.resolve_left (by decide)
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Nat.reduceLeDiff,
      and_self, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_setReg_self, BitVec.getLsbD_or, hacc' p hp, hr3, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h1 : p < 16
    · simp [h1, show p < 16 * 2 by omega]
    · simp [h1, hp, show p - 16 < 32 by omega,
        show 2 * q + p / 16 = 2 * q + 1 by omega, show p % 16 = p - 16 by omega]

/-- The registers computing a pair of decryption subkeys writes. -/
abbrev pairWrites : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]

theorem pairWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 26) (hi : i < 2) (t : State)
    (hz : KeyOk z t) (hm : MaskOk t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa}
    {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → Keep pairWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (2 * q + i)) (.seq (.block (invPlace (2 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega) t hz hm) fun t₁ h₁ => ?_
  obtain ⟨v₁, e₁⟩ := h₁
  apply WP.seq
  have hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.reg .r7 (by decide)]; exact h p hp
  obtain ⟨t₂, h₂, a₂, e₂⟩ := invPlace_run z q i hi t₁ v₁ hacc₁
  exact WP.of_runBlock ⟨t₂, h₂, hrest t₂ a₂ ((e₁.weaken (by decide)).trans (e₂.weaken (by decide)))⟩

/-- What the subkey loop needs of the state `s₁` it starts from: the
encryption subkeys (104 bytes at `r0`) readable, the decryption subkeys (104
bytes at `r1`) writable, apart, neither wrapping around, and the mask. -/
structure InvPre (s : State) : Prop where
  sched : ⟨State.addr (s.gpr .r0), 104⟩ ∈ s.rd ++ s.wr
  out : ⟨State.addr (s.gpr .r1), 104⟩ ∈ s.wr
  sep : (⟨State.addr (s.gpr .r0), 104⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 104⟩
  fit0 : (s.gpr .r0).toNat + 104 ≤ 2 ^ 32
  fit1 : (s.gpr .r1).toNat + 104 ≤ 2 ^ 32
  mask : MaskOk s

/-- After `q` pairs of decryption subkeys. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  keep : Keep pairWrites s₀ { t with mem := s₀.mem }
  frame : Frame [⟨State.addr (s₀.gpr .r1), 4 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 32,
    (t.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i)) 32).getLsbD p =
      (dk (Spec.Idea.scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (2 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (hi : QInv s₀ q t) (hq : q ≤ 26) :
    KeyOk (Spec.Idea.scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) t := by
  have hr0 : t.gpr .r0 = s₀.gpr .r0 := hi.keep.reg .r0 (by decide)
  refine ⟨by rw [hr0, hi.keep.rd, hi.keep.wr]; exact hp.sched, by rw [hr0]; exact hp.fit0, ?_⟩
  rw [hr0]
  exact scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega))) (by decide))

theorem invPair_ok (s₀ : State) (hp : InvPre s₀) (q : Nat) (hq : q < 26) (t : State)
    (hi : QInv s₀ q t) : WP isa (invPair q) t (QInv s₀ (q + 1)) := by
  have hz := hi.keyOk hp (by omega)
  have hm : MaskOk t := (hi.keep.reg .r12 (by decide)).trans hp.mask
  simp only [invPair, show List.range 2 = [0, 1] from rfl, List.foldr_cons, List.foldr_nil]
  refine pairWord_ok _ q 0 hq (by decide) t hz hm (Or.inl rfl) fun t₁ a₁ e₁ => ?_
  have m₁ : MaskOk t₁ := (e₁.reg .r12 (by decide)).trans hm
  refine pairWord_ok _ q 1 hq (by decide) t₁ (hz.keep e₁ (by decide)) m₁ (Or.inr a₁)
    fun t₂ a₂ e₂ => ?_
  have e := e₁.trans e₂
  have r1₂ : t₂.gpr .r1 = s₀.gpr .r1 := (e.reg .r1 (by decide)).trans (hi.keep.reg .r1 (by decide))
  have hfit : (t₂.gpr .r1).toNat + 4 * q < 2 ^ 32 := by rw [r1₂]; have := hp.fit1; omega
  have hw : InRegions t₂.wr (State.addr (t₂.gpr .r1 + BitVec.ofNat 32 (4 * q))) 4 := by
    rw [addr_add hfit, r1₂, e.wr, hi.keep.wr]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.of_runBlock ⟨({ t₂ with
      mem := t₂.mem.writeW (State.addr (t₂.gpr .r1 + BitVec.ofNat 32 (4 * q))) (t₂.gpr .r7) } : State), by rw [runBlock_cons, exec_str (by omega) hw, runStep_some, runBlock_nil], ?_⟩
  rw [addr_add hfit, r1₂]
  refine ⟨⟨fun r hr => (e.reg r hr).trans (hi.keep.reg r hr), rfl, e.rd.trans hi.keep.rd,
    e.wr.trans hi.keep.wr, e.sp.trans hi.keep.sp⟩, ?_, ?_⟩
  · show Frame _ s₀.mem (t₂.mem.writeW _ _)
    rw [e.mem]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · intro i hiq p hp32
    show ((t₂.mem.writeW _ _).readW _ 32).getLsbD p = _
    rw [e.mem]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self32, a₂ p hp32, ite_eq_left (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words i (by omega) p hp32

/-- Pairs `q … q + n - 1`. -/
def pairs (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invPair q) rest) (.block [])

theorem pairs_ok (s₀ : State) (hp : InvPre s₀) :
    ∀ n q, q + n = 26 → ∀ t, QInv s₀ q t → WP isa (pairs q n) t (QInv s₀ 26)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [pairs, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invPair_ok s₀ hp q (by omega) t hi) fun t₁ h₁ =>
      pairs_ok s₀ hp n (q + 1) (by omega) t₁ h₁

theorem invertKey_eq : invertKey =
    .seq (.block (save .r2 invSaved ++ [setMask])) (.seq (pairs 0 26) (.block (restore .r2 invSaved))) :=
  rfl

/-- `vg_idea_invert_key` on ARMv7, with the scratch buffer (24 bytes) at `r2`. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 104⟩
    let out : Region := ⟨State.addr (s.gpr .r1), 104⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 24⟩
    s.rd = [sched] ∧ s.wr = [out, scratch] ∧ sched.Disjoint out ∧ sched.Disjoint scratch ∧
      out.Disjoint scratch ∧
      (s.gpr .r0).toNat + 104 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 104 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 24 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)))
  pub := PublicRegs [.r0, .r1, .r2]

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ invertContract.post s s') := by
  obtain ⟨hrd, hwr, dSO, dSS, dOS, fit0, fit1, fit2⟩ := hs
  have hslots : Slots 0 24 invSaved := by decide
  have hinS : ∀ d, 0 ≤ d → d + 4 ≤ 24 → InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 d) 4 :=
    fun d _ h => ⟨⟨State.addr (s.gpr .r2), 24⟩, by rw [hwr]; simp, Offset.contains_base _ h (by omega)⟩
  rw [invertKey_eq]
  refine WP.seq (save_slots_ok hslots fit2 hinS ?_)
  have hf₁ : Frame [⟨State.addr (s.gpr .r2), 24⟩] s.mem
      (saveMem s.mem (State.addr (s.gpr .r2)) s.gpr invSaved) :=
    saveMem_frame _ _ _ (by decide) _ (by decide)
  have hsv₁ := saveMem_saved (State.addr (s.gpr .r2)) s.gpr s.mem invSaved hslots
  generalize saveMem s.mem (State.addr (s.gpr .r2)) s.gpr invSaved = M₁ at hf₁ hsv₁
  let s₁ : State := { s with mem := M₁ }
  obtain ⟨s₂, h₂, m₂, e₂⟩ := setMask_run s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have g₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => e₂.reg r (by simpa using hr)
  have mem₂ : s₂.mem = M₁ := e₂.mem
  have hp : InvPre s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, m₂⟩
    · rw [g₂ _ (by decide), e₂.rd, e₂.wr]; show _ ∈ s.rd ++ s.wr; rw [hrd]; simp
    · rw [g₂ _ (by decide), e₂.wr]; show _ ∈ s.wr; rw [hwr]; simp
    · rw [g₂ _ (by decide), g₂ _ (by decide)]; exact dSO
    · rw [g₂ _ (by decide)]; exact fit0
    · rw [g₂ _ (by decide)]; exact fit1
  have sched₂ : Spec.Idea.scheduleAt s₂.mem (State.addr (s₂.gpr .r0)) =
      Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
    rw [mem₂, g₂ _ (by decide)]
    exact scheduleAt_congr (frame_bytes hf₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact dSS) (by decide))
  refine WP.seq (WP.mono (pairs_ok s₂ hp 26 0 rfl s₂ ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩,
    Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun t ht => ?_)
  -- Restoring the registers.
  have r2t : t.gpr .r2 = s.gpr .r2 := (ht.keep.reg .r2 (by decide)).trans (g₂ _ (by decide))
  have hsv : Saved t.mem (State.addr (t.gpr .r2)) s.gpr invSaved := by
    rw [r2t]
    refine hsv₁.frame hslots (mem₂ ▸ ht.frame) fun q hq => ?_
    simp only [List.mem_singleton] at hq; subst hq
    rw [BitVec.add_zero, g₂ _ (by decide)]
    exact dOS.symm.sub_right (Region.sub_prefix (by omega))
  have hin : ∀ d, 0 ≤ d → d + 4 ≤ 24 →
      InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r2) + BitVec.ofNat 64 d) 4 := fun d h0 h => by
    obtain ⟨R, hR, hc⟩ := hinS d h0 h
    rw [ht.keep.rd, ht.keep.wr, e₂.rd, e₂.wr, r2t]
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  refine WP.mono (restore_block_ok hslots (by decide) (by rw [r2t]; exact fit2) hin hsv)
    fun u hu' => ?_
  obtain ⟨hu, ho, hm, -⟩ := hu'
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu (.r4, 0) (by decide)
    · exact hu (.r5, 4) (by decide)
    · exact hu (.r6, 8) (by decide)
    · exact hu (.r7, 12) (by decide)
    · exact hu (.r8, 16) (by decide)
    · exact hu (.r9, 20) (by decide)
    all_goals rw [ho _ (by decide), ht.keep.reg _ (by decide), g₂ _ (by decide)]
  · show Spec.Idea.scheduleAt u.mem _ = _
    rw [hm, ← g₂ .r1 (by decide), ← sched₂]
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [scheduleAt_getLsbD32 _ _ hn hb, ht.words (n / 2) (by omega) _ (by omega),
      show 2 * (n / 2) + (16 * (n % 2) + b) / 16 = n by omega,
      show (16 * (n % 2) + b) % 16 = b by omega]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := invert_wp s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he⟩, hp⟩

def invertSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩, ⟨0x3000, 24⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 := by
  simp [PublicRegs]

theorem invertKey_verified : Verified target invertKey (Proof.Idea.invertKeyScratchContract32 abi 6) := by
  refine Verified.of_correct invert_correct (invertKey_constantTime _) ?_
  sig_implies [Proof.Idea.invertKeyScratchContract32, Proof.Idea.invertKeyScratchSig32,
    Spec.Idea.invertKeyPost, abi, argRegs, reduceClassify, Loc.val, State.addr, invertContract,
    publicRegs_three] [invertSat] using invertSat

end VG.Proof.Idea.Arm
