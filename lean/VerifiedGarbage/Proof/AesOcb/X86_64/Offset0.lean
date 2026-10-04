import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
import VerifiedGarbage.Proof.Ocb.Stretch

/-!
# AES-OCB on x86-64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf ror_mask sel_mask shl3 bit_bottom)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt)

theorem sel_mask' (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b then 1 else 0))) = if b then x' else x := sel_mask x x' b

theorem bit_bottom0 {v : Nat} (hv : v < 64) :
    BitVec.ofNat 64 v &&& BitVec.signExtend 64 (1 : BitVec 32) = if v.testBit 0 then 1 else 0 := by
  have := bit_bottom hv 0
  rwa [BitVec.ushiftRight_zero] at this

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .rax ++ s'.gpr .rdx ++ s'.gpr .rcx = shlIf (v.testBit k) a (s.gpr .rax ++ s.gpr .rdx ++ s.gpr .rcx) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hm : 0#64 - ((BitVec.ofNat 64 v >>> k) &&& BitVec.signExtend 64 (1 : BitVec 32)) =
      0#64 - (if v.testBit k then 1 else 0) := by rw [bit_bottom hv]
  have c1 : 1 ≤ 64 - a ∧ 64 - a ≤ 63 := ⟨by omega, by omega⟩
  by_cases hk : k = 0
  · subst hk
    refine ⟨_, by orun [stage, hbx, c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, bit_bottom0 hv, ror_mask _ ha ha', sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl
  · have ck : 1 ≤ k ∧ k ≤ 63 := ⟨by omega, by omega⟩
    refine ⟨_, by orun [stage, hbx, hk, c1, ck, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, hm, ror_mask _ ha ha', sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]

/-- `Stretch` shifted left by `bottom`: its top 128 bits are `Offset_0`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {v : Nat} (hv : v < 64)
    (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      Off0Post W ((stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  have h15 := E.r15
  simp only [botO] at hbot
  -- `Stretch` in three words
  obtain ⟨s₁, run₁, w₁, rbx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .rax .r15 tmpO, .bswap .rax, ld .rdx .r15 (tmpO + 8), .bswap .rdx,
       mvr .rcx .rax, .shift .ror .rcx 56, .movImm64 .r8 (BitVec.allOnes 64 <<< 8),
       .alu .and .rcx (.reg .r8), mvr .r8 .rdx, .shift .shr .r8 56, .alu .or .rcx (.reg .r8),
       .alu .xor .rcx (.reg .rax), ld .rbx .r15 botO] s = some s₁ ∧
      s₁.gpr .rax ++ s₁.gpr .rdx ++ s₁.gpr .rcx = stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .rbx = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have r₀ := E.perm.wR (show 112 + 8 ≤ 2560 by decide)
    have r₁ := E.perm.wR (show 120 + 8 ≤ 2560 by decide)
    have r₂ := E.perm.wR (show 256 + 8 ≤ 2560 by decide)
    have rm := ror_mask (bswap64 (s.mem.readW (W + BitVec.ofNat 64 112) 64)) (a := 8) (by decide) (by decide)
    simp only [show 64 - 8 = 56 from rfl] at rm
    refine ⟨_, by orun [h15, r₀, r₁, r₂, hbot], ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rm]
      have hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          bswap64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ bswap64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.X86_64.blockAt_bswap s.mem (W + BitVec.ofNat 64 112)
        rw [show W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 112 from BitVec.add_zero _,
          Offset.add_add] at this
        exact this.symm
      rw [stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbot]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, ite_false]
    all_goals rfl
  -- the six stages
  have keep : ∀ {t t' : State}, (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      t'.gpr r = t.gpr r) → t.gpr .rbx = BitVec.ofNat 64 v → t'.gpr .rbx = BitVec.ofNat 64 v := fun g h => by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, rd₂, wr₂⟩ := stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv rbx₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, rd₃, wr₃⟩ := stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (keep g₂ rbx₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, rd₄, wr₄⟩ := stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep g₃ (keep g₂ rbx₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, rd₅, wr₅⟩ := stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep g₄ (keep g₃ (keep g₂ rbx₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, rd₆, wr₆⟩ := stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ rbx₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, rd₇, wr₇⟩ := stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ rbx₁)))))
  have hw : s₇.gpr .rax ++ s₇.gpr .rdx ++ s₇.gpr .rcx =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .rax ++ s₇.gpr .rdx =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .rcx), hw, Proof.Ocb.offset_shl _ (by omega)]
  -- the stores
  have hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have h15₇ : s₇.gpr .r15 = W := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h15]
  have w₁₆ : InRegions s₇.wr (W + BitVec.ofNat 64 16) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₄ : InRegions s₇.wr (W + BitVec.ofNat 64 24) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₇₂ : InRegions s₇.wr (W + BitVec.ofNat 64 272) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₈₀ : InRegions s₇.wr (W + BitVec.ofNat 64 280) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.bswap .rax, .bswap .rdx, st .r15 ofsO .rax,
      st .r15 (ofsO + 8) .rdx, st .r15 o0O .rax, st .r15 (o0O + 8) .rdx] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (bswap64 (s₇.gpr .rax))).writeW (W + BitVec.ofNat 64 24)
        (bswap64 (s₇.gpr .rdx))).writeW (W + BitVec.ofNat 64 272) (bswap64 (s₇.gpr .rax))).writeW
        (W + BitVec.ofNat 64 280) (bswap64 (s₇.gpr .rdx)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [h15₇, w₁₆, w₂₄, w₂₇₂, w₂₈₀], ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, h1, h2, ite_false]
    all_goals rfl
  have val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (bswap64 (s₇.gpr .rax)) ++ Proof.Cmac.le8 (bswap64 (s₇.gpr .rdx))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.CmacAes.X86_64.le8_bswap, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  have run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  have f272 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 272, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 272) (bswap64 (s₇.gpr .rax))).writeW (W + BitVec.ofNat 64 280)
        (bswap64 (s₇.gpr .rdx))) := fun M => by
    rw [← addr8 W 272]; exact frame_store2 _ _ _ _
  refine ⟨s₈, run, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 272) (k := 16) (d := 280) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, blockAtMem]
    rw [Proof.AesCcm.X86_64.bytesAt_frame (f272 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 272) (k := 16) (.inl (by decide)) (by decide) (by decide)) (by decide)]
    rw [← blockAtMem, show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 272) = _
    rw [m₈, show W + BitVec.ofNat 64 280 = W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8 from (addr8 W 272).symm,
      blockAtMem_store2, val]
  · rw [g₈ r h1 h2, g₇ r h1 h2 h3 h5 h6 h7 h8, g₆ r h1 h2 h3 h5 h6 h7 h8, g₅ r h1 h2 h3 h5 h6 h7 h8,
      g₄ r h1 h2 h3 h5 h6 h7 h8, g₃ r h1 h2 h3 h5 h6 h7 h8, g₂ r h1 h2 h3 h5 h6 h7 h8, g₁ r h1 h2 h3 h4 h5]
