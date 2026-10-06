import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Spec
import VerifiedGarbage.Impl.Sha1.X86.ShaNi

/-!
# SHA-1 with the SHA extensions on x86: the 80 rounds of a block

The rounds of `Impl.Sha1.X86.ShaNi`, which are those of x86-64
(`Proof/Sha1/X86_64/ShaNi/Compress.lean`) but for the registers holding the
block pointer: rounds `0 … 4n-1` from `ABCD` in `xmm0` and `E` in `xmm1`
compute the specification's rounds, keeping the last sixteen schedule words.
-/

namespace VG.Proof.Sha1.X86.ShaNi

open VG VG.X86 VG.Impl.Sha1.X86.ShaNi
open VG.Spec.Sha1 (HashValue Word Block W)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The registers of a group of four rounds are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem msg_other (n : Nat) (r : XReg)
    (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

/-- `msg k` for the three registers other than `msg n` that hold schedule words. -/
theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

/-! ## Four rounds -/

theorem rounds4_ok (n : Nat) (s : State) (a x q : BitVec 128)
    (h0 : s.xmm .xmm0 = a) (h1 : s.xmm .xmm1 = x) (hq : s.xmm (msg n) = q) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = sha1Rnds4 a (XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x q)
        (BitVec.ofNat 8 (n / 5)) ∧
      s'.xmm .xmm1 = a ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4]
  generalize msg n = y at *
  generalize (if n = 0 then XBinOp.paddd else XBinOp.sha1nexte) = op
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, reduceCtorEq, hd, h0, h1, hq,
    eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, not_false_eq_true]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 2)) = c)
    (hd' : s.xmm (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = sha1Msg2 (XBinOp.eval .pxor (XBinOp.eval .sha1msg1 a b) c) d ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 4 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, hd'', ha, hb, hc, hd',
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r h0 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, not_false_eq_true]

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * n)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (addr (s.gpr .ecx) (16 * n)) 128) (s.xmm .xmm7) ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h7 := (msg_other n .xmm7 (.inr (.inr (.inr rfl)))).symm
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, State.load128, ea_at, hin,
    h7, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h0 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, not_false_eq_true]

/-- What `xmm1` holds before rounds `4n …`: for `n = 0`, `E` and zeros; after
that, `ABCD` of four rounds before, whose `A` rotated left by 30 is `E`. -/
def ECarry (n : Nat) (v : HashValue) (x : BitVec 128) : Prop :=
  if n = 0 then x = eReg v else (dword x 3).rotateLeft 30 = v[4]

/-- The value added to rounds `4n … 4n+3`: `W₄ₙ + E`, then `W₄ₙ₊₁ … W₄ₙ₊₃`. -/
theorem wk_eq (M : Block) (n : Nat) (v : HashValue) (x : BitVec 128) (hx : ECarry n v x) :
    XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x (quad M n) =
      ofDwords (W M (4 * n + 3)) (W M (4 * n + 2)) (W M (4 * n + 1)) (W M (4 * n) + v[4]) := by
  by_cases h : n = 0
  · subst h
    simp only [ECarry, ite_true] at hx
    simp only [ite_true, hx, paddd_e]
  · simp only [ECarry, h, ite_false] at hx
    simp only [h, ite_false, nexte_e, hx]

theorem rounds_four (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) :
    Spec.Sha1.rounds H M (4 * (n + 1)) =
      hw4 (n / 5) (Spec.Sha1.rounds H M (4 * n)) (W M (4 * n)) (W M (4 * n + 1)) (W M (4 * n + 2))
        (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ,
    round_hw _ _ (by omega), round_hw _ _ (by omega), round_hw _ _ (by omega), round_hw _ _ (by omega),
    show (4 * n) / 20 = n / 5 by omega, show (4 * n + 1) / 20 = n / 5 by omega,
    show (4 * n + 2) / 20 = n / 5 by omega, show (4 * n + 3) / 20 = n / 5 by omega]
  rfl

theorem rounds4_step (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) (s : State)
    (h0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n)))
    (h1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)) (hq : s.xmm (msg n) = quad M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * (n + 1))) ∧
      ECarry (n + 1) (Spec.Sha1.rounds H M (4 * (n + 1))) (s'.xmm .xmm1) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ _ h0 rfl hq) fun s' ⟨e0, e1, hx, hg, hm, hrd, hwr⟩ => ?_
  rw [wk_eq M n _ _ h1, rnds4_eq _ (by omega)] at e0
  refine ⟨by rw [e0, rounds_four H M hn], ?_, hx, hg, hm, hrd, hwr⟩
  simp only [ECarry, Nat.add_one_ne_zero, ite_false, e1, abcd, dword_ofDwords_3]
  rw [rounds_four H M hn, hw4_e]

/-! ## Loading the message words -/

theorem getLsbD_bswap_block' (x : BitVec 32) {j r : Nat} (hj : j < 4) (hr : r < 8) :
    (bswap x).getLsbD (8 * j + r) = x.getLsbD (8 * (3 - j) + r) := by
  rw [getLsbD_bswap_block x hj hr]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
  simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, Nat.zero_add] <;>
  exact congrArg _ (by omega)

/-- Reversing the bytes of a register reverses the order of its doublewords
and the bytes of each. -/
theorem pshufb_rev (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask =
      ofDwords (bswap (dword a 3)) (bswap (dword a 2)) (bswap (dword a 1)) (bswap (dword a 0)) := by
  have hb : XBinOp.eval .pshufb a bswapMask = ofBytes fun j => byte a (15 - j) := by
    simp only [XBinOp.eval, ofBytes, bswapMask]
    rfl
  rw [hb]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
  have hm := Nat.mod_lt k (by decide : 4 > 0)
  rcases (by omega : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3) with h | h | h | h <;>
  simp only [h, ↓reduceIte, Nat.reduceEqDiff] <;>
  rw [getLsbD_bswap_block' _ hm hr] <;>
  simp only [byte, dword, BitVec.getLsbD_extractLsb', decide_eq_true hr,
    decide_eq_true (show 8 * (3 - k % 4) + r < 32 by omega), Bool.true_and] <;>
  exact congrArg a.getLsbD (by omega)

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (bp : BitVec 32) (hfit : bp.toNat + 64 ≤ 2 ^ 32)
    {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap (m.readW (addr bp (4 * t)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (addr bp (16 * n)) 128) bswapMask = quad M n := by
  rw [pshufb_rev]
  have e : ∀ j, j < 4 → bswap (dword (m.readW (addr bp (16 * n)) 128) j) = W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega)]
    refine congrArg (fun a => bswap (m.readW a 32)) ?_
    rw [addr_eq (by omega), addr_eq (by omega), Offset.add_ofNat_add_ofNat,
      show 16 * n + 4 * j = 4 * (4 * n + j) by omega]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rfl

/-! ## The rounds -/

/-- What holds after rounds `0 … 4n-1` of a block `M`, from the state `sB` at its start. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n))
  x1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad M k
  x7 : s.xmm .xmm7 = sB.xmm .xmm7
  gpr : s.gpr = sB.gpr
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_ok (H : HashValue) (M : Block) (bp : BitVec 32) (sB : State)
    (hecx : sB.gpr .ecx = bp) (hfit : bp.toNat + 64 ≤ 2 ^ 32) (hmask : sB.xmm .xmm7 = bswapMask)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (addr bp (16 * n)) 16)
    (hblk : ∀ t : Nat, t < 16 → bswap (sB.mem.readW (addr bp (4 * t)) 32) = W M t)
    (h0 : sB.xmm .xmm0 = abcd H) (h1 : sB.xmm .xmm1 = eReg H) :
    ∀ n ≤ 20, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h0, by simp only [ECarry, ite_true]; exact h1,
      fun _ h => absurd h (by omega), rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_ecx : s.gpr .ecx = bp := by rw [hs.gpr, hecx]
    -- The schedule: `msg n` gets `quad M n`; nothing else changes.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad M n ∧ (∀ r, r ≠ msg n → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_ecx]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        rw [e, hs_ecx, hs.mem, hs.x7, hmask]
        exact load_quad M sB.mem bp hfit hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        refine WP.mono (schedule_hi (i + 4) (by omega) s (quad M i) (quad M (i + 1)) (quad M (i + 2))
          (quad M (i + 3)) ?_ ?_ ?_ ?_) fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [msg_add4]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 4 + 1 = i + 1 + 4 by omega, msg_add4]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 4 + 2 = i + 2 + 4 by omega, msg_add4]; exact hs.msgs (i + 2) (by omega) (by omega)
        · rw [show i + 4 + 3 = i + 3 + 4 by omega, msg_add4]; exact hs.msgs (i + 3) (by omega) (by omega)
        · rw [e]; exact schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o0 := msg_other n .xmm0 (.inl rfl)
    have o1 := msg_other n .xmm1 (.inr (.inl rfl))
    have o7 := msg_other n .xmm7 (.inr (.inr (.inr rfl)))
    refine WP.mono (rounds4_step H M (n := n) (by omega) s₁ (by rw [hx₁ _ (Ne.symm o0)]; exact hs.x0)
      (by rw [hx₁ _ (Ne.symm o1)]; exact hs.x1) hq)
      fun s₂ ⟨e0, e1, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e0, e1, fun k hk hk' => ?_, ?_, by rw [hg₂, hg₁, hs.gpr], by rw [hm₂, hm₁, hs.mem],
      by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · rw [hx₂ _ (msg_other k _ (.inl rfl)) (msg_other k _ (.inr (.inl rfl)))
        (msg_other k _ (.inr (.inr (.inl rfl))))]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega))]
        exact hs.msgs k (by omega) (by omega)
    · rw [hx₂ _ (by decide) (by decide) (by decide), hx₁ _ (Ne.symm o7)]
      exact hs.x7

end VG.Proof.Sha1.X86.ShaNi
