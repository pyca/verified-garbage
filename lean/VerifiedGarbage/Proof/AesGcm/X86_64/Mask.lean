import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# The AEADs on x86-64: masking the data (`maskTail`)

Untrusted: everything here is checked by Lean. `maskTail` ANDs the `n`
bytes at `D` (in `r12`) with the mask `0 − ok` in `r11`, for `ok` 1 or 0
(`c`): the data stays if `c`, and is zeroed if not (`maskTail_wp`). Its
whole words go 8 bytes at a time (`maskWords_wp`), the rest one at a time
(`maskBytes_wp`); both loops keep the first `j` bytes masked (`MInv`).
AES-CCM and AES-GCM-SIV share it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)

/-- Runs a block of the masking loops. -/
macro "mrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.load64, State.store64, State.load8, State.store8, State.ea, imm, maskByte, Option.bind_some,
    Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
    wr_arithFlags, zf_setReg, zf_arithFlags, ite_true, ite_false, reduceCtorEq, ↓reduceIte, $ts,*]) <;> try rfl)

/-- The data masked: itself if `c`, zeros if not. -/
abbrev masked (m : Mem) (D : Addr) (c : Bool) (j : Nat) : List Byte :=
  if c then bytesAt m D j else List.replicate j 0

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem mask_word (v : BitVec 64) (c : Bool) :
    v &&& ((0 : BitVec 64) - (if c then 1 else 0)) = if c then v else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskByteStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s.gpr .rbp = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rbp)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by mrun [ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, hbp]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem maskWordStep_ok (s : State) {P : Addr} {j w : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hcx : s.gpr .rcx = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 8) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem maskByte), .alu .and .rax (.reg .r11), .store maskByte .rax,
        .alu .add .r10 (imm 8), .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (if c then s.mem.readW (P + BitVec.ofNat 64 j) 64 else (0 : BitVec 64)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 8 ∧ s'.gpr .rcx = BitVec.ofNat 64 w - 1 ∧
      s'.zf = some (BitVec.ofNat 64 w - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by mrun [ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h11,
      mask_word]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, hcx]
  · simp [gpr_setReg, hcx]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

theorem length_masked (m : Mem) (P : Addr) (c : Bool) (j : Nat) : (masked m P c j).length = j := by
  cases c <;> simp [masked, Proof.Cmac.bytesAt_length]

theorem masked_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    masked m P c (j + 1) = masked m P c j ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [masked, bytesAt_succ, List.replicate_succ']

theorem masked_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    masked m P c (a + b) = masked m P c a ++
      (if c then bytesAt m (P + BitVec.ofNat 64 a) b else List.replicate b 0) := by
  cases c <;> simp [masked, bytesAt_append, ← List.replicate_append_replicate]

/-- A word written is its 8 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 64) :
    m.writeW a v = writeBytes m a ((List.range 8).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 8 v

/-- The word at `a`, or zero, written back: the 8 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 64 else (0 : BitVec 64)) =
      writeBytes m' a (if c then bytesAt m a 8 else List.replicate 8 0) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 8) hk]
    rfl

/-- What both loops keep: the first `j` bytes of the data masked, from `s`. -/
structure MInv (s t : State) (D : Addr) (c : Bool) (j : Nat) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem D (masked s.mem D c j)
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {s t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s t D c j) :
    Frame [⟨D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_masked]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {s t : State} {D : Addr} {c : Bool} {j i : Nat} (h : MInv s t D c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) :=
  (h.frame (D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat D hi'] at hcon; omega)

theorem MInv.readW {s t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s t D c j)
    (hj : j + 8 < 2 ^ 64) : t.mem.readW (D + BitVec.ofNat 64 j) 64 = s.mem.readW (D + BitVec.ofNat 64 j) 64 := by
  refine Mem.readW_congr fun k hk => ?_
  simp only [Offset.add_add]
  exact h.at (by omega) (by omega)

/-- The words: from `j = 8 i`, with `⌊n / 8⌋ − i` words left in `rcx`, to `8 ⌊n / 8⌋`. -/
theorem maskWords_wp {s t : State} {D : Addr} {n : Nat} {c : Bool} {i : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s.gpr .r12 = D) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hi : i < n / 8) (ht : MInv s t D c (8 * i)) (hcx : t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) :
    WP isa maskWords t fun t' => MInv s t' D c (8 * (n / 8)) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n / 8 - i ∧ i < n / 8 ∧ MInv s t D c (8 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) ?_ (n / 8 - i) t ⟨i, rfl, hi, ht, hcx⟩
  rintro k t ⟨i, rfl, hi, ht, hcx⟩
  have hin : 8 * i + 8 ≤ n := by omega
  have cov (rs : List Region) (h : Covers [⟨D, n⟩] rs) : InRegions rs (D + BitVec.ofNat 64 (8 * i)) 8 :=
    h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hin (by omega)⟩
  obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := maskWordStep_ok t (P := D) (j := 8 * i)
    (w := n / 8 - i) (c := c) (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11]) hcx
    (by rw [ht.rd, ht.wr]; exact cov _ hD) (by rw [ht.wr]; exact cov _ hDw)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (masked s.mem D c (8 * (i + 1))) := by
    rw [mem', ht.readW (by omega), ht.mem, writeW_mask, show 8 * (i + 1) = 8 * i + 8 by omega, masked_add,
      ← writeBytes_append _ _ _ _ (by
        rw [length_masked, show (if c then bytesAt s.mem (D + BitVec.ofNat 64 (8 * i)) 8 else List.replicate 8 0).length
          = 8 by cases c <;> simp [Proof.Cmac.bytesAt_length]]; omega), length_masked]
  have hcx' : t'.gpr .rcx = BitVec.ofNat 64 (n / 8 - (i + 1)) := by
    rw [rcx', show n / 8 - i = (n / 8 - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]
  have hz : t'.zf = some (decide (i + 1 = n / 8)) := by
    rw [zf', show BitVec.ofNat 64 (n / 8 - i) - 1 = BitVec.ofNat 64 (n / 8 - (i + 1)) by
      rw [show n / 8 - i = (n / 8 - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]]
    by_cases he : i + 1 = n / 8
    · rw [he, Nat.sub_self]; simp
    · have : BitVec.ofNat 64 (n / 8 - (i + 1)) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this]; simp [he]
  have ht' : MInv s t' D c (8 * (i + 1)) :=
    ⟨by rw [r10', show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = n / 8
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n / 8 - (i + 1), by omega, i + 1, rfl, by omega, ht', hcx'⟩
where
  eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
    show s.zf.map _ = _; rw [h]; rfl

/-- The last bytes: from `j < n` to `n`. -/
theorem maskBytes_wp {s t : State} {D : Addr} {n : Nat} {c : Bool} {j : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s.gpr .r12 = D) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (hj : j < n) (ht : MInv s t D c j) :
    WP isa maskBytes t fun t' => MInv s t' D c n := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ MInv s t D c j) ?_ (n - j) t ⟨j, rfl, hj, ht⟩
  rintro k t ⟨j, rfl, hj, ht⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskByteStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11])
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hbp]) (by rw [ht.rd, ht.wr]; exact in_of_covers hD hj hn)
    (by rw [ht.wr]; exact in_of_covers hDw hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (masked s.mem D c (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega), ht.mem, masked_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_masked]; omega), length_masked]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have ht' : MInv s t' D c (j + 1) :=
    ⟨by rw [r10', succ_ofNat], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨(maskWords_wp.eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(maskWords_wp.eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, ht'⟩

theorem ofNat_shr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- `maskTail`, from the state `s` its first block leaves: the data masked,
and the registers but `rax`, `r10` and `rcx` as they were. -/
theorem maskTail_wp {s : State} {D : Addr} {n : Nat} {c : Bool} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s.gpr .r12 = D) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (n / 8))
    (hzf : s.zf = some (decide (n / 8 = 0))) :
    WP isa maskTail s fun t => MInv s t D c n := by
  have inv₀ : MInv s s D c 0 :=
    ⟨h10, by cases c <;> simp [masked, bytesAt, writeBytes_nil], fun _ _ _ _ => rfl, rfl, rfl⟩
  have words : WP isa (.ite .e (.block []) maskWords) s fun t => MInv s t D c (8 * (n / 8)) := by
    refine WP.ite (decide (n / 8 = 0)) hzf (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₀
    · exact maskWords_wp hn hD hDw h12 h11 (Nat.pos_of_ne_zero (of_decide_eq_false hb))
        (by simpa using inv₀) (by rw [hcx, Nat.sub_zero])
  refine WP.seq (WP.mono words fun t ht => ?_)
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.alu .cmp .r10 (.reg .rbp)] t = some t₁ ∧
      t₁.zf = some (decide (8 * (n / 8) = n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by mrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, ht.r10, ht.keep .rbp (by decide) (by decide) (by decide), hbp]
      rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    all_goals rfl
  have ht₁ : MInv s t₁ D c (8 * (n / 8)) :=
    ⟨by rw [g₁, ht.r10], by rw [m₁, ht.mem], fun r h₁ h₂ h₃ => by rw [g₁, ht.keep r h₁ h₂ h₃],
      by rw [rd₁, ht.rd], by rw [wr₁, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (8 * (n / 8) = n)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [← of_decide_eq_true hb]; exact ht₁
  · exact maskBytes_wp hn hD hDw h12 h11 hbp (by have := of_decide_eq_false hb; omega) ht₁

end VG.Proof.AesGcm.X86_64
