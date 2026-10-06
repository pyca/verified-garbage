import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# The AEADs on x86-64: masking the data (`maskTail`)

Untrusted: everything here is checked by Lean. `maskTail` ANDs the `n`
bytes at `D` (in `r12`) with the mask `0 − ok` in `r11`, for `ok` 1 or 0
(`c`): the data stays if `c`, and is zeroed if not (`maskTail_wp`). Its
whole blocks go 16 bytes at a time, with the mask in both halves of `xmm0`
(`maskBlocks_wp`), the rest one at a time (`maskBytes_wp`); both loops keep
the first `j` bytes masked (`MInv`).
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
    execAlu, State.load64, State.store64, State.load8, State.store8, State.load128, State.store128, XOp.exec,
    State.ea, imm, maskByte, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, zf_setReg, zf_arithFlags, gpr_setXmm,
    mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm, xmm_setReg, xmm_arithFlags, ite_true, ite_false, reduceCtorEq,
    ↓reduceIte, $ts,*]) <;> try rfl)

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

/-- `0 − ok` in both halves of an SSE register. -/
def maskV (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

theorem maskV_eq (c : Bool) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ ((0 : BitVec 64) - (if c then 1 else 0)))
      ((0 : BitVec 64) ++ ((0 : BitVec 64) - (if c then 1 else 0))) = maskV c := by
  cases c <;> decide

theorem mask_block (v : BitVec 128) (c : Bool) : XBinOp.eval .pand v (maskV c) = if c then v else 0 := by
  cases c
  · simp [maskV, XBinOp.eval]
  · simp only [maskV, XBinOp.eval, ite_true, BitVec.and_allOnes]

theorem xmm_setXmm' (s : State) (r : XReg) (v : BitVec 128) (r' : XReg) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

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

theorem maskBlockStep_ok (s : State) {P : Addr} {j w : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (hx0 : s.xmm .xmm0 = maskV c)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 16) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm1 maskByte, .xop (.bin .pand .xmm1 .xmm0), .movdquStore maskByte .xmm1,
        .alu .add .r10 (imm 16), .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (if c then s.mem.readW (P + BitVec.ofNat 64 j) 128 else (0 : BitVec 128)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 16 ∧ s'.gpr .rcx = BitVec.ofNat 64 w - 1 ∧
      s'.zf = some (BitVec.ofNat 64 w - 1 == 0) ∧ s'.xmm .xmm0 = s.xmm .xmm0 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by mrun [ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', ite_true, ite_false, reduceCtorEq, hx0,
      mask_block]
  · simp [gpr_setReg, gpr_setXmm, h10]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm', reduceCtorEq, ite_false]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, gpr_setXmm, h₁, h₂, h₃]
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

/-- A block written is its 16 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 128) :
    m.writeW a v = writeBytes m a ((List.range 16).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 16 v

/-- The block at `a`, or zero, written back: the 16 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 128 else (0 : BitVec 128)) =
      writeBytes m' a (if c then bytesAt m a 16 else List.replicate 16 0) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 16) hk]
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
    (hj : j + 16 < 2 ^ 64) : t.mem.readW (D + BitVec.ofNat 64 j) 128 = s.mem.readW (D + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  simp only [Offset.add_add]
  exact h.at (by omega) (by omega)

/-- The blocks: from `j = 16 i`, with `⌊n / 16⌋ − i` blocks left in `rcx`
and the mask in `xmm0`, to `16 ⌊n / 16⌋`. -/
theorem maskBlocks_wp {s t : State} {D : Addr} {n : Nat} {c : Bool} {i : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr) (h12 : s.gpr .r12 = D)
    (hi : i < n / 16) (ht : MInv s t D c (16 * i)) (hcx : t.gpr .rcx = BitVec.ofNat 64 (n / 16 - i))
    (hx0 : t.xmm .xmm0 = maskV c) :
    WP isa maskBlocks t fun t' => MInv s t' D c (16 * (n / 16)) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n / 16 - i ∧ i < n / 16 ∧ MInv s t D c (16 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (n / 16 - i) ∧ t.xmm .xmm0 = maskV c) ?_ (n / 16 - i) t
    ⟨i, rfl, hi, ht, hcx, hx0⟩
  rintro k t ⟨i, rfl, hi, ht, hcx, hx0⟩
  have hin : 16 * i + 16 ≤ n := by omega
  have cov (rs : List Region) (h : Covers [⟨D, n⟩] rs) : InRegions rs (D + BitVec.ofNat 64 (16 * i)) 16 :=
    h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hin (by omega)⟩
  obtain ⟨t', run', mem', r10', rcx', zf', x0', g', rd', wr'⟩ := maskBlockStep_ok t (P := D) (j := 16 * i)
    (w := n / 16 - i) (c := c) (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10 hx0 hcx
    (by rw [ht.rd, ht.wr]; exact cov _ hD) (by rw [ht.wr]; exact cov _ hDw)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (masked s.mem D c (16 * (i + 1))) := by
    rw [mem', ht.readW (by omega), ht.mem, writeW_mask, show 16 * (i + 1) = 16 * i + 16 by omega, masked_add,
      ← writeBytes_append _ _ _ _ (by
        rw [length_masked, show (if c then bytesAt s.mem (D + BitVec.ofNat 64 (16 * i)) 16 else
          List.replicate 16 0).length = 16 by cases c <;> simp [Proof.Cmac.bytesAt_length]]; omega), length_masked]
  have hsub : BitVec.ofNat 64 (n / 16 - i) - 1 = BitVec.ofNat 64 (n / 16 - (i + 1)) := by
    rw [show n / 16 - i = (n / 16 - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]
  have hcx' : t'.gpr .rcx = BitVec.ofNat 64 (n / 16 - (i + 1)) := by rw [rcx', hsub]
  have hz : t'.zf = some (decide (i + 1 = n / 16)) := by
    rw [zf', hsub]
    by_cases he : i + 1 = n / 16
    · rw [he, Nat.sub_self]; simp
    · have : BitVec.ofNat 64 (n / 16 - (i + 1)) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this]; simp [he]
  have ht' : MInv s t' D c (16 * (i + 1)) :=
    ⟨by rw [r10', show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = n / 16
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n / 16 - (i + 1), by omega, i + 1, rfl, by omega, ht', hcx',
      by rw [x0', hx0]⟩
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
    exact ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, ht'⟩

theorem ofNat_shr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- `maskTail`, from the state `s` its first block leaves: the data masked,
and the registers but `rax`, `r10` and `rcx` as they were. -/
theorem maskTail_wp {s : State} {D : Addr} {n : Nat} {c : Bool} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s.gpr .r12 = D) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (n / 16))
    (hzf : s.zf = some (decide (n / 16 = 0))) :
    WP isa maskTail s fun t => MInv s t D c n := by
  have inv₀ : MInv s s D c 0 :=
    ⟨h10, by cases c <;> simp [masked, bytesAt, writeBytes_nil], fun _ _ _ _ => rfl, rfl, rfl⟩
  have words : WP isa (.ite .e (.block []) (.seq (.block maskX) maskBlocks)) s
      fun t => MInv s t D c (16 * (n / 16)) := by
    refine WP.ite (decide (n / 16 = 0)) hzf (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₀
    · obtain ⟨s₁, run₁, x0₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa maskX s = some s₁ ∧
          s₁.xmm .xmm0 = maskV c ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
        refine ⟨_, by mrun [maskX], ?_, ?_, ?_, ?_, ?_⟩
        · simp only [xmm_setXmm', ite_true, h11]; exact maskV_eq c
        all_goals rfl
      refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
      exact maskBlocks_wp hn hD hDw h12 (Nat.pos_of_ne_zero (of_decide_eq_false hb))
        ⟨by rw [g₁, h10], by rw [m₁]; simpa using inv₀.mem, fun r _ _ _ => by rw [g₁], rd₁, wr₁⟩
        (by rw [g₁, hcx, Nat.sub_zero]) x0₁
  refine WP.seq (WP.mono words fun t ht => ?_)
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.alu .cmp .r10 (.reg .rbp)] t = some t₁ ∧
      t₁.zf = some (decide (16 * (n / 16) = n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by mrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, ht.r10, ht.keep .rbp (by decide) (by decide) (by decide), hbp]
      rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    all_goals rfl
  have ht₁ : MInv s t₁ D c (16 * (n / 16)) :=
    ⟨by rw [g₁, ht.r10], by rw [m₁, ht.mem], fun r h₁ h₂ h₃ => by rw [g₁, ht.keep r h₁ h₂ h₃],
      by rw [rd₁, ht.rd], by rw [wr₁, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (16 * (n / 16) = n)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [← of_decide_eq_true hb]; exact ht₁
  · exact maskBytes_wp hn hD hDw h12 h11 hbp (by have := of_decide_eq_false hb; omega) ht₁

end VG.Proof.AesGcm.X86_64
