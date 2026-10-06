import VerifiedGarbage.Proof.AesSiv.X86_64.Seal

/-!
# AES-SIV on x86-64: the end of `vg_aes_siv_decrypt`

From S2V's state of the associated data on, `decrypt` sets the counter from
the IV it is given (`counter_ok`), decrypts the data in place with CTR
(`ctr_wp`), finishes S2V with the plaintext into `W + 112` (`finish_wp`),
compares the two IVs without a branch (`compare_ok`), ANDs the data with the
mask of the result, a word at a time and then its last bytes one at a time
(`maskData_wp`), and restores the registers (`openTail_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 succ_ofNat bytesAt_succ)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW W 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, le8_append_eq, Offset.add_add]

theorem compare_ok (h : Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .rax = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .r11 = 0 - s'.gpr .rax ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 dbOff) (s'.gpr .rax) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  have r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.AesSiv.X86_64.compare, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, execShift, State.load64, State.store64, State.ea,
      State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags,
      wr_setFlags, ite_true, ite_false, h15, r₀, r₁, r₂, r₃, w₀]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rw [show (1#32 : BitVec 32) = 1 from rfl, eqz, k0]
    simp only [ivs_eq]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rfl
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄]
  all_goals rfl

/-! ## Masking the data -/

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h13 : s.gpr .r13 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .r14)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp (config := {decide := true}) only [maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, ea, rq, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, h14]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- A word of the data ANDed with the mask in `r11`, at `P + j`; `rcx`, the
words left, one fewer (ZF set when none is). -/
theorem maskWord_ok (s : State) {P : Addr} {j n : Nat} {c : Bool} (h13 : s.gpr .r13 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 64)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 8) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem maskByte), .alu .and .rax (.reg .r11), .store maskByte .rax,
        .alu .add .r10 (imm 8), .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (s.mem.readW (P + BitVec.ofNat 64 j) 64 &&& (0 - if c then 1 else 0)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 (j + 8) ∧ s'.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      s'.zf = some (decide (n - 1 = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
      ea, rq, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11]
  · simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags, h10,
      sx_ofNat (show 8 < 2 ^ 31 by decide), BitVec.ofNat_add]
  · simp only [↓reduceIte, gpr_setReg, hrcx,
      sx_ofNat (show 1 < 2 ^ 31 by decide), Offset.ofNat_sub_ofNat hn]
  · simp only [zf_setReg, zf_arithFlags, hrcx, sx_ofNat (show 1 < 2 ^ 31 by decide),
      Offset.ofNat_sub_ofNat hn]
    rw [Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat (by omega)]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_length]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

/-- The next word, ANDed with the mask. -/
theorem mask_word (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 8) else Spec.Siv.zeros (j + 8)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++
        Proof.Cmac.le8 (m.readW (P + BitVec.ofNat 64 j) 64 &&& (0 - if c then 1 else 0)) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : BitVec 64) - 0 = 0 from rfl,
      show m.readW (P + BitVec.ofNat 64 j) 64 &&& 0 = 0 from BitVec.and_zero,
      show Proof.Cmac.le8 0 = Spec.Siv.zeros 8 by decide,
      Spec.Siv.zeros, Spec.Siv.zeros, Spec.Siv.zeros, ← List.replicate_append_replicate]
  · simp only [↓reduceIte]
    rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, Proof.Cmac.le8_readW,
      Proof.Cmac.Stream.bytesAt_append]

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW_le8 (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (Proof.Cmac.le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

theorem shr3 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 3 = BitVec.ofNat 64 (c / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- The data's words then bytes from `P + j` on, where those before are done. -/
structure MaskInv (s : State) (P : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (hwP : P.toNat + L ≤ 2 ^ 64)
    (h13 : s.gpr .r13 = P) (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hr : ∀ i n, i + n ≤ L → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) n)
    (hw : ∀ i n, i + n ≤ L → InRegions s.wr (P + BitVec.ofNat 64 i) n) :
    WP isa maskData s (Masked s P L c) := by
  have g13 {t : State} (ht : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t.gpr r = s.gpr r) : t.gpr .r13 = P := by
    rw [ht _ (by decide) (by decide) (by decide), h13]
  have g14 {t : State} (ht : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t.gpr r = s.gpr r) :
      t.gpr .r14 = BitVec.ofNat 64 L := by
    rw [ht _ (by decide) (by decide) (by decide), h14]
  have g11 {t : State} (ht : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t.gpr r = s.gpr r) :
      t.gpr .r11 = 0 - (if c then 1 else 0) := by
    rw [ht _ (by decide) (by decide) (by decide), h11]
  -- What the data before `P + j` is written to.
  have fP {t : State} {j : Nat}
      (hm : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)) :
      Frame [⟨P, j⟩] s.mem t.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain ⟨s₁, run₁, r10₁, rcx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0),
      .mov .rcx (.reg .r14), .shift .shr .rcx 3, .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (L / 8) ∧ s₁.zf = some (decide (L / 8 = 0)) ∧
      (∀ r, r ≠ .rcx → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, exec, readSrc, readSrc32, execShift, State.setReg32, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [reduceCtorEq, ↓reduceIte, gpr_arithFlags, gpr_setReg, gpr_setFlags]
      rfl
    · simp only [reduceCtorEq, ↓reduceIte, gpr_arithFlags, gpr_setReg, h14, shr3 hL]
    · simp only [reduceCtorEq, ↓reduceIte, zf_arithFlags, gpr_setReg, h14,
        shr3 hL, BitVec.and_self]
      rw [Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat (by omega)]
    · intro r h₁ h₂
      simp only [reduceCtorEq, ↓reduceIte, gpr_arithFlags, gpr_setReg, gpr_setFlags, h₁, h₂]
    all_goals simp only [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags,
      rd_setReg, rd_setFlags, wr_arithFlags, wr_setReg, wr_setFlags]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have inv₁ : MaskInv s P c 0 s₁ :=
    ⟨r10₁, by rw [m₁]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r _ h₂ h₃ => g₁ r h₂ h₃, rd₁, wr₁⟩
  -- The words.
  have words : WP isa (.ite .e (.block [])
      (.loop (.block [.mov .rax (.mem maskByte), .alu .and .rax (.reg .r11), .store maskByte .rax,
        .alu .add .r10 (imm 8), .alu .sub .rcx (imm 1)]) .ne)) s₁ (MaskInv s P c (8 * (L / 8))) := by
    refine WP.ite (decide (L / 8 = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₁
    have hn0 : L / 8 ≠ 0 := of_decide_eq_false hb
    refine WP.loop (M := isa) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ j, k = L / 8 - j ∧ j < L / 8 ∧ t.gpr .rcx = BitVec.ofNat 64 (L / 8 - j) ∧
        MaskInv s P c (8 * j) t) ?_ (L / 8 - 0) _ ⟨0, rfl, by omega, rcx₁, inv₁⟩
    rintro k t ⟨j, rfl, hj, rcx, it⟩
    obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := maskWord_ok t (P := P) (j := 8 * j)
      (n := L / 8 - j) (c := c) (g13 it.other) it.r10 (g11 it.other) rcx (by omega) (by omega)
      (by rw [it.rd, it.wr]; exact hr _ _ (by omega)) (by rw [it.wr]; exact hw _ _ (by omega))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen := length_mask s.mem P c (8 * j)
    have hmem : t'.mem = writeBytes s.mem P
        (if c then Spec.Aes.bytesAt s.mem P (8 * (j + 1)) else Spec.Siv.zeros (8 * (j + 1))) := by
      have hv : t.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 :=
        (fP it.mem).readW (w := 64) (Region.contains_self _ _) (fun r hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (Offset.base_disjoint P (e := 8 * j) (n := 8) (k := 8 * j) (by omega) (by omega)).symm) (by decide)
      have hwa := writeBytes_append s.mem P (if c then Spec.Aes.bytesAt s.mem P (8 * j) else Spec.Siv.zeros (8 * j))
        (Proof.Cmac.le8 (s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 &&& (0 - if c then 1 else 0)))
        (by rw [Proof.Cmac.length_le8, hlen]; omega)
      rw [hlen] at hwa
      rw [mem', hv, it.mem, writeW_le8, hwa, ← mask_word, show 8 * (j + 1) = 8 * j + 8 by omega]
    have gg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
      rw [g' r h₁ h₂ h₃, it.other r h₁ h₂ h₃]
    by_cases he : L / 8 - j - 1 = 0
    · left
      refine ⟨by simp [eval, zf', he], ⟨by rw [r10', show 8 * j + 8 = 8 * (L / 8) by omega], ?_, gg,
        by rw [rd', it.rd], by rw [wr', it.wr]⟩⟩
      rw [hmem, show j + 1 = L / 8 by omega]
    · right
      refine ⟨by simp [eval, zf', he], L / 8 - (j + 1), by omega, j + 1, rfl, by omega,
        by rw [rcx', show L / 8 - j - 1 = L / 8 - (j + 1) by omega],
        ⟨by rw [r10', show 8 * j + 8 = 8 * (j + 1) by omega], hmem, gg, by rw [rd', it.rd], by rw [wr', it.wr]⟩⟩
  refine WP.seq (WP.mono words fun t it => ?_)
  -- The bytes.
  have hj₀ : 8 * (L / 8) ≤ L := by omega
  obtain ⟨t₁, run₁', zf₁', g₁', m₁', rd₁', wr₁'⟩ : ∃ t₁, runBlock isa [.alu .cmp .r10 (.reg .r14)] t = some t₁ ∧
      t₁.zf = some (decide (8 * (L / 8) = L)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags, it.r10, g14 it.other, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    all_goals rfl
  have it₁ : MaskInv s P c (8 * (L / 8)) t₁ :=
    ⟨by rw [g₁', it.r10], by rw [m₁', it.mem], fun r h₁ h₂ h₃ => by rw [g₁', it.other r h₁ h₂ h₃],
      by rw [rd₁', it.rd], by rw [wr₁', it.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁', ?_⟩)
  refine WP.ite (decide (8 * (L / 8) = L)) zf₁' (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have he : 8 * (L / 8) = L := of_decide_eq_true hb
    rw [he] at it₁
    exact ⟨it₁.mem, it₁.other, it₁.rd, it₁.wr⟩
  have hlt₀ : 8 * (L / 8) < L := by have := of_decide_eq_false hb; omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ MaskInv s P c j t) ?_ (L - 8 * (L / 8)) _
    ⟨8 * (L / 8), rfl, hlt₀, it₁⟩
  rintro k t ⟨j, rfl, hj, it⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t (P := P) (j := j) (L := L) (c := c)
    (g13 it.other) it.r10 (g11 it.other) (g14 it.other) (by rw [it.rd, it.wr]; exact hr j 1 (by omega))
    (by rw [it.wr]; exact hw j 1 (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fP it.mem _ fun r hr' hcon => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, it.mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₃, it.other r h₁ h₂ h₃]
  by_cases he : j + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', it.rd], by rw [wr', it.wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (j + 1), by omega, j + 1, rfl, by omega,
      ⟨by rw [r10', succ_ofNat], hmem, gg, by rw [rd', it.rd], by rw [wr', it.wr]⟩⟩

/-! ## From S2V's state on -/

/-- `decrypt` from S2V's state of the associated data at `D` on: the counter
from the IV at `W` (`counter_ok`), CTR over the data in place (`ctr_wp`),
S2V's end with the plaintext into `W + 112` (`finish_wp`), the comparison of
the IVs (`compare_ok`), the mask of the data (`maskData_wp`) and the restore. -/
theorem openTail_wp (v : UpdateImpl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64}
    (hsv : Spill.Saved s.mem W g saved) :
    WP isa (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.X86_64.compare)
          (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore))))))) s
      fun s' => (∀ r ∈ saved.map Prod.fst, s'.gpr r = g r) ∧ s'.gpr .rsp = s₀.gpr .rsp ∧
        Frame (endRegions W P L (s₀.gpr .rsp)) s.mem s'.mem ∧
        match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R)
            (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem W 16) (Spec.Aes.bytesAt s.mem P L) with
        | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
        | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  -- The counter.
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have hr₁ : Regs s₀ C D P W R L s₁ := hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁
  have fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fc.readW (Region.contains_self _ _) (cnt_dis (by omega) (by omega)) (by decide)
  have h208 : s₁.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), hs.d208]
  have h216 : s₁.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), hs.d216]
  have hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) := by
    rw [m₁]; exact counter_cnt s.mem W
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₁ (length_counter _) (counter_low _) hcnt h208 h216)
    fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, rax₄, r11₄, m₄, g₄, rd₄, wr₄⟩ := compare_ok h h₃.regs.r15 h₃.regs.rd h₃.regs.wr
  have hr₄ : Regs s₀ C D P W R L s₄ := h₃.regs.keep (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₄ wr₄
  have f₄ : Frame [⟨W + BitVec.ofNat 64 dbOff, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt h.wP hr₄.r13 hr₄.r14
    (by rw [r11₄, rax₄]; simp only [decide_eq_true_eq]) (fun _ _ hi => h.inRP hr₄.rd hr₄.wr hi)
    (fun _ _ hi => h.inWP hPw hr₄.wr hi)) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  -- The result, then the restore.
  have dP144 := h.p_w.sub_right (h.sW (d := dbOff) (n := 8) (by decide))
  have r144 : s₅.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = s₄.gpr .rax := by
    rw [f₅.readW (Region.contains_self _ _) (one_out dP144.symm) (by decide), m₄, Mem.readW_writeW_self64]
  have hr₅ : Regs s₀ C D P W R L s₅ := hr₄.keep (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) h₅.rd h₅.wr
  have run₆ : runBlock isa [.mov .rax (.mem (at_ .r15 dbOff))] s₅ =
      some (s₅.setReg .rax (s₄.gpr .rax)) := by
    have r := h.inRW hr₅.rd hr₅.wr (d := dbOff) (n := 8) (by decide)
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hr₅.r15, r, ite_true, r144]
  have hsv₅ : Spill.Saved (s₅.setReg .rax (s₄.gpr .rax)).mem W g saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨saved_ge p hp, saved_le p hp⟩
    rw [mem_setReg]
    refine ((((hsv.frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      f₄ fun p hp => ?_).frame f₅ fun p hp => ?_
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by simp only [tOff]; omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by simp only [dbOff]; omega) (by omega) (by decide)
    · have := hb p hp
      exact one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  rw [show [.mov .rax (.mem (at_ .r15 dbOff))] ++ restore =
    ([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restoreCode .r15 saved from rfl]
  refine WP.block_append (WP.of_runBlock ⟨_, run₆, ?_⟩)
  refine WP.mono (Spill.restore_ok .r15 saved g _ (by decide) (fun p hp => by
      rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15, rd_setReg, wr_setReg, hr₅.rd, hr₅.wr]
      exact h.inRW rfl rfl (by have := saved_le p hp; omega))
    (by rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15]; exact hsv₅)) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have rax₇ : s₇.gpr .rax = s₄.gpr .rax := by rw [h₇b _ (by decide), gpr_setReg_self]
  have mem₇ : s₇.mem = s₅.mem := by rw [m₇, mem_setReg]
  -- The IV, the plaintext and S2V's end.
  have hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s.mem W 16 := by
    have d₃ := fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have d₂ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have dc := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [bytesAt_frame f₃ d₃ (by decide), bytesAt_frame f₂ d₂ (by decide), bytesAt_frame fc dc (by decide)]
  have hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₂.data, ctxCiph_frame fc (cnt_out h.c_w) hRb, bytesAt_frame fc (cnt_out h.p_w) hL]
  have hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) := by
    rw [h₃.out, hp, ctxMac_frame f₂ (ctr_out hcp h.c_w h.stk_c) hRb, ctxMac_frame fc (cnt_out h.c_w) hRb,
      bytesAt_frame f₂ (ctr_out h.d_p h.d_w h.stk_d) (by decide), bytesAt_frame fc (cnt_out h.d_w) (by decide)]
  have hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L) else Spec.Siv.zeros L := by
    have hl := length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    have hw := VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [mem₇, h₅.mem, hw, bytesAt_frame f₄ (one_out dP144) hL, bytesAt_frame f₃ (fin_out (by decide) h.p_w h.stk_p) hL, hp]
    simp only [decide_eq_true_eq]
  have f₄' : Frame (endRegions W P L (s₀.gpr .rsp)) s₃.mem s₄.mem :=
    f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  have f₅' : Frame (endRegions W P L (s₀.gpr .rsp)) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₇a, by rw [h₇b _ (by decide), gpr_setReg_of_ne _ _ (by decide), hr₅.rsp], ?_, ?_⟩
  · rw [mem₇]
    exact ((((fc.sub (cnt_sub h)).trans (f₂.sub (ctr_sub h))).trans (f₃.sub (fin_sub h (by decide)))).trans
      f₄').trans f₅'
  · rw [rax₇, rax₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) = Spec.Aes.bytesAt s.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86_64
