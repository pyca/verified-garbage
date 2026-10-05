import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-CCM on x86-64: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`, for `ok` 1 or 0: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`). Its whole words go 8 bytes at a time
(`maskWords_wp`), the rest one at a time (`maskBytes_wp`); both loops keep
the first `j` bytes masked (`MInv`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Cmac.Stream (bytesAt_append)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
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
  refine ⟨_, by crun [maskByte, ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, hbp]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem mask_word (v : BitVec 64) (c : Bool) :
    v &&& ((0 : BitVec 64) - (if c then 1 else 0)) = if c then v else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskWord_ok (s : State) {P : Addr} {j w : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
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
  refine ⟨_, by crun [maskByte, ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h11,
      mask_word]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, hcx]
  · simp [gpr_setReg, hcx]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem mask_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    (if c then bytesAt m P (a + b) else zeros (a + b)) =
      (if c then bytesAt m P a else zeros a) ++
        (if c then bytesAt m (P + BitVec.ofNat 64 a) b else zeros b) := by
  cases c <;> simp [zeros, bytesAt_append, ← List.replicate_append_replicate]

/-- A word written is its 8 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 64) :
    m.writeW a v = writeBytes m a ((List.range 8).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 8 v

/-- The word at `a`, or zero, written back: the 8 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 64 else (0 : BitVec 64)) =
      writeBytes m' a (if c then bytesAt m a 8 else zeros 8) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp [zeros]; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 8) hk]
    rfl

/-- What both loops keep: the first `j` bytes of the data masked. -/
structure MInv (s s₁ t : State) (D : Addr) (c : Bool) (j : Nat) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j)
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → t.gpr r = s₁.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j) :
    Frame [⟨D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {s s₁ t : State} {D : Addr} {c : Bool} {j i : Nat} (h : MInv s s₁ t D c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) :=
  (h.frame (D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat D hi'] at hcon; omega)

theorem MInv.readW {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j)
    (hj : j + 8 < 2 ^ 64) : t.mem.readW (D + BitVec.ofNat 64 j) 64 = s.mem.readW (D + BitVec.ofNat 64 j) 64 := by
  refine Mem.readW_congr fun k hk => ?_
  simp only [Offset.add_add]
  exact h.at (by omega) (by omega)

/-- The words: from `j = 8 i`, with `w − i` words left in `rcx`, to `8 w`. -/
theorem maskWords_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {i : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s₁.gpr .r12 = D) (h11 : s₁.gpr .r11 = 0 - (if c then 1 else 0))
    (hi : i < n / 8) (ht : MInv s s₁ t D c (8 * i)) (hcx : t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) :
    WP isa maskWords t fun t' => MInv s s₁ t' D c (8 * (n / 8)) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n / 8 - i ∧ i < n / 8 ∧ MInv s s₁ t D c (8 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) ?_ (n / 8 - i) t ⟨i, rfl, hi, ht, hcx⟩
  rintro k t ⟨i, rfl, hi, ht, hcx⟩
  have hin : 8 * i + 8 ≤ n := by omega
  have cov (rs : List Region) (h : Covers [⟨D, n⟩] rs) : InRegions rs (D + BitVec.ofNat 64 (8 * i)) 8 :=
    h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hin (by omega)⟩
  obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := maskWord_ok t (P := D) (j := 8 * i)
    (w := n / 8 - i) (c := c) (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11]) hcx
    (by rw [ht.rd, ht.wr]; exact cov _ hD) (by rw [ht.wr]; exact cov _ hDw)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (8 * (i + 1)) else zeros (8 * (i + 1))) := by
    rw [mem', ht.readW (by omega), ht.mem, writeW_mask, show 8 * (i + 1) = 8 * i + 8 by omega, mask_add,
      ← writeBytes_append _ _ _ _ (by rw [length_mask, length_mask]; omega), length_mask]
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
  have ht' : MInv s s₁ t' D c (8 * (i + 1)) :=
    ⟨by rw [r10', show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = n / 8
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n / 8 - (i + 1), by omega, i + 1, rfl, by omega, ht', hcx'⟩

/-- The last bytes: from `j < n` to `n`. -/
theorem maskBytes_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {j : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s₁.gpr .r12 = D) (h11 : s₁.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s₁.gpr .rbp = BitVec.ofNat 64 n) (hj : j < n) (ht : MInv s s₁ t D c j) :
    WP isa maskBytes t fun t' => MInv s s₁ t' D c n := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ MInv s s₁ t D c j) ?_ (n - j) t ⟨j, rfl, hj, ht⟩
  rintro k t ⟨j, rfl, hj, ht⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11])
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hbp]) (by rw [ht.rd, ht.wr]; exact in_of_covers hD hj hn)
    (by rw [ht.wr]; exact in_of_covers hDw hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega), ht.mem, mask_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have ht' : MInv s s₁ t' D c (j + 1) :=
    ⟨by rw [r10', succ_ofNat], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, ht'⟩

theorem ofNat_shr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (hD : Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have hn := hD.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, m₁, h12₁, hbp₁, h11₁, r10₁, rcx₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 3, .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      s₁.gpr .r11 = 0 - (if c then 1 else 0) ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n / 8) ∧ s₁.zf = some (decide (n / 8 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂, r₃, execShift], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl, ofNat_shr3 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hl, ofNat_shr3 hn, and_self_beq (show n / 8 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  have hD' : Covers [⟨D, n⟩] (s.rd ++ s.wr) := hD.rd
  have inv₀ : MInv s s₁ s₁ D c 0 :=
    ⟨r10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun _ _ _ _ => rfl, rd₁, wr₁⟩
  -- The words.
  have words : WP isa (.ite .e (.block []) maskWords) s₁ fun t => MInv s s₁ t D c (8 * (n / 8)) := by
    refine WP.ite (decide (n / 8 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₀
    · exact maskWords_wp hn hD' hDw h12₁ h11₁ (Nat.pos_of_ne_zero (of_decide_eq_false hb))
        (by simpa using inv₀) (by rw [rcx₁, Nat.sub_zero])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono words fun t ht => ?_)
  -- The rest.
  have fin {t : State} (ht : MInv s s₁ t D c n) :
      Env K W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) :=
    ⟨E₁.keep (fun r hr => ht.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [ht.rd, rd₁]) (by rw [ht.wr, wr₁]), ht.rd, ht.wr, ht.mem⟩
  obtain ⟨t₁, run₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₁, runBlock isa [.alu .cmp .r10 (.reg .rbp)] t = some t₁ ∧
      t₁.zf = some (decide (8 * (n / 8) = n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, ht.r10, ht.keep .rbp (by decide) (by decide) (by decide), hbp₁]
      rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    all_goals rfl
  have ht₁ : MInv s s₁ t₁ D c (8 * (n / 8)) :=
    ⟨by rw [g₂, ht.r10], by rw [m₂, ht.mem], fun r h₁ h₂ h₃ => by rw [g₂, ht.keep r h₁ h₂ h₃],
      by rw [rd₂, ht.rd], by rw [wr₂, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₂, ?_⟩)
  refine WP.ite (decide (8 * (n / 8) = n)) (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [← of_decide_eq_true hb] at fin ⊢; exact fin ht₁
  · exact WP.mono (maskBytes_wp hn hD' hDw h12₁ h11₁ hbp₁ (by have := of_decide_eq_false hb; omega) ht₁)
      fun t' ht' => fin ht'

end VG.Proof.AesCcm.X86_64
