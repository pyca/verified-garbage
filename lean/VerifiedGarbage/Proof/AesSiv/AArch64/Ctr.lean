import VerifiedGarbage.Proof.AesSiv.AArch64.Finish

/-!
# AES-SIV on AArch64: CTR (`ctr`)

Each block: the counter `Q + i` (two byte-reversed words at `W + 64`) is
copied to the counter block at `W + 96`, `vg_aes_ctr32` writes its cipher to
the zeroed keystream block at `W + 80`, its first `min(16, left)` bytes are
XORed into the data a byte at a time (`xorBytes_wp`), and the counter is
incremented as a 128-bit integer (`inc_words`). After block `i` the data is
CTR's output on its first `16 (i + 1)` bytes (`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (ctrPart ctrPart_zero ctrPart_all ctrPart_step length_ctrPart be128_add take_bytesAt)
open VG.Proof.CmacAes.AArch64 (k0 CallPre CallPost ctr_call ctr_rel read_one succ_ofNat ofNat_ne_zero
  le8_rev)
open VG.Proof.CmacAes.Stream.AArch64 (copyMem copyMem_frame copyMem_bytes toNat_ofNat toNat_add_lt eval_zero
  eval_nonzero mz0 mz1 mz16)
open VG.Proof.Gcm.AArch64 (rev64_rev64)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## XORing a keystream block into the data -/

/-- The loop body of `xorBytes`. -/
abbrev xorBody : List Instr :=
  [.ldrb .x9 .x6 0, .ldrb .x10 .x7 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x6 0,
    .addImm .x .x6 .x6 1, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]

theorem byte_xor (a b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a) ^^^
      BitVec.setWidth 64 (BitVec.setWidth 32 b))) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem xorStep_ok (s : State) {A B : Addr} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x7 + BitVec.ofNat 64 0 = B) (ra : InRegions (s.rd ++ s.wr) A 1)
    (rb : InRegions (s.rd ++ s.wr) B 1) (wa : InRegions s.wr A 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧ s'.mem = s.mem.writeW A ((s.mem A ^^^ s.mem B : Byte)) ∧
      s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x7 = s.gpr .x7 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, xorBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, ra, rb, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, byte_xor, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- What `xorBytes` leaves. -/
structure Xored (s : State) (Q : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem Q xs
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xorBytes_wp (s : State) {Q K : Addr} {n : Nat} (hn : 0 < n) (hn16 : n ≤ 16) (h6 : s.gpr .x6 = Q)
    (h7 : s.gpr .x7 = K) (h8 : s.gpr .x8 = BitVec.ofNat 64 n)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hrk : ∀ i < n, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (Q + BitVec.ofNat 64 i) 1)
    (hdis : (⟨Q, n⟩ : Region).Disjoint ⟨K, n⟩) (hwq : Q.toNat + n ≤ 2 ^ 64) :
    WP isa xorBytes s
      (Xored s Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q n) (Spec.Aes.bytesAt s.mem K n))) := by
  refine WP.loop (M := isa) (body := .block xorBody) (c := .nonzero .x .x8)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .x6 = Q + BitVec.ofNat 64 j ∧
      t.gpr .x7 = K + BitVec.ofNat 64 j ∧ t.gpr .x8 = BitVec.ofNat 64 (n - j) ∧
      t.mem = writeBytes s.mem Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn, by rw [h6]; simp, by rw [h7]; simp, by rw [h8, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, Spec.Cmac.xor, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hj, x6, x7, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x6', x7', x8', g', sp', rd', wr'⟩ := xorStep_ok t (A := Q + BitVec.ofNat 64 j)
    (B := K + BitVec.ofNat 64 j) (by rw [x6, BitVec.add_zero]) (by rw [x7, BitVec.add_zero])
    (by rw [rd, wr]; exact hr j hj) (by rw [rd, wr]; exact hrk j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)).length = j := by
    simp [Proof.Cmac.length_xor, Spec.Aes.bytesAt]
  have fr : Frame [⟨Q, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  have hq : t.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat Q (show j < 2 ^ 64 by omega)] at hcon; omega
  have hkk : t.mem (K + BitVec.ofNat 64 j) = s.mem (K + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdis _ (Region.sub_prefix (by omega) _ hcon) (Offset.contains_base K (by omega) (by omega))
  have hmem : t'.mem = writeBytes s.mem Q
      (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q (j + 1)) (Spec.Aes.bytesAt s.mem K (j + 1))) := by
    rw [mem', hq, hkk, mem, Proof.Cmac.bytesAt_succ, Proof.Cmac.bytesAt_succ,
      Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt]),
      show Spec.Cmac.xor [s.mem (Q + BitVec.ofNat 64 j)] [s.mem (K + BitVec.ofNat 64 j)] =
        [s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)] from rfl,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev : isa.eval (.nonzero .x .x8) t' = some !decide (n - (j + 1) = 0) :=
    eval_nonzero (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
  by_cases he : j + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega,
      by rw [x6', x6, BitVec.add_assoc, succ_ofNat], by rw [x7', x7, BitVec.add_assoc, succ_ofNat], x8'', hmem,
      gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The counter -/

/-- `adds 1` on the low word and `adc 0` on the high word increment the
128-bit integer `hi ++ lo`. -/
theorem inc_words (hi lo : BitVec 64) :
    ((hi + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + (1 : BitVec 64).toNat + false.toNat)).toNat :
        BitVec 64) ++ (lo + 1 + BitVec.ofNat 64 false.toNat : BitVec 64) : BitVec 128) =
      (hi ++ lo : BitVec 128) + (1 : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false,
    show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 128).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  by_cases h : 2 ^ 64 ≤ lo.toNat + 1 + 0
  · have : lo.toNat = 2 ^ 64 - 1 := by omega
    rw [decide_eq_true h, Bool.toNat_true, this]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

/-! ## A block -/

theorem ctrPre_ok (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (h20 : s.gpr .x20 = C)
    (h21 : s.gpr .x21 = BitVec.ofNat 64 R) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa ctrPre s = some s' ∧ s'.gpr .x0 = C + BitVec.ofNat 64 272 ∧
      s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s'.gpr .x3 = W + BitVec.ofNat 64 80 ∧ s'.gpr .x4 = 1 ∧ s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = copyMem (Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 80)) (W + BitVec.ofNat 64 96)
        (W + BitVec.ofNat 64 64) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok h19 hwr (d := ksOff) (by decide) (by decide)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), h19]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := copy16_ok x19₁ (src := cntOff) (dst := cbOff) (by decide) (by decide)
    (h.inRW (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (by decide))
    (h.inRW (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (by decide))
    (h.inW (by rw [wr₁, hwr]) (by decide)) (h.inW (by rw [wr₁, hwr]) (by decide))
  have g (r : Reg) (hr : r ≠ .x9) : s₂.gpr r = s.gpr r := by rw [g₂ r hr, g₁ r hr]
  refine ⟨_, by
    rw [ctrPre, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, mov, csOff, cbOff, ksOff, runBlock_cons, runStep_some, runBlock_nil,
      exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, g _ (by decide : Reg.x20 ≠ .x9), h20],
    by simp [gpr_write, g _ (by decide : Reg.x21 ≠ .x9), h21],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19], by simp [gpr_write],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19], fun r hr => ?_,
    by simp only [mem_write, m₂, m₁], by simp only [sp_write, sp₂, sp₁], by simp only [rd_write, rd₂, rd₁],
    by simp only [wr_write, wr₂, wr₁]⟩
  rw [← g r (by rintro rfl; revert hr; decide)]
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem ctrMin_wp {s : State} {Q : Addr} {left : Nat} (h23 : s.gpr .x23 = BitVec.ofNat 64 left)
    (h22 : s.gpr .x22 = Q) (h19 : s.gpr .x19 = W) (hl : left < 2 ^ 64) :
    WP isa ctrMin s fun s' => s'.gpr .x8 = BitVec.ofNat 64 (min 16 left) ∧ s'.gpr .x6 = Q ∧
      s'.gpr .x7 = W + BitVec.ofNat 64 80 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [ctrMin]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, ksOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : (((s.write .x .x9 (s.gpr .x23 >>> 4)).write .x .x8 (s.gpr .x23 + BitVec.ofNat 64 0)).write .x
      .x6 (s.gpr .x22 + BitVec.ofNat 64 0)).write .x .x7 (s.gpr .x19 + BitVec.ofNat 64 80) = t
  have x9 : t.gpr .x9 = BitVec.ofNat 64 (left / 16) := by rw [← ht]; simp [gpr_write, h23, lsr4 hl]
  have x8 : t.gpr .x8 = BitVec.ofNat 64 left := by rw [← ht]; simp [gpr_write, h23]
  have x6 : t.gpr .x6 = Q := by rw [← ht]; simp [gpr_write, h22]
  have x7 : t.gpr .x7 = W + BitVec.ofNat 64 80 := by rw [← ht]; simp [gpr_write, h19]
  have gt : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r := fun r a b c d => by
    rw [← ht]; simp [gpr_write, a, b, c, d]
  have ev := eval_zero (s := t) (r := .x9) (x := left / 16) (by omega) x9
  have e : t.sp = s.sp ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by rw [← ht]; exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases hl16 : left < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x8, Nat.min_eq_right (by omega)], x6, x7, gt, e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, Nat.min_eq_left (show 16 ≤ left by omega)], by simp [gpr_write, x6],
      by simp [gpr_write, x7], fun r a b c d => by simp [gpr_write, c, gt r a b c d], e.1, e.2.1, e.2.2.1,
      e.2.2.2⟩

theorem ctrPost_ok {s : State} {Q : Addr} {left : Nat} {hi lo : BitVec 64} (h19 : s.gpr .x19 = W)
    (h22 : s.gpr .x22 = Q) (h23 : s.gpr .x23 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (hhi : s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi)
    (hlo : s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 cntOff) 8)
    (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (cntOff + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 cntOff) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 (cntOff + 8)) 8) :
    ∃ s', runBlock isa ctrPost s = some s' ∧
      (∃ hi' lo' : BitVec 64, s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (rev64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (rev64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + 1) ∧
      s'.gpr .x22 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .x9 = BitVec.ofNat 64 (left / 16) ∧
      s'.gpr .x10 = BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, ctrPost, cntOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, State.addWithCarry, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀,
      r₈, w₀, w₈]
    rfl, ?_⟩
  refine ⟨⟨_, _, rfl, ?_⟩, ?_, ?_, ?_, fun r a b c d => ?_, rfl, rfl, rfl⟩
  · have hhi' : s.mem.read (W + BitVec.ofNat 64 64) 8 = rev64 hi := by rw [← hhi]; simp [Mem.readW]
    have hlo' : s.mem.read (W + BitVec.ofNat 64 (64 + 8)) 8 = rev64 lo := by rw [← hlo]; simp [Mem.readW]
    simp only [c_write, hhi', hlo', rev64_rev64, 
      ]
    exact inc_words hi lo
  · simp [gpr_write, h22]
  · simp [gpr_write, h23, lsr4 hl]
  · simp [gpr_write]
  · simp [gpr_write, a, b, c, d]

/-- `min(16, left)` subtracted from the length left. -/
theorem ctrLeft_wp {s : State} {left : Nat} (h23 : s.gpr .x23 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (left / 16)) (h10 : s.gpr .x10 = BitVec.ofNat 64 16) :
    WP isa ctrLeft s fun s' => s'.gpr .x23 = BitVec.ofNat 64 (left - min 16 left) ∧
      (∀ r, r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ev := eval_zero (s := s) (r := .x9) (x := left / 16) (by omega) h9
  by_cases hl16 : left < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, Nat.min_eq_right (show left ≤ 16 by omega)],
      fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, BitVec.setWidth_eq]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, h23, h10, Nat.min_eq_left (show 16 ≤ left by omega),
        ofNat_sub (show 16 ≤ left by omega) hl],
      fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

/-! ## The loop -/

/-- The regions CTR writes: the data, the counter, keystream and counter
blocks, and the working space of `vg_aes_ctr32`. -/
abbrev ctrRegions (W P : Addr) (L : Nat) : List Region :=
  [⟨P, L⟩, ⟨W + BitVec.ofNat 64 64, 48⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩]

/-- The registers of block `i`. -/
structure CR (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x22 : s.gpr .x22 = P + BitVec.ofNat 64 (16 * i)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (L - 16 * i)
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CR.keep {s₀ s s' : State} {C D P W : Addr} {R L i : Nat} (h : CR s₀ C D P W R L i s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CR s₀ C D P W R L i s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    by rw [hs _ (by decide) (by decide), h.x23], by rw [hs _ (by decide) (by decide), h.x26],
    by rw [hs _ (by decide) (by decide), h.x27], by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- The state at the start of block `i`: the data is CTR's output on its
first `16 i` bytes, the counter is `Q + i`, and the context (so the
cipher) is as at the start. -/
structure CInv (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (i : Nat) (s : State) :
    Prop where
  cr : CR s₀ C D P W R L i s
  lt : 16 * i < L
  cnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
    (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i
  data : Spec.Aes.bytesAt s.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i)
  frame : Frame (ctrRegions W P L) m₀ s.mem

/-- What the setup of a block, the call and the length leave. -/
structure CHead (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q : List Byte) (i : Nat) (s s' : State) :
    Prop where
  cr : CR s₀ C D P W R L i s'
  x8 : s'.gpr .x8 = BitVec.ofNat 64 (min 16 (L - 16 * i))
  x6 : s'.gpr .x6 = P + BitVec.ofNat 64 (16 * i)
  x7 : s'.gpr .x7 = W + BitVec.ofNat 64 80
  ks : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 80) 16 = Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i
  frame : Frame [⟨W + BitVec.ofNat 64 80, 32⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩] s.mem s'.mem

theorem ctr_head (v : Proof.Aes.AArch64.Ctr32Impl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) {m₀ : Mem}
    {q x : List Byte} {i : Nat} {s : State} (hi : CInv s₀ C D P W R L m₀ q x i s) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ s', CHead s₀ C D P W R L m₀ q i s s' → WP isa k s' Q) :
    WP isa (.seq (.block ctrPre) (.seq (.call v.callee.name v.callee.code) (.seq ctrMin k))) s Q := by
  have hwW := h.wW
  have hlt := h.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, g₁, m₁, sp₁, rd₁, wr₁⟩ :=
    ctrPre_ok h hi.cr.x19 hi.cr.x20 hi.cr.x21 hi.cr.rd hi.cr.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  have s₉₆ : Region.Sub ⟨W + BitVec.ofNat 64 96, 16⟩ ⟨W + BitVec.ofNat 64 80, 32⟩ := by
    rw [show W + BitVec.ofNat 64 96 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
    exact Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 80, 32⟩] s.mem s₁.mem := by
    rw [m₁, Proof.Cmac.zero2]
    exact ((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).trans
      ((copyMem_frame _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s₉₆⟩)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 80 16 96 16 (by omega) (by omega) (by omega))
      (by decide), Proof.Cmac.zero2_bytes]
  have hc := h.cargs (s := s₁) (by rw [rd₁, hi.cr.rd]) (by rw [wr₁, hi.cr.wr]) x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ hz
  refine WP.seq (WP.mono (ctr_call v hc) fun s₂ h₂ => ?_)
  have cr₂ : CR s₀ C D P W R L i s₂ :=
    (hi.cr.keep (fun r hr _ => g₁ r hr) sp₁ rd₁ wr₁).keep h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (ctrMin_wp (left := L - 16 * i) cr₂.x23 cr₂.x22 cr₂.x19 (by omega))
    fun s₃ ⟨x8₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => hk s₃ ?_)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩]
      s₁.mem s₂.mem := h₂.frame
  refine ⟨cr₂.keep (fun r hr _ => g₃ r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) sp₃ rd₃ wr₃, x8₃, x6₃, x7₃, ?_, ?_⟩
  · -- The keystream block: the cipher of the counter block, a copy of `Q + i`.
    obtain ⟨hi', lo', hhi, hlo, hq⟩ := hi.cnt
    have dC (r : Region) (hr : r ∈ ctrRegions W P L) :
        (⟨C + BitVec.ofNat 64 272, 16 * (R + 1)⟩ : Region).Disjoint r := by
      have sub := h.sC (d := 272) (n := 16 * (R + 1)) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hcp.sub_left sub
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
    have sch : Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        Spec.Aes.bytesAt m₀ (C + BitVec.ofNat 64 272) (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.c_w.sub_left (h.sC (by omega))).sub_right (h.sW (by decide))) (by omega),
        Proof.Cmac.bytesAt_frame hi.frame dC (by omega)]
    have hhi' : s.mem.readW (W + BitVec.ofNat 64 64) 64 = rev64 hi' := hhi
    have hlo' : s.mem.readW (W + BitVec.ofNat 64 (64 + 8)) 64 = rev64 lo' := hlo
    have cb : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
      rw [m₁, copyMem_bytes _ (dWW 96 16 64 16 (by omega) (by omega) (by omega)), Proof.Cmac.zero2,
        Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 64 16 80 16 (by omega) (by omega) (by omega))
          (by decide),
        Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, hhi', hlo',
        le8_rev, hq, be128_add]
    rw [m₃, h₂.out, sch, cb]
    rfl
  · rw [m₃]
    exact (f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s₉₆⟩
      · exact ⟨⟨W + BitVec.ofNat 64 80, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

/-- The state after the last block: the data is CTR's output. -/
structure CDone (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : Spec.Aes.bytesAt s.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph m₀ C R) q x
  frame : Frame (ctrRegions W P L) m₀ s.mem

theorem ctxCiph_length (m : Mem) (C : Addr) (R : Nat) (y : List Byte) : (Spec.Siv.ctxCiph m C R y).length = 16 :=
  Proof.Cmac.aesWith_length _ _ _

theorem ctr_tail (h : Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {m₀ : Mem} {q x : List Byte} {i : Nat}
    {s s₃ : State} (hi : CInv s₀ C D P W R L m₀ q x i s) (hh : CHead s₀ C D P W R L m₀ q i s s₃) :
    WP isa (.seq xorBytes (.seq (.block ctrPost) ctrLeft)) s₃ fun s' =>
      (L - 16 * i ≤ 16 ∧ s'.gpr .x23 = 0 ∧ CDone s₀ C D P W R L m₀ q x s') ∨
      (16 < L - 16 * i ∧ s'.gpr .x23 ≠ 0 ∧ CInv s₀ C D P W R L m₀ q x (i + 1) s') := by
  have hwW := h.wW
  have hwP := h.wP
  have hlt := h.lt
  have hiL := hi.lt
  have hxL : x.length = L := by
    have := congrArg List.length hi.data
    rw [Proof.Cmac.bytesAt_length, length_ctrPart] at this; exact this.symm
  have hn : 0 < min 16 (L - 16 * i) := by omega
  have hn16 : min 16 (L - 16 * i) ≤ 16 := Nat.min_le_left _ _
  have dP (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2048⟩]) :
      (⟨P, L⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.p_w.sub_right (h.sW (by decide))
  have data₃ : Spec.Aes.bytesAt s₃.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i) := by
    rw [Proof.Cmac.bytesAt_frame hh.frame dP (by omega), hi.data]
  have sQ : Region.Sub ⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩ ⟨P, L⟩ := h.sP (by omega)
  refine WP.seq (WP.mono (xorBytes_wp s₃ (Q := P + BitVec.ofNat 64 (16 * i)) (K := W + BitVec.ofNat 64 80) hn hn16
    hh.x6 hh.x7 hh.x8
    (fun j hj => by rw [Offset.add_add]; exact h.inRP hh.cr.rd hh.cr.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inRW hh.cr.rd hh.cr.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inWP hPw hh.cr.wr (by omega))
    ((h.p_w.sub_left sQ).sub_right (h.sW (by omega)))
    (by rw [toNat_add_lt P hwP (show 16 * i < L by omega)]; omega)) fun s₄ h₄ => ?_)
  obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hi.cnt
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * i)) (min 16 (L - 16 * i)))
      (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)))).length = min 16 (L - 16 * i) := by
    rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length, Nat.min_self]
  have fx : Frame [⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have dW (d n : Nat) (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨P + BitVec.ofNat 64 (16 * i),
      min 16 (L - 16 * i)⟩ : Region)]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.p_w.sub_left sQ).symm.sub_left (h.sW hd)
  have dH (d : Nat) (hd : d + 8 ≤ 80) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2048⟩]) : (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
  have c₄ (d : Nat) (hd : d + 8 ≤ 80) :
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fx.readW (w := 64) (Region.contains_self _ _) (dW d 8 (by omega)) (by decide),
      hh.frame.readW (w := 64) (Region.contains_self _ _) (dH d hd) (by decide)]
  have g₄ (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄' : r ≠ .x9) (h₅ : r ≠ .x10) :=
    h₄.other r h₁ h₂ h₃ h₄' h₅
  have x19₄ : s₄.gpr .x19 = W := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x19]
  have x22₄ : s₄.gpr .x22 = P + BitVec.ofNat 64 (16 * i) := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x22]
  have x23₄ : s₄.gpr .x23 = BitVec.ofNat 64 (L - 16 * i) := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x23]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, hh.cr.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, hh.cr.wr]
  obtain ⟨s₅, run₅, ⟨hi₁, lo₁, m₅, hq₁⟩, x22₅, x9₅, x10₅, g₅, sp₅, rd₅, wr₅⟩ := ctrPost_ok (W := W) (s := s₄)
    (left := L - 16 * i) (hi := hi₀) (lo := lo₀) x19₄ x22₄ x23₄ (by omega)
    (by rw [c₄ cntOff (by decide)]; exact hhi) (by rw [c₄ (cntOff + 8) (by decide)]; exact hlo)
    (h.inRW rd₄ wr₄ (by decide)) (h.inRW rd₄ wr₄ (by decide)) (h.inW wr₄ (by decide)) (h.inW wr₄ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have x23₅ : s₅.gpr .x23 = BitVec.ofNat 64 (L - 16 * i) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), x23₄]
  refine WP.mono (ctrLeft_wp x23₅ (by omega) x9₅ x10₅) fun s₆ ⟨x23₆, g₆, sp₆, m₆, rd₆, wr₆⟩ => ?_
  have fp : Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅]
    have c64 : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Contains (W + BitVec.ofNat 64 cntOff) (64 / 8) := by
      show Region.Contains _ (W + BitVec.ofNat 64 64) 8
      simpa using Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c64).writeW
      (List.mem_singleton_self _) _ (by
        rw [show W + BitVec.ofNat 64 (cntOff + 8) = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
          rw [Offset.add_add]]
        exact Offset.contains_base _ (by decide) (by decide))
  -- The data.
  have kt : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)) =
      (Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i).take (min 16 (L - 16 * i)) := by
    rw [← hh.ks]
    have := take_bytesAt s₃.mem (W + BitVec.ofNat 64 80) (a := min 16 (L - 16 * i)) (b := 16 - min 16 (L - 16 * i))
    rw [show min 16 (L - 16 * i) + (16 - min 16 (L - 16 * i)) = 16 by omega] at this
    exact this.symm
  have st := ctrPart_step (Spec.Siv.ctxCiph m₀ C R) (ctxCiph_length m₀ C R) q x s₃.mem P (i := i)
    (n := min 16 (L - 16 * i)) (by omega) hn16 (by omega) (by rw [hxL]; exact data₃)
  rw [hxL, ← kt, ← h₄.mem] at st
  have data₆ : Spec.Aes.bytesAt s₆.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i + min 16 (L - 16 * i)) := by
    rw [Proof.Cmac.bytesAt_frame fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide))) (by omega), st]
  -- The frame.
  have frame : Frame (ctrRegions W P L) m₀ s₆.mem :=
    ((hi.frame.trans (hh.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
          rw [show W + BitVec.ofNat 64 80 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)).trans
      (fx.sub fun r hr => ⟨⟨P, L⟩, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact sQ⟩)).trans
      (fp.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
  have keep (r : Reg) (hr : r ∈ preserved) (h22 : r ≠ .x22) (h23 : r ≠ .x23) : s₆.gpr r = s₃.gpr r := by
    have a : r ≠ .x6 := by rintro rfl; revert hr; decide
    have b : r ≠ .x7 := by rintro rfl; revert hr; decide
    have c : r ≠ .x8 := by rintro rfl; revert hr; decide
    have d : r ≠ .x9 := by rintro rfl; revert hr; decide
    have e : r ≠ .x10 := by rintro rfl; revert hr; decide
    have f : r ≠ .x11 := by rintro rfl; revert hr; decide
    rw [g₆ r h23, g₅ r d e f h22, g₄ r a b c d e]
  have sp₆' : s₆.sp = s₀.sp := by rw [sp₆, sp₅, h₄.sp, hh.cr.sp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄]
  by_cases hfin : L - 16 * i ≤ 16
  · left
    have hn' : min 16 (L - 16 * i) = L - 16 * i := Nat.min_eq_right hfin
    refine ⟨hfin, by rw [x23₆, hn', Nat.sub_self]; rfl, ⟨by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x19],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x20],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x21],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x26],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x27], sp₆', rd₆', wr₆', ?_, frame⟩⟩
    rw [data₆, hn', show 16 * i + (L - 16 * i) = L by omega]
    exact ctrPart_all _ (ctxCiph_length m₀ C R) q x (by omega)
  · right
    have hn' : min 16 (L - 16 * i) = 16 := Nat.min_eq_left (by omega)
    have x23' : s₆.gpr .x23 = BitVec.ofNat 64 (L - 16 * (i + 1)) := by
      rw [x23₆, hn', show L - 16 * i - 16 = L - 16 * (i + 1) by omega]
    have ne : BitVec.ofNat 64 (L - 16 * (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [toNat_ofNat (by omega)] at this; simp at this; omega
    refine ⟨by omega, by rw [x23']; exact ne,
      ⟨⟨by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x19],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x20],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x21],
      by rw [g₆ _ (by decide), x22₅, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega], x23',
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x26],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x27], sp₆', rd₆', wr₆'⟩, by omega,
      ⟨hi₁, lo₁, ?_, ?_, ?_⟩, ?_, frame⟩⟩
    · rw [m₆, m₅, Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [m₆, m₅, Mem.readW_writeW_self64]
    · rw [hq₁, hq, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [data₆, hn', show 16 * i + 16 = 16 * (i + 1) by omega]

/-! ## The whole -/

/-- What `ctr` leaves: the data is CTR's output, and the registers are back. -/
structure CPost' (s₀ : State) (C D P W : Addr) (R L : Nat) (q : List Byte) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  x26 : s'.gpr .x26 = P
  x27 : s'.gpr .x27 = BitVec.ofNat 64 L
  data : Spec.Aes.bytesAt s'.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P L)
  frame : Frame (ctrRegions W P L) s.mem s'.mem

theorem ctr_nil (ciph : Spec.Cmac.Cipher) (q : List Byte) : Spec.Siv.ctr ciph q [] = [] := by
  simp [Spec.Siv.ctr, Spec.Siv.xor]

theorem ctrEnd_ok {s : State} (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) :
    ∃ s', runBlock isa [mov .x22 .x26, mov .x23 .x27] s = some s' ∧
      s'.gpr .x22 = P ∧ s'.gpr .x23 = BitVec.ofNat 64 L ∧ (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  exact ⟨by simp [gpr_write, h26], by simp [gpr_write, h27], fun r a b => by simp [gpr_write, a, b], rfl, rfl,
    rfl, rfl⟩

theorem ctr_wp (v : Proof.Aes.AArch64.Ctr32Impl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : Regs s₀ C D P W R L s) {q : List Byte}
    (hcnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q)
    (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) :
    WP isa (ctr v.callee) s (CPost' s₀ C D P W R L q s) := by
  have hwW := h.wW
  have hlt := h.lt
  have finish {t : State} (hd : CDone s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) t) :
      WP isa (.block [mov .x22 .x26, mov .x23 .x27]) t (CPost' s₀ C D P W R L q s) := by
    obtain ⟨t', run, x22, x23, g, sp, m, rd, wr⟩ := ctrEnd_ok hd.x26 hd.x27
    exact WP.of_runBlock ⟨t', run, ⟨⟨by rw [g _ (by decide) (by decide), hd.x19],
      by rw [g _ (by decide) (by decide), hd.x20], by rw [g _ (by decide) (by decide), hd.x21], x22, x23,
      by rw [sp, hd.sp], by rw [rd, hd.rd], by rw [wr, hd.wr]⟩, by rw [g _ (by decide) (by decide), hd.x26],
      by rw [g _ (by decide) (by decide), hd.x27], by rw [m]; exact hd.data, by rw [m]; exact hd.frame⟩⟩
  have ev := eval_zero (s := s) (r := .x23) (x := L) hlt hr.x23
  refine WP.seq (WP.ite (decide (L = 0)) ev (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine finish ⟨hr.x19, hr.x20, hr.x21, h26, h27, hr.sp, hr.rd, hr.wr, ?_, Frame.refl _ _⟩
    simp [Spec.Aes.bytesAt, ctr_nil]
  · have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
    refine WP.loop (M := isa) (c := .nonzero .x .x23)
      (fun (n : Nat) (t : State) => ∃ i, n = L - 16 * i ∧
        CInv s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) i t) ?_ (L - 16 * 0) s ⟨0, rfl, ?_⟩
    · rintro n t ⟨i, rfl, hi⟩
      refine ctr_head v h hcp hi fun t₃ hh => WP.mono (ctr_tail h hPw hi hh) fun t' ht => ?_
      rcases ht with ⟨_, hz, hd⟩ | ⟨_, hz, hi'⟩
      · exact Or.inl ⟨by show some (t'.read .x .x23 != 0) = some false; simp [State.read, hz], finish hd⟩
      · exact Or.inr ⟨by show some (t'.read .x .x23 != 0) = some true; simp [State.read]; exact hz,
          L - 16 * (i + 1), by have := hi.lt; omega, i + 1, rfl, hi'⟩
    · obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hcnt
      exact ⟨⟨hr.x19, hr.x20, hr.x21, by rw [hr.x22, Nat.mul_zero, k0], by rw [hr.x23, Nat.mul_zero, Nat.sub_zero],
        h26, h27, hr.sp, hr.rd, hr.wr⟩, by omega, ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩,
        by rw [Nat.mul_zero, ctrPart_zero], Frame.refl _ _⟩

end VG.Proof.AesSiv.AArch64
