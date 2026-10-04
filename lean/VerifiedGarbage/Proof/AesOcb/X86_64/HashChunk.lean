import VerifiedGarbage.Proof.AesOcb.X86_64.HashFill

/-!
# AES-OCB on x86-64: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`rbx` points at block `j`, `rbp` is `j + 1`, and `m − j` is kept in `W`.
`hashChunk` takes `c = min(8, m − j)` blocks: fills the buffer with each
block XORed with its offset (`fill_ok`), enciphers the buffer, adds it to
the sum (`hashSum_ok`), and leaves `HInv` at `j + c` (`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne eval_b bytesAt_frame)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, the rest's length and the
offset (`[48, 64)`, `[96, 160)`), the blocks left, the buffer and the working
space of the functions called, and the stack below `SP`. -/
abbrev hashR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩, ⟨W + BitVec.ofNat 64 248, 8⟩, wC W, below SP 8]

theorem hashR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (hashR W SP) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (K W SP D : Addr) (n : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env K W SP s
  frame : Frame (hashR W SP) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l j
  rbx : s.gpr .rbx = A + BitVec.ofNat 64 (16 * j)
  rbp : s.gpr .rbp = BitVec.ofNat 64 (j + 1)
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  rest : s.mem.readW (W + BitVec.ofNat 64 tmpO) 64 = BitVec.ofNat 64 (a.length % 16)
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W`, the stack and the
data at `D`), the rounds in `W`. -/
structure HCtx (K W SP D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : Buf W SP s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  rnd : s₀.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  short : a.length < 2 ^ 64

namespace HCtx

variable {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : HCtx K W SP D n R ciph l A a s₀)
include C

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ mutR W SP D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.buf.stk.symm
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))]

theorem rnd' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) :
    m.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
  rw [kept_read C.lay C.dw h (by decide), C.rnd]

theorem ciph' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) : ctxLstar m K = l := by
  rw [← C.lstar]
  show blockAtMem m (K + BitVec.ofNat 64 240) = blockAtMem s₀.mem (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut C.lay C.kd r hr).sub_left (Lay.kSub (by decide))

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (K W SP D : Addr) (n : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env K W SP t
  frame : Frame (hashR W SP) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  rbx : t.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i))
  rbp : t.gpr .rbp = BitVec.ofNat 64 (j + i + 1)
  rsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i)
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  r12 : t.gpr .r12 = BitVec.ofNat 64 c
  oh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  alen : t.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  rest : t.mem.readW (W + BitVec.ofNat 64 tmpO) 64 = BitVec.ofNat 64 (a.length % 16)
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    {t : State} {i : Nat} (hi : i < c) (F : FillInv K W SP D n ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => FillInv K W SP D n ciph l A a s₀ j c t' (i + 1) ∧
      t'.zf = some (decide (i + 1 = c)) := by
  have L := C.lay
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).w
  refine WP.mono (hashFill_ok L F.env hi hc (by have := C.short; omega) F.rbp F.rbx F.rsi F.r13 F.r12 F.l0 F.oh hA hAW)
    fun t' P => ⟨?_, P.zf⟩
  have hfr : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ hashR W SP, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        sub_wC (by omega) (by omega)⟩
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (W + BitVec.ofNat 64 d) = blockAtMem t.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)
  have keepW : ∀ {d : Nat}, (d + 8 ≤ 96 ∨ (112 ≤ d ∧ d + 8 ≤ 144) ∨ (160 ≤ d ∧ d + 8 ≤ 384)) → d + 8 ≤ 2560 →
      t'.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    P.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)) (by decide)
  refine
    { env := F.env.keep (fun r hr => P.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
          P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      rbx := by rw [P.rbx, show j + i + 1 = j + (i + 1) by omega]
      rbp := by rw [P.rbp, show j + i + 2 = j + (i + 1) + 1 by omega]
      rsi := P.rsi
      r13 := P.r13
      r12 := by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), F.r12]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega) (by decide), F.sum]
      alen := by rw [keepW (by simp only [alenO]; omega) (by decide), F.alen]
      rest := by rw [keepW (by simp only [tmpO]; omega) (by decide), F.rest]
      l0 := by rw [keepB (by simp only [l0O]; omega) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega) (by omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (hashR_mut F.frame) (by omega)]

theorem fill_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ a.length / 16) {t : State} (F : FillInv K W SP D n ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => FillInv K W SP D n ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ FillInv K W SP D n ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (fill_step C hc hjc hi F) fun u' ⟨F', hz⟩ => ?_
  by_cases he : i + 1 = c
  · left; exact ⟨(eval_ne hz).trans (by simp [he]), he ▸ F'⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

theorem bufStart_ok {W : Addr} {t : State} (h15 : t.gpr .r15 = W) :
    ∃ t', runBlock isa bufStart t = some t' ∧ t'.gpr .r13 = BitVec.ofNat 64 0 ∧
      t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * 0) ∧
      (∀ r, r ≠ .r13 → r ≠ .rsi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by orun [bufStart, h15], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {k c : Nat} (hk : k < c)
    (hc : c ≤ 8) (hsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * k)) (h13 : t.gpr .r13 = BitVec.ofNat 64 k)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    ∃ t', runBlock isa (xor16 .rsi 0 sumO ++ [addi .rsi 16, addi .r13 1, .alu .cmp .r13 (.reg .r12)]) t = some t' ∧
      BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) [.rax, .rdx, .rsi, .r13] t t' ∧
      t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t'.zf = some (decide (k + 1 = c)) := by
  have h15 := E.r15
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .rsi) (a := 0) (d := sumO) h15 hsi (by decide) (by decide)
    (by rw [e0]; exact E.perm.wR (by omega)) (by rw [Offset.add_add]; exact E.perm.wR (by omega))
    (E.perm.wW (by decide)) (E.perm.wW (by decide))
  rw [e0] at B₁
  have hsi₁ : t₁.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * k) := by rw [B₁.gpr _ (by decide), hsi]
  have h13₁ : t₁.gpr .r13 = BitVec.ofNat 64 k := by rw [B₁.gpr _ (by decide), h13]
  have h12₁ : t₁.gpr .r12 = BitVec.ofNat 64 c := by rw [B₁.gpr _ (by decide), h12]
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some]; orun [hsi₁, h13₁, h12₁], ?_, ?_, ?_, ?_⟩
  · exact ⟨B₁.frame, B₁.val, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
      exact B₁.gpr r (by simp [hr.1, hr.2.1]), B₁.rd, B₁.wr⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi₁, Offset.add_add]
    rw [show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₁, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₁, h12₁,
      ← BitVec.ofNat_add]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

theorem hashSum_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {c : Nat} (hc0 : 0 < c)
    (hc : c ≤ 8) (h12 : t.gpr .r12 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r13₁, rsi₁, g₁, m₁, rd₁, wr₁⟩ := bufStart_ok (W := W) (t := t) E.r15
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ Env K W SP u ∧
      u.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .r13 = BitVec.ofNat 64 i ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧ u.wr = t.wr)
    ?_ (c - 0) _ ⟨0, rfl, hc0, E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁, rsi₁, r13₁, by rw [m₁]; exact Frame.refl _ _,
      by rw [m₁]; rfl, fun r _ _ h3 h4 => g₁ r h4 h3, rd₁, wr₁⟩
  rintro k u ⟨i, rfl, hi, Eu, rsi, r13, fr, sum, gu, rd, wr⟩
  obtain ⟨u', run', B, rsi', r13', zf'⟩ := sumStep_ok Eu hi hc rsi r13 (by
    rw [gu _ (by decide) (by decide) (by decide) (by decide), h12])
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have Eu' : Env K W SP u' := Eu.keep (fun r hr => B.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B.rd B.wr
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega)) (by omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → u'.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [B.gpr r (by simp [h1, h2, h3, h4]), gu r h1 h2 h3 h4]
  by_cases he : i + 1 = c
  · left
    exact ⟨(eval_ne zf').trans (by simp [he]), fr', he ▸ sum', gu', by rw [B.rd, rd], by rw [B.wr, wr]⟩
  · right
    exact ⟨(eval_ne zf').trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, Eu', rsi', r13', fr',
      sum', gu', by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

/-- The `c` blocks of the buffer. -/
theorem bufArgs_ok {W : Addr} {t : State} (h15 : t.gpr .r15 = W) {c : Nat} (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    ArgsOk [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12] t (W + BitVec.ofNat 64 384) c := by
  refine ⟨_, by orun [h15, h12], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- A chunk from `bufStart` on, with its `c` blocks in `r12`. -/
theorem chunkRest_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : HInv K W SP D n ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    WP isa (.seq (.block bufStart) (.seq (.loop hashFill .ne)
        (.seq (callBlocks (callees v).enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12])
          (.seq hashSum (.block [ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))))) t
      fun t' => HInv K W SP D n ciph l A a s₀ t' (j + c) ∧ t'.zf = some (decide (a.length / 16 - (j + c) = 0)) := by
  have L := C.lay
  obtain ⟨t₁, run₁, r13₁, rsi₁, g₁, m₁, rd₁, wr₁⟩ := bufStart_ok (W := W) (t := t) H.env.r15
  have F₀ : FillInv K W SP D n ciph l A a s₀ j c t₁ 0 :=
    { env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      rbx := by rw [g₁ _ (by decide) (by decide), H.rbx]; rfl
      rbp := by rw [g₁ _ (by decide) (by decide), H.rbp]
      rsi := rsi₁
      r13 := r13₁
      r12 := by rw [g₁ _ (by decide) (by decide), h12]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L F.env
    C.rounds (C.rnd' (hashR_mut F.frame)) (bufArgs_ok F.env.r15 F.r12) (dstW L F.env.perm (d := 384) (n := c) (by omega)))
    fun t₃ P₃ => ?_)
  have E₃ : Env K W SP t₃ := F.env.of_saved P₃.saved P₃.rd P₃.wr
  have F₃ : Frame (hashR W SP) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_wC (by decide) (by omega)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [F.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 → blockAtMem t₃.mem (W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · rw [F.env.rsp]; exact (L.stk_w' (by omega)).symm
  have kw₃ : ∀ {d : Nat}, d + 8 ≤ 384 → t₃.mem.readW (W + BitVec.ofNat 64 d) 64 = t₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hd => P₃.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · rw [F.env.rsp]; exact (L.stk_w' (by omega)).symm) (by decide)
  have hg : ∀ k < c, blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (hashR_mut F.frame)) _
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 c := by rw [P₃.saved _ (by decide), F.r12]
  refine WP.seq (WP.mono (hashSum_ok L E₃ hc0 hc h12₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => g₄ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₄ wr₄
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₄.mem (W + BitVec.ofNat 64 d) = blockAtMem t₃.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)
  have kw₄ : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ 64 ≤ d) → d + 8 ≤ 2560 →
      t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₃.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    fr₄.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide))
      (by decide)
  have alen₄ : t₄.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [kw₄ (by simp only [alenO]; omega) (by decide), kw₃ (by simp only [alenO]; omega), F.alen]
  have h15₄ := E₄.r15
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 c := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h12₃]
  have r₄ : InRegions (t₄.rd ++ t₄.wr) (W + BitVec.ofNat 64 alenO) 8 := E₄.perm.wR (by decide)
  have w₄ : InRegions t₄.wr (W + BitVec.ofNat 64 alenO) 8 := E₄.perm.wW (by decide)
  simp only [alenO] at alen₄ r₄ w₄
  refine WP.of_runBlock ⟨_, by orun [h15₄, h12₄, alen₄, r₄, w₄], ?_⟩
  have fw : ∀ (M : Mem) (x : BitVec 64), Frame [⟨W + BitVec.ofNat 64 248, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 248) x) := fun M x =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have kf : ∀ (M : Mem) (x : BitVec 64) {d : Nat}, d + 16 ≤ 248 →
      blockAtMem (M.writeW (W + BitVec.ofNat 64 248) x) (W + BitVec.ofNat 64 d) = blockAtMem M (W + BitVec.ofNat 64 d) :=
    fun M x d hd => blockAtMem_frame (fw M x) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨⟨E₄.keep (fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false])
      (by simp only [rd_setReg, rd_arithFlags]) (by simp only [wr_setReg, wr_arithFlags]), ?_, ?_, ?_, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact F.frame.trans (F₃.trans ((fr₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans ((fw _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩)))
  · simp only [rd_setReg, rd_arithFlags]; rw [rd₄, P₃.rd, F.rd]
  · simp only [wr_setReg, wr_arithFlags]; rw [wr₄, P₃.wr, F.wr]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), sum₄, k₃ (by decide), F.sum, hsum_add]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), k₄ (by simp only [ohO]; omega) (by decide), k₃ (by decide), F.oh]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), P₃.saved _ (by decide), F.rbx]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), P₃.saved _ (by decide), F.rbp]
  · simp only [mem_setReg, mem_arithFlags, Mem.readW_writeW_self64]
    have hs := C.short
    rw [Proof.AesCcm.X86_64.ofNat_sub (show c ≤ a.length / 16 - j by omega) (by omega),
      show a.length / 16 - j - c = a.length / 16 - (j + c) by omega]
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [mem_setReg, mem_arithFlags]
    rw [Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      kw₄ (by simp only [tmpO]; omega) (by decide), kw₃ (by simp only [tmpO]; omega), F.rest]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), k₄ (by simp only [l0O]; omega) (by decide), k₃ (by decide), F.l0]
  · simp only [zf_arithFlags, gpr_setReg, ite_true]
    have hs := C.short
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- A chunk of `min(8, m − j)` blocks, after `j` of the `m` whole blocks. -/
theorem hashChunk_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : HCtx K W SP D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : HInv K W SP D n ciph l A a s₀ t j) (hj : j < a.length / 16) :
    WP isa (hashChunk (callees v)) t fun t' =>
      HInv K W SP D n ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) ∧
        t'.zf = some (decide (a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0)) := by
  have hs := C.short
  have h15 := H.env.r15
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 248) 8 := H.env.perm.wR (by decide)
  have alen := H.alen
  simp only [alenO] at alen
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide
  obtain ⟨t₁, run₁, r12₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length / 16 - j) ∧ t₁.cf = some (decide (a.length / 16 - j < 8)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [h15, r₁, alen], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [cf_arithFlags, gpr_setReg, ite_true, e8, toNat_ofNat_of_lt (show a.length / 16 - j < 2 ^ 64 by omega),
        toNat_ofNat_of_lt (show 8 < 2 ^ 64 by decide)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have H₁ : HInv K W SP D n ciph l A a s₀ t₁ j :=
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  unfold hashChunk
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.ite (decide (a.length / 16 - j < 8)) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have hlt : a.length / 16 - j < 8 := of_decide_eq_true hb
    rw [show min 8 (a.length / 16 - j) = a.length / 16 - j by omega]
    exact chunkRest_ok v C H₁ (by omega) (by omega) (by omega) r12₁
  · have hge : ¬ a.length / 16 - j < 8 := of_decide_eq_false hb
    obtain ⟨t₂, run₂, r12₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.mov .r12 (.imm 8)] t₁ = some t₂ ∧
        t₂.gpr .r12 = BitVec.ofNat 64 8 ∧ (∀ r, r ≠ .r12 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧
        t₂.wr = t₁.wr := by
      refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, e8]
      · simp only [gpr_setReg, h, ite_false]
      all_goals rfl
    have H₂ : HInv K W SP D n ciph l A a s₀ t₂ j :=
      { H₁ with
        env := H₁.env.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
        frame := by rw [m₂]; exact H₁.frame
        rd := by rw [rd₂, H₁.rd]
        wr := by rw [wr₂, H₁.wr]
        sum := by rw [m₂, H₁.sum]
        oh := by rw [m₂, H₁.oh]
        rbx := by rw [g₂ _ (by decide), H₁.rbx]
        rbp := by rw [g₂ _ (by decide), H₁.rbp]
        alen := by rw [m₂, H₁.alen]
        rest := by rw [m₂, H₁.rest]
        l0 := by rw [m₂, H₁.l0] }
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    rw [show min 8 (a.length / 16 - j) = 8 by omega]
    exact chunkRest_ok v C H₂ (by decide) (by decide) (by omega) r12₂

end VG.Proof.AesOcb.X86_64
