import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.Ocb.Nonce

/-!
# AES-OCB on x86-64: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the nonce copied to the end
(`copyLoop`), the 1 before it, `TAGLEN mod 128` ORed into the first byte,
and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt length_bytesAt bytesAt_writeBytes_at
  bytesAt_writeW8_at bytesAt_writeW8_base and15' imm_eq)

theorem or_byte (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 64 ||| BitVec.ofNat 64 v).setWidth 8 : Byte) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow b.isLt (by omega))

theorem and_byte (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 64 &&& BitVec.ofNat 64 v).setWidth 8 : Byte) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left b.isLt)

theorem and63 (b : Byte) : b.setWidth 64 &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem sub_one_addr (p : Addr) {a : Nat} (ha : 1 ≤ a) (ha' : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (a - 1) := by
  rw [BitVec.add_assoc]
  refine congrArg (p + ·) ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_ofNat_of_lt ha', toNat_ofNat_of_lt (by omega),
    show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 by simp]
  omega

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rbx → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonceBlock_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {N : Addr} {nl t : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64)
    (hB : Buf W SP s N nl) :
    WP isa nonceBlock s (NoncePost W t (bytesAt s.mem N nl) s) := by
  have h15r := E.r15
  simp only [nO, nlO, tlO] at hN hnl htl
  -- `zero16 tmpO`
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := tmpO) h15r (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), h15r]
  have kept₁ : ∀ {d}, (d + 8 ≤ tmpO ∨ tmpO + 16 ≤ d) → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (by simp only [tmpO] at h₁ ⊢; omega) h₂ (by decide)) (by decide)
  -- the pointers and the count
  obtain ⟨s₂, run₂, rbx₂, r12₂, rsi₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [ld .rbx .r15 nO, ld .r12 .r15 nlO, mvr .rsi .r15, addi .rsi (tmpO + 16), .alu .sub .rsi (.reg .r12),
        .mov .rcx (.imm 0)] s₁ = some s₂ ∧
      s₂.gpr .rbx = N ∧ s₂.gpr .r12 = BitVec.ofNat 64 nl ∧ s₂.gpr .rsi = W + BitVec.ofNat 64 (128 - nl) ∧
      s₂.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nO) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
    have r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nlO) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
    have hN₁ := kept₁ (d := nO) (by decide) (by decide)
    have hnl₁ := kept₁ (d := nlO) (by decide) (by decide)
    simp only [nO, nlO] at r₁ r₂ hN₁ hnl₁
    refine ⟨_, by orun [h15₁, r₁, r₂, hN₁, hnl₁, hN, hnl], ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₁]
      exact Offset.add_ofNat_sub W (by omega)
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, h4, ite_false]
    all_goals rfl
  have eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [m₂]
    exact Proof.AesCcm.X86_64.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega)
  have hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hB.rd
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact E.perm.wC (by omega)
  have hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega))
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ (by omega) (by omega) rbx₂ rsi₂ rcx₂ r12₂ hS₂ hD₂ hSD) fun s₃ h₃ => ?_)
  obtain ⟨m₃, rcx₃, g₃, rd₃, wr₃⟩ := h₃
  rw [eN] at m₃
  have h15₃ : s₃.gpr .r15 = W := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), h15₁]
  have rsi₃ : s₃.gpr .rsi = W + BitVec.ofNat 64 (128 - nl) := by rw [g₃ _ (by decide) (by decide), rsi₂]
  have ea₁ : s₃.gpr .rsi + BitVec.ofInt 64 (-1) = W + BitVec.ofNat 64 (127 - nl) := by
    rw [rsi₃, sub_one_addr W (by omega) (by omega), show 128 - nl - 1 = 127 - nl by omega]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, B₁.wr]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, B₁.rd]
  have w127n : InRegions s₃.wr (W + BitVec.ofNat 64 (127 - nl)) 1 := by rw [wr₃']; exact E.perm.wW (by omega)
  have rtl : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 224) 8 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have r112 : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 112) 1 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have w112 : InRegions s₃.wr (W + BitVec.ofNat 64 112) 1 := by rw [wr₃']; exact E.perm.wW (by decide)
  have r127 : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 127) 1 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have w127 : InRegions s₃.wr (W + BitVec.ofNat 64 127) 1 := by rw [wr₃']; exact E.perm.wW (by decide)
  have w256 : InRegions s₃.wr (W + BitVec.ofNat 64 256) 8 := by rw [wr₃']; exact E.perm.wW (by decide)
  -- the 1 before the nonce
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.mov .rax (.imm 1),
      .store8 { base := .rsi, disp := -1 } .rax] s₃ = some s₄ ∧
      s₄.mem = s₃.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧
      (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by orun [ea₁, w127n], ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [mem_setReg, sext1]; rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  -- `TAGLEN mod 128` in the top bits of a byte
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega))
  have htl₄ : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by omega) (by decide) (by omega)) (by decide),
      fr₃.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by decide) (by omega))
        (by decide), m₂]
    exact (kept₁ (d := 224) (by decide) (by decide)).trans htl
  have h15₄ : s₄.gpr .r15 = W := by rw [g₄ _ (by decide), h15₃]
  obtain ⟨s₅, run₅, rax₅, g₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [ld .rax .r15 tlO, .alu .and .rax (.imm 15),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax)] s₄ = some s₅ ∧ s₅.gpr .rax = BitVec.ofNat 64 (16 * (t % 16)) ∧
      (∀ r, r ≠ .rax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    have r₄ : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 224) 8 := by rw [rd₄, wr₄]; exact rtl
    have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
    refine ⟨_, by orun [h15₄, r₄, htl₄], ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, e15, and15', toNat_ofNat_of_lt ht, ← BitVec.ofNat_add]
      congr 1; omega
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have h15₅ : s₅.gpr .r15 = W := by rw [g₅ _ (by decide), h15₄]
  have r112₅ : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 112) 1 := by rw [rd₅, wr₅, rd₄, wr₄]; exact r112
  have w112₅ : InRegions s₅.wr (W + BitVec.ofNat 64 112) 1 := by rw [wr₅, wr₄]; exact w112
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ : ∃ s₆, runBlock isa [.movzx8 .rcx (at_ .r15 tmpO), .alu .or .rcx (.reg .rax),
      .store8 (at_ .r15 tmpO) .rcx] s₅ = some s₆ ∧
      s₆.mem = s₅.mem.writeW (W + BitVec.ofNat 64 112)
        (s₅.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16))) ∧
      (∀ r, r ≠ .rcx → s₆.gpr r = s₅.gpr r) ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by orun [h15₅, r112₅, w112₅], ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rax₅]
      rw [or_byte _ (by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have h15₆ : s₆.gpr .r15 = W := by rw [g₆ _ (by decide), h15₅]
  have r127₆ : InRegions (s₆.rd ++ s₆.wr) (W + BitVec.ofNat 64 127) 1 := by
    rw [rd₆, wr₆, rd₅, wr₅, rd₄, wr₄]; exact r127
  have w127₆ : InRegions s₆.wr (W + BitVec.ofNat 64 127) 1 := by rw [wr₆, wr₅, wr₄]; exact w127
  have w256₆ : InRegions s₆.wr (W + BitVec.ofNat 64 256) 8 := by rw [wr₆, wr₅, wr₄]; exact w256
  obtain ⟨s₇, run₇, m₇, g₇, rd₇, wr₇⟩ : ∃ s₇, runBlock isa [.movzx8 .rax (at_ .r15 (tmpO + 15)), mvr .rcx .rax,
      .alu .and .rcx (.imm 63), st .r15 botO .rcx, .alu .and .rax (.imm 0xc0), .store8 (at_ .r15 (tmpO + 15)) .rax]
      s₆ = some s₇ ∧
      s₇.mem = (s₆.mem.writeW (W + BitVec.ofNat 64 256)
          (BitVec.ofNat 64 ((s₆.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s₆.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₇.gpr r = s₆.gpr r) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    have e63 : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 63 := by decide
    have e192 : BitVec.signExtend 64 (0xc0 : BitVec 32) = BitVec.ofNat 64 192 := by decide
    refine ⟨_, by orun [h15₆, r127₆, w127₆, w256₆], ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e63,
        e192, and63, and_byte _ (show 192 < 256 by decide)]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
    all_goals rfl
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  have L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  have e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega]
  have e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega]
  have L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (16 - nl) ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (16 - nl) 16 = 16 - nl by omega,
      Nat.sub_self, List.replicate_zero, List.append_nil]
  have L₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₄, e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₃]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, show min (15 - nl) (16 - nl) = 15 - nl by omega, show 15 - nl - (16 - nl) = 0 by omega,
      show 16 - nl - (15 - nl + 1) = 0 by omega, show 15 - nl + 1 - (16 - nl) = 0 by omega, List.take_zero,
      List.drop_zero, List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
      rw [hlen] at this; rw [L₄]; exact this
  have e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 := (Offset.add_add W 112 15).symm
  have h0 : W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 112 := BitVec.add_zero _
  have b0e : s₅.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := getD_bytesAt_eq s₄.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [h0] at this
    rw [m₅, this, L₄d 0 (by decide)]
  have L₆d : ∀ k < 16, (bytesAt s₆.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₆, bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0e, m₅]
    unfold nb
    rcases k with _ | k
    · rfl
    · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        show 1 + k = k + 1 by omega]
      exact L₄d (k + 1) hk
  have b15e : s₆.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', getD_bytesAt_eq s₆.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide), L₆d 15 (by decide)]
  have fr256 : ∀ v : BitVec 64, Frame [⟨W + BitVec.ofNat 64 256, 8⟩] s₆.mem (s₆.mem.writeW (W + BitVec.ofNat 64 256) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₇d : ∀ k < 16, (bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    generalize hb : s₆.mem (W + BitVec.ofNat 64 127) = b at m₇ b15e
    rw [m₇, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.AesCcm.X86_64.bytesAt_frame (fr256 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 256) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk, b15e]
    split
    · rfl
    · exact L₆d k hk
  have hlen16 := length_bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16
  -- the whole block
  have run : runBlock isa ([.mov .rax (.imm 1), .store8 { base := .rsi, disp := -1 } .rax] ++
      ([ld .rax .r15 tlO, .alu .and .rax (.imm 15), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)] ++
      ([.movzx8 .rcx (at_ .r15 tmpO), .alu .or .rcx (.reg .rax), .store8 (at_ .r15 tmpO) .rcx] ++
      [.movzx8 .rax (at_ .r15 (tmpO + 15)), mvr .rcx .rax, .alu .and .rcx (.imm 63), st .r15 botO .rcx,
        .alu .and .rax (.imm 0xc0), .store8 (at_ .r15 (tmpO + 15)) .rax]))) s₃ = some s₇ := by
    rw [runBlock_append, run₄, Option.bind_some, runBlock_append, run₅, Option.bind_some, runBlock_append, run₆,
      Option.bind_some, run₇]
  refine WP.of_runBlock ⟨s₇, run, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the frame
    have F₁ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
      (B₁.frame.mono (fun r hr => by simp at hr; simp [hr])).trans (by
        rw [← m₂]
        exact fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
          simp only [List.mem_singleton] at hr; subst hr
          rw [e128]; exact Offset.sub_base _ (by omega)⟩)
    rw [m₇, m₆, m₅, m₄]
    refine (((F₁.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _ ?_).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_).writeW (List.mem_cons_self ..) _ ?_
    · rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact contains_pre _ (by decide)
    · exact Region.contains_self _ _
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · -- the block
    show blockAtMem s₇.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₇d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · -- `bottom`
    show s₇.mem.readW (W + BitVec.ofNat 64 256) 64 = _
    rw [m₇, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15e, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · intro r h1 h2 h3 h4 h5
    rw [g₇ r h1 h2, g₆ r h2, g₅ r h1, g₄ r h1, g₃ r h1 h2, g₂ r h4 h5 h3 h2, B₁.gpr r (by simp [h1])]
  · rw [rd₇, rd₆, rd₅, rd₄, rd₃']
  · rw [wr₇, wr₆, wr₅, wr₄, wr₃']

end VG.Proof.AesOcb.X86_64
