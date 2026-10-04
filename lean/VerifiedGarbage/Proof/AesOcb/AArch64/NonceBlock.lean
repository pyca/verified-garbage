import VerifiedGarbage.Proof.AesOcb.AArch64.PadTo
import VerifiedGarbage.Proof.Ocb.Nonce

/-!
# AES-OCB on AArch64: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the 1 before where the nonce goes, the
nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into the first
byte, and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base
  toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok in_left in_off read_one and15 lsl4_ofNat)

theorem or_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) ||| BitVec.ofNat 64 v)) =
      b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega,
    show i < 64 by omega, hi, decide_true, Bool.true_and]

theorem and_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 v)) =
      b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega,
    show i < 64 by omega, hi, decide_true, Bool.true_and]

theorem and63 (b : Byte) :
    BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem one_byte : BitVec.setWidth 8 (BitVec.setWidth 32 (1#64 : BitVec 64)) = (1 : Byte) := by decide

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
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The first block of `nonceBlock`: zeros, and the nonce's address and length. -/
theorem nonceHead_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa (zero16 tmpO ++ [ld .x12 .x19 nO, ld .x13 .x19 nlO]) s = some s₁ ∧
      s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x13 → s₁.gpr r = s.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₁.mem ∧ blockAtMem s₁.mem (W + BitVec.ofNat 64 tmpO) = 0 ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := tmpO) (by decide) h19 (wW (by decide)) (wW (by decide))
  have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  have kept : ∀ {d}, (d + 8 ≤ 112 ∨ 128 ≤ d) → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [tmpO]; exact Offset.disjoint W (by omega) (by omega) (by omega)) (by decide)
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  have r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nlO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  have hN₁ := (kept (d := nO) (by decide) (by decide)).trans hN
  have hnl₁ := (kept (d := nlO) (by decide) (by decide)).trans hnl
  simp only [nO, nlO] at r₁ r₂ hN₁ hnl₁
  obtain ⟨s₂, run₂, h₂⟩ : ∃ s₂, runBlock isa [ld .x12 .x19 nO, ld .x13 .x19 nlO] s₁ = some s₂ ∧ s₂ = _ :=
    ⟨_, by orun [h19₁, r₁, r₂], rfl⟩
  subst h₂
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, fun r h1 h2 h3 => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19₁, hN₁]
  · simp [gpr_write, h19₁, hnl₁]
  · simp only [gpr_write, h2, h3, ite_false]; exact B₁.gpr r (by simp [h1])
  · exact B₁.frame
  · exact B₁.val
  · exact B₁.sp
  · exact B₁.rd
  · exact B₁.wr

/-- The second block: the 1 before where the nonce goes, and the arguments of
the copy. -/
theorem nonceOne_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (h12 : s.gpr .x12 = N) (h13 : s.gpr .x13 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 (tmpO + 16), .sub .x .x11 .x11 .x13,
        .subImm .x .x14 .x11 1, Impl.AesGcm.AArch64.imm .x9 1, .strb .x9 .x14 0] s = some s₁ ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 (128 - nl) ∧ s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x14 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have e1 : W + 128#64 - BitVec.ofNat 64 nl = W + BitVec.ofNat 64 (128 - nl) := Offset.add_ofNat_sub W (by omega)
  have e2 : W + BitVec.ofNat 64 (128 - nl) - 1#64 = W + BitVec.ofNat 64 (127 - nl) := by
    rw [Offset.add_ofNat_sub W (by omega)]; congr 2; omega
  have w : InRegions s.wr (W + BitVec.ofNat 64 (127 - nl)) 1 := in_off hw (by omega) (by decide)
  refine ⟨_, by orun [h19, h13, e1, e2, w, write1], ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19, h13, e1]
  · simp [gpr_write, h12]
  · simp [gpr_write, h13]
  · simp [gpr_write, a, b, c]
  all_goals rfl

/-- The last block: `TAGLEN mod 128` into the first byte, `bottom`, and the
last byte's bits cleared. -/
theorem nonceTail_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {t : Nat}
    (ht : t < 2 ^ 64) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) :
    ∃ s₁, runBlock isa [ld .x10 .x19 tlO, Impl.AesGcm.AArch64.imm .x11 15, .logic .and .x .x10 .x10 .x11,
        .lsl .x .x10 .x10 4, .ldrb .x9 .x19 tmpO, .logic .orr .x .x9 .x9 .x10, .strb .x9 .x19 tmpO,
        .ldrb .x9 .x19 (tmpO + 15), Impl.AesGcm.AArch64.imm .x11 63, .logic .and .x .x10 .x9 .x11,
        st .x19 botO .x10, Impl.AesGcm.AArch64.imm .x11 0xc0, .logic .and .x .x9 .x9 .x11,
        .strb .x9 .x19 (tmpO + 15)] s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 112)
          (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16)))).writeW (W + BitVec.ofNat 64 288)
          (BitVec.ofNat 64 ((s.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 tlO) 8 := in_left (in_off hw (by decide) (by decide))
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 1 := in_left (in_off hw (by decide) (by decide))
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 1 := in_off hw (by decide) (by decide)
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 127) 1 := in_left (in_off hw (by decide) (by decide))
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 127) 1 := in_off hw (by decide) (by decide)
  have w₃ : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  have ne : (W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [tlO] at r₀ htl
  refine ⟨_, by orun [h19, r₀, htl, r₁, w₁, r₂, w₂, w₃, write1, read_one, WriteBytes.writeW8_apply, ne], ?_,
    fun r a b c => ?_, ?_, ?_, ?_⟩
  · simp only [and15, toNat_ofNat_of_lt ht, lsl4_ofNat, or_byte, and_byte, and63]
  · simp [gpr_write, a, b, c]
  all_goals rfl

theorem nonceBlock_ok {K W : Addr} (L : Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {N : Addr} {nl t : Nat} (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : Buf W s N nl) :
    WP isa nonceBlock s (NoncePost W t (bytesAt s.mem N nl) s) := by
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, f₁, z₁, sp₁, rd₁, wr₁⟩ := nonceHead_ok h19 hw hN hnl
  have h19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide) (by decide), h19]
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ :=
    nonceOne_ok h19₁ (by rw [wr₁]; exact hw) h1 h15 x12₁ x13₁
  have hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, rd₁, wr₁]; exact hB.rd
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂, wr₁]; exact Proof.AesGcm.AArch64.covers_off hw (by omega) (by decide)
  have hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega))
  have f₂ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [show W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) by
      rw [Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  have eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega),
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega)]
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega) ⟨by omega, hS₂, hD₂, hSD⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, _, g₃, sp₃, rd₃, wr₃⟩ := h₃
  rw [eN] at m₃
  have h19₃ : s₃.gpr .x19 = W := by
    rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide), h19₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega))
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t := by
    have k : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
        (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 tlO, 8⟩ : Region).Disjoint r) →
        m'.readW (W + BitVec.ofNat 64 tlO) 64 = m.readW (W + BitVec.ofNat 64 tlO) 64 :=
      fun h hd => h.readW (r := ⟨W + BitVec.ofNat 64 tlO, 8⟩) (Region.contains_self _ _) hd (by decide)
    rw [k fr₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by simp only [tlO]; omega)) (by decide)
          (by omega)),
      k f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      k f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), htl]
  obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := nonceTail_ok h19₃ (by rw [wr₃']; exact hw) ht htl₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  have L₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := bytesAt_of_zero z₁
  have e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega]
  have e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega]
  have L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - nl) ++ [1] ++ Spec.Ocb.zeros (nl) := by
    rw [m₂, e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - nl) 16 = 15 - nl by omega,
      show 16 - (15 - nl + 1) = nl by omega]
  have L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - nl) (15 - nl) = 15 - nl by omega, show 16 - nl - (15 - nl) = 1 by omega,
      show 16 - (15 - nl) = nl + 1 by omega, show 15 - nl + (1 + nl) = 16 by omega]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - nl - 16 = 0 by omega, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ nl + 1 by simp), show nl - (nl + 1 - 1) = 0 by omega,
      List.append_nil]
  have L₃d : ∀ k < 16, (bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
      rw [hlen] at this; rw [L₃]; exact this
  have b0 : s₃.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  have e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add W 112 15).symm
  have b15 : s₃.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  have fr288 : ∀ (M : Mem) (v : BitVec 64), Frame [⟨W + BitVec.ofNat 64 288, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 288) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₄, b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr288 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 288) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega]
        exact L₃d (k + 1) hk
  have hlen16 := length_bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16
  have f₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
    ((f₁.trans f₂).mono (fun r hr => by simp at hr; simp [hr])).trans ((fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact Offset.sub_base _ (by omega)⟩))
  refine ⟨?_, ?_, ?_, fun r hr => ?_, by rw [sp₄, sp₃, sp₂, sp₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃']⟩
  · rw [m₄]
    refine ((f₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · show blockAtMem s₄.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · show s₄.mem.readW (W + BitVec.ofNat 64 288) 64 = _
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.1 hr.2.1 hr.2.2.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g₂ r hr.1 hr.2.2.1 hr.2.2.2.2.2.1, g₁ r hr.1 hr.2.2.2.1 hr.2.2.2.2.1]

end VG.Proof.AesOcb.AArch64
