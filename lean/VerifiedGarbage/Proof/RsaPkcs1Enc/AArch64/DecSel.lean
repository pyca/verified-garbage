import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecScan

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the output

The validity of the padding, the selected length and the mask of the
private-key operation's success (`validBlock_ok`), `*msg_len` (`outInit`) and
the output, byte by byte (`selLoop_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc (firstZero vOf lselOf outByte)

theorem two_mask (b : Byte) :
    (if (1 : BitVec 64).toNat ≤ (b.setWidth 64 ^^^ 2).toNat then (0 : BitVec 64) else BitVec.allOnes 64) =
      bm (decide (b = 2)) := by
  by_cases h : b = 2
  · subst h; rfl
  · have : (1 : BitVec 64).toNat ≤ (b.setWidth 64 ^^^ 2).toNat := by
      have hne : b.setWidth 64 ^^^ 2 ≠ 0 := fun e => h (by
        have := congrArg (BitVec.setWidth 8) ((BitVec.xor_eq_zero_iff).mp e)
        rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this)
      have : (b.setWidth 64 ^^^ 2).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
      show 1 ≤ _; omega
    simp only [this, ↓reduceIte, bm, h, decide_false, Bool.false_eq_true]

theorem ten_mask {sep : Nat} (h : sep < 2 ^ 64) :
    (if (BitVec.setWidth 64 (10 : BitVec 16) <<< 0).toNat ≤ (BitVec.ofNat 64 sep).toNat then (0 : BitVec 64)
      else BitVec.allOnes 64) = bm (decide (sep < 10)) := by
  rw [show (BitVec.setWidth 64 (10 : BitVec 16) <<< 0).toNat = 10 from rfl, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  by_cases hs : sep < 10
  · simp only [show ¬ 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_true]
  · simp only [show 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_false, Bool.false_eq_true]

theorem one_mask (R : BitVec 64) :
    (if (1 : BitVec 64).toNat ≤ (R ^^^ 1).toNat then (0 : BitVec 64) else BitVec.allOnes 64) =
      bm (decide (R = 1)) := by
  by_cases h : R = 1
  · subst h; rfl
  · have : (1 : BitVec 64).toNat ≤ (R ^^^ 1).toNat := by
      have hne : R ^^^ 1 ≠ 0 := fun e => h ((BitVec.xor_eq_zero_iff).mp e)
      have : (R ^^^ 1).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
      show 1 ≤ _; omega
    simp only [this, ↓reduceIte, bm, h, decide_false, Bool.false_eq_true]

theorem bm_and (a b : Bool) : bm a &&& bm b = bm (a && b) := by
  cases a <;> cases b <;> rfl

theorem bm_bic (a b : Bool) : bm a &&& ~~~(bm b).rotateRight 0 = bm (a && !b) := by
  cases a <;> cases b <;> rfl

theorem sel_xor (x y : BitVec 64) (v : Bool) : x ^^^ ((y ^^^ x) &&& bm v) = if v then y else x := by
  cases v
  · simp [bm]
  · simp only [bm, ite_true, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem vOf_eq (a b : Byte) (f : Bool) (sep : Nat) :
    (f && (decide (a = 0) && decide (b = 2)) && !decide (sep < 10)) = vOf a b f sep := by
  have e : (!decide (sep < 10)) = decide (10 ≤ sep) := by
    by_cases hs : sep < 10
    · simp only [hs, decide_true, Bool.not_true, show ¬ 10 ≤ sep by omega, decide_false]
    · simp only [hs, decide_false, Bool.not_false, show 10 ≤ sep by omega, decide_true]
  rw [e]
  unfold vOf
  cases f <;> by_cases ha : a = 0 <;> by_cases hb : b = 2 <;> by_cases hs : 10 ≤ sep <;> simp [ha, hb, hs]

theorem slot_eq (t : State) (Q : Addr) (d : Nat) : slot t Q d = t.mem.read (Q + BitVec.ofNat 64 d) 8 := rfl

theorem imm2 : BitVec.setWidth 64 (2 : BitVec 16) <<< 0 = 2 := rfl

theorem validBlock_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (h0 : InRegions (t.rd ++ t.wr) (slot t Q oOut + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (slot t Q oOut + BitVec.ofNat 64 1) 1) (h17 : t.gpr .x17 = 1)
    {f : Bool} {sep al k : Nat} (h15 : t.gpr .x15 = bm f) (h16 : t.gpr .x16 = BitVec.ofNat 64 sep)
    (h13 : t.gpr .x13 = BitVec.ofNat 64 al) (hK : slot t Q oK = BitVec.ofNat 64 k) (hsep : sep < 2 ^ 64) :
    WP isa (.block validBlock) t fun u => Same t u ∧ u.gpr .x11 = slot t Q oOut ∧
      u.gpr .x12 = BitVec.ofNat 64 k ∧ u.gpr .x17 = 1 ∧
      u.gpr .x15 = bm (vOf (t.mem (slot t Q oOut)) (t.mem (slot t Q oOut + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .x14 = bm (decide (slot t Q oR = 1)) ∧
      u.gpr .x13 = (if vOf (t.mem (slot t Q oOut)) (t.mem (slot t Q oOut + BitVec.ofNat 64 1)) f sep then
          BitVec.ofNat 64 k - BitVec.ofNat 64 sep - 1 else BitVec.ofNat 64 al) &&& bm (decide (slot t Q oR = 1)) ∧
      u.gpr .x16 = BitVec.ofNat 64 k - (if vOf (t.mem (slot t Q oOut)) (t.mem (slot t Q oOut + BitVec.ofNat 64 1))
          f sep then BitVec.ofNat 64 k - BitVec.ofNat 64 sep - 1 else BitVec.ofNat 64 al) := by
  have h96 := h 96 (by decide)
  have h120 := h 120 (by decide)
  have h176 := h 176 (by decide)
  have h0' : InRegions (t.rd ++ t.wr) (t.mem.read (Q + BitVec.ofNat 64 96) 8 + BitVec.ofNat 64 0) 1 := h0
  have h1' : InRegions (t.rd ++ t.wr) (t.mem.read (Q + BitVec.ofNat 64 96) 8 + BitVec.ofNat 64 1) 1 := h1
  have hK' : t.mem.read (Q + BitVec.ofNat 64 120) 8 = BitVec.ofNat 64 k := hK
  apply WP.of_runBlock
  simp only [validBlock, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load,
    State.addWithCarry, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oOut, oK, oR, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h96, h120, h176, h0', h1', h17, h13, h15, h16, hK']
  refine ⟨⟨rfl, rfl, hsp.symm, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals try simp only [BitVec.add_zero, Bytes.read_one, Bytes.byte64, sbc_self, zero_mask, two_mask,
    ten_mask hsep, one_mask, bm_and, bm_bic, imm2]
  all_goals try simp only [slot_eq, vOf_eq, sel_xor]
  all_goals rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
