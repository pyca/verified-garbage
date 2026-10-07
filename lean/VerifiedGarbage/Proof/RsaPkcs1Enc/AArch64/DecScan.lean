import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecAl

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the scan of `EM`

The first zero of `EM` from index 2 (`scanPart_ok`): whether there is one as
a mask in `x15`, and where in `x16`, as `firstZero` says.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc (firstZero)

/-- A Boolean as a mask. -/
def bm (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem zero_mask (b : Byte) :
    (if (1 : BitVec 64).toNat ≤ (b.setWidth 64).toNat then (0 : BitVec 64) else BitVec.allOnes 64) =
      bm (decide (b = 0)) := by
  by_cases h : b = 0
  · subst h; rfl
  · have : (1 : BitVec 64).toNat ≤ (b.setWidth 64).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
      have : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
      show 1 ≤ _; omega
    simp only [this, ↓reduceIte, bm, h, decide_false, Bool.false_eq_true]

theorem scanInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block scanInit) t fun u => Same t u ∧ u.gpr .x11 = slot t Q oOut + BitVec.ofNat 64 2 ∧
      u.gpr .x12 = slot t Q oK - BitVec.ofNat 64 2 ∧ u.gpr .x14 = BitVec.ofNat 64 2 ∧ u.gpr .x15 = 0 ∧
      u.gpr .x16 = 0 ∧ u.gpr .x17 = 1 ∧ u.gpr .x13 = t.gpr .x13 := by
  have h96 := h 96 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [scanInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oOut, oK,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq, ite_false, h96, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl, rfl,
    rfl, rfl, trivial⟩

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1)
    (h17 : t.gpr .x17 = 1) :
    WP isa (.block scanBody) t fun u => Same t u ∧ u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧
      u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧ u.gpr .x14 = t.gpr .x14 + BitVec.ofNat 64 1 ∧
      u.gpr .x15 = t.gpr .x15 ||| bm (decide (t.mem (t.gpr .x11) = 0)) ∧
      u.gpr .x16 = t.gpr .x16 ||| (bm (decide (t.mem (t.gpr .x11) = 0)) &&& ~~~(t.gpr .x15) &&& t.gpr .x14) ∧
      u.gpr .x13 = t.gpr .x13 ∧ u.gpr .x17 = 1 := by
  apply WP.of_runBlock
  simp only [scanBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load,
    State.addWithCarry, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, reduceCtorEq, ite_false,
    h0, h17]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, trivial, trivial,
    trivial, ?_, ?_, trivial⟩ <;>
  simp only [sbc_self, zero_mask, BitVec.add_zero, Bytes.read_one, Bytes.byte64, Bytes.rotateRight_zero]

theorem x16_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| (bm true &&& ~~~(bm false) &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  simp only [bm, ite_true, Bool.false_eq_true, ite_false, BitVec.not_zero, BitVec.allOnes_and, BitVec.ofNat_eq_ofNat]
  exact BitVec.zero_or

theorem x16_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| (bm false &&& ~~~(bm false) &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem bm_or_true (x : BitVec 64) : BitVec.allOnes 64 ||| x = BitVec.allOnes 64 := BitVec.allOnes_or

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h11 : t₀.gpr .x11 = O + BitVec.ofNat 64 2) (h12 : t₀.gpr .x12 = BitVec.ofNat 64 (k - 2))
    (h14 : t₀.gpr .x14 = BitVec.ofNat 64 2) (h15 : t₀.gpr .x15 = 0) (h16 : t₀.gpr .x16 = 0)
    (h17 : t₀.gpr .x17 = 1) :
    WP isa scanLoop t₀ fun u => Same t₀ u ∧ u.gpr .x15 = bm (firstZero EM k).isSome ∧
      u.gpr .x16 = BitVec.ofNat 64 ((firstZero EM k).getD 0) ∧ u.gpr .x13 = t₀.gpr .x13 ∧ u.gpr .x17 = 1 := by
  refine (Bytes.count_loop (n := k - 2) (by omega) (fun j u => Same t₀ u ∧
    u.gpr .x11 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .x12 = BitVec.ofNat 64 (k - 2 - j) ∧
    u.gpr .x14 = BitVec.ofNat 64 (2 + j) ∧ u.gpr .x15 = bm (firstZero EM (2 + j)).isSome ∧
    u.gpr .x16 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0) ∧ u.gpr .x13 = t₀.gpr .x13 ∧ u.gpr .x17 = 1)
    (fun j hj u ⟨hs, u11, u12, u14, u15, u16, u13, u17⟩ => ?_)
    ⟨Same.refl _, h11, h12, h14, by rw [h15]; rfl, by rw [h16]; rfl, rfl, h17⟩).mono
    fun u ⟨hs, _, _, _, u15, u16, u13, u17⟩ => by
      rw [show 2 + (k - 2) = k by omega] at u15 u16
      exact ⟨hs, u15, u16, u13, u17⟩
  have hr0 := hr (2 + j) (by omega)
  rw [← hs.rd, ← hs.wr] at hr0
  have hb : u.mem (u.gpr .x11) = EM.getD (2 + j) 1 := by rw [u11, hs.mem, hEM _ (by omega)]
  refine WP.mono (scanBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) u17)
    fun w ⟨hw, w11, w12, w14, w15, w16, w13, w17⟩ => ⟨⟨hs.trans hw, by rw [w11, u11, Enc.add_add]; rfl, by
      rw [w12, u12, show k - 2 - j = (k - 2) - j from rfl, Bytes.counter_step hj (by omega)],
      by rw [w14, u14, ← BitVec.ofNat_add]; rfl, ?_, ?_,
      by rw [w13, u13], w17⟩, ?_⟩
  · rw [w15, u15, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.allOnes_or]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, bm, hz, decide_true, Bool.false_eq_true, ite_true, ite_false,
          Option.isSome_some]
        rfl
      · simp only [Option.isSome_none, bm, hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
  · rw [w16, u16, u15, u14, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.not_allOnes, BitVec.and_zero,
        BitVec.zero_and, BitVec.or_zero, Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact x16_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact x16_neg _
  · rw [w12, u12, show k - 2 - j = (k - 2) - j from rfl, Bytes.counter_step hj (by omega)]
    exact Bytes.counter_ne hj (by omega)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}
  {kd : List Byte}

/-- After the scan. -/
structure SC (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR L g vv m₀ R EM kd t
  al : t.gpr .x13 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength L.k.toNat (clOf kd))
  x15 : t.gpr .x15 = bm (firstZero EM L.k.toNat).isSome
  x16 : t.gpr .x16 = BitVec.ofNat 64 ((firstZero EM L.k.toNat).getD 0)
  x17 : t.gpr .x17 = 1

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- A byte of `out` is accessible. -/
theorem Ctx.outR {t : State} (hc : Ctx L g vv m₀ t) {i : Nat} (hi : i < L.k.toNat) :
    InRegions (t.rd ++ t.wr) (L.out + BitVec.ofNat 64 i) 1 :=
  ⟨L.OUT, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem scanPart_ok (hL : L.Ok) {t : State} (h : AL L g vv m₀ R EM kd t) : WP isa scanPart t (SC L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hc := h.amr.post
  refine WP.seq (WP.mono (scanInit_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x11, x12, x14, x15, x16, x17, x13⟩ => ?_)
  rw [slot, hc.ctx.kept.out] at x11
  rw [slot, hc.ctx.kept.k] at x12
  have hc₁ := hc.same S₁
  have e12 : L.k - BitVec.ofNat 64 2 = BitVec.ofNat 64 (L.k.toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e12] at x12
  refine WP.mono (scanLoop_ok (O := L.out) (EM := EM) (k := L.k.toNat) (by omega) (by omega)
    (fun i hi => by rw [← hc₁.em, bytes_getD' _ _ hi]) (fun i hi => hc₁.ctx.outR hi) x11 x12 x14 x15 x16 x17)
    fun u ⟨hs, u15, u16, u13, u17⟩ => ⟨(h.amr.same S₁).same hs, by rw [u13, x13, h.al], u15, u16, u17⟩

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
