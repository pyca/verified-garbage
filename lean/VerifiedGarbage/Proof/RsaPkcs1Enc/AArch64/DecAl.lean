import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Select

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the alternative length

The mask of the candidates, `bitMask (k - 11)`, by doublings (`maskPart_ok`),
and the alternative length, the last masked candidate of `CL` not above
`k - 11` (`alPart_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc (bitMask altStep)

/-- `sbc` of a register from itself after `subs a, b`: the borrow of `a - b`, as a mask. -/
theorem sbc_self (r a b : BitVec 64) :
    r + ~~~r + BitVec.ofNat 64 (decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + true.toNat)).toNat =
      if b.toNat ≤ a.toNat then 0 else BitVec.allOnes 64 := by
  have hn : r + ~~~r = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_allOnes]
    have := r.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hb : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := BitVec.toNat_not
  have := b.isLt
  rw [hn, hb]
  by_cases h : b.toNat ≤ a.toNat
  · rw [show decide (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + true.toNat) = true by
      simp only [Bool.toNat_true, decide_eq_true_eq]; omega]
    simp only [h, ↓reduceIte]; rfl
  · rw [show decide (2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + true.toNat) = false by
      simp only [Bool.toNat_true, decide_eq_false_iff_not]; omega]
    simp only [h, ↓reduceIte]; rfl

theorem maskBody_ok {t : State} :
    WP isa (.block [.add .x .x8 .x8 .x8, .addImm .x .x8 .x8 1, .subs .x .x10 .x8 .x9, .sbc .x .x10 .x10 .x10]) t
      fun u => Same t u ∧ u.gpr .x8 = t.gpr .x8 + t.gpr .x8 + 1 ∧ u.gpr .x9 = t.gpr .x9 ∧
        u.gpr .x10 = if (t.gpr .x9).toNat ≤ (t.gpr .x8 + t.gpr .x8 + 1).toNat then 0 else BitVec.allOnes 64 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.addWithCarry, Size.bits,
    BitVec.setWidth_eq, Nat.reduceLT, ite_true, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, trivial,
    sbc_self _ _ _⟩

theorem Same.trans {t u w : State} (h : Same t u) (h' : Same u w) : Same t w :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v, h'.mem.trans h.mem,
    fun r hr => (h'.cs r hr).trans (h.cs r hr)⟩

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem maskInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block maskInit) t fun u => Same t u ∧ u.gpr .x9 = slot t Q oK - BitVec.ofNat 64 11 ∧
      u.gpr .x8 = 0 := by
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [maskInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oK, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl⟩

theorem dbl (p : Nat) (h1 : 1 ≤ p) (h : p * 2 < 2 ^ 34) :
    BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 (p - 1) + 1 = BitVec.ofNat 64 (p * 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h8 : t₀.gpr .x8 = BitVec.ofNat 64 0)
    (h9 : t₀.gpr .x9 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun u => Same t₀ u ∧ u.gpr .x8 = BitVec.ofNat 64 (bitMask x) ∧
      u.gpr .x9 = BitVec.ofNat 64 x := by
  have hb : 0 < Spec.RsaPkcs1Enc.bitLength x := by
    simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega
  have hp : ∀ j, j < Spec.RsaPkcs1Enc.bitLength x → 2 ^ (j + 1) < 2 ^ 34 := fun j hj => by
    have := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega) hj
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega
  refine Bytes.count_loop hb (fun j u => Same t₀ u ∧ u.gpr .x8 = BitVec.ofNat 64 (2 ^ j - 1) ∧
    u.gpr .x9 = BitVec.ofNat 64 x) (fun j hj u ⟨hs, hu8, hu9⟩ => ?_) ⟨Same.refl _, by rw [h8]; rfl, h9⟩ |>.mono
    fun u ⟨hs, hu8, hu9⟩ => ⟨hs, by rw [hu8]; rfl, hu9⟩
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega) hj
  have hpj := hp j hj
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + 1 = BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨hw, w8, w9, w10⟩ => ⟨⟨hs.trans hw, by rw [w8, hu8, e8], by rw [w9, hu9]⟩, ?_⟩
  rw [w10, hu9, hu8, e8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega)
    rw [he]
    simp only [h1, ↓reduceIte, ne_eq, not_true_eq_false, decide_false]; rfl
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega) (by omega)
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega, ↓reduceIte, he, ne_eq, not_false_eq_true, decide_true]; rfl

/-- The carry of `subs a, c`: no borrow. -/
theorem carry_sub (a c : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~c).toNat + true.toNat) = decide (c.toNat ≤ a.toNat) := by
  have hn : (~~~c).toNat = 2 ^ 64 - 1 - c.toNat := BitVec.toNat_not
  have := c.isLt
  rw [hn]
  simp only [Bool.toNat_true, decide_eq_decide]
  omega

theorem alBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 1) 1) :
    WP isa (.block alBody) t fun u => Same t u ∧
      u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 2 ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      u.gpr .x13 = (let c := ((t.mem (t.gpr .x11)).setWidth 64 <<< 8 +
          (t.mem (t.gpr .x11 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .x8
        if c.toNat ≤ (t.gpr .x9).toNat then c else t.gpr .x13) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → u.gpr r = t.gpr r) := by
  apply WP.of_runBlock
  simp only [alBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load,
    State.addWithCarry, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h0, h1]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, trivial, trivial,
    ?_, fun r h10 h11 h12 h13 h14 => ?_⟩
  · simp only [carry_sub, decide_eq_true_eq, BitVec.add_zero, Bytes.read_one, Bytes.byte64]
  · simp only [h10, h11, h12, h13, h14, ite_false]

theorem alInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block alInit) t fun u => Same t u ∧ u.gpr .x11 = slot t Q oScr + BitVec.ofNat 64 sCL ∧
      u.gpr .x12 = BitVec.ofNat 64 128 ∧ u.gpr .x13 = 0 ∧ u.gpr .x8 = t.gpr .x8 ∧ u.gpr .x9 = t.gpr .x9 := by
  have h168 := h 168 (by decide)
  apply WP.of_runBlock
  simp only [alInit, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, sCL, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    reduceCtorEq, ite_false, h168]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    trivial⟩

theorem cand_bv (a b : Byte) {M : Nat} (hM : M < 2 ^ 64) :
    (a.setWidth 64 <<< 8 + b.setWidth 64) &&& BitVec.ofNat 64 M =
      BitVec.ofNat 64 ((256 * a.toNat + b.toNat) &&& M) := by
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  have hl : (256 * a.toNat + b.toNat) &&& M ≤ 256 * a.toNat + b.toNat := Nat.and_le_left
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt (a := M) hM, Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8 + b.toNat) (by omega), show a.toNat * 2 ^ 8 = 256 * a.toNat by omega,
    Nat.mod_eq_of_lt (by omega)]

theorem bytes_get (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n)[i]'(by simp [Spec.Rsa.bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt]

theorem alLoop_ok {t₀ : State} {x M : Nat} {CL : List Byte} {B : Addr}
    (hx : x < 2 ^ 32) (hM : M = bitMask x) (hMl : M < 2 ^ 64)
    (hm : ∀ i < 256, t₀.mem (B + BitVec.ofNat 64 i) = CL.getD i 0)
    (hr : ∀ i < 256, InRegions (t₀.rd ++ t₀.wr) (B + BitVec.ofNat 64 i) 1)
    (h8 : t₀.gpr .x8 = BitVec.ofNat 64 M) (h9 : t₀.gpr .x9 = BitVec.ofNat 64 x) (h11 : t₀.gpr .x11 = B)
    (h12 : t₀.gpr .x12 = BitVec.ofNat 64 128) (h13 : t₀.gpr .x13 = 0) :
    WP isa alLoop t₀ fun u => Same t₀ u ∧
      u.gpr .x13 = BitVec.ofNat 64 ((List.range 128).foldl (altStep (x + 11) CL) 0) := by
  refine (Bytes.count_loop (n := 128) (by decide) (fun j u => Same t₀ u ∧ u.gpr .x8 = BitVec.ofNat 64 M ∧
    u.gpr .x9 = BitVec.ofNat 64 x ∧ u.gpr .x11 = B + BitVec.ofNat 64 (2 * j) ∧
    u.gpr .x12 = BitVec.ofNat 64 (128 - j) ∧
    u.gpr .x13 = BitVec.ofNat 64 ((List.range j).foldl (altStep (x + 11) CL) 0))
    (fun j hj u ⟨hs, u8, u9, u11, u12, u13⟩ => ?_) ⟨Same.refl _, h8, h9, by rw [h11]; exact (BitVec.add_zero _).symm,
      h12, h13⟩).mono fun u ⟨hs, _, _, _, _, h⟩ => ⟨hs, h⟩
  have hr0 := hr (2 * j) (by omega)
  have hr1 := hr (2 * j + 1) (by omega)
  rw [← hs.rd, ← hs.wr] at hr0 hr1
  refine WP.mono (alBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) (by rw [u11, Enc.add_add]; exact hr1))
    fun w ⟨hw, w11, w12, w13, wo⟩ => ⟨⟨hs.trans hw, by rw [wo .x8 (by decide) (by decide) (by decide) (by decide)
      (by decide), u8], by rw [wo .x9 (by decide) (by decide) (by decide) (by decide) (by decide), u9],
      by rw [w11, u11, Enc.add_add]; rfl, by rw [w12, u12, Bytes.counter_step hj (by decide)], ?_⟩, ?_⟩
  · rw [w13, u13, u8, u9, u11, Enc.add_add]
    dsimp only
    rw [hs.mem, hm _ (by omega), hm _ (by omega), cand_bv _ _ hMl,
      Proof.RsaPkcs1Enc.foldl_range_succ]
    have hc : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M < 2 ^ 64 :=
      Nat.lt_of_le_of_lt Nat.and_le_right hMl
    have he : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M =
        Spec.Rsa.os2ip [CL.getD (2 * j) 0, CL.getD (2 * j + 1) 0] % 2 ^ Spec.RsaPkcs1Enc.bitLength (x + 11 - 11) := by
      rw [Proof.RsaPkcs1Enc.cand_eq, Nat.add_sub_cancel, hM, Proof.RsaPkcs1Enc.bitMask,
        Nat.and_two_pow_sub_one_eq_mod]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega), he]
    simp only [altStep, Nat.add_sub_cancel]
    split <;> rfl
  · rw [w12, u12, Bytes.counter_step hj (by decide)]; exact Bytes.counter_ne hj (by decide)

/-! ## The parts -/

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}
  {kd : List Byte}

theorem AMR.same {t u : State} (h : AMR L g vv m₀ R EM kd t) (hs : Same t u) : AMR L g vv m₀ R EM kd u :=
  ⟨h.post.same hs, by rw [hs.mem]; exact h.cl, by rw [hs.mem]; exact h.am⟩

/-- After the mask: `bitMask (k - 11)` in `x8` and `k - 11` in `x9`. -/
structure MK (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR L g vv m₀ R EM kd t
  x8 : t.gpr .x8 = BitVec.ofNat 64 (bitMask (L.k.toNat - 11))
  x9 : t.gpr .x9 = BitVec.ofNat 64 (L.k.toNat - 11)

theorem maskPart_ok (hL : L.Ok) {t : State} (h : AMR L g vv m₀ R EM kd t) : WP isa maskPart t (MK L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hc := h.post
  refine WP.seq (WP.mono (maskInit_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x9, x8⟩ => ?_)
  rw [slot, hc.ctx.kept.k] at x9
  have e9 : L.k - BitVec.ofNat 64 11 = BitVec.ofNat 64 (L.k.toNat - 11) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e9] at x9
  exact WP.mono (maskLoop_ok (x := L.k.toNat - 11) (by omega) (by omega) x8 x9) fun u ⟨hs, u8, u9⟩ =>
    ⟨(h.same S₁).same hs, u8, u9⟩

/-- `CL`. -/
abbrev clOf (kd : List Byte) : List Byte := Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After the alternative length. -/
structure AL (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR L g vv m₀ R EM kd t
  al : t.gpr .x13 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength L.k.toNat (clOf kd))

theorem bytes_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem alPart_ok (hL : L.Ok) {t : State} (h : MK L g vv m₀ R EM kd t) : WP isa alPart t (AL L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hc := h.amr.post
  refine WP.seq (WP.mono (alInit_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x11, x12, x13, x8, x9⟩ => ?_)
  rw [slot, hc.ctx.kept.scr] at x11
  have hc₁ := hc.same S₁
  have hcl : Spec.Rsa.bytesAt t.mem (scA L sCL) 256 = clOf kd := h.amr.cl
  refine WP.mono (alLoop_ok (x := L.k.toNat - 11) (M := bitMask (L.k.toNat - 11)) (CL := clOf kd)
    (B := scA L sCL) (by omega) rfl
    (Nat.lt_of_le_of_lt (Proof.RsaPkcs1Enc.bitMask_le (by omega)) (by omega))
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, S₁.mem])
    (fun i hi => by
      rw [Enc.add_add]
      exact (Covers.right (scCov hL hc₁.ctx (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega))) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (by rw [x8, h.x8]) (by rw [x9, h.x9]) x11 x12 x13) fun u ⟨hs, u13⟩ =>
    ⟨(h.amr.same S₁).same hs, by rw [u13, Nat.sub_add_cancel (by omega)]; rfl⟩

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
