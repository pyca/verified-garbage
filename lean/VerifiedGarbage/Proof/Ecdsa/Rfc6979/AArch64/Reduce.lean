import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Bits

/-!
# Deterministic ECDSA on AArch64: `h = bits2octets(digest)`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the digest's
leftmost `8 w` bytes, a word at a time from the least significant: each to
`V`'s place, and it minus the word of `n` (with the borrow of the words
before, the complement of the carry) to `K`'s (`subs_ok`); then, by the
mask of the last borrow, the number's words or the difference's, big-endian
to `h` (`sels_ok`). The number is below `2^(64 w) < 2n`, so this is it
modulo `n` (`mod_mathK`, `reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut)
open VG.Proof.Mont.AArch64 (sub_borrow)
open VG.Proof.Mont (word wordsVal wordsVal_lt wordsVal_succ_top Outside off ofs writeW_outside)

/-- `x ^ d` masked, then `^ d`: `x` if the mask is all ones, `d` if zero. -/
theorem sel_mask (x d : BitVec 64) (b : Bool) :
    ((x ^^^ d) &&& (if b then BitVec.allOnes 64 else 0)) ^^^ d = if b then x else d := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The low `k + 1` words of `n`: its low `k`, and word `k`. -/
theorem n_split (n k : Nat) :
    n % 2 ^ (64 * (k + 1)) = n % 2 ^ (64 * k) + 2 ^ (64 * k) * (BitVec.ofNat 64 (n >>> (64 * k))).toNat := by
  rw [show 64 * (k + 1) = 64 * k + 64 by omega_arith, Nat.pow_add, Nat.mod_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := Proof.Gcm.byteRev64_byteRev64 a

/-- An 8-byte access at an aligned offset of at most `32760`. -/
theorem addr8 (s : State) (n : Reg) {o : Nat} (h₁ : o % 8 = 0) (h₂ : o < 32768) :
    addr s 8 n o = some (s.gpr n + BitVec.ofNat 64 o) := by
  simp only [addr, h₁, show o < 4096 * 8 by omega_arith, and_self, ite_true]

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- Word `j` of the number at `digest`, least significant first: a top
word of four bytes is zero-extended. -/
def xw (P : RfcHash) (L : Lay dn E) (m : Mem) (j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ P.Q then rev64 (m.readW (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
  else if P.Q ≤ 8 * j then 0
  else (rev32 (m.readW L.dg 32)).setWidth 64

theorem cat8_shr (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) >>> 32 =
      (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp only [← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h2,
    ← Nat.shiftLeft_add_eq_or_of_lt h3, ← Nat.shiftLeft_add_eq_or_of_lt h4, ← Nat.shiftLeft_add_eq_or_of_lt h5,
    ← Nat.shiftLeft_add_eq_or_of_lt h6, ← Nat.shiftLeft_add_eq_or_of_lt h7]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The first four bytes at `a`, big-endian: the eight bytes', shifted right. -/
theorem rev32_readW (m : Mem) (a : Addr) :
    (rev32 (m.readW a 32)).setWidth 64 = byteRev64 (m.readW a 64) >>> 32 := by
  rw [show rev32 (m.readW a 32) = byteRev32 (m.readW a 32) from rfl, byteRev32_readW, byteRev64_readW,
    cat8_shr]

/-- The words, as `loadBytes` reads them. -/
theorem xw_eq (P : RfcHash) (L : Lay dn E) (m : Mem) {j : Nat} (h : 8 * (j + 1) ≤ P.Q ∨ 8 * (j + 1) = P.Q + 4 ∨ 8 * (j + 1) = P.Q + 8) :
    xw P L m j = if 8 * (j + 1) ≤ P.Q then byteRev64 (m.readW (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
      else byteRev64 (m.readW L.dg 64) >>> (8 * (8 * (j + 1) - P.Q)) := by
  unfold xw
  split
  · rfl
  · split
    · rw [BitVec.ushiftRight_eq_zero (by omega_arith)]; rfl
    · rw [rev32_readW, show 8 * (8 * (j + 1) - P.Q) = 32 by omega_arith]

/-- Only `x2`, `x6`, `x8` and `x12` (and the flags and memory) changed since `t`. -/
structure RK (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  gpr : ∀ r, r ≠ .x2 → r ≠ .x6 → r ≠ .x8 → r ≠ .x12 → u.gpr r = t.gpr r

theorem RK.refl (t : State) : RK t t := ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem RK.trans {t u v : State} (h₁ : RK t u) (h₂ : RK u v) : RK t v :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r a b c d => (h₂.gpr r a b c d).trans (h₁.gpr r a b c d)⟩

theorem RK.x1 {t u : State} (h : RK t u) : u.gpr .x1 = t.gpr .x1 := h.gpr _ (by decide) (by decide) (by decide) (by decide)
theorem RK.x7 {t u : State} (h : RK t u) : u.gpr .x7 = t.gpr .x7 := h.gpr _ (by decide) (by decide) (by decide) (by decide)
theorem RK.x15 {t u : State} (h : RK t u) : u.gpr .x15 = t.gpr .x15 :=
  h.gpr _ (by decide) (by decide) (by decide) (by decide)

/-- `r = v`, keeping the carry flag. -/
theorem const64c_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (Impl.Mont.AArch64.const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [Impl.Mont.AArch64.const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-- `r = v`, keeping the carry flag, with what else it keeps spelled out. -/
theorem const64k_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (Impl.Mont.AArch64.const64 r v)) s fun t =>
      t.gpr r = v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.c = s.c ∧
        ∀ r', r' ≠ r → t.gpr r' = s.gpr r' := by
  apply WP.of_runBlock
  simp only [Impl.Mont.AArch64.const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, rfl, rfl, rfl, rfl, rfl, fun r' h => ?_⟩
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-! ## The subtraction -/

theorem read4 (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- Where the number's words are loaded from: `x1`, or `x13` if `Q` is not a
multiple of 8. -/
theorem dgBase_ne : (cfgOf P).dgBase ≠ .x2 ∧ (cfgOf P).dgBase ≠ .x6 ∧ (cfgOf P).dgBase ≠ .x8 ∧
    (cfgOf P).dgBase ≠ .x12 := by
  unfold Cfg.dgBase; split <;> decide

/-- Word `j` of the number at `digest`, in `x8`, the flags kept. -/
theorem loadWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hdn : P.Q ≤ dn) {u : State}
    (hk : RK t u) (h1 : u.gpr .x1 = L.dg) (h13 : u.gpr (cfgOf P).dgBase = L.dg + BitVec.ofNat 64 (P.Q % 8))
    {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).loadWord j)) u fun u' => u'.gpr .x8 = xw P L u.mem j ∧ u'.mem = u.mem ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.c = u.c ∧ ∀ r, r ≠ .x8 → u'.gpr r = u.gpr r := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  apply WP.of_runBlock
  by_cases h : 8 * (j + 1) ≤ P.Q
  · have hr : InRegions (u.rd ++ u.wr) (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 8 := by
      rw [hk.rd, hk.wr]; exact hc.inDg (by omega_arith) (by omega_arith)
    have h' : 8 * (j + 1) ≤ (cfgOf P).len := h
    have aD : addr u 8 (cfgOf P).dgBase (P.Q - P.Q % 8 - 8 * (j + 1)) =
        some (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) := by
      rw [addr8 u _ (by omega_arith) (by omega_arith), h13, Offset.add_add,
        show P.Q % 8 + (P.Q - P.Q % 8 - 8 * (j + 1)) = P.Q - 8 * (j + 1) by omega_arith]
    rw [Cfg.loadWord, ite_eq_left_of_eq_true _ _ (eq_true h'), show (cfgOf P).len = P.Q from rfl]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aD, Size.bytes, Size.bits, Option.bind_some,
      State.load, State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
      RegUpd.mem_write, ite_true, hr, Option.map_some, read8, Option.some.injEq, exists_eq_left']
    refine ⟨?_, by atriv, by atriv, by atriv, by atriv, by atriv, fun r hr8 => ?_⟩
    · simp only [xw, h, ite_true]
    · simp only [hr8, ite_false]
  · by_cases hz : P.Q ≤ 8 * j
    · rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 8 * (j + 1) ≤ (cfgOf P).len from h)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.mul_zero,
        show 0 < 64 by decide, ite_true, RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
      refine ⟨?_, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      · simp [xw, h, hz]
      · simp only [hr, ite_false]
    · have hr : InRegions (u.rd ++ u.wr) (L.dg + BitVec.ofNat 64 0) 4 := by
        rw [hk.rd, hk.wr]; exact hc.inDg (by omega_arith) (by omega_arith)
      have h' : ¬ 8 * (j + 1) ≤ (cfgOf P).len := h
      have aD : addr u 4 .x1 0 = some (L.dg + BitVec.ofNat 64 0) := by
        simp only [addr, Nat.zero_mod, show 0 < 4096 * 4 by decide, and_self, ite_true, h1]
      rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aD, Size.bytes, Size.bits, Option.bind_some,
        State.load, State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.mem_write, ite_true, hr, Option.map_some, read4, Option.some.injEq, exists_eq_left']
      refine ⟨?_, by atriv, by atriv, by atriv, by atriv, by atriv, fun r hr8 => ?_⟩
      · simp only [xw, h, hz, ite_false, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
          BitVec.add_zero]
      · simp only [hr8, ite_false]

/-- Word `j`: of the number to `V`'s place, of the difference to `K`'s,
with the carry `!b` in (the complement of the borrow `b`). -/
theorem subWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg) (hdn : P.Q ≤ dn)
    (h13 : t.gpr (cfgOf P).dgBase = L.dg + BitVec.ofNat 64 (P.Q % 8))
    {u : State} (hk : RK t u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16) {j : Nat} (hj : j < P.w)
    {b : Bool} (hb : (if j = 0 then true else u.c) = !b) :
    WP isa (.block ((cfgOf P).subWord j)) u fun u' => RK u u' ∧
      u'.mem = (u.mem.writeW (off L.B (80 + 8 * j)) (xw P L u.mem j)).writeW (off L.B (16 + 8 * j))
        (Word64.addCarry (xw P L u.mem j) (~~~(cfgOf P).nWord j) (!b)) ∧
      u'.c = Word64.carryOut (xw P L u.mem j) (~~~(cfgOf P).nWord j) (!b) := by
  have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
  have hw : (cfgOf P).w = P.w := rfl
  have hx1 : u.gpr .x1 = L.dg := hk.x1.trans h1
  have hx13 : u.gpr (cfgOf P).dgBase = L.dg + BitVec.ofNat 64 (P.Q % 8) := by
    obtain ⟨n2, n6, n8, n12⟩ := dgBase_ne (P := P)
    rw [hk.gpr _ n2 n6 n8 n12, h13]
  have hV : InRegions u.wr (L.B + BitVec.ofNat 64 (80 + 8 * j)) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)
  have hK : InRegions u.wr (L.B + BitVec.ofNat 64 (16 + 8 * j)) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)
  have aV : ∀ s : State, addr s 8 .x15 (fV + 8 * j) = some (s.gpr .x15 + BitVec.ofNat 64 (fV + 8 * j)) :=
    fun s => addr8 s .x15 (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)
  have aK : ∀ s : State, addr s 8 .x15 (fK + 8 * j) = some (s.gpr .x15 + BitVec.ofNat 64 (fK + 8 * j)) :=
    fun s => addr8 s .x15 (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
  have e80 : 16 + (fV + 8 * j) = 80 + 8 * j := by simp only [fV]; omega_arith
  have e16 : 16 + (fK + 8 * j) = 16 + 8 * j := by simp only [fK]; omega_arith
  simp only [Cfg.subWord]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- The word, to `V`'s place.
  refine WP.mono (loadWord_ok hA hc hdn hk hx1 hx13 hj) fun u₀ ⟨e₀, m₀', rd₀, wr₀, sp₀, c₀, g₀⟩ => ?_
  refine WP.mono (show WP isa (.block [.str .x .x8 .x15 (fV + 8 * j)]) u₀ fun u₁ =>
      u₁.gpr .x8 = xw P L u.mem j ∧
      u₁.mem = u.mem.writeW (off L.B (80 + 8 * j)) (xw P L u.mem j) ∧ u₁.rd = u.rd ∧ u₁.wr = u.wr ∧
      u₁.sp = u.sp ∧ u₁.c = u.c ∧ ∀ r, r ≠ .x8 → u₁.gpr r = u.gpr r by
    have h15₀ : u₀.gpr .x15 = L.B + BitVec.ofNat 64 16 := (g₀ _ (by decide)).trans h15
    have hV₀ : InRegions u₀.wr (L.B + BitVec.ofNat 64 (80 + 8 * j)) 8 := by rw [wr₀]; exact hV
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aV, Size.bytes, Size.bits, Option.bind_some,
      State.store, State.read, BitVec.setWidth_eq, ite_true, h15₀, Offset.add_add, e80,
      hV₀, write8, Option.some.injEq, exists_eq_left']
    refine ⟨e₀, by rw [m₀', e₀], rd₀, wr₀, sp₀, c₀, g₀⟩) fun u₁ ⟨e₁, m₁, rd₁, wr₁, sp₁, c₁, g₁⟩ => ?_
  -- The word of `n`.
  refine WP.mono (const64k_ok u₁ .x12 ((cfgOf P).nWord j)) fun u₂ ⟨e₂, m₂, rd₂, wr₂, sp₂, c₂, g₂⟩ => ?_
  have h8 : u₂.gpr .x8 = xw P L u.mem j := (g₂ _ (by decide)).trans e₁
  have h15₂ : u₂.gpr .x15 = L.B + BitVec.ofNat 64 16 := by rw [g₂ _ (by decide), g₁ _ (by decide), h15]
  have hK₂ : InRegions u₂.wr (L.B + BitVec.ofNat 64 (16 + 8 * j)) 8 := by rw [wr₂, wr₁]; exact hK
  have hc₂ : (if j = 0 then true else u₂.c) = !b := by rw [c₂, c₁]; exact hb
  -- The difference, to `K`'s place.
  apply WP.of_runBlock
  by_cases hj0 : j = 0
  · simp only [eq_true hj0, ite_true] at hc₂ ⊢
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aK, Size.bytes, Size.bits,
      Option.bind_some, State.store, State.read, BitVec.setWidth_eq, RegUpd.gpr_addWithCarry,
      RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
      RegUpd.sp_addWithCarry, reduceCtorEq, ite_false, ite_true, h15₂, Offset.add_add, e16, hK₂, h8, e₂,
      write8, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, fun r a _ c d => ?_⟩, ?_, ?_⟩
    · show (State.addWithCarry u₂ Size.x Reg.x2 _ _ true).gpr r = u.gpr r
      rw [RegUpd.gpr_addWithCarry]; simp only [a, ite_false]; rw [g₂ r d, g₁ r c]
    · rw [m₂, m₁, ← hc₂]; rfl
    · rw [← hc₂]; rfl
  · simp only [eq_false hj0, ite_false] at hc₂ ⊢
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aK, Size.bytes, Size.bits,
      Option.bind_some, State.store, State.read, BitVec.setWidth_eq, RegUpd.gpr_addWithCarry,
      RegUpd.c_addWithCarry, RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
      RegUpd.sp_addWithCarry, reduceCtorEq, ite_false, ite_true, h15₂, Offset.add_add, e16, hK₂, h8, e₂,
      hc₂, write8, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, fun r a _ c d => ?_⟩, ?_, ?_⟩
    · show (State.addWithCarry u₂ Size.x Reg.x2 _ _ _).gpr r = u.gpr r
      rw [RegUpd.gpr_addWithCarry]; simp only [a, ite_false]; rw [g₂ r d, g₁ r c]
    · rw [m₂, m₁]; rfl
    · rfl

/-- The digest is apart from the stack, so code that writes only in the
frame keeps its words. -/
theorem dg_kept (hL : L.Ok) {m m' : Mem} {n : Nat} (h : Outside L.B 16 n m m') (hn : 16 + n ≤ 256 + L.e) {d : Nat}
    (hd : d + 8 ≤ dn) : m'.readW (L.dg + BitVec.ofNat 64 d) 64 = m.readW (L.dg + BitVec.ofNat 64 d) 64 :=
  Proof.Weierstrass.readW_keep fun i hi =>
    Proof.Weierstrass.keep_of_disjoint (k := dn) h ((hL.kg.symm).sub_right (Offset.sub_base _ hn))
      (by have := L.he; omega_arith) (by omega_arith) (by have := hL.ng; omega_arith)

/-- The words of the number at `digest`, kept by code that writes only in the frame. -/
theorem xw_kept (hL : L.Ok) {m m' : Mem} {n : Nat} (h : Outside L.B 16 n m m') (hn : 16 + n ≤ 256 + L.e)
    (hdn : P.Q ≤ dn) (h8 : 8 ≤ P.Q) (j : Nat) : xw P L m' j = xw P L m j := by
  unfold xw
  split
  · rw [dg_kept hL h hn (by omega_arith)]
  · split
    · rfl
    · refine congrArg (fun x => (rev32 x).setWidth 64) (Mem.readW_congr fun i hi => ?_)
      exact (Proof.Weierstrass.keep_of_disjoint (k := dn) h ((hL.kg.symm).sub_right (Offset.sub_base _ hn))
        (by have := L.he; omega_arith) (i := i) (by omega_arith) (by have := hL.ng; omega_arith))

/-- One more word of a subtraction with borrow: the words below `k` (`hs`)
and word `k` (`e`), weighted by `Q = 2^(64 k)`. -/
private theorem borrow_step {a b r x y z c d Q : Nat} (hs : a + r = b + Q * c)
    (e : x + y + c = z + 2 ^ 64 * d) : a + Q * x + (r + Q * y) = b + Q * z + 2 ^ 64 * Q * d := by
  grind

/-- After `k` words: the number's in `V`'s place, and the difference in
`K`'s, with the borrow `b`. -/
theorem subs_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) (h1 : t.gpr .x1 = L.dg) (hdn : P.Q ≤ dn)
    (h13 : t.gpr (cfgOf P).dgBase = L.dg + BitVec.ofNat 64 (P.Q % 8))
    (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) t fun u =>
      RK t u ∧ Outside L.B 16 128 t.mem u.mem ∧ (∀ j < k, word u.mem L.B (80 + 8 * j) = xw P L t.mem j) ∧
      ∃ b : Bool, (k = 0 → b = false) ∧ (0 < k → u.c = !b) ∧
        wordsVal u.mem L.B 16 k + P.R.E.C.n % 2 ^ (64 * k) = wordsVal u.mem L.B 80 k + 2 ^ (64 * k) * b.toNat
  | 0, _ => WP.block_nil ⟨RK.refl _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      false, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _), by simp [wordsVal, Nat.mod_one]⟩
  | k + 1, hk => by
    have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (subs_ok hA hc hL h1 hdn h13 h15 k (by omega_arith)) fun u₁ ⟨k₁, O₁, e₁, b, hb0, hcf, hs⟩ => ?_
    have hb : (if k = 0 then true else u₁.c) = !b := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; rw [hb0 rfl]; rfl
      · split
        · omega_arith
        · exact hcf h
    refine WP.mono (subWord_ok (P := P) hA hc h1 hdn h13 k₁ (k₁.x15.trans h15) (j := k) (by omega_arith) hb)
      fun u₂ ⟨k₂, m₂, cf₂⟩ => ?_
    have hx : xw P L u₁.mem k = xw P L t.mem k := xw_kept hL O₁ (by omega_arith) hdn P.R.len_words.1 k
    rw [hx] at m₂ cf₂
    -- Each write is outside the other's word, and outside the words below `k`.
    have oK : Outside L.B (16 + 8 * k) 8 _ _ := writeW_outside (u₁.mem.writeW (off L.B (80 + 8 * k)) (xw P L t.mem k))
      L.B (Word64.addCarry (xw P L t.mem k) (~~~(cfgOf P).nWord k) (!b)) (d := 16 + 8 * k) (by omega_arith)
    have oV : Outside L.B (80 + 8 * k) 8 _ _ := writeW_outside u₁.mem L.B (xw P L t.mem k) (d := 80 + 8 * k)
      (by omega_arith)
    rw [← m₂] at oK
    have wK : ∀ d, d + 8 ≤ 16 + 8 * k ∨ 16 + 8 * k + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
        d + 8 ≤ 80 + 8 * k ∨ 80 + 8 * k + 8 ≤ d → word u₂.mem L.B d = word u₁.mem L.B d := fun d h₁ h₂ h₃ => by
      rw [Proof.Mont.Outside.word oK h₁ h₂, Proof.Mont.Outside.word oV h₃ h₂]
    have wsK : wordsVal u₂.mem L.B 16 k = wordsVal u₁.mem L.B 16 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inl (by omega_arith)) (by omega_arith),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_arith)) (by omega_arith)]
    have wsV : wordsVal u₂.mem L.B 80 k = wordsVal u₁.mem L.B 80 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inr (by omega_arith)) (by omega_arith),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_arith)) (by omega_arith)]
    have hV : word u₂.mem L.B (80 + 8 * k) = xw P L t.mem k := by
      rw [Proof.Mont.Outside.word oK (.inr (by omega_arith)) (by omega_arith), Proof.Mont.word_writeW_self]
    have hK : word u₂.mem L.B (16 + 8 * k) = Word64.addCarry (xw P L t.mem k) (~~~(cfgOf P).nWord k) (!b) := by
      rw [m₂, Proof.Mont.word_writeW_self]
    refine ⟨k₁.trans k₂, O₁.trans ?_, fun j hj => ?_, _, fun h => absurd h (by omega_arith), fun _ => by
      rw [cf₂, Bool.not_not], ?_⟩
    · rw [m₂]
      exact ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wK _ (.inr (by omega_arith)) (by omega_arith) (.inl (by omega_arith)), e₁ j hj]
      · exact hV
    · rw [wordsVal_succ_top, wordsVal_succ_top, wsK, wsV, hK, hV, n_split]
      have e := sub_borrow (xw P L t.mem k) ((cfgOf P).nWord k) (!b)
      rw [Bool.not_not] at e
      have hn : (cfgOf P).nWord k = BitVec.ofNat 64 (P.R.E.C.n >>> (64 * k)) := rfl
      rw [hn] at e ⊢
      rw [Proof.Mont.pow64_succ]
      generalize 2 ^ (64 * k) = Q at *
      exact borrow_step hs e

/-! ## The selection -/

theorem hBase_ne : (cfgOf P).hBase ≠ .x2 ∧ (cfgOf P).hBase ≠ .x6 ∧ (cfgOf P).hBase ≠ .x8 ∧
    (cfgOf P).hBase ≠ .x12 := by
  unfold Cfg.hBase; split <;> decide

/-- Word `j` of the result, by the mask `x6`, to `h + Q - 8 (j + 1)`. -/
theorem selWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (h14 : u.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8)) {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).selWord j)) u fun u' => RK u u' ∧ u'.gpr .x6 = u.gpr .x6 ∧
      u'.mem = u.mem.writeW (off L.B (144 + P.Q - 8 * (j + 1)))
        (rev64 (((word u.mem L.B (80 + 8 * j) ^^^ word u.mem L.B (16 + 8 * j)) &&& u.gpr .x6) ^^^
          word u.mem L.B (16 + 8 * j))) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have hV : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (80 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_arith) (by omega_arith)
  have hK : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (16 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_arith) (by omega_arith)
  have hH : InRegions u.wr (L.B + BitVec.ofNat 64 (144 + P.Q - 8 * (j + 1))) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)
  have aV : ∀ s : State, addr s 8 .x15 (fV + 8 * j) = some (s.gpr .x15 + BitVec.ofNat 64 (fV + 8 * j)) :=
    fun s => addr8 s .x15 (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)
  have aK : ∀ s : State, addr s 8 .x15 (fK + 8 * j) = some (s.gpr .x15 + BitVec.ofNat 64 (fK + 8 * j)) :=
    fun s => addr8 s .x15 (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
  have aH : ∀ s : State, addr s 8 (cfgOf P).hBase (fH + P.Q - P.Q % 8 - 8 * (j + 1)) =
      some (s.gpr (cfgOf P).hBase + BitVec.ofNat 64 (fH + P.Q - P.Q % 8 - 8 * (j + 1))) :=
    fun s => addr8 s _ (by simp only [fH]; omega_arith) (by simp only [fH]; omega_arith)
  have e80 : 16 + (fV + 8 * j) = 80 + 8 * j := by simp only [fV]; omega_arith
  have e16 : 16 + (fK + 8 * j) = 16 + 8 * j := by simp only [fK]; omega_arith
  have e144 : 16 + P.Q % 8 + (fH + P.Q - P.Q % 8 - 8 * (j + 1)) = 144 + P.Q - 8 * (j + 1) := by
    simp only [fH]; omega_arith
  have hl : (cfgOf P).len = P.Q := rfl
  have h14' : u.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8) := h14
  obtain ⟨n2, -, n8, -⟩ := hBase_ne (P := P)
  simp only [Cfg.selWord, hl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, aV, aK, aH, Size.bytes, Size.bits, Option.bind_some,
    State.load, State.store, State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, reduceCtorEq, ite_false, ite_true, h15, Offset.add_add, e80, e16, hV, hK, n2, n8, h14',
    e144, hH, Option.map_some, read8, write8, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by atriv, by atriv, by atriv, fun r a _ c _ => ?_⟩, by atriv, by atriv⟩
  simp only [RegUpd.gpr_write, a, c, ite_false]

/-- After `k` words of the result, with the mask of the borrow `b` in `x6`. -/
theorem sels_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (h14 : u.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8)) {b : Bool}
    (hm : u.gpr .x6 = if b then BitVec.allOnes 64 else 0) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).selWord)) u fun u' =>
      RK u u' ∧ u'.gpr .x6 = u.gpr .x6 ∧ Outside L.B 136 56 u.mem u'.mem ∧
      ∀ j < k, word u'.mem L.B (144 + P.Q - 8 * (j + 1)) = rev64 (word u.mem L.B ((if b then 80 else 16) + 8 * j))
  | 0, _ => WP.block_nil ⟨RK.refl _, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk' => by
    obtain ⟨hQ, h6, -⟩ := P.sizesA hA
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sels_ok hA hc hk h15 h14 hm k (by omega_arith)) fun u₁ ⟨k₁, d₁, O₁, e₁⟩ => ?_
    have h14₁ : u₁.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8) := by
      obtain ⟨n2, n6, n8, n12⟩ := hBase_ne (P := P)
      rw [k₁.gpr _ n2 n6 n8 n12, h14]
    refine WP.mono (selWord_ok (P := P) hA hc (hk.trans k₁) (k₁.x15.trans h15) h14₁ (j := k) (by omega_arith))
      fun u₂ ⟨k₂, d₂, m₂⟩ => ?_
    have oH : Outside L.B (144 + P.Q - 8 * (k + 1)) 8 u₁.mem u₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    have hV : word u₁.mem L.B (80 + 8 * k) = word u.mem L.B (80 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_arith)) (by omega_arith)
    have hK : word u₁.mem L.B (16 + 8 * k) = word u.mem L.B (16 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_arith)) (by omega_arith)
    refine ⟨k₁.trans k₂, d₂.trans d₁, O₁.trans (oH.mono (by omega_arith) (by omega_arith)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Proof.Mont.Outside.word oH (by omega_arith) (by omega_arith), e₁ j hj]
    · rw [m₂, Proof.Mont.word_writeW_self, hV, hK, d₁, hm, sel_mask]
      cases b <;> rfl

/-! ## The whole of it -/

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {k : Nat} (hn : k ≤ dn) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg k) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg k) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega_arith)).symm

/-- `digest` in `x1`. -/
theorem digestPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.digestPtr) t (Upd L g m₀ t .x1 L.dg) := by
  have p := hc.inFr (d := 208) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.digestPtr, fDigest, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, State.load, hc.sp, Offset.add_add, Nat.reduceAdd, p, Option.map_some,
    read8, hc.pDg, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x1) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl, rfl,
    by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- A callee-saved register is none of the registers `rs` the code writes. -/
theorem not_pres {r : Reg} (hr : r ∈ preserved) (rs : List Reg) (h : ∀ q ∈ rs, q ∉ preserved) : r ∉ rs :=
  fun h' => h r h' hr

/-- `x7 = 0` and the frame in `x15`. -/
theorem setup_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block ([.movz .x .x7 0 0, .addSp .x15 0] : List Instr)) t fun u =>
      u.gpr .x7 = 0 ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ ∀ r, r ≠ .x7 → r ≠ .x15 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide,
    ite_true, Nat.reduceLT, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, reduceCtorEq, ite_false, hc.sp, BitVec.add_zero, BitVec.setWidth_eq, Option.some.injEq,
    exists_eq_left']
  refine ⟨by atriv, by atriv, by atriv, by atriv, by atriv, by atriv, fun r h₁ h₂ => ?_⟩
  simp only [h₁, h₂, ite_false]

/-- The bases the words are loaded and stored through (`Cfg.dgBase`,
`Cfg.hBase`): `x1` and `x15`, or `x13 = digest + Q % 8` and
`x14 = sp + Q % 8`. -/
theorem bases_ok {t : State} (h1 : t.gpr .x1 = L.dg) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16) :
    WP isa (.block (if (cfgOf P).len % 8 = 0 then []
        else [.addImm .x .x13 .x1 ((cfgOf P).len % 8), .addImm .x .x14 .x15 ((cfgOf P).len % 8)])) t fun u =>
      u.gpr (cfgOf P).dgBase = L.dg + BitVec.ofNat 64 (P.Q % 8) ∧
      u.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8) ∧ u.mem = t.mem ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ u.sp = t.sp ∧ u.c = t.c ∧ ∀ r, r ≠ .x13 → r ≠ .x14 → u.gpr r = t.gpr r := by
  have hl : (cfgOf P).len = P.Q := rfl
  have h8 := P.R.len_words
  by_cases hq : P.Q % 8 = 0
  · have hq' : (cfgOf P).len % 8 = 0 := hq
    have db : (cfgOf P).dgBase = .x1 := by unfold Cfg.dgBase; rw [ite_eq_left_of_eq_true _ _ (eq_true hq')]
    have hb : (cfgOf P).hBase = .x15 := by unfold Cfg.hBase; rw [ite_eq_left_of_eq_true _ _ (eq_true hq')]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hq')]
    exact WP.block_nil ⟨by rw [db, h1, hq, BitVec.add_zero], by rw [hb, h15, hq], rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  · have hq' : ¬ (cfgOf P).len % 8 = 0 := hq
    have db : (cfgOf P).dgBase = .x13 := by unfold Cfg.dgBase; rw [ite_eq_right_of_eq_false _ _ (eq_false hq')]
    have hb : (cfgOf P).hBase = .x14 := by unfold Cfg.hBase; rw [ite_eq_right_of_eq_false _ _ (eq_false hq')]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hq'), db, hb, hl]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show P.Q % 8 < 4096 by omega_arith, ite_true, read_x,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, reduceCtorEq,
      ite_false, h1, h15, Offset.add_add, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨by atriv, by atriv, by atriv, by atriv, by atriv, by atriv, by atriv, fun r h₁ h₂ => ?_⟩
    simp only [h₁, h₂, ite_false]

/-- `h`: the digest's leftmost `Q` bytes (at `x1`) modulo `n`, big-endian
in the frame's `Q` bytes at `h`. -/
theorem reduce_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h1 : t.gpr .x1 = L.dg)
    (hdn : P.Q ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 176⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.Q) % P.R.E.C.n) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_syms (setup_ok hc) fun u₀ ⟨z₀, f₀, m₀', rd₀, wr₀, sp₀, g₀⟩ sy₀ => ?_
  refine WP.mono_syms (bases_ok (P := P) ((g₀ _ (by decide) (by decide)).trans h1) f₀)
    fun v₀ ⟨b13, b14, mv, rdv, wrv, spv, _, gv⟩ syv => ?_
  have g₀' : ∀ r, r ≠ .x7 → r ≠ .x15 → r ≠ .x13 → r ≠ .x14 → v₀.gpr r = t.gpr r := fun r a b c d =>
    (gv r c d).trans (g₀ r a b)
  have hc₀ : Ctx L g m₀ v₀ := hc.regs hL (rdv.trans rd₀) (wrv.trans wr₀) (mv.trans m₀') (spv.trans sp₀)
    (fun r hr _ => g₀' r (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide)))
    (syv.trans sy₀)
  have z₀' : v₀.gpr .x7 = 0 := (gv _ (by decide) (by decide)).trans z₀
  have f₀' : v₀.gpr .x15 = L.B + BitVec.ofNat 64 16 := (gv _ (by decide) (by decide)).trans f₀
  have h1' : v₀.gpr .x1 = L.dg := (g₀' _ (by decide) (by decide) (by decide) (by decide)).trans h1
  refine WP.mono_syms (subs_ok hA hc₀ hL h1' hdn b13 f₀' P.w (Nat.le_refl _))
    fun u₁ ⟨k₁, O₁, e₁, b, _, hcf, hs⟩ sy₁ => ?_
  have h4 : 4 ≤ P.w := P.R.n4
  have hcf₁ : u₁.c = !b := hcf (by omega_arith)
  -- The mask of the borrow.
  refine WP.mono_syms (show WP isa (.block ([.sbc .x .x6 .x7 .x7] : List Instr)) u₁ fun u₂ =>
      RK u₁ u₂ ∧ u₂.mem = u₁.mem ∧ u₂.gpr .x6 = if b then BitVec.allOnes 64 else 0 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, RegUpd.mem_write,
      BitVec.setWidth_eq, k₁.x7, z₀', hcf₁, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨by atriv, by atriv, by atriv, fun r _ h₂ _ _ => ?_⟩, by atriv, ?_⟩
    · simp only [RegUpd.gpr_write, h₂, ite_false]
    · cases b <;> decide) fun u₂ ⟨k₂, m₂, d₂⟩ sy₂ => ?_
  have h14₂ : u₂.gpr (cfgOf P).hBase = L.B + BitVec.ofNat 64 (16 + P.Q % 8) := by
    obtain ⟨n2, n6, n8, n12⟩ := hBase_ne (P := P)
    rw [k₂.gpr _ n2 n6 n8 n12, k₁.gpr _ n2 n6 n8 n12, b14]
  refine WP.mono_syms (sels_ok (P := P) hA hc₀ (k₁.trans k₂) ((k₂.x15.trans k₁.x15).trans f₀') h14₂ d₂ P.w
    (Nat.le_refl _)) fun t' ⟨k₃, _, O₃, e₃⟩ sy₃ => ?_
  have k' : RK v₀ t' := (k₁.trans k₂).trans k₃
  have O' : Outside L.B 16 176 t.mem t'.mem := by
    rw [← m₀', ← mv]
    exact (O₁.mono (by omega_arith) (by omega_arith)).trans
      ((by rw [m₂]; exact Outside.refl _ _ _ _ : Outside L.B 16 176 u₁.mem u₂.mem).trans
        (O₃.mono (by omega_arith) (by omega_arith)))
  have hf : Frame [⟨L.B + BitVec.ofNat 64 16, 176⟩] t.mem t'.mem := frame_of_outside O' (by omega_arith)
  refine ⟨hc.keep hL (k'.rd.trans (rdv.trans rd₀)) (k'.wr.trans (wrv.trans wr₀)) (k'.sp.trans (spv.trans sp₀))
    (fun r hr _ => (k'.gpr r (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide))).trans
      (g₀' r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
        (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))))
    hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith))
    (sy₃.trans (sy₂.trans (sy₁.trans (syv.trans sy₀)))), hf, ?_⟩
  -- The number, the difference, and the one selected.
  obtain ⟨w', hw'⟩ : ∃ w', P.w = w' + 1 := ⟨P.w - 1, by omega_arith⟩
  have hX : wordsVal u₁.mem L.B 80 P.w = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt v₀.mem L.dg P.Q) := by
    rw [hw']
    exact Proof.Weierstrass.wordsVal_eq_ofBytes_len _ _ _ _ 80 w' P.Q (by omega_arith) (by omega_arith) fun j hj => by
      rw [e₁ j (by omega_arith), xw_eq P L v₀.mem (by omega_arith)]
  have hsel := Proof.Weierstrass.bytesAt_eq_toBytes t'.mem u₂.mem L.B (L.B + BitVec.ofNat 64 (144 + P.Q - 8 * P.w))
    (a := if b then 80 else 16) (n := P.w) true fun j hj => by
      rw [Offset.add_add, show 144 + P.Q - 8 * P.w + 8 * (P.w - 1 - j) = 144 + P.Q - 8 * (j + 1) by omega_arith]
      simp only [ite_true, BitVec.and_allOnes]
      exact e₃ j hj
  simp only [ite_true] at hsel
  have hd := dg_ofBytes hL hc hdn
  rw [mv, m₀'] at hX
  rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl] at hX hd ⊢
  have hu : ∀ d, wordsVal u₂.mem L.B d P.w = wordsVal u₁.mem L.B d P.w := fun d => by rw [m₂]
  have hn : P.R.E.C.n % 2 ^ (64 * P.w) = P.R.E.C.n := Nat.mod_eq_of_lt P.R.n_lt
  rw [hn] at hs
  have hN := (P.R.sizesA hA).2.2.2
  have hXl : wordsVal u₁.mem L.B 80 P.w < 2 * P.R.E.C.n := by
    rw [hX]
    have := Rfc6979.ofBytes_lt (Spec.Ecdsa.bytesAt t.mem L.dg P.Q)
    rw [Proof.Weierstrass.length_bytesAt] at this
    exact Nat.lt_trans this hN
  have key := Rfc6979.mod_math2 _ _ _ _ b hs (wordsVal_lt _ _ _ _) hXl
  have hv : (if b then wordsVal u₂.mem L.B 80 P.w else wordsVal u₂.mem L.B 16 P.w) =
      Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n := by
    rw [← hX, ← key, hu, hu]
  have hlt : Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n < 2 ^ (8 * P.Q) := by
    have := Nat.mod_lt (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q)) (Nat.pos_of_ne_zero P.R.n_ne)
    have hb : P.R.E.C.n < 2 ^ (8 * P.R.E.C.len) := by
      have := Nat.lt_log2_self (n := P.R.E.C.n)
      rwa [show P.R.E.C.n.log2 + 1 = 8 * P.R.E.C.len from (P.R.sizesA hA).2.2.1] at this
    show _ < 2 ^ (8 * P.R.E.C.len)
    omega_arith
  have hsel' : Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (144 + P.Q - 8 * P.w)) (8 * P.w) =
      Spec.Weierstrass.toBytes (8 * P.w) (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n) := by
    rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl, hsel]
    refine congrArg _ ?_
    rw [← hv]; cases b <;> rfl
  rw [show 8 * P.w = (8 * P.w - P.Q) + P.Q by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show 144 + P.Q - ((8 * P.w - P.Q) + P.Q) + (8 * P.w - P.Q) = 144 by omega_arith,
    Rfc6979.toBytes_pad _ _ _ hlt] at hsel'
  rw [hd]
  exact (List.append_inj' hsel' (by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range, Proof.Weierstrass.length_toBytes])).2

end VG.Proof.Ecdsa.Rfc6979.AArch64
