import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Deterministic ECDSA on x86-64: `h = bits2octets(digest)`

The digest's leftmost `Q` bytes, a word at a time from the least
significant (a top word of four bytes, if `Q = 8 w - 4`, by a 32-bit load:
`loadWord_ok`): each to `V`'s place, and it minus the word of `n` (with the
borrow of the words before) to `K`'s (`subs_ok`); then, by the mask of the
last borrow, the number's words or the difference's, big-endian to the `Q`
bytes at `h` (`sels_ok`), the top word's zero bytes below them. The number
is below `2^(8 Q) < 2n`, so this is it modulo `n` (`mod_mathK`,
`reduce_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.X25519.X86_64 (sub_borrow sbb_borrow)
open VG.Proof.Mont (word wordsVal wordsVal_lt wordsVal_succ_top Outside off ofs writeW_outside)

theorem sel_mask (x d : BitVec 64) (y : BitVec 64) (c : Bool) :
    ((x ^^^ d) &&& (y - y - (BitVec.ofBool c).setWidth 64)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · have : y - y - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp

/-- The low `k + 1` words of `n`: its low `k`, and word `k`. -/
theorem n_split (n k : Nat) :
    n % 2 ^ (64 * (k + 1)) = n % 2 ^ (64 * k) + 2 ^ (64 * k) * (BitVec.ofNat 64 (n >>> (64 * k))).toNat := by
  rw [show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add, Nat.mod_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- Word `j` of the number at `digest`, least significant first: a top
word of four bytes is zero-extended. -/
def xw (P : RfcHash) (L : Lay dn) (m : Mem) (j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ P.Q then bswap64 (m.readW (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
  else if P.Q ≤ 8 * j then 0
  else (bswap32 (m.readW L.dg 32)).setWidth 64

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
  omega

/-- The first four bytes at `a`, big-endian: the eight bytes', shifted right. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    (bswap32 (m.readW a 32)).setWidth 64 = byteRev64 (m.readW a 64) >>> 32 := by
  rw [show bswap32 (m.readW a 32) = byteRev32 (m.readW a 32) from rfl, byteRev32_readW, byteRev64_readW,
    cat8_shr]

/-- The words, as `loadBytes` reads them (`Proof.Weierstrass.X86_64.ldWord`). -/
theorem xw_eq (P : RfcHash) (L : Lay dn) (m : Mem) {j : Nat} (h : 8 * (j + 1) ≤ P.Q ∨ 8 * (j + 1) = P.Q + 4 ∨ 8 * (j + 1) = P.Q + 8) :
    xw P L m j = if 8 * (j + 1) ≤ P.Q then byteRev64 (m.readW (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
      else byteRev64 (m.readW L.dg 64) >>> (8 * (8 * (j + 1) - P.Q)) := by
  unfold xw
  split
  · rfl
  · split
    · rw [BitVec.ushiftRight_eq_zero (by omega)]; rfl
    · rw [bswap32_readW, show 8 * (8 * (j + 1) - P.Q) = 32 by omega]

/-- Only `rax`, `rcx` and `rdx` (and the flags and memory) changed since `t`. -/
structure RK (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r

theorem RK.refl (t : State) : RK t t := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem RK.trans {t u v : State} (h₁ : RK t u) (h₂ : RK u v) : RK t v :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c)⟩

/-! ## The subtraction -/

/-- Word `j` of the number at `digest`, in `rax`, the flags kept. -/
theorem loadWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg)
    (hdn : P.Q ≤ dn) {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).loadWord j)) u fun u' => RK u u' ∧ u'.mem = u.mem ∧ u'.cf = u.cf ∧
      u'.gpr .rax = xw P L u.mem j := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have hrsi : u.gpr .rsi = L.dg := by rw [hk.gpr _ (by decide) (by decide) (by decide), hsi]
  apply WP.of_runBlock
  by_cases h : 8 * (j + 1) ≤ P.Q
  · have hr : InRegions (u.rd ++ u.wr) (L.dg + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 8 := by
      rw [hk.rd, hk.wr]; exact hc.inDg (by omega) (by omega)
    have h' : 8 * (j + 1) ≤ (cfgOf P).len := h
    rw [Cfg.loadWord, ite_eq_left_of_eq_true _ _ (eq_true h'), show (cfgOf P).len = P.Q from rfl]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
      RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
    · simp only [RegUpd.gpr_setReg, h₁, ite_false]
    · simp only [xw, h, ite_true]
  · by_cases hz : P.Q ≤ 8 * j
    · rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 8 * (j + 1) ≤ (cfgOf P).len from h)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, fun r hr _ _ => ?_⟩, trivial, trivial, ?_⟩
      · simp only [RegUpd.gpr_setReg, hr, ite_false]
      · simp [xw, h, hz]
    · have hr : InRegions (u.rd ++ u.wr) (L.dg + BitVec.ofNat 64 0) 4 := by
        rw [hk.rd, hk.wr]; exact hc.inDg (by omega) (by omega)
      have h' : ¬ 8 * (j + 1) ≤ (cfgOf P).len := h
      rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
        State.load32, State.setReg32, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
        RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
      · simp only [RegUpd.gpr_setReg, h₁, ite_false]
      · simp only [xw, h, hz, ite_false, add_ofNat_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_eq]

/-- Word `j`: of the number to `V`'s place, of the difference to `K`'s. -/
theorem subWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg)
    (hdn : P.Q ≤ dn) {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) {c : Bool}
    (hcf : j = 0 ∨ u.cf = some c) :
    WP isa (.block ((cfgOf P).subWord j)) u fun u' => RK u u' ∧
      u'.mem = (u.mem.writeW (off L.B (88 + 8 * j)) (xw P L u.mem j)).writeW (off L.B (24 + 8 * j))
        (xw P L u.mem j - (cfgOf P).nWord j - (BitVec.ofBool (j != 0 && c)).setWidth 64) ∧
      u'.cf = some (decide ((xw P L u.mem j).toNat < ((cfgOf P).nWord j).toNat + (j != 0 && c).toNat)) := by
  have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
  rw [Cfg.subWord, WP.block_append_iff]
  refine WP.mono (loadWord_ok hA hc hsi hdn hk hj) fun u₁ ⟨k₁, m₁, cf₁, ax₁⟩ => ?_
  have hk₁ := hk.trans k₁
  have hrsp : u₁.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hk₁.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  have hV : InRegions u₁.wr (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega) (by omega)
  have hK : InRegions u₁.wr (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega) (by omega)
  have e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega
  rw [← m₁] at ax₁ ⊢
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [fV, fK, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      Option.bind_some, reduceCtorEq, ite_false, hV, hK, Nat.mul_zero, Nat.add_zero,
      Option.some.injEq, exists_eq_left']
    have hb : (0 != 0 && c) = false := rfl
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · have h0 : ∀ a : BitVec 64, a - (BitVec.ofBool false).setWidth 64 = a := fun a => by simp
      rw [hb, h0]
    · simp only [hb, Bool.toNat_false, Nat.add_zero]
  · have hcf' : u₁.cf = some c := cf₁.trans (hcf.resolve_left (by omega))
    have hj' : j ≠ 0 := by omega
    simp only [fV, fK, hj', ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88, Nat.zero_add,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      hcf', Option.map_some, Option.bind_some, reduceCtorEq, hV, hK, ite_true, Option.some.injEq,
      exists_eq_left']
    have hb : (j != 0 && c) = c := by simp [hj']
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · rw [hb]
    · simp only [hb]

/-- The digest is apart from the stack, so code that writes only in the
frame keeps its words. -/
theorem dg_kept (hL : L.Ok) {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240) {d : Nat}
    (hd : d + 8 ≤ dn) : m'.readW (L.dg + BitVec.ofNat 64 d) 64 = m.readW (L.dg + BitVec.ofNat 64 d) 64 :=
  Proof.Weierstrass.readW_keep fun i hi =>
    Proof.Weierstrass.keep_of_disjoint (k := dn) h ((hL.kg.symm).sub_right (Offset.sub_base _ (by omega))) (by omega)
      (by omega) (by have := hL.ng; omega)

/-- The words of the number at `digest`, kept by code that writes only in the frame. -/
theorem xw_kept (hL : L.Ok) {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240)
    (hdn : P.Q ≤ dn) (h8 : 8 ≤ P.Q) (j : Nat) : xw P L m' j = xw P L m j := by
  unfold xw
  split
  · rw [dg_kept hL h hn (by omega)]
  · split
    · rfl
    · refine congrArg (fun x => (bswap32 x).setWidth 64) (Mem.readW_congr fun i hi => ?_)
      have e := Proof.Weierstrass.keep_of_disjoint (k := dn) h ((hL.kg.symm).sub_right (Offset.sub_base _ (by omega)))
        (by omega) (i := i) (by omega) (by have := hL.ng; omega)
      exact e

/-- One more word of a subtraction with borrow: the words below `k` (`hs`)
and word `k` (`e`), weighted by `Q = 2^(64 k)`. -/
private theorem borrow_step {a b r x y z c d Q : Nat} (hs : a + r = b + Q * c)
    (e : x + y + c = z + 2 ^ 64 * d) : a + Q * x + (r + Q * y) = b + Q * z + 2 ^ 64 * Q * d := by
  grind

/-- After `k` words: the number's in `V`'s place, and the difference in
`K`'s with the borrow. -/
theorem subs_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) (hsi : t.gpr .rsi = L.dg) (hdn : P.Q ≤ dn) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) t fun u =>
      RK t u ∧ Outside L.B 24 128 t.mem u.mem ∧ (∀ j < k, word u.mem L.B (88 + 8 * j) = xw P L t.mem j) ∧
      ∃ c : Bool, (k = 0 → c = false) ∧ (0 < k → u.cf = some c) ∧
        wordsVal u.mem L.B 24 k + P.R.E.C.n % 2 ^ (64 * k) = wordsVal u.mem L.B 88 k + 2 ^ (64 * k) * c.toNat
  | 0, _ => WP.block_nil ⟨RK.refl _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      false, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _), by simp [wordsVal, Nat.mod_one]⟩
  | k + 1, hk => by
    have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (subs_ok hA hc hL hsi hdn k (by omega)) fun u₁ ⟨k₁, O₁, e₁, c, hc0, hcf, hs⟩ => ?_
    refine WP.mono (subWord_ok (P := P) hA hc hsi hdn k₁ (j := k) (by omega) (c := c)
      (by rcases Nat.eq_zero_or_pos k with h | h; exacts [.inl h, .inr (hcf h)])) fun u₂ ⟨k₂, m₂, cf₂⟩ => ?_
    have hx : xw P L u₁.mem k = xw P L t.mem k := xw_kept hL O₁ (by omega) hdn P.R.len_words.1 k
    have hb : (k != 0 && c) = c := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; rw [hc0 rfl]; rfl
      · simp [show k ≠ 0 by omega]
    rw [hx, hb] at m₂ cf₂
    -- Each write is outside the other's word, and outside the words below `k`.
    have oK : Outside L.B (24 + 8 * k) 8 _ _ := writeW_outside (u₁.mem.writeW (off L.B (88 + 8 * k)) (xw P L t.mem k))
      L.B (xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64) (d := 24 + 8 * k) (by omega)
    have oV : Outside L.B (88 + 8 * k) 8 _ _ := writeW_outside u₁.mem L.B (xw P L t.mem k) (d := 88 + 8 * k)
      (by omega)
    rw [← m₂] at oK
    have wK : ∀ d, d + 8 ≤ 24 + 8 * k ∨ 24 + 8 * k + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
        d + 8 ≤ 88 + 8 * k ∨ 88 + 8 * k + 8 ≤ d → word u₂.mem L.B d = word u₁.mem L.B d := fun d h₁ h₂ h₃ => by
      rw [Proof.Mont.Outside.word oK h₁ h₂, Proof.Mont.Outside.word oV h₃ h₂]
    have wsK : wordsVal u₂.mem L.B 24 k = wordsVal u₁.mem L.B 24 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inl (by omega)) (by omega),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega)) (by omega)]
    have wsV : wordsVal u₂.mem L.B 88 k = wordsVal u₁.mem L.B 88 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inr (by omega)) (by omega),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega)) (by omega)]
    have hV : word u₂.mem L.B (88 + 8 * k) = xw P L t.mem k := by
      rw [Proof.Mont.Outside.word oK (.inr (by omega)) (by omega), Proof.Mont.word_writeW_self]
    have hK : word u₂.mem L.B (24 + 8 * k) =
        xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64 := by
      rw [m₂, Proof.Mont.word_writeW_self]
    refine ⟨k₁.trans k₂, O₁.trans ?_, fun j hj => ?_, _, fun h => absurd h (by omega), fun _ => cf₂, ?_⟩
    · rw [m₂]
      exact ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
        ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wK _ (.inr (by omega)) (by omega) (.inl (by omega)), e₁ j hj]
      · exact hV
    · rw [wordsVal_succ_top, wordsVal_succ_top, wsK, wsV, hK, hV, n_split]
      have e := sbb_borrow (xw P L t.mem k) ((cfgOf P).nWord k) c
      have hn : (cfgOf P).nWord k = BitVec.ofNat 64 (P.R.E.C.n >>> (64 * k)) := rfl
      rw [hn] at e ⊢
      rw [Proof.Mont.pow64_succ]
      generalize 2 ^ (64 * k) = Q at *
      exact borrow_step hs e

/-! ## The selection -/

/-- Word `j` of the result, by the mask `rdx`, to `h`. -/
theorem selWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).selWord j)) u fun u' => RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧
      u'.mem = u.mem.writeW (off L.B (152 + P.Q - 8 * (j + 1)))
        (bswap64 (((word u.mem L.B (88 + 8 * j) ^^^ word u.mem L.B (24 + 8 * j)) &&& u.gpr .rdx) ^^^
          word u.mem L.B (24 + 8 * j))) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have hrsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [hk.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  have hV : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega) (by omega)
  have hK : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega) (by omega)
  have hH : InRegions u.wr (L.B + BitVec.ofNat 64 (152 + P.Q - 8 * (j + 1))) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega) (by omega)
  have e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega
  have hwn : P.Q = P.R.E.C.len := rfl
  have e152 : 24 + (128 + P.R.E.C.len - 8 * (j + 1)) = 152 + P.Q - 8 * (j + 1) := by omega
  apply WP.of_runBlock
  simp only [Cfg.selWord, cfgOf, fV, fK, fH, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, State.store64, ea_stk, hrsp, Offset.add_add, e88, e152, Nat.zero_add,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hV, hK, hH, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by trivial, by trivial, fun r h₁ h₂ _ => ?_⟩, by trivial, by trivial⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₂, ite_false]

/-- After `k` words of the result, with the mask of the borrow `c` in `rdx`. -/
theorem sels_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u) {c : Bool} {y : BitVec 64}
    (hm : u.gpr .rdx = y - y - (BitVec.ofBool c).setWidth 64) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).selWord)) u fun u' =>
      RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧ Outside L.B 144 56 u.mem u'.mem ∧
      ∀ j < k, word u'.mem L.B (152 + P.Q - 8 * (j + 1)) = bswap64 (word u.mem L.B ((if c then 88 else 24) + 8 * j))
  | 0, _ => WP.block_nil ⟨RK.refl _, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk' => by
    obtain ⟨hQ, h6, -⟩ := P.sizesA hA
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sels_ok hA hc hk hm k (by omega)) fun u₁ ⟨k₁, d₁, O₁, e₁⟩ => ?_
    refine WP.mono (selWord_ok (P := P) hA hc (hk.trans k₁) (j := k) (by omega)) fun u₂ ⟨k₂, d₂, m₂⟩ => ?_
    have oH : Outside L.B (152 + P.Q - 8 * (k + 1)) 8 u₁.mem u₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    have hV : word u₁.mem L.B (88 + 8 * k) = word u.mem L.B (88 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega)) (by omega)
    have hK : word u₁.mem L.B (24 + 8 * k) = word u.mem L.B (24 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega)) (by omega)
    refine ⟨k₁.trans k₂, d₂.trans d₁, O₁.trans (oH.mono (by omega) (by omega)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Proof.Mont.Outside.word oH (by omega) (by omega), e₁ j hj]
    · rw [m₂, Proof.Mont.word_writeW_self, hV, hK, d₁, hm, sel_mask]
      cases c <;> rfl

/-! ## The whole of it -/

theorem dg_ofBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {k : Nat} (hn : k ≤ dn) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg k) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg k) := by
  congr 1
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega)).symm

/-- `digest` in `rsi`, and, if two `V`s make a candidate, `scratch` in `rdi`. -/
theorem digestPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).digestPtr) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .rsi = L.dg ∧
      (P.R.wide = true → t'.gpr .rdi = L.scr) := by
  have p := hc.inFr (d := 216) (by omega) (by omega)
  have p' := hc.inFr (d := 208) (by omega) (by omega)
  apply WP.of_runBlock
  cases hw : P.R.wide
  · simp only [Cfg.digestPtr, cfgOf, hw, Bool.false_eq_true, ite_false, List.append_nil, fDigest, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, p,
      ite_true, Option.map_some, hc.pDg, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self,
      RegUpd.mem_setReg, Bool.false_eq_true]
    exact ⟨hc.set hL (d := .rsi) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial,
      trivial, fun h => absurd h (by decide)⟩
  · simp only [Cfg.digestPtr, cfgOf, hw, ite_true, fDigest, fScratch, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add,
      Nat.reduceAdd, p, p', ite_true, Option.map_some, hc.pDg, hc.pScr, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false,
      forall_const]
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

/-- `h`: the digest's leftmost `Q` bytes (at `rsi`) modulo `n`, big-endian
in the frame. -/
theorem reduce_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) (hdn : P.Q ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 176⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 152) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.Q) % P.R.E.C.n) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have h4 : 4 ≤ P.w := P.R.n4
  refine WP.of_syms ?_
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (subs_ok hA hc hL hsi hdn P.w (Nat.le_refl _)) fun u₁ ⟨k₁, O₁, e₁, c, _, hcf, hs⟩ => ?_
  have hcf₁ : u₁.cf = some c := hcf (by omega)
  -- The mask of the borrow.
  refine WP.mono (show WP isa (.block ([.alu .sbb .rdx (.reg .rdx)] : List Instr)) u₁ fun u₂ =>
      RK u₁ u₂ ∧ u₂.mem = u₁.mem ∧ u₂.gpr .rdx = u₁.gpr .rdx - u₁.gpr .rdx - (BitVec.ofBool c).setWidth 64 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hcf₁, Option.map_some,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by trivial, by trivial, fun r _ _ h₃ => ?_⟩, by trivial, by trivial⟩
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₃, ite_false]) fun u₂ ⟨k₂, m₂, d₂⟩ => ?_
  refine WP.mono (sels_ok (P := P) hA hc (k₁.trans k₂) d₂ P.w (Nat.le_refl _)) fun t' ⟨k₃, _, O₃, e₃⟩ hsy => ?_
  have k' : RK t t' := (k₁.trans k₂).trans k₃
  have O' : Outside L.B 24 176 t.mem t'.mem :=
    (O₁.mono (by omega) (by omega)).trans ((by rw [m₂]; exact Outside.refl _ _ _ _ : Outside L.B 24 176 u₁.mem u₂.mem).trans
      (O₃.mono (by omega) (by omega)))
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 176⟩] t.mem t'.mem := frame_of_outside O' (by omega)
  refine ⟨hc.keep hL k'.rd k'.wr (k'.gpr _ (by decide) (by decide) (by decide))
    (fun r hr _ => k'.gpr r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide))) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)) hsy, hf, ?_⟩
  -- The number, the difference, and the one selected.
  obtain ⟨w', hw'⟩ : ∃ w', P.w = w' + 1 := ⟨P.w - 1, by omega⟩
  have hX : wordsVal u₁.mem L.B 88 P.w = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.Q) := by
    rw [hw']
    exact Proof.Weierstrass.wordsVal_eq_ofBytes_len _ _ _ _ 88 w' P.Q (by omega) (by omega) fun j hj => by
      rw [e₁ j (by omega), xw_eq P L t.mem (by omega)]
  have hsel := Proof.Weierstrass.bytesAt_eq_toBytes t'.mem u₂.mem L.B (L.B + BitVec.ofNat 64 (152 + P.Q - 8 * P.w))
    (a := if c then 88 else 24) (n := P.w) true fun j hj => by
      rw [Offset.add_add, show 152 + P.Q - 8 * P.w + 8 * (P.w - 1 - j) = 152 + P.Q - 8 * (j + 1) by omega]
      simp only [ite_true, BitVec.and_allOnes]
      exact e₃ j hj
  simp only [ite_true] at hsel
  have hd := dg_ofBytes hL hc hdn
  rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl] at hX hd ⊢
  have hu : ∀ d, wordsVal u₂.mem L.B d P.w = wordsVal u₁.mem L.B d P.w := fun d => by rw [m₂]
  have hn : P.R.E.C.n % 2 ^ (64 * P.w) = P.R.E.C.n := Nat.mod_eq_of_lt P.R.n_lt
  rw [hn] at hs
  have hN := (P.R.sizesA hA).2.2.2
  have hXl : wordsVal u₁.mem L.B 88 P.w < 2 * P.R.E.C.n := by
    rw [hX]
    have := Proof.Ecdsa.Rfc6979.ofBytes_lt (Spec.Ecdsa.bytesAt t.mem L.dg P.Q)
    rw [Proof.Weierstrass.length_bytesAt] at this
    exact Nat.lt_trans this hN
  have key := Proof.Ecdsa.Rfc6979.mod_math2 _ _ _ _ c hs (wordsVal_lt _ _ _ _) hXl
  -- `h`'s `Q` bytes are the last of the `8 w` the words were stored to.
  have hv : (if c then wordsVal u₂.mem L.B 88 P.w else wordsVal u₂.mem L.B 24 P.w) =
      Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n := by
    rw [← hX, ← key, hu, hu]
  have hlt : Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n < 2 ^ (8 * P.Q) := by
    have := Nat.mod_lt (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q)) (Nat.pos_of_ne_zero P.R.n_ne)
    have hb : P.R.E.C.n < 2 ^ (8 * P.R.E.C.len) := by
      have := Nat.lt_log2_self (n := P.R.E.C.n)
      rwa [show P.R.E.C.n.log2 + 1 = 8 * P.R.E.C.len from (P.R.sizesA hA).2.2.1] at this
    show _ < 2 ^ (8 * P.R.E.C.len)
    omega
  have hsel' : Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (152 + P.Q - 8 * P.w)) (8 * P.w) =
      Spec.Weierstrass.toBytes (8 * P.w) (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t.mem L.dg P.Q) % P.R.E.C.n) := by
    rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl, hsel]
    refine congrArg _ ?_
    rw [← hv]; cases c <;> rfl
  rw [show 8 * P.w = (8 * P.w - P.Q) + P.Q by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show 152 + P.Q - ((8 * P.w - P.Q) + P.Q) + (8 * P.w - P.Q) = 152 by omega,
    Proof.Ecdsa.Rfc6979.toBytes_pad _ _ _ hlt] at hsel'
  rw [hd]
  exact (List.append_inj' hsel' (by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range, Proof.Weierstrass.length_toBytes])).2

end VG.Proof.Ecdsa.Rfc6979.X86_64
