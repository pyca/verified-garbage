import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Deterministic ECDSA on x86-64: `h = bits2octets(digest)`

The digest's leftmost `8 w` bytes, a word at a time from the least
significant: each to `V`'s place, and it minus the word of `n` (with the
borrow of the words before) to `K`'s (`subs_ok`); then, by the mask of the
last borrow, the number's words or the difference's, big-endian to `h`
(`sels_ok`). The number is below `2^(64 w) < 2n`, so this is it modulo `n`
(`mod_mathK`, `reduce_ok`).
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

/-- Word `j` of the number at `digest`, least significant first. -/
abbrev xw (P : RfcHash) (L : Lay dn) (m : Mem) (j : Nat) : BitVec 64 :=
  bswap64 (m.readW (L.dg + BitVec.ofNat 64 (8 * (P.w - 1 - j))) 64)

/-- Only `rax`, `rcx` and `rdx` (and the flags and memory) changed since `t`. -/
structure RK (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r

theorem RK.refl (t : State) : RK t t := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem RK.trans {t u v : State} (h₁ : RK t u) (h₂ : RK u v) : RK t v :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c)⟩

/-! ## The subtraction -/

/-- Word `j`: of the number to `V`'s place, of the difference to `K`'s. -/
theorem subWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg)
    (hdn : 8 * P.w ≤ dn) {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) {c : Bool}
    (hcf : j = 0 ∨ u.cf = some c) :
    WP isa (.block ((cfgOf P).subWord j)) u fun u' => RK u u' ∧
      u'.mem = (u.mem.writeW (off L.B (88 + 8 * j)) (xw P L u.mem j)).writeW (off L.B (24 + 8 * j))
        (xw P L u.mem j - (cfgOf P).nWord j - (BitVec.ofBool (j != 0 && c)).setWidth 64) ∧
      u'.cf = some (decide ((xw P L u.mem j).toNat < ((cfgOf P).nWord j).toNat + (j != 0 && c).toNat)) := by
  have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
  have hrsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [hk.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  have hrsi : u.gpr .rsi = L.dg := by rw [hk.gpr _ (by decide) (by decide) (by decide), hsi]
  have hr : InRegions (u.rd ++ u.wr) (L.dg + BitVec.ofNat 64 (8 * (P.w - 1 - j))) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inDg (by omega) (by omega)
  have hV : InRegions u.wr (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega) (by omega)
  have hK : InRegions u.wr (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega) (by omega)
  have e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [Cfg.subWord, cfgOf, fV, fK, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.load64, State.store64, ea_stk, ea_at, hrsp, hrsi, Offset.add_add, e88,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_false, hr, hV, hK, Nat.mul_zero, Nat.add_zero,
      Option.some.injEq, exists_eq_left']
    have hb : (0 != 0 && c) = false := rfl
    refine ⟨⟨rfl, rfl, fun r h₁ _ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]
    · have h0 : ∀ a : BitVec 64, a - (BitVec.ofBool false).setWidth 64 = a := fun a => by simp
      rw [hb, h0]
    · simp only [hb, Bool.toNat_false, Nat.add_zero]
  · have hcf' : u.cf = some c := hcf.resolve_left (by omega)
    have hj' : j ≠ 0 := by omega
    simp only [Cfg.subWord, cfgOf, fV, fK, hj', ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.load64, State.store64, ea_stk, ea_at, hrsp, hrsi, Offset.add_add, e88, Nat.zero_add,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      hcf', Option.map_some, Option.bind_some, reduceCtorEq, hr, hV, hK, ite_true, Option.some.injEq,
      exists_eq_left']
    have hb : (j != 0 && c) = c := by simp [hj']
    refine ⟨⟨rfl, rfl, fun r h₁ _ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]
    · rw [hb]
    · simp only [hb]

/-- The digest is apart from the stack, so code that writes only in the
frame keeps its words. -/
theorem dg_kept (hL : L.Ok) {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240) {d : Nat}
    (hd : d + 8 ≤ dn) : m'.readW (L.dg + BitVec.ofNat 64 d) 64 = m.readW (L.dg + BitVec.ofNat 64 d) 64 :=
  Proof.Weierstrass.readW_keep fun i hi =>
    Proof.Weierstrass.keep_of_disjoint (k := dn) h ((hL.kg.symm).sub_right (Offset.sub_base _ (by omega))) (by omega)
      (by omega) (by have := hL.ng; omega)

/-- After `k` words: the number's in `V`'s place, and the difference in
`K`'s with the borrow. -/
theorem subs_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) (hsi : t.gpr .rsi = L.dg) (hdn : 8 * P.w ≤ dn) :
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
    have hx : xw P L u₁.mem k = xw P L t.mem k := by
      simp only [xw]; rw [dg_kept hL O₁ (by omega) (by omega)]
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
      grind

/-! ## The selection -/

/-- Word `j` of the result, by the mask `rdx`, to `h`. -/
theorem selWord_ok (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).selWord j)) u fun u' => RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧
      u'.mem = u.mem.writeW (off L.B (152 + 8 * (P.w - 1 - j)))
        (bswap64 (((word u.mem L.B (88 + 8 * j) ^^^ word u.mem L.B (24 + 8 * j)) &&& u.gpr .rdx) ^^^
          word u.mem L.B (24 + 8 * j))) := by
  have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
  have hrsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [hk.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  have hV : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega) (by omega)
  have hK : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega) (by omega)
  have hH : InRegions u.wr (L.B + BitVec.ofNat 64 (152 + 8 * (P.w - 1 - j))) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega) (by omega)
  have e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega
  have hwn : P.w = P.R.E.n := rfl
  have e152 : 24 + (128 + 8 * (P.R.E.n - 1 - j)) = 152 + 8 * (P.w - 1 - j) := by omega
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
      RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧ Outside L.B 152 48 u.mem u'.mem ∧
      ∀ j < k, word u'.mem L.B (152 + 8 * (P.w - 1 - j)) = bswap64 (word u.mem L.B ((if c then 88 else 24) + 8 * j))
  | 0, _ => WP.block_nil ⟨RK.refl _, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk' => by
    have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sels_ok hA hc hk hm k (by omega)) fun u₁ ⟨k₁, d₁, O₁, e₁⟩ => ?_
    refine WP.mono (selWord_ok (P := P) hA hc (hk.trans k₁) (j := k) (by omega)) fun u₂ ⟨k₂, d₂, m₂⟩ => ?_
    have oH : Outside L.B (152 + 8 * (P.w - 1 - k)) 8 u₁.mem u₂.mem := by
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
    exact ⟨hc.set hL (d := .rsi) (by decide) rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial,
      trivial, fun h => absurd h (by decide)⟩
  · simp only [Cfg.digestPtr, cfgOf, hw, ite_true, fDigest, fScratch, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk, hc.rsp, Offset.add_add,
      Nat.reduceAdd, p, p', ite_true, Option.map_some, hc.pDg, hc.pScr, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false,
      forall_const]
    exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

/-- `h`: the digest's leftmost `8 w` bytes (at `rsi`) modulo `n`, big-endian
in the frame. -/
theorem reduce_ok (hA : P.R.wide = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) (hdn : 8 * P.w ≤ dn) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 176⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 152) (8 * P.w) =
        Spec.Weierstrass.toBytes (8 * P.w)
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg (8 * P.w)) % P.R.E.C.n) := by
  have h6 : P.w ≤ 6 := (P.sizesA hA).2.1
  have h4 : 4 ≤ P.w := P.R.n4
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
  refine WP.mono (sels_ok (P := P) hA hc (k₁.trans k₂) d₂ P.w (Nat.le_refl _)) fun t' ⟨k₃, _, O₃, e₃⟩ => ?_
  have k' : RK t t' := (k₁.trans k₂).trans k₃
  have O' : Outside L.B 24 176 t.mem t'.mem :=
    (O₁.mono (by omega) (by omega)).trans ((by rw [m₂]; exact Outside.refl _ _ _ _ : Outside L.B 24 176 u₁.mem u₂.mem).trans
      (O₃.mono (by omega) (by omega)))
  have hf : Frame [⟨L.B + BitVec.ofNat 64 24, 176⟩] t.mem t'.mem := frame_of_outside O' (by omega)
  refine ⟨hc.keep hL k'.rd k'.wr (k'.gpr _ (by decide) (by decide) (by decide))
    (fun r hr _ => k'.gpr r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide))) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)), hf, ?_⟩
  -- The number, the difference, and the one selected.
  have hX : wordsVal u₁.mem L.B 88 P.w = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg (8 * P.w)) :=
    Proof.Weierstrass.wordsVal_eq_ofBytes _ _ _ _ _ _ fun j hj => e₁ j hj
  have hsel := Proof.Weierstrass.bytesAt_eq_toBytes t'.mem u₂.mem L.B (L.B + BitVec.ofNat 64 152)
    (a := if c then 88 else 24) (n := P.w) true fun j hj => by
      rw [Offset.add_add]
      simp only [ite_true, BitVec.and_allOnes]
      exact e₃ j hj
  simp only [ite_true] at hsel
  have hd := dg_ofBytes hL hc hdn
  rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl] at hX hd ⊢
  rw [hsel, hd, ← hX]
  have hu : ∀ d, wordsVal u₂.mem L.B d P.w = wordsVal u₁.mem L.B d P.w := fun d => by rw [m₂]
  have hn : P.R.E.C.n % 2 ^ (64 * P.w) = P.R.E.C.n := Nat.mod_eq_of_lt P.R.n_lt
  rw [hn] at hs
  have key := mod_mathK _ _ _ _ c hs (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) (P.R.sizesA hA).2.2.2
  congr 1
  rw [← key, hu]
  cases c <;> rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
