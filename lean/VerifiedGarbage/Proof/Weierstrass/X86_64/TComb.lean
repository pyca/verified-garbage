import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombPublic
import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.CombFrame

/-!
# The fixed-base comb from tables in memory on x86-64

As on AArch64 (`Proof/Weierstrass/AArch64/TComb.lean`): iteration `j`
selects the entry of the digit's magnitude (`digit_ok`, `select_ok`, whose
words are the entry's coordinates in Montgomery form, `tbl_entry`), negates
`y` for a negative digit (`tentry_ok`), and adds it to `A` with the mixed
addition for `a = -3` (`rcb3m_ok`, `Law.add3m`; the entry's `Z` is 1 unless
the digit is zero, `TEntryPost.z`), into `D`, which `A` takes unless the digit
is zero (`selPtKeep_ok`), when the entry is the point at infinity and the sum
`A` (`add_infinity`), so that `A`, which represented `[combEW (j+1)]G`,
represents `[combEW j]G` (`combW_add`, `tstep_ok`); after the `J` digits,
`[k]G` (`tcomb_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- What the comb needs of its tables `tbl` (affine points, whose Montgomery
forms `tcombWords` are in memory) and constants: `J` tables of `H` entries,
entry `m` of table `j` the point `[(m + 1) 2^(wj)]G`, the start (in
Montgomery form) `[H Σ_{i<J} 2^(wi)]G`, and `R mod p` one. -/
structure TCombVals (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : Prop where
  len : tbl.length = K.J
  lenH : ∀ j < K.J, (tbl.getD j []).length = K.H
  unit : UnitMod C.p (2 ^ (64 * K.M.n))
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < K.H, Rep C (Fin.ofNat C.p (combAt tbl j m).1)
    (Fin.ofNat C.p (combAt tbl j m).2) 1 (combPtW C K.w j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (K.H * geomW K.w K.J) (G C))

/-- `x ∈ l` for the comb's lists, through `toComb`. -/
macro "tcomb_mem" : tactic => `(tactic| first
  | list_mem
  | (simp only [List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true, combSlots,
      combWs, combRo, rcbW, rcbR, List.cons_append, List.nil_append, TCombCfg.toComb]))

/-- `a ≠ b` (or a conjunction of such, or `a ∉ [b, …]`) from `h`, the conjunction of `¬ x = y`
that a `Nodup` of the slots simplifies to, in either orientation: not `grind`, which takes a tenth
of a second for each. -/
macro "nd_ne " h:ident : tactic => `(tactic| (
  try simp only [ne_eq, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals first
    | nd_find $h:ident
    | simp only [ne_eq, $h:ident, not_false_eq_true]
    | exact Ne.symm (by simp only [ne_eq, $h:ident, not_false_eq_true])))

theorem r8_mem_clob (n : Nat) : Reg.r8 ∈ clob n := by
  simp [clob, acc]

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
structure TEntryPost (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (signedPtW C K.w k i)
  /-- The entry is affine (`Z = 1`) unless the digit is zero. -/
  z : tmv C K.M.n base s' K.E.z = if 1 ≤ magH K.H (combWin K.w k i) then 1 else 0

/-- The entry of digit `i`, selected (from `rbx = i`) and negated for a
negative digit. -/
theorem tentry_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (publicLookup : Bool := false) :
    WP isa (.block (K.digit ++ (if publicLookup then K.selectPublic else K.select))) s fun s₂ =>
      WP isa (.block K.negY) s₂ (TEntryPost K C base size k i s) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnn := hL.n
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hbits' := hL.bits
  have hH2 : 2 ^ K.w = 2 * K.H := by
    unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega_using [hw]
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have htmp : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.comb.lay.tmp x hx
  have hmo : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ K.M.mo ∨ K.M.mo + 8 * K.M.n ≤ x :=
    fun x hx => hL.comb.lay.mo x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  -- Apart slots as a function, not as facts in the context: `omega` would split every
  -- disjunction in the context at each of its calls.
  have ap : ∀ {x y : Nat}, x ∈ combWs K.toComb → y ∈ combWs K.toComb → x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun hx hy h => hL.comb.apart₂ hx hy h
  have hexy := hL.exy
  have hEx := hle K.E.x (by tcomb_mem)
  have hEy := hle K.E.y (by tcomb_mem)
  have hEz := hle K.E.z (by tcomb_mem)
  have hneg := hle K.neg (by tcomb_mem)
  have hzl := hle K.zero (by tcomb_mem)
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi); rwa [Nat.mul_succ] at this
  rw [WP.block_append_iff]
  refine WP.mono_syms (digit_ok K hs (k := k) (j := i) (N := K.w * K.J) hw.1 hw.2 hwi (by omega_using [hzw, hbits']) hx hbits)
    fun s₁ ⟨a₁, m₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hx₁ : s₁.gpr .rbx = BitVec.ofNat 64 i := by rw [k₁.1 _ (by decide), hx]
  have hwlt := combWin_lt K.w k i
  have hmag : magH K.H (combWin K.w k i) ≤ K.H := magH_le (by rw [← hH2]; exact hwlt)
  have hlen := tcombWords_length (n := K.M.n) (R := 2 ^ (64 * K.M.n)) (p := C.p) hV.len hV.lenH
  have hreg : InRegions (s₁.rd ++ s₁.wr) (T + BitVec.ofNat 64 (i * K.tblBytes)) K.tblBytes := by
    obtain ⟨r, hr, hc⟩ := hTM.rd
    refine ⟨r, by rw [k₁.2.2.1, k₁.2.2.2]; exact hr, Region.contains_off hc ?_⟩
    rw [hlen, TCombCfg.tblBytes]
    have h2 := Nat.mul_le_mul_right (16 * K.M.n * K.H) (show i + 1 ≤ K.J from hi)
    rw [Nat.succ_mul] at h2
    have e : 16 * K.M.n * K.H = 8 * (K.H * (2 * K.M.n)) := by
      rw [Nat.mul_comm K.H, ← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [Nat.mul_left_comm 8 K.J, ← e]
    omega_using [h2]
  refine WP.mono (selectChoice_ok publicLookup K hs₁ hnn (by omega_using [hHle]) hL.tbl hexy hEy hEz (by
      have := ap (x := K.E.x) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
      have := ap (x := K.E.y) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega)
    (Nat.lt_trans hV.one_lt hpn) hx₁ m₁ hmag (by rw [sy₁]; exact hT) hreg) fun s₂ S₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  rw [k₁.2.1] at ex₂ ey₂ U₂
  generalize ha : magH K.H (combWin K.w k i) = a at ex₂ ey₂ ez₂ hmag
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  -- The selected coordinates.
  have hent : 1 ≤ a → wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n =
        (combAt tbl i (a - 1)).1 * 2 ^ (64 * K.M.n) % C.p ∧
      wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
        (combAt tbl i (a - 1)).2 * 2 ^ (64 * K.M.n) % C.p := fun h1 => by
    rw [TCombCfg.tblBytes]
    exact tbl_entry hTM hV.len hV.lenH hi (by omega_using [hmag, h1]) (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
      (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := hmo K.E.x (by tcomb_mem); dsimp only; omega_using [this]
    · have := hmo K.E.y (by tcomb_mem); dsimp only; omega_using [this]
    · have := hmo K.E.z (by tcomb_mem); dsimp only; omega_using [this]
  have hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE hn
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    have hzW := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (by simp [combW, combWs, TCombCfg.toComb])) (by omega_using [hn, hzl]), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · rw [(hent ‹_›).2]; exact Nat.mod_lt _ hp0
    · exact hV.one_lt
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ hM₂ (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl hEy
    (htmp _ (by tcomb_mem)) (htmp _ (by tcomb_mem)) (htmp _ (by tcomb_mem)) (hmo _ (by tcomb_mem))
    (by rw [hz₂]; exact hp0) hEy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have hs₃ : Scr s₃ base size := k₃.scr hs₂
  have U₃ := k₃.unch
  have hx₃ : s₃.gpr .rbx = BitVec.ofNat 64 i := by
    rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide), hx₁]
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    have hbw := hL.bits_w
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := hbw (K.neg, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.M.tmp, 8 * K.M.n) (by simp [combW, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]) (by omega_using [hn, hzw, hbits', ht]),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hbw (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]) (by omega_using [hn, hzw, hbits', ht])]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K hs₃ (k := k) (j := i) (N := K.w * K.J) hw.1 (by omega_using [hw]) hwi (by omega_using [hzw, hbits'])
    hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (decide (combWin K.w k i < 2 ^ (K.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _)) 
      (by have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega_using [this])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega_using [hexy]) (by omega_using [hn, hEx]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := ap (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.x (by tcomb_mem); dsimp only; omega_using [this]) (by omega_using [hn, hEx])]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (ap (x := K.E.z) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)) (by omega_using [hn, hEz]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := ap (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.z (by tcomb_mem); dsimp only; omega_using [this]) (by omega_using [hn, hEz])]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.y (by tcomb_mem); dsimp only; omega_using [this]) (by omega_using [hn, hEy])
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (combWin K.w k i < 2 ^ (K.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  -- The point the selected entry represents.
  have hR : Rep C (tmv C K.M.n base s₂ K.E.x) (tmv C K.M.n base s₂ K.E.y) (tmv C K.M.n base s₂ K.E.z)
      (combPtW C K.w i a) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₂, ey₂, ez₂]
    by_cases h1 : 1 ≤ a
    · obtain ⟨hx, hy⟩ := hent h1
      simp only [h1, ↓reduceIte, hx, hy, toM_mont hV.unit, hV.one]
      have := hV.entry i hi (a - 1) (by omega_using [hmag, h1])
      rwa [Nat.sub_add_cancel h1] at this
    · have h0 : a = 0 := by omega_using [h1]
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega_using [], ↓reduceIte, toM_zero, hV.one]
      rw [show combPtW C K.w i 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
      exact rep_infinity' hC
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ⟨k₃.gpr, k₃.rd, k₃.wr⟩).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hw ⊢
    (repeat' (obtain rfl | hw := hw)) <;> simp only [true_or, or_true]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; split
      · rw [(hent ‹_›).1]; exact Nat.mod_lt _ hp0
      · exact hp0
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact hV.one_lt
      · exact hp0
  · have ex : tmv C K.M.n base s₅ K.E.x = tmv C K.M.n base s₂ K.E.x := by
      show toM _ _ _ = toM _ _ _; rw [vx]
    have ez : tmv C K.M.n base s₅ K.E.z = tmv C K.M.n base s₂ K.E.z := by
      show toM _ _ _ = toM _ _ _; rw [vz]
    rw [ex, ez]
    unfold signedPtW
    have hHd : K.H = 2 ^ (K.w - 1) := rfl
    by_cases h8 : 2 ^ (K.w - 1) ≤ combWin K.w k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (show ¬ combWin K.w k i < 2 ^ (K.w - 1) by omega_using [h8])]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = combWin K.w k i - 2 ^ (K.w - 1) := by rw [← ha, hHd, magH]; simp [h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (show combWin K.w k i < 2 ^ (K.w - 1) by omega_using [h8])]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₂]), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = 2 ^ (K.w - 1) - combWin K.w k i := by rw [← ha, hHd, magH]; simp [h8]
      rw [this] at hR
      exact Rep.negY hR
  · show toM _ _ _ = _
    rw [vz, ez₂, ha]
    split
    · exact hV.one
    · exact toM_zero _ _

/-! ## The loop -/

/-- What the comb reads and never writes, at the start: the curve's `a` and
`b`, zero, the table of the scalar's bits (`kbytes` bytes, the rest of its
`w J` zero after `init`), the tables' address, and the tables, apart from the
working space. -/
structure TCombFixed (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (k : Nat)
    (T : Addr) (ws : List (BitVec 64)) : Prop where
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K.toComb, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < K.kbytes, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  k_lt : k < 2 ^ K.kbytes
  tsym : s₀.syms K.tsym = T
  tbl : TblMem s₀ T ws
  out : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)

/-- The loop's invariant at `rbx = j`: `A` represents `[combEW w k J j]G`, and
the table of bits (all `w J` bytes) and the tables are where the digits and
the selection read them. -/
structure TCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : s.syms K.tsym = T

/-- What the comb writes is in the working space. -/
theorem tcombW_size {K : TCombCfg} {C : Curve} {size : Nat} {mem : Mem} {base : Addr}
    (hL : TCombLay K size) (hM : ModOkW K.M size C.p mem base) : ∀ w ∈ tcombW K, w.1 + w.2 ≤ size := by
  intro w hw
  simp only [tcombW, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
  · exact hL.comb.lay.le y (combWs_slots _ y hy)
  · exact hM.tmp
  · exact hL.bits

/-- What the comb writes is apart from the modulus. -/
theorem tcombW_mo {K : TCombCfg} {size m : Nat} {mem : Mem} {base : Addr} (hL : TCombLay K size)
    (hM : ModOkW K.M size m mem base) : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [tcombW, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
  · have := hL.comb.lay.mo y (combWs_slots _ y hy); dsimp only [TCombCfg.toComb] at this ⊢; omega_using [this]
  · have := hM.sep; dsimp only [TCombCfg.toComb] at this ⊢; omega_using [this]
  · have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega_using [this]

/-- A slot read only is apart from what the comb writes. -/
theorem tcombW_ro {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {x : Nat}
    (hx : x ∈ combRo K.toComb) : ∀ w ∈ tcombW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ro hL.comb hx w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.bits_sl x (List.mem_cons_of_mem _ (combRo_slots x hx)); dsimp only; omega_using [this]

/-- The bytes of the table of bits, apart from what the loop writes. -/
theorem combW_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.w * K.J) :
    ∀ w ∈ combW K.toComb, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  have : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  intro w hw; have := hL.bits_w w hw; omega

/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.rax] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok n hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 (by omega_using [pxa])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy_ok n hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 (by omega_using [pyb])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok n hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 (by omega_using [pzc]))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega_using [pxz]) (by omega_using [hn, hle]), O₂.wordsVal (by omega_using [pxy]) (by omega_using [hn, hle]), e₁]
  · rw [O₃.wordsVal (by omega_using [pyz]) (by omega_using [hn, hle]), e₂, O₁.wordsVal (by omega_using [pxb]) (by omega_using [hn, hle])]
  · rw [e₃, O₂.wordsVal (by omega_using [pyc]) (by omega_using [hn, hle]), O₁.wordsVal (by omega_using [pxc]) (by omega_using [hn, hle])]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

theorem clob_powClob {n : Nat} : ∀ r ∈ clob n, r ∈ powClob n := fun _ h => List.mem_cons_of_mem _ h

/-- An iteration. -/
theorem tstep_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) (publicLookup : Bool := false) :
    WP isa (K.step publicLookup).inline s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hsz : size ≤ 2 ^ 64 := by omega_using [hn]
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  refine WP.of_syms ?_
  unfold TCombCfg.step
  simp only [Code.inline]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (decRbx_ok s hj (by omega_using [hjn, hJ]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ sy₁ => ?_
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hM₁ : ModOkW K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  have hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.2.2.1, k₁.2.2.2]) fun _ _ _ _ => by rw [hm₁]
  refine WP.mono (tentry_ok hL hC hV hpn hs₁ hM₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ hbits₁ hz hT hTM publicLookup)
    fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ E₃ => ?_)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := combEntryW_sub (K := K.toComb)
  have U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := by
    rw [← hm₁]; exact E₃.unch.mono hEW
  have hmoW := tcombW_mo hL hI.mod
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by rw [← hm₁]; exact hL.comb.wordsVal_entry hsz E₃.unch x hx
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega_using [hn, this])
  have hSl : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  have hSl' : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq ((WP.mono (rcb3m_ok hL.comb.lay hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄⟩ => ?_))
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  -- The sum.
  have tb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.b
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  rw [tb] at t₄
  have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  have hEz := E₃.z
  have hErep := E₃.rep
  generalize ha : magH K.H (combWin K.w k (j - 1)) = a at hEz
  -- For a nonzero digit, the entry is affine, and `D` is the sum.
  have hRD : 1 ≤ a → Rep C (runOps (rcb3m K.S K.A K.E K.D) (tmv C K.M.n base s₃) K.D.x)
      (runOps (rcb3m K.S K.A K.E K.D) (tmv C K.M.n base s₃) K.D.y)
      (runOps (rcb3m K.S K.A K.E K.D) (tmv C K.M.n base s₃) K.D.z)
      (mul (combEW K.w k K.J (j - 1)) (G C)) := fun h1 => by
    rw [hEz] at hErep
    simp only [h1, ↓reduceIte] at hErep
    have hR := hC.add3m hM3 hP hQ hRA hErep t₄.symm
    rw [hsp, hadd] at hR
    exact hR
  -- For a zero digit, the entry is the point at infinity, and the sum is `A`.
  have hRA0 : a = 0 → Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J (j - 1)) (G C)) := fun h0 => by
    have hw : combWin K.w k (j - 1) = 2 ^ (K.w - 1) := by
      have e : K.H = 2 ^ (K.w - 1) := rfl
      unfold magH at ha; rw [e] at ha; split at ha <;> omega
    rw [← hadd, hw]
    simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self]
    rw [show combPtW C K.w (j - 1) 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul], add_infinity]
    exact hRA
  -- The digit again, and `A = D` unless it is zero.
  have hs₄ := I₄.scr
  have hb₄ : s₄.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [P₄.gpr _ (rbx_not_clob _), E₃.keep.gpr _ (rbx_not_clob _), b₁]
  have U₄ : Unch base (combW K.toComb) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h
    · exact Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩
    · exact Or.inr (by rw [h]; rfl)
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hbits₄ : ∀ t < K.w * K.J, s₄.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [(U₁₃.trans U₄).byte (fun w hw => by
      rcases List.mem_append.mp hw with h | h <;> exact combW_bits hL ht w h)
      (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  have hAE₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := hL.comb.wordsVal_add hsz P₄.unch
  have hA₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => hAE₄ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])
  have hw := hL.w
  have hwi : K.w * (j - 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j - 1 + 1 ≤ K.J by omega_using [hjn, hJ]); rwa [Nat.mul_succ] at this
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (digit_ok K hs₄ (k := k) (j := j - 1) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb₄ hbits₄) fun s₅ ⟨_, r₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [ha] at r₅
  have hH2 : 2 ^ K.w = 2 * K.H := by
    unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega_using [hw]
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hmag : a ≤ K.H := by
    rw [← ha]; exact magH_le (by rw [← hH2]; exact combWin_lt K.w k (j - 1))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₅ (v := 0) (a := a) (by decide) (by omega_using [hHle, hmag]) r₅) fun s₆ ⟨c₆, k₆, _⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₆ (decide (a = 0)) (by rw [c₆]) (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    hL.comb.apart_A hL.comb.apart_AD) fun s₇ ⟨ex₇, ey₇, ez₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have hb₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₇.gpr _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide), hb₄]
  refine WP.mono (testRbx_ok s₇ (by omega_using [hjn, hJ]) hb₇) fun s₈ ⟨z₈, k₈⟩ sy₈ => ?_
  have m₈ : s₈.mem = s₇.mem := k₈.2.1
  have m₆ : s₆.mem = s₄.mem := by rw [k₆.2.1, k₅.2.1]
  have U₈ : Unch base (combW K.toComb) s₄.mem s₈.mem := by
    rw [m₈, ← m₆]
    refine Unch.mono (W := [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)])
      (fun x hx => O₇ x (hx (K.A.x, 8 * K.M.n) (by simp)) (hx (K.A.y, 8 * K.M.n) (by simp))
        (hx (K.A.z, 8 * K.M.n) (by simp))) (combSelW_A_sub (K := K.toComb))
  have U : Unch base (combW K.toComb) s.mem s₈.mem := (U₁₃.trans (U₄.trans U₈)).mono fun w hw => by
    simp only [List.mem_append] at hw; rcases hw with h | h | h <;> exact h
  have hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E :=
    fun _ hx => List.mem_append_left _ hx
  have hDval : ∀ x ∈ [K.D.x, K.D.y, K.D.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps (rcb3m K.S K.A K.E K.D) (tmv C K.M.n base s₃) x := fun x hx => I₄.val x (hDv x hx)
  have hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  rw [m₆] at ex₇ ey₇ ez₇
  refine ⟨⟨hs₇.of_keeps k₈ (by decide), by rw [k₈.1 _ (by decide), hb₇], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [sy₈]; exact hI.tsym⟩, z₈⟩
  · have c₁ : KeepRegs (powClob K.M.n) s s₁ := (Keeps.regs k₁).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    have c₃ : KeepRegs (powClob K.M.n) s₁ s₃ := E₃.keep.mono clob_powClob
    have c₄ : KeepRegs (powClob K.M.n) s₃ s₄ :=
      (⟨P₄.gpr, P₄.rd, P₄.wr⟩ : KeepRegs (clob K.M.n) s₃ s₄).mono clob_powClob
    have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ powClob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (r8_mem_clob _)
    have c₅ : KeepRegs (powClob K.M.n) s₄ s₅ := (Keeps.regs k₅).mono hcl
    have c₆ : KeepRegs (powClob K.M.n) s₅ s₆ := (Keeps.regs k₆).mono fun r hr => hcl r (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    have c₇ : KeepRegs (powClob K.M.n) s₆ s₇ := k₇.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₈ : KeepRegs (powClob K.M.n) s₇ s₈ := (Keeps.regs k₈).mono fun r hr => absurd hr List.not_mem_nil
    exact hI.keep.trans (c₁.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans c₈))))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  · have hA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
      rw [hA₄ x hx, hAx x hx]; exact hI.lt x hx
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₈, ex₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
    · rw [m₈, ey₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
    · rw [m₈, ez₇]; split
      · exact hA _ (by simp)
      · exact hDlt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₈.mem base x K.M.n = wordsVal s₄.mem base y K.M.n →
        tmv C K.M.n base s₈ x = tmv C K.M.n base s₄ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    by_cases h0 : a = 0
    · simp only [decide_eq_true h0, ↓reduceIte] at ex₇ ey₇ ez₇
      rw [e (by rw [m₈, ex₇]), e (by rw [m₈, ey₇]), e (by rw [m₈, ez₇])]
      have e₃ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ x :=
        fun x hx => by show toM _ _ _ = toM _ _ _; rw [hA₄ x hx]
      rw [e₃ _ (by simp), e₃ _ (by simp), e₃ _ (by simp)]
      exact hRA0 h0
    · simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte] at ex₇ ey₇ ez₇
      rw [e (by rw [m₈, ex₇]), e (by rw [m₈, ey₇]), e (by rw [m₈, ez₇])]
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [hDval _ (by simp), hDval _ (by simp), hDval _ (by simp)]
      exact hRD (by omega_using [h0])
  · intro t ht
    rw [U.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [k₈.2.2.1, k₈.2.2.2, k₇.rd, k₇.wr, k₆.2.2.1, k₆.2.2.2, k₅.2.2.1,
      k₅.2.2.2, P₄.rd, P₄.wr, E₃.keep.rd, E₃.keep.wr, k₁.2.2.1, k₁.2.2.2]) U
      (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out

/-- Zero stored to the `m` words at `o`, from `rax = 0`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .rax = 0)
    {o : Nat} : ∀ m, o + 8 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => .store (sc (o + 8 * i)) .rax)) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (8 * m) s.mem s'.mem ∧
        ∀ d < 8 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega_using [])⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz m (by omega_using [hm])) fun s₁ ⟨k₁, O₁, z₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have hrax : s₁.gpr .rax = 0 := (k₁.gpr _ (by simp)).trans hz
    apply WP.of_runBlock
    simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      ea_sc, hs₁.rdi, hrax, st_sc hs₁ (d := o + 8 * m) (by omega_using [hm]), ite_true, Option.some.injEq,
      exists_eq_left']
    have Ow := writeW_outside s₁.mem base (d := o + 8 * m) (0 : BitVec 64) (by omega_using [hm, hn])
    refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr⟩, fun x hx => (Ow x (by omega_using [hx])).trans (O₁ x (by omega_using [hx])),
      fun d hd => ?_⟩
    by_cases hd' : d < 8 * m
    · show (s₁.mem.writeW (off base (o + 8 * m)) (0 : BitVec 64)) (off base (o + d)) = 0
      rw [Ow _ (by rw [ofs_off0 base (by omega_using [hm, hn, hd'])]; omega_using [hd'])]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 8 * m) = BitVec.ofNat 64 (d - 8 * m) := by
        simp only [off]; rw [show o + d = o + 8 * m + (d - 8 * m) by omega_using [hd'], Offset.add_ofNat_add_sub]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 8 * m < 2 ^ 64 by omega_using [hd]), show d - 8 * m < 64 / 8 by omega_using [hd],
        ↓reduceIte]
      simp

theorem zeroRax_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s fun s' => s'.gpr .rax = 0 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `[k]G` into `A`, for `k < 2^kbytes` whose bits are the table at `K.bits`;
only `powClob` and `tcombW` change. -/
theorem tcomb_init_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.init) s fun t =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s t K.J := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ size := fun x hx =>
    hL.comb.lay.le x (combWs_slots _ x hx)
  have b64 : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have axy := hL.comb.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  have axz := hL.comb.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  have ayz := hL.comb.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  dsimp only [TCombCfg.toComb] at axy axz ayz
  have hsl : ∀ x ∈ combWs K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ (combWs_slots _ x hx))
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hJ31 : K.J < 2 ^ 31 := by omega_using [hJ]
  refine WP.of_syms ?_
  have e : K.init = setConst K.M.n K.A.x K.start.1 ++ (setConst K.M.n K.A.y K.start.2 ++
      (setConst K.M.n K.A.z K.one ++ ([.mov32 .rax (.imm 0)] ++ ((List.range K.zw).map
        (fun i => .store (sc (K.bits + K.kbytes + 8 * i)) .rax) ++
          [.mov32 .rbx (.imm (BitVec.ofNat 32 K.J))])))) := by
    unfold TCombCfg.init
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  have hlt : ∀ {x}, x < C.p → x < 2 ^ (64 * K.M.n) := fun h => Nat.lt_trans h hpn
  refine WP.mono (setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) (le _ (by tcomb_mem))
    (hlt hV.start_lt.1)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) (le _ (by tcomb_mem))
    (hlt hV.start_lt.2)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) (le _ (by tcomb_mem))
    (hlt hV.one_lt)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroRax_ok s₃) fun s₄ ⟨z₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zstores_ok hs₄ z₄ K.zw hL.bits) fun s₅ ⟨k₅, O₅, z₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by simp)
  refine WP.mono (mov32Rbx_ok s₅ hJ31) fun s₆ ⟨b₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  have U₃ : Unch base (combW K.toComb) s.mem s₃.mem :=
    (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hw ⊢
      (repeat' (obtain rfl | hw := hw)) <;> simp only [true_or, or_true]
  have U₆ : Unch base (tcombW K) s.mem s₆.mem := by
    rw [m₆]
    refine (U₃.trans (show Unch base [(K.bits + K.kbytes, 8 * K.zw)] s₃.mem s₅.mem by
      rw [← k₄.2.1]; exact O₅.unch)).mono fun w hw => hw
  have hmo := tcombW_mo hL hM
  -- `A`, apart from the cleared words.
  have hA5 : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [m₆, O₅.wordsVal (by have := hsl x hxs; omega_using [this]) (b64 x hxs), k₄.2.1]
  have vx : wordsVal s₆.mem base K.A.x K.M.n = K.start.1 := by
    rw [hA5 _ (by simp), O₃.wordsVal axz (b64 _ (by tcomb_mem)), O₂.wordsVal axy (b64 _ (by tcomb_mem)), e₁]
  have vy : wordsVal s₆.mem base K.A.y K.M.n = K.start.2 := by
    rw [hA5 _ (by simp), O₃.wordsVal ayz (b64 _ (by tcomb_mem)), e₂]
  have vz : wordsVal s₆.mem base K.A.z K.M.n = K.one := by rw [hA5 _ (by simp), e₃]
  intro sy₆
  have I₆ : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s₆ K.J := by
    refine ⟨hs₅.of_keeps k₆ (by decide), b₆, ?_, U₆, hM.unch U₆ hmo hn, ?_, ?_, fun t ht => ?_, ?_,
      by rw [sy₆]; exact hF.tsym⟩
    · have c : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
      exact ((((k₁.mono c).trans (k₂.mono c)).trans (k₃.mono c)).trans ((Keeps.regs k₄).mono c)).trans
        ((k₅.mono fun r hr => absurd hr List.not_mem_nil).trans ((Keeps.regs k₆).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..))
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hV.start_lt.1
      · rw [vy]; exact hV.start_lt.2
      · rw [vz]; exact hV.one_lt
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, hV.one, combEW_top]
      exact hV.start
    · by_cases htk : t < K.kbytes
      · rw [U₆.byte (fun w hw => by
          rcases List.mem_append.mp hw with hw | hw
          · exact combW_bits hL ht w hw
          · simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega_using [htk])
          (by omega_using [hbz, hzw, ht, hn])]
        exact hF.bits t htk
      · have := z₅ (t - K.kbytes) (by omega_using [hzw, ht, htk])
        rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega_using [htk]] at this
        rw [m₆, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
          (Nat.pow_le_pow_right (by decide) (by omega_using [htk])))]
        rfl
    · exact TblMem.of_unch hF.tbl (by rw [k₆.2.2.1, k₆.2.2.2, k₅.rd, k₅.wr, k₄.2.2.1, k₄.2.2.2, k₃.rd,
        k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]) U₆ (tcombW_size hL hM) hF.out
  exact I₆

theorem tcomb_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) (publicLookup : Bool := false) :
    WP isa (K.comb publicLookup).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  unfold TCombCfg.comb
  refine WP.seq (WP.mono (tcomb_init_ok hL hV hpn hs hM hF) fun s₆ I₆ => ?_)
  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (fun j s' h1 h2 hi => tstep_ok hL hC hM3 hG hV hpn hF h1 h2 hi publicLookup)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.X86_64
