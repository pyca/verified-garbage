import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ

/-!
# The fixed-base comb with Booth's digits and Jacobian mixed additions on x86-64

`TCombCfg.combJ` (`Impl/Weierstrass/X86_64/TCombJ.lean`). Iteration `j`
selects the entry of Booth's digit `d_j`'s magnitude (`bdigit_ok`,
`select_ok`) and negates `y` for a negative digit (`tentryJ_ok`), so that `E`
represents `[d_j 2^(wj)]G` (`bentry_eq`), affine unless the digit is zero.
`A` holds a Jacobian triple (`InvJ`) of `[Σ_{i<j} d_i 2^(wi)]G` (`bpart`):
window `0` puts its entry there (`firstJ_ok`); each later one adds its entry
with the mixed addition (`maddJ_ok`, `InvJ.madd`), which needs `A` other than
`O` (else the sum is the entry, which the code takes where `A`'s `Z` is zero)
and other than the entry, which `booth_ne` proves from the order of `G`;
for a zero digit `A` is kept (`stepJ_ok`). After the `J` digits, `[k]G`
(`bpart_top`), in projective coordinates (`InvJ.out`, `tcombJ_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- After the selection and negation: `E` represents Booth's entry `i`, and
only `E`, `-y` and the temporary area changed. -/
structure TEntryPostJ (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (bentry C K.w k i)
  /-- The entry is affine (`Z = 1`) unless the digit is zero. -/
  z : tmv C K.M.n base s' K.E.z = if 1 ≤ bmag K.w k i then 1 else 0

/-- Booth's entry `i`, selected (from `rbx = i`) and negated for a negative
digit; `c` for `i ≥ 1`. -/
theorem tentryJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .rbx = BitVec.ofNat 64 i)
    (hb1 : 1 ≤ K.bits) {c : Bool} (hc : (c = true ∧ 1 ≤ i) ∨ (c = false ∧ i = 0))
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block (K.bdigit c ++ K.select)) s fun s₂ =>
      WP isa (.block K.bnegY) s₂ (TEntryPostJ K C base size k i s) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnn := hL.n
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hbits' := hL.bits
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega))
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
  have xy := hL.comb.apart₂ (x := K.E.x) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have xz := hL.comb.apart₂ (x := K.E.x) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have yz := hL.comb.apart₂ (x := K.E.y) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have yneg := hL.comb.apart₂ (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by grind)
  have xneg := hL.comb.apart₂ (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by grind)
  have zneg := hL.comb.apart₂ (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by grind)
  dsimp only [TCombCfg.toComb] at xy xz yz yneg xneg zneg
  have hexy := hL.exy
  have hEx := hle K.E.x (by tcomb_mem)
  have hEy := hle K.E.y (by tcomb_mem)
  have hEz := hle K.E.z (by tcomb_mem)
  have hneg := hle K.neg (by tcomb_mem)
  have hzl := hle K.zero (by tcomb_mem)
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi); rwa [Nat.mul_succ] at this
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J) hw.1 hw.2 hwi (by omega) hb1 hx
    hbits hc) fun s₁ ⟨a₁, m₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hx₁ : s₁.gpr .rbx = BitVec.ofNat 64 i := by rw [k₁.1 _ (by decide), hx]
  have hmag : bmag K.w k i ≤ K.H := bmag_le hw.1 k i
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
    omega
  refine WP.mono (select_ok K hs₁ hnn (by omega) hL.tbl hexy hEy hEz (by omega)
    (Nat.lt_trans hV.one_lt hpn) hx₁ m₁ hmag (by rw [sy₁]; exact hT) hreg) fun s₂ S₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  rw [k₁.2.1] at ex₂ ey₂ U₂
  generalize ha : bmag K.w k i = a at ex₂ ey₂ ez₂ hmag
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  -- The selected coordinates.
  have hent : 1 ≤ a → wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n =
        (combAt tbl i (a - 1)).1 * 2 ^ (64 * K.M.n) % C.p ∧
      wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
        (combAt tbl i (a - 1)).2 * 2 ^ (64 * K.M.n) % C.p := fun h1 => by
    rw [TCombCfg.tblBytes]
    exact tbl_entry hTM hV.len hV.lenH hi (by omega) (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
      (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := hmo K.E.x (by tcomb_mem); dsimp only; omega
    · have := hmo K.E.y (by tcomb_mem); dsimp only; omega
    · have := hmo K.E.z (by tcomb_mem); dsimp only; omega
  have hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE hn
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    have hzW := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (by simp [combW, combWs, TCombCfg.toComb])) (by omega), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · rw [(hent ‹_›).2]; exact Nat.mod_lt _ hp0
    · exact hV.one_lt
  rw [TCombCfg.bnegY, List.append_assoc, WP.block_append_iff]
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
          omega
        · have := hbw (K.M.tmp, 8 * K.M.n) (by simp [combW, TCombCfg.toComb]); dsimp only at this ⊢
          omega) (by omega),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hbw (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega
        · have := hbw (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega
        · have := hbw (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega) (by omega)]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (bsignMask_ok K hs₃ (k := k) (j := i) (N := K.w * K.J) hw.1 (by omega) hwi (by omega)
    hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (decide (bcar K.w k (i + 1) = 1)) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _)) (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := htmp K.E.x (by tcomb_mem); dsimp only; omega) (by omega)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := htmp K.E.z (by tcomb_mem); dsimp only; omega) (by omega)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · dsimp only; omega
      · have := htmp K.E.y (by tcomb_mem); dsimp only; omega) (by omega)
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (bcar K.w k (i + 1) = 1) then
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
      have := hV.entry i hi (a - 1) (by omega)
      rwa [Nat.sub_add_cancel h1] at this
    · have h0 : a = 0 := by omega
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, toM_zero, hV.one]
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
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
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
    unfold bentry
    rw [ha]
    by_cases h1 : bcar K.w k (i + 1) = 1
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true h1]
        simp only [↓reduceIte]
        rw [toM_sub (by omega), toM_zero]
        grind
      rw [hy]
      simp only [h1, ↓reduceIte]
      exact Rep.negY hR
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false h1]; rfl
      rw [hy]
      simp only [h1, ↓reduceIte]
      exact hR
  · show toM _ _ _ = _
    rw [vz, ez₂, ha]
    split
    · exact hV.one
    · exact toM_zero _ _

/-! ## The loop -/

/-- `rbx = j + 1`, and `ZF` for `j + 1 = J`. -/
theorem incCmpRbx_ok (s : State) {j J : Nat} (hj : j + 1 ≤ J) (hJ : J < 2 ^ 31)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 J))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (j + 1) ∧ s'.zf = some (decide (j + 1 = J)) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb, inc_eq,
    ite_true, RegUpd.zf_arithFlags, cmp_eq hj hJ]
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The loop's invariant at `rbx = j`: `A` is a Jacobian triple of
`[Σ_{i<j} d_i 2^(wi)]G`, and the table of bits (all `w J` bytes) and the
tables are where the digits and the selection read them. -/
structure TCombJInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (zmul (bpart K.w k j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : s.syms K.tsym = T

/-- `[Σ_{i≤j} d_i 2^(wi)]G` from the sum below `j` and the entry `j`. -/
theorem bpart_succ_pt {C : Curve} (hC : Law C) (hG : onCurve C (G C) = true) {w : Nat} (hw : 1 ≤ w)
    (k j : Nat) :
    zmul (bpart w k (j + 1)) (G C) = Spec.Weierstrass.add (zmul (bpart w k j) (G C)) (bentry C w k j) := by
  rw [bentry_eq hw, hC.add_zmul hG, bpart_succ]

/-- An iteration, `1 ≤ j < J`. -/
theorem stepJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j < K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) :
    WP isa K.stepJ s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
        s'.zf = some (decide (j + 1 = K.J)) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hNZ : NeZero C.p := ⟨by omega⟩
  refine WP.of_syms ?_
  unfold TCombCfg.stepJ
  refine WP.seq ?_
  have hz : wordsVal s.mem base K.zero K.M.n = 0 := by
    rw [hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  refine WP.mono (tentryJ_ok hL hC hV hpn hI.scr hI.mod hjn hI.rbx hb1 (c := true) (Or.inl ⟨rfl, hj⟩)
    hI.bits hz hI.tsym hI.tbl) fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ E₃ => ?_)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h | h | h <;> subst h <;> simp
  have U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := E₃.unch.mono hEW
  have hmoW := tcombW_mo hL hI.mod
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [E₃.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.lay.tmp x (combWs_slots _ x hxs))
        (by have := hle x (combWs_slots _ x hxs); omega)]
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega)
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
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono (maddJ_ok hL.comb.lay hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄⟩ => ?_))
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  have hs₄ := I₄.scr
  have hb₄ : s₄.gpr .rbx = BitVec.ofNat 64 j := by
    rw [P₄.gpr _ (rbx_not_clob _), E₃.keep.gpr _ (rbx_not_clob _), hI.rbx]
  have U₄ : Unch base (combW K.toComb) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h
    · exact Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩
    · exact Or.inr (by rw [h]; rfl)
  -- `A` and `E` are not written by the addition.
  have hAE₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := fun x hx => by
    have hxs : x ∈ combWs K.toComb := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
    refine P₄.unch.wordsVal (fun w hw => ?_) (by have := hle x (combWs_slots _ x hxs); omega)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      have hys : y ∈ combWs K.toComb := by
        simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy
      refine hL.comb.apart₂ hxs hys ?_
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      grind
    · simp only [List.mem_singleton] at hw; subst hw
      exact hL.comb.lay.tmp x (combWs_slots _ x hxs)
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hw := hL.w
  have hnn := hL.n
  -- `D = E` where `A` is `O`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs₄ hnn.1 (hle K.A.z (by tcomb_mem))) fun s₅ ⟨c₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hsel := fun (x : Nat) (hx : x ∈ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]) =>
    hle x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem)
  refine WP.mono (selPtKeep_ok hs₅ (decide (wordsVal s₄.mem base K.A.z K.M.n ≠ 0)) (by rw [c₅])
    (n := K.M.n) (o := K.D) (a := K.E) hsel
    ⟨hL.comb.apart₂ (x := K.D.x) (y := K.D.y) (by tcomb_mem) (by tcomb_mem) (by grind),
      hL.comb.apart₂ (x := K.D.x) (y := K.D.z) (by tcomb_mem) (by tcomb_mem) (by grind),
      hL.comb.apart₂ (x := K.D.y) (y := K.D.z) (by tcomb_mem) (by tcomb_mem) (by grind)⟩
    (fun x hx y hy => hL.comb.apart₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> tcomb_mem) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      grind))) fun s₆ ⟨dx₆, dy₆, dz₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  rw [m₅] at dx₆ dy₆ dz₆ O₆
  have UD₆ : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s₄.mem s₆.mem :=
    fun x hx => O₆ x (hx (K.D.x, 8 * K.M.n) (by simp)) (hx (K.D.y, 8 * K.M.n) (by simp))
      (hx (K.D.z, 8 * K.M.n) (by simp))
  have U₆ : Unch base (combW K.toComb) s₄.mem s₆.mem := by
    refine UD₆.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, rcbW, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h <;> subst h <;> simp
  have hA₆ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [← hAx x hx, ← hAE₄ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])]
      refine UD₆.wordsVal (fun w hw => ?_) (by have := hle x (combWs_slots _ x hxs); omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hw with rfl | rfl | rfl <;> exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
  have hb₆ : s₆.gpr .rbx = BitVec.ofNat 64 j := by
    rw [k₆.gpr _ (by decide), k₅.1 _ (by decide), hb₄]
  have hbits₆ : ∀ t < K.w * K.J, s₆.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [(U₁₃.trans (U₄.trans U₆)).byte (fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with h | h | h <;> exact combW_bits hL ht w h)
      (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  have hwi : K.w * j + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 ≤ K.J by omega); rwa [Nat.mul_succ] at this
  -- The digit again, and `A = D` unless it is zero.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (bdigit_ok K hs₆ (k := k) (j := j) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb1 hb₆ hbits₆ (Or.inl ⟨rfl, hj⟩)) fun s₇ ⟨_, r₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have hmag : bmag K.w k j ≤ 128 := by
    have := bmag_le hw.1 k j
    exact Nat.le_trans this (Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega))
      (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₇ (v := 0) (a := bmag K.w k j) (by decide) (by omega) r₇)
    fun s₈ ⟨c₈, k₈, _⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₈ (decide (bmag K.w k j = 0)) (by rw [c₈]) (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    ⟨hL.comb.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind),
      hL.comb.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind),
      hL.comb.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)⟩
    (fun x hx y hy => hL.comb.apart₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> tcomb_mem) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      grind))) fun s₉ ⟨ex₉, ey₉, ez₉, k₉, O₉⟩ => ?_
  have hs₉ := hs₈.of_keepRegs k₉ (by decide)
  have hb₉ : s₉.gpr .rbx = BitVec.ofNat 64 j := by
    rw [k₉.gpr _ (by decide), k₈.1 _ (by decide), k₇.1 _ (by decide), hb₆]
  refine WP.mono (incCmpRbx_ok s₉ (j := j) (J := K.J) (by omega) (by omega) hb₉)
    fun s₁₀ ⟨b₁₀, z₁₀, k₁₀⟩ sy₁₀ => ?_
  have m₁₀ : s₁₀.mem = s₉.mem := k₁₀.2.1
  have m₈ : s₈.mem = s₆.mem := by rw [k₈.2.1, k₇.2.1]
  rw [m₈] at ex₉ ey₉ ez₉ O₉
  have U₁₀ : Unch base (combW K.toComb) s₆.mem s₁₀.mem := by
    rw [m₁₀]
    refine Unch.mono (W := [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)])
      (fun x hx => O₉ x (hx (K.A.x, 8 * K.M.n) (by simp)) (hx (K.A.y, 8 * K.M.n) (by simp))
        (hx (K.A.z, 8 * K.M.n) (by simp))) fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h <;> subst h <;> simp
  have U : Unch base (combW K.toComb) s.mem s₁₀.mem :=
    (U₁₃.trans (U₄.trans (U₆.trans U₁₀))).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with h | h | h | h <;> exact h
  have hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E :=
    fun _ hx => List.mem_append_left _ hx
  have hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  refine ⟨⟨hs₉.of_keeps k₁₀ (by decide), b₁₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [sy₁₀]; exact hI.tsym⟩, z₁₀⟩
  · have c₃ : KeepRegs (powClob K.M.n) s s₃ := E₃.keep.mono clob_powClob
    have c₄ : KeepRegs (powClob K.M.n) s₃ s₄ :=
      (⟨P₄.gpr, P₄.rd, P₄.wr⟩ : KeepRegs (clob K.M.n) s₃ s₄).mono clob_powClob
    have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ powClob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (r8_mem_clob _)
    have c₅ : KeepRegs (powClob K.M.n) s₄ s₅ := (Keeps.regs k₅).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₆ : KeepRegs (powClob K.M.n) s₅ s₆ := k₆.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₇ : KeepRegs (powClob K.M.n) s₆ s₇ := (Keeps.regs k₇).mono hcl
    have c₈ : KeepRegs (powClob K.M.n) s₇ s₈ := (Keeps.regs k₈).mono fun r hr => hcl r (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    have c₉ : KeepRegs (powClob K.M.n) s₈ s₉ := k₉.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₁₀ : KeepRegs (powClob K.M.n) s₉ s₁₀ := (Keeps.regs k₁₀).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact hI.keep.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans (c₈.trans (c₉.trans c₁₀)))))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) hn
  · have hA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
      rw [hA₆ x hx]; exact hI.lt x hx
    have hE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
      rw [hAE₄ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])]
      exact E₃.lt x hx
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₁₀, ex₉]; split
      · exact hA _ (by simp)
      · rw [dx₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
    · rw [m₁₀, ey₉]; split
      · exact hA _ (by simp)
      · rw [dy₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
    · rw [m₁₀, ez₉]; split
      · exact hA _ (by simp)
      · rw [dz₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
  · -- The point.
    have e : ∀ {x y : Nat} {t : State}, wordsVal s₁₀.mem base x K.M.n = wordsVal t.mem base y K.M.n →
        tmv C K.M.n base s₁₀ x = tmv C K.M.n base t y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    have eA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s x :=
      fun x hx => by show toM _ _ _ = toM _ _ _; rw [hAx x hx]
    have eE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ x :=
      fun x hx => by
        show toM _ _ _ = toM _ _ _
        rw [hAE₄ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])]
    rw [bpart_succ_pt hC hG hw.1]
    have hErep := E₃.rep
    have hEz := E₃.z
    by_cases h0 : bmag K.w k j = 0
    · simp only [decide_eq_true h0, ↓reduceIte] at ex₉ ey₉ ez₉
      rw [e (t := s) (by rw [m₁₀, ex₉, hA₆ _ (by simp)]), e (t := s) (by rw [m₁₀, ey₉, hA₆ _ (by simp)]),
        e (t := s) (by rw [m₁₀, ez₉, hA₆ _ (by simp)])]
      have hQ : bentry C K.w k j = .infinity := by
        unfold bentry
        rw [h0, show combPtW C K.w j 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
        split <;> rfl
      rw [hQ, add_infinity]
      exact hI.rep
    · have h1 : 1 ≤ bmag K.w k j := by omega
      simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte] at ex₉ ey₉ ez₉
      simp only [h1, ↓reduceIte] at hEz
      rw [hEz] at hErep
      have hQa := Rep.eq_affine hC hErep
      have hZiff : wordsVal s₄.mem base K.A.z K.M.n = 0 ↔ tmv C K.M.n base s K.A.z = 0 := by
        rw [hAE₄ _ (by simp), hAx _ (by simp)]
        exact (toM_eq_zero_iff hV.unit (hI.lt _ (by simp))).symm
      by_cases hz0 : wordsVal s₄.mem base K.A.z K.M.n = 0
      · simp only [hz0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆]), eE _ (by simp), eE _ (by simp), eE _ (by simp)]
        have hP : zmul (bpart K.w k j) (G C) = .infinity := by
          have h := hI.rep
          rw [hZiff.mp hz0] at h
          exact InvJ.eq_infinity h
        rw [hP, infinity_add']
        rw [← hEz] at hErep
        exact InvJ.of_rep01 hErep (Or.inl hEz)
      · simp only [hz0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆])]
        have hD : (tmv C K.M.n base s₄ K.D.x, tmv C K.M.n base s₄ K.D.y, tmv C K.M.n base s₄ K.D.z) =
            maddJF (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y) (tmv C K.M.n base s₃ K.A.z)
              (tmv C K.M.n base s₃ K.E.x) (tmv C K.M.n base s₃ K.E.y) := by
          rw [← t₄]
          show (toM _ _ _, toM _ _ _, toM _ _ _) = _
          rw [I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp))]
        have hrepA : InvJ C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
            (tmv C K.M.n base s₃ K.A.z) (zmul (bpart K.w k j) (G C)) := by
          rw [eA _ (by simp), eA _ (by simp), eA _ (by simp)]; exact hI.rep
        have hZ : tmv C K.M.n base s₃ K.A.z ≠ 0 := by
          rw [eA _ (by simp)]; exact fun h => hz0 (hZiff.mpr h)
        have hon : onCurve C (bentry C K.w k j) = true := by
          rw [bentry_eq hw.1]; exact hC.onCurve_zmul hG _
        have hne : zmul (bpart K.w k j) (G C) ≠ bentry C K.w k j := by
          rw [bentry_eq hw.1]
          exact booth_ne hC hG hB.n hB.n0 hB.cop hB.safe hw.1 hB.J2 hB.kmax hk hj hjn h0
        rw [hQa] at hon hne ⊢
        have h := InvJ.madd hC hM3 (hC.onCurve_zmul hG _) hon hrepA hZ hne
        rw [← hD] at h
        exact h
  · intro t ht
    rw [U.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [k₁₀.2.2.1, k₁₀.2.2.2, k₉.rd, k₉.wr, k₈.2.2.1, k₈.2.2.2, k₇.2.2.1,
      k₇.2.2.2, k₆.rd, k₆.wr, k₅.2.2.1, k₅.2.2.2, P₄.rd, P₄.wr, E₃.keep.rd, E₃.keep.wr]) U
      (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out

/-- Window `0`: the table of bits cleared past the scalar, and `A` its entry. -/
theorem firstJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa K.first s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' 1 := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  have hsl : ∀ x ∈ combSlots K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ hx)
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  have hmo := tcombW_mo hL hM
  refine WP.of_syms ?_
  unfold TCombCfg.first
  refine WP.seq ?_
  have e : K.clearBits ++ [.mov32 .rbx (.imm 0)] ++ K.bdigit false ++ K.select = [.mov32 .rax (.imm 0)] ++
      ((List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 8 * i)) .rax) ++
        ([.mov32 .rbx (.imm (BitVec.ofNat 32 0))] ++ (K.bdigit false ++ K.select))) := by
    unfold TCombCfg.clearBits
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e, WP.block_append_iff]
  refine WP.mono_syms (zeroRax_ok s) fun s₁ ⟨z₁, k₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (zstores_ok hs₁ z₁ K.zw hL.bits) fun s₂ ⟨k₂, O₂, z₂⟩ sy₂ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (mov32Rbx_ok s₂ (j := 0) (by decide)) fun s₃ ⟨b₃, k₃⟩ sy₃ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have U₃ : Unch base [(K.bits + K.kbytes, 8 * K.zw)] s.mem s₃.mem := by
    rw [m₃, ← k₁.2.1]; exact O₂.unch
  have U₃' : Unch base (tcombW K) s.mem s₃.mem := U₃.mono fun w hw => List.mem_append_right _ hw
  have hro : ∀ x ∈ combSlots K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by rw [m₃, O₂.wordsVal (by have := hsl x hx; omega) (b64 x hx), k₁.2.1]
  have hM₃ : ModOkW K.M size C.p s₃.mem base := hM.unch U₃' hmo hn
  have hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [hro _ (by tcomb_mem)]; exact hF.zero
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    by_cases htk : t < K.kbytes
    · rw [U₃.byte (fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega)
        (by omega_using [hbz, hzw, ht, hn])]
      exact hF.bits t htk
    · have := z₂ (t - K.kbytes) (by omega)
      rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega] at this
      rw [m₃, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      rfl
  have hT₃ : s₃.syms K.tsym = T := by rw [sy₃, sy₂, sy₁]; exact hF.tsym
  have hTM₃ : TblMem s₃ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    TblMem.of_unch hF.tbl (by rw [k₃.2.2.1, k₃.2.2.2, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]) U₃'
      (tcombW_size hL hM) hF.out
  refine WP.mono (tentryJ_ok hL hC hV hpn hs₃ hM₃ (i := 0) (by omega) b₃ hb1 (c := false)
    (Or.inr ⟨rfl, rfl⟩) hbits₃ hz₃ hT₃ hTM₃) fun s₄ h₄ => WP.seq (WP.mono h₄ fun s₅ E₅ => ?_)
  rw [WP.block_append_iff]
  have hAE : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z], x ∈ combWs K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  refine WP.mono (copyPt_ok E₅.scr (o := K.A) (a := K.E) (n := K.M.n)
    (fun x hx => hle x (combWs_slots _ x (hAE x hx)))
    (fun x hx y hy hxy => hL.comb.apart₂ (hAE x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))
      (hAE y hy) hxy)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> grind)
    ⟨by grind, by grind, by grind⟩) fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_
  refine WP.mono (mov32Rbx_ok s₆ (j := 1) (by decide)) fun s₇ ⟨b₇, k₇⟩ sy₇ => ?_
  have m₇ : s₇.mem = s₆.mem := k₇.2.1
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h | h | h <;> subst h <;> simp
  have hAW : ∀ w ∈ [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)], w ∈ combW K.toComb := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h <;> subst h <;> simp
  have U : Unch base (combW K.toComb) s₃.mem s₇.mem := by
    rw [m₇]; exact (E₅.unch.trans U₆).mono fun w hw => by
      rcases List.mem_append.mp hw with h | h
      · exact hEW w h
      · exact hAW w h
  have UT : Unch base (tcombW K) s.mem s₇.mem := (U₃'.trans U).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · exact List.mem_append_left _ h
  refine ⟨E₅.scr.of_keepRegs k₆ (by decide) |>.of_keeps k₇ (by decide), b₇, ?_, UT, hM.unch UT hmo hn,
    ?_, ?_, fun t ht => ?_, ?_, by rw [sy₇]; exact hF.tsym⟩
  · have c : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
    have cb : ∀ r ∈ [Reg.rbx], r ∈ powClob K.M.n := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact (((((Keeps.regs k₁).mono c).trans (k₂.mono fun r hr => absurd hr List.not_mem_nil)).trans
      ((Keeps.regs k₃).mono cb)).trans (E₅.keep.mono clob_powClob)).trans
      ((k₆.mono c).trans ((Keeps.regs k₇).mono cb))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₇, ex₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ey₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ez₆]; exact E₅.lt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base y K.M.n →
        tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    rw [e (by rw [m₇, ex₆]), e (by rw [m₇, ey₆]), e (by rw [m₇, ez₆])]
    rw [show (1 : Nat) = 0 + 1 from rfl, bpart_succ_pt hC hG hw.1, bpart_zero,
      show zmul (0 : Int) (G C) = .infinity by simp [zmul, Spec.Weierstrass.mul], infinity_add']
    refine InvJ.of_rep01 E₅.rep ?_
    rw [E₅.z]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [U.byte (combW_bits hL ht) (by omega_using [hbz, hzw, ht, hn])]
    exact hbits₃ t ht
  · exact TblMem.of_unch hF.tbl (by rw [k₇.2.2.1, k₇.2.2.2, k₆.rd, k₆.wr, E₅.keep.rd, E₅.keep.wr,
      k₃.2.2.1, k₃.2.2.2, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]) UT (tcombW_size hL hM) hF.out

/-- `[k]G` into `A`, in projective coordinates, for `k < kmax` (`BoothOk`)
whose bits are the table at `K.bits`; only `powClob` and `tcombW` change. -/
theorem tcombJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa K.combJ s fun s' => KeepRegs (powClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hJ2 := hB.J2
  have hw := hL.w
  have hnn := hL.n
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hNZ : NeZero C.p := ⟨by omega⟩
  unfold TCombCfg.combJ
  refine WP.seq (WP.mono (firstJ_ok hL hC hG hV hpn hb1 hs hM hF) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J)
    (Inv := fun r s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s'
      (K.J - r)) (n := K.J - 1)
    (fun r s' h1 h2 hi => WP.mono (stepJ_ok hL hC hM3 hG hV hpn hb1 hB hk hF (j := K.J - r) (by omega)
      (by omega) hi) fun s'' ⟨h, z⟩ => ⟨by rw [show K.J - (r - 1) = K.J - r + 1 by omega]; exact h, by
        rw [z]; congr 1; exact decide_eq_decide.mpr (by omega)⟩)
    (fun s' hi => by rw [Nat.sub_zero] at hi; exact hi) (by omega)
    (by rw [show K.J - (K.J - 1) = 1 by omega]; exact I₁)) fun s₂ I₂ => ?_)
  -- `Y = 1` where `Z = 0`.
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [I₂.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have ayz : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y := by
    have := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb]) (K.A.y, 8 * K.M.n)
      (by simp [combW, combWs, TCombCfg.toComb])
    dsimp only [TCombCfg.toComb] at this; omega
  refine WP.seq (WP.mono (outFix_ok K I₂.scr hnn.1 (Nat.lt_trans hV.one_lt hpn) (hle _ (by tcomb_mem))
    (hle _ (by tcomb_mem)) (hle _ (by tcomb_mem)) ayz hz₂) fun s₃ ⟨ey₃, k₃, O₃⟩ => ?_)
  have hs₃ := I₂.scr.of_keepRegs k₃ (by decide)
  have b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  have ex₃ : wordsVal s₃.mem base K.A.x K.M.n = wordsVal s₂.mem base K.A.x K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by grind)) (b64 _ (by tcomb_mem))
  have ez₃ : wordsVal s₃.mem base K.A.z K.M.n = wordsVal s₂.mem base K.A.z K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by grind)) (b64 _ (by tcomb_mem))
  have UA : Unch base [(K.A.y, 8 * K.M.n)] s₂.mem s₃.mem := O₃.unch
  have hmoW := tcombW_mo hL hM
  have hAyW : (K.A.y, 8 * K.M.n) ∈ tcombW K := List.mem_append_left _ (by
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      TCombCfg.toComb]; simp)
  have U₃ : Unch base (tcombW K) s.mem s₃.mem := (I₂.unch.trans UA).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact hAyW
  have hM₃ : ModOkW K.M size C.p s₃.mem base := hM.unch U₃ hmoW hn
  have hlt₃ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₃]; exact I₂.lt _ (by simp)
    · rw [ey₃]; split
      · exact hV.one_lt
      · exact I₂.lt _ (by simp)
    · rw [ez₃]; exact I₂.lt _ (by simp)
  have hSlA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], x ∈ combSlots K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> tcomb_mem
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) [K.A.x, K.A.y, K.A.z] (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, hM₃, hSlA, hlt₃, fun _ _ => rfl⟩
  have hS : ∀ op ∈ K.outOps, ∀ x ∈ op.out :: op.ins, x ∈ combSlots K.toComb := by
    intro op hop x hx
    simp only [TCombCfg.outOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
  have hR : readsOk K.outOps [K.A.x, K.A.y, K.A.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out]
  refine (fprogB_wp _ _).mpr (WP.mono (fprog_ok hL.comb.lay hV.unit K.outOps I₃ hS hR)
    fun s₄ ⟨P₄, I₄⟩ => ?_)
  have hval : ∀ x ∈ [K.A.x, K.A.y, K.A.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps K.outOps (tmv C K.M.n base s₃) x ∧ wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
    have hm : x ∈ validAfter K.outOps [K.A.x, K.A.y, K.A.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₄.val x hm, I₄.lt x hm⟩
  have U₄ : Unch base (tcombW K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      simp only [TCombCfg.outOps, FOp.out, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hy
      refine List.mem_append_left _ ?_
      simp only [combW, combWs, rcbW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false, TCombCfg.toComb]
      rcases hy with rfl | rfl | rfl <;> simp
    · rw [List.mem_singleton.mp h]
      exact List.mem_append_left _ (by simp [combW])
  refine ⟨?_, U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hM.unch (U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h)
      hmoW hn, fun x hx => (hval x hx).2, ?_⟩
  · exact (I₂.keep.trans (k₃.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob])).trans
      ((⟨P₄.gpr, P₄.rd, P₄.wr⟩ : KeepRegs (clob K.M.n) s₃ s₄).mono clob_powClob)
  · -- The values.
    have e : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₄ x = runOps K.outOps (tmv C K.M.n base s₃) x :=
      fun x hx => (hval x hx).1
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]
    have hxt : K.A.x ≠ K.S.t0 := by grind
    have hzt : K.A.z ≠ K.S.t0 := by grind
    have hxz : K.A.x ≠ K.A.z := by grind
    have hxy : K.A.x ≠ K.A.y := by grind
    have hyt : K.A.y ≠ K.S.t0 := by grind
    have hyz : K.A.y ≠ K.A.z := by grind
    simp only [TCombCfg.outOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
    have hy : tmv C K.M.n base s₃ K.A.y = if tmv C K.M.n base s₂ K.A.z = 0 then 1
        else tmv C K.M.n base s₂ K.A.y := by
      show toM _ _ _ = _
      rw [ey₃]
      by_cases h : wordsVal s₂.mem base K.A.z K.M.n = 0
      · have h' : tmv C K.M.n base s₂ K.A.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
        simp only [h, h', ↓reduceIte]; exact hV.one
      · have h' : tmv C K.M.n base s₂ K.A.z ≠ 0 := fun h0 =>
          h ((toM_eq_zero_iff hV.unit (I₂.lt _ (by simp))).mp h0)
        simp only [h, h', ↓reduceIte]
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s₂ K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [ex₃]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s₂ K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [ez₃]
    rw [hy, ex, ez]
    have h := InvJ.out hC I₂.rep
    rwa [bpart_top (by omega) (Nat.lt_of_lt_of_le hk hB.kmax), zmul_natCast] at h

end VG.Proof.Weierstrass.X86_64
