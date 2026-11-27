module

public import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.CombFrame
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# The fixed-base comb by complete additions on x86 (32-bit)

`TCombCfg.comb` (`Impl/Weierstrass/X86/TComb.lean`): the accumulator `A`
starts at `[H Σ_{i<J} 2^(wi)]G`, and the iteration for `esi = j` adds the
signed entry of digit `j - 1` (`entry_ok`: its magnitude from the window,
which for the top one is only the scalar's bits, `digitT_ok`; the selection,
`select_ok`; and `-y` under the mask of the digit's sign, `signMaskT_ok`) by
the complete addition, so that `A` represents `[combEW w k J (j - 1)]G`
(`step_ok`, by `combW_add`): after the `J` iterations, `[k]G` (`comb_ok`), for
any `k` below `2^kbytes`, whatever the curve's `a` and the order of `G`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- What the comb by complete additions needs of its windows, besides its
layout: the top window is partial (its top bit is past the scalar's bits, so
its digit is negative), and `3b` is in `S.b3`. -/
structure TCombTop (K : TCombCfg) : Prop where
  lo : K.w * (K.J - 1) ≤ K.kbytes
  hi : K.kbytes < K.w * K.J

/-- `ZF` for the top window. -/
theorem topTest_ok (K : TCombCfg) (s : State) {j : Nat} (hj : j < K.J) (hJ : K.J < 2 ^ 31)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block K.topTest) s fun t => t.zf = some (decide (j = K.J - 1)) ∧ CKeeps [] s t := by
  have hz : (BitVec.ofNat 32 j - BitVec.ofNat 32 (K.J - 1) == 0) = decide (j = K.J - 1) := by
    by_cases h : j = K.J - 1
    · rw [h, BitVec.sub_self, decide_eq_true rfl]; rfl
    · rw [decide_eq_false h, beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      have h0 : (0 : BitVec 32).toNat = 0 := rfl
      omega_using [hj, hJ, h, this, h0]
  unfold TCombCfg.topTest
  refine wp_cmpS rfl fun t F z => WP.block_nil ⟨?_, fun r _ => by rw [F.gpr], F.mem, F.rd, F.wr⟩
  rw [z, hb]
  exact congrArg some hz

/-- The magnitude of digit `j` into `eax` and `ebx`, from the `cnt` low bits
of its window, which are all of its bits that may be set. -/
theorem digitN_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j cnt N : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hc : cnt ≤ K.w) (hj : K.w * j + cnt ≤ N)
    (hj32 : j < 2 ^ 32) (hN : K.bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hwin : hornerVal (fun i => (k.testBit (K.w * j + i)).toNat) 0 cnt = combWin K.w k j) :
    WP isa (.block (winIndex K.w ++ hornerBits K.bits cnt ++ magnitudeH K.H)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧ CKeeps [.eax, .ecx, .edx, .ebx] s t := by
  have hn := hs.nowrap
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega_arith) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv cnt K.bits (s := a) (by omega_arith) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (K.w * j + i)) := by
      rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1) (by omega_arith)]
      exact congrArg (off base) (by omega_arith)
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega_arith)⟩, ?_⟩
    rw [he, ka.2.1, hbits _ (by omega_arith), show K.bits + i - K.bits = i by omega_arith]
    cases k.testBit (K.w * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (K.w * j + (t - K.bits))).toNat) K.bits cnt = combWin K.w k j := by
      rw [← hwin]
      exact hornerVal_congr fun i _ => by
        simp only [show K.bits + i - K.bits = i by omega_arith, Nat.zero_add]
    have hlt := combWin_lt K.w k j
    refine WP.mono (magnitudeH_ok b hw hlt (by rw [b2, hw'])) fun t ⟨t1, t2, kt⟩ =>
      ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩

/-- The magnitude of digit `esi = j` into `eax` and `ebx`: `|k_j - H|`, the
top window from the scalar's bits only. -/
theorem digitT_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : j < K.J) (hJ : K.J < 2 ^ 31)
    (hT : TCombTop K) (hk : k < 2 ^ K.kbytes)
    (hN : K.bits + K.kbytes ≤ size) (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < K.kbytes, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa K.digitT s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧ CKeeps [.eax, .ecx, .edx, .ebx] s t := by
  have hlo := hT.lo
  have hhi := hT.hi
  unfold TCombCfg.digitT
  refine WP.seq (WP.mono (topTest_ok K s hj hJ hx) fun s₁ ⟨z₁, k₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 j := by rw [k₁.1 _ List.not_mem_nil, hx]
  have hb₁ : ∀ t < K.kbytes, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [k₁.2.1]; exact hbits t ht
  have hcl : ∀ r ∈ ([] : List Reg), r ∈ [Reg.eax, .ecx, .edx, .ebx] := fun _ h => nomatch h
  refine WP.ite (decide (j = K.J - 1)) z₁ (fun h => ?_) (fun h => ?_)
  · have hjt : j = K.J - 1 := of_decide_eq_true h
    have hb := windowBits_bounds (w := K.w) (J := K.J) (bits := K.kbytes) hj hlo (Nat.le_of_lt hhi)
    dsimp only at hb
    rw [ite_eq_left hjt] at hb
    refine WP.mono (digitN_ok K hs₁ (k := k) (j := j) (cnt := K.topBits) (N := K.kbytes) hw1 hw hb.1 hb.2.1
      (by omega_using [hj, hJ]) hN hx₁ hb₁ (window_without_padding hb.1 hb.2.2 hk)) fun t ⟨a, b, kt⟩ =>
      ⟨a, b, (k₁.mono hcl).trans kt⟩
  · have hjt : j ≠ K.J - 1 := of_decide_eq_false h
    have hwj : K.w * j + K.w ≤ K.kbytes := by
      have := Nat.mul_le_mul_left K.w (show j + 1 ≤ K.J - 1 by omega_using [hj, hjt])
      rw [Nat.mul_succ] at this
      omega_using [this, hlo]
    refine WP.mono (digit_ok K hs₁ (k := k) (j := j) (N := K.kbytes) hw1 hw hwj hN hx₁ hb₁) fun t ⟨a, b, kt⟩ =>
      ⟨a, b, (k₁.mono hcl).trans kt⟩

/-- `ecx` all ones if digit `esi = j` is negative: always for the top window. -/
theorem signMaskT_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j : Nat} (hw1 : 1 ≤ K.w) (hw : K.w < 9) (hj : j < K.J) (hJ : K.J < 2 ^ 31)
    (hT : TCombTop K) (hk : k < 2 ^ K.kbytes)
    (hN : K.bits + K.kbytes ≤ size) (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < K.kbytes, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa K.signMaskT s fun t =>
      t.gpr .ecx = bmask (decide (combWin K.w k j < 2 ^ (K.w - 1))) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  have hlo := hT.lo
  have hhi := hT.hi
  unfold TCombCfg.signMaskT
  refine WP.seq (WP.mono (topTest_ok K s hj hJ hx) fun s₁ ⟨z₁, k₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 j := by rw [k₁.1 _ List.not_mem_nil, hx]
  have hb₁ : ∀ t < K.kbytes, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [k₁.2.1]; exact hbits t ht
  have hcl : ∀ r ∈ ([] : List Reg), r ∈ [Reg.eax, .ecx, .edx] := fun _ h => nomatch h
  refine WP.ite (decide (j = K.J - 1)) z₁ (fun h => ?_) (fun h => ?_)
  · have hjt : j = K.J - 1 := of_decide_eq_true h
    have hneg : combWin K.w k j < 2 ^ (K.w - 1) := by
      have e : K.kbytes = K.w * j + (K.kbytes - K.w * j) := by rw [hjt]; omega_using [hlo]
      have hdiv : k / 2 ^ (K.w * j) < 2 ^ (K.kbytes - K.w * j) := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        rw [← Nat.pow_add, Nat.add_comm, ← e]
        exact hk
      have hle : 2 ^ (K.kbytes - K.w * j) ≤ 2 ^ (K.w - 1) := Nat.pow_le_pow_right (by decide) (by
        have e2 : K.w * K.J = K.w * (K.J - 1) + K.w := by
          rw [← Nat.mul_succ]; congr 1; omega_using [hj]
        rw [hjt]; omega_using [hhi, e2, hw1])
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_lt_of_le hdiv hle)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, k₁.2.1, k₁.2.2.1, k₁.2.2.2⟩
    · rw [RegUpd.gpr_setReg_self, decide_eq_true hneg]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.1]
      exact k₁.1 r List.not_mem_nil
  · have hjt : j ≠ K.J - 1 := of_decide_eq_false h
    have hwj : K.w * j + K.w ≤ K.kbytes := by
      have := Nat.mul_le_mul_left K.w (show j + 1 ≤ K.J - 1 by omega_using [hj, hjt])
      rw [Nat.mul_succ] at this
      omega_using [this, hlo]
    refine WP.mono (signMask_ok K hs₁ (k := k) (j := j) (N := K.kbytes) hw1 (by omega_using [hw]) hwj hN hx₁ hb₁)
      fun t ⟨a, kt⟩ => ⟨a, (k₁.mono hcl).trans kt⟩

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
structure TEntryPost (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (signedPtW C K.w k i)

/-- The entry of digit `i`, selected (from `esi = i`) and negated for a
negative digit. -/
theorem entry_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hT : TCombTop K) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .esi = BitVec.ofNat 32 i)
    (hk : k < 2 ^ K.kbytes)
    (hbits : ∀ t < K.kbytes, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hTs : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hout : ∀ q < (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * q) + BitVec.ofNat 64 b)) :
    WP isa K.entry s (TEntryPost K C base size k i s) := by
  have hn := hs.nowrap
  have hsz := hL.sz
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnn := hL.n
  have hbits' := hL.bits
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
  have ap : ∀ {x y : Nat}, x ∈ combWs K.toComb → y ∈ combWs K.toComb → x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun hx hy h => hL.comb.apart₂ hx hy h
  have hexy := hL.exy
  have hEx := hle K.E.x (by tcomb_mem)
  have hEy := hle K.E.y (by tcomb_mem)
  have hEz := hle K.E.z (by tcomb_mem)
  have hneg := hle K.neg (by tcomb_mem)
  have hzl := hle K.zero (by tcomb_mem)
  have hJ31 : K.J < 2 ^ 31 := by omega_using [hJ]
  have hbN : K.bits + K.kbytes ≤ size := by omega_using [hbits']
  unfold TCombCfg.entry
  refine WP.seq (WP.mono (digitT_ok K hs (k := k) (j := i) hw.1 hw.2 hi hJ31 hT hk hbN hx hbits)
    fun s₁ ⟨a₁, m₁, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 i := by rw [k₁.1 _ (by decide), hx]
  have hmag : magH K.H (combWin K.w k i) ≤ K.H := magH_le (by
    have := combWin_lt K.w k i
    have h2 : 2 ^ K.w = 2 * 2 ^ (K.w - 1) :=
      (congrArg (2 ^ ·) (Nat.sub_add_cancel hw.1).symm).trans Nat.pow_succ'
    unfold TCombCfg.H; omega_using [this, h2])
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
  have hbytes : 8 * (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length = K.J * K.tblBytes := by
    rw [hlen, TCombCfg.tblBytes]
    calc
      _ = (8 * 2) * (K.J * K.H * K.M.n) := by ac_rfl
      _ = K.J * (16 * K.M.n * K.H) := by change 16 * _ = _; ac_rfl
  have hbound : T.toNat + i * K.tblBytes + K.tblBytes ≤ 2 ^ 32 := by
    have ht := hTM.nowrap
    rw [hbytes] at ht
    have hb := Nat.mul_le_mul_right K.tblBytes (show i + 1 ≤ K.J from hi)
    rw [Nat.add_mul, Nat.one_mul] at hb; omega_using [ht, hb]
  have hptrnat : (s.mem.readW (off base K.ptr) 32).toNat = T.toNat := by
    rw [← hTs, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
      have := (s.mem.readW (off base K.ptr) 32).isLt; omega_using [])]
  have hpos : 0 < K.tblBytes := by
    unfold TCombCfg.tblBytes TCombCfg.H
    exact Nat.mul_pos (by omega_using [hnn]) (Nat.two_pow_pos _)
  have haddr : ((s.mem.readW (off base K.ptr) 32 + BitVec.ofNat 32 (i * K.tblBytes)).setWidth 64) =
      T + BitVec.ofNat 64 (i * K.tblBytes) := by
    change addr _ _ = _
    rw [addr_eq (by omega_using [hbound, hptrnat, hpos]), hTs]
  have haddrNat : (T + BitVec.ofNat 64 (i * K.tblBytes)).toNat = T.toNat + i * K.tblBytes := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hbound] : i * K.tblBytes < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [hbound])]
  have h0x := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  have h0y := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  have h0z := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  refine WP.seq (WP.mono (select_ok K hs₁ hnn (by omega_using [hHle]) (by have := hL.tbl; omega_using [this]) hL.ptr_le hexy hEy hEz
    (by
      have := ap (x := K.E.x) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
      have := ap (x := K.E.y) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega_arith) hzl (by dsimp only [TCombCfg.toComb] at h0x h0y; omega_using [hexy, h0x, h0y]) h0z (Nat.lt_trans hV.one_lt hpn)
    (by rw [k₁.2.1]; exact hz) hx₁ m₁ hmag (T := s.mem.readW (off base K.ptr) 32)
    (by rw [k₁.2.1]) (by rw [haddr]; exact hreg) (by rw [haddr, haddrNat]; exact hbound)
    (by rw [haddr]; exact tbl_out_at hout hbytes hi)) fun s₂ S₂ => ?_)
  rw [haddr] at S₂
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := S₂
  rw [k₁.2.1] at ex₂ ey₂ U₂
  have hmagdef : magH K.H (combWin K.w k i) =
      if 2 ^ (K.w - 1) ≤ combWin K.w k i then combWin K.w k i - 2 ^ (K.w - 1)
        else 2 ^ (K.w - 1) - combWin K.w k i := rfl
  generalize ha : magH K.H (combWin K.w k i) = a at ex₂ ey₂ ez₂ hmag hmagdef
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  -- The selected coordinates.
  have hent : 1 ≤ a → wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n =
        (combAt tbl i (a - 1)).1 * 2 ^ (64 * K.M.n) % C.p ∧
      wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
        (combAt tbl i (a - 1)).2 * 2 ^ (64 * K.M.n) % C.p := fun h1 => by
    rw [TCombCfg.tblBytes]
    exact tbl_entry hTM hV.len hV.lenH hi (by omega_using [hmag, h1]) (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
      (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · have := hmo K.E.x (by tcomb_mem); dsimp only; omega_using [this]
    · have := hmo K.E.y (by tcomb_mem); dsimp only; omega_using [this]
    · have := hmo K.E.z (by tcomb_mem); dsimp only; omega_using [this]
  have hM₂ : ModOkW K.M size C.p s₂.mem base := hM.unch U₂ hmoE (by omega_using [hn])
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    have hzW := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (by simp [combW, combWs, TCombCfg.toComb])) (by omega_using [hsz, hzl]), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · rw [(hent ‹_›).2]; exact Nat.mod_lt _ hp0
    · exact hV.one_lt
  refine WP.seq (WP.mono (subC_ok (hL.wkOk hV.fn).toCallCfg hs₂ (o := K.neg) (a := K.zero) (b := K.E.y)
    (hL.wsl _ (by tcomb_mem)) (hL.wsl _ (by tcomb_mem)) (hL.wsl _ (by tcomb_mem))
    (by rw [hz₂]; exact hp0) hEy₂) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ : Scr s₃ base size := k₃.scr hs₂
  have U₃ := k₃.unch
  have hwkx := hL.wsl K.E.x (by tcomb_mem)
  have hwky := hL.wsl K.E.y (by tcomb_mem)
  have hwkz := hL.wsl K.E.z (by tcomb_mem)
  have hwkbits := hL.wk_bits
  have hx₃ : s₃.gpr .esi = BitVec.ofNat 32 i := by
    rw [k₃.gpr _ esi_not_clob, k₂.gpr _ (by decide), hx₁]
  have hbits₃ : ∀ t < K.kbytes, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    have hbw := hL.bits_w
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · have := hbw (K.neg, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [ht, this]
        · have := hbw (K.M.tmp, 8 * K.M.n) (by simp [combW, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [ht, this]
        · dsimp only; omega_using [hwkbits, ht]
        · dsimp only [Mont.outW]; omega_using [hsz, hbits', ht]) (by omega_using [hsz, hbits', ht]),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hbw (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [ht, this]
        · have := hbw (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [ht, this]
        · have := hbw (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [ht, this]) (by omega_using [hsz, hbits', ht])]
    exact hbits t ht
  refine WP.seq (WP.mono (signMaskT_ok K hs₃ (k := k) (j := i) hw.1 hw.2 hi hJ31 hT hk hbN hx₃ hbits₃)
    fun s₄ ⟨x₄, k₄⟩ => ?_)
  have hs₄ := hs₃.of_keeps k₄.keeps (by decide)
  refine WP.mono (selWords_ok hs₄ (decide (combWin K.w k i < 2 ^ (K.w - 1))) x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _))
      (by have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega_using [this])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (ap (x := K.E.x) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)) (by omega_using [hsz, hEx]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.x (by tcomb_mem); dsimp only; omega_using [this]
      · dsimp only; omega_using [hwkx]
      · dsimp only [Mont.outW]; omega_using [hsz, hEx]) (by omega_using [hsz, hEx])]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (ap (x := K.E.z) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)) (by omega_using [hsz, hEz]), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.z (by tcomb_mem); dsimp only; omega_using [this]
      · dsimp only; omega_using [hwkz]
      · dsimp only [Mont.outW]; omega_using [hsz, hEz]) (by omega_using [hsz, hEz])]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega_using [this]
      · have := htmp K.E.y (by tcomb_mem); dsimp only; omega_using [this]
      · dsimp only; omega_using [hwky]
      · dsimp only [Mont.outW]; omega_using [hsz, hEy]) (by omega_using [hsz, hEy])
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
  have hcl : ∀ r ∈ [Reg.eax, .ecx, .edx, .ebx], r ∈ clob := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · simp [clob]
  refine ⟨hs₄.of_keeps k₅ (by decide), ?_, ?_, ?_, ?_⟩
  · exact (((((CKeeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ⟨k₃.gpr, k₃.rd, k₃.wr⟩).trans ((CKeeps.regs k₄).mono fun r hr => hcl r (by
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
    by_cases h1 : 2 ^ (K.w - 1) ≤ combWin K.w k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (by omega_using [h1])]; rfl
      rw [hy, ite_eq_left h1]
      rw [ite_eq_left h1] at hmagdef
      rw [← hmagdef]
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (by omega_using [h1])]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₂]), toM_zero]
        grind
      rw [hy, ite_eq_right h1]
      rw [ite_eq_right h1] at hmagdef
      rw [← hmagdef]
      exact Rep.negY hR

/-- The loop's invariant at `esi = j`: `A` represents `[combEW w k J j]G`,
and the table of bits and the tables are where the digits and the selection
read them. -/
structure TCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : KeepRegs (powClob) s₀ s
  unch : Unch base (combWx K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.kbytes, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T

/-- The table of the scalar's bits is apart from what the comb writes. -/
theorem combWx_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.kbytes) :
    ∀ w ∈ combWx K, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have := hL.bits_w w hw; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rcases hL.wk_bits with h | h
      · exact .inl (by omega_arith)
      · exact .inr (by omega_arith)
    · have := hL.bits; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega_arith)

/-- An iteration, from `esi = j ≥ 1`: the entry of digit `j - 1` added. -/
theorem step_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hT : TCombTop K) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hb3 : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p (3 * C.b))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (hsp : SpOk K.step 20) :
    WP isa K.step s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain hsz : size ≤ 2 ^ 64 := by have := hL.sz; omega_using [this]
  obtain hX : ∀ x ∈ combWs K.toComb, ∀ w ∈ [(K.wk, 64 * K.M.n), Mont.outW],
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
    intro x hx w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inl (hL.wsl x (combWs_slots _ x hx))
    · have h1 := hle x (combWs_slots _ x hx); have := hL.sz
      exact .inl (by dsimp only [Mont.outW]; omega_using [h1, this])
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  obtain hNZ : NeZero C.p := ⟨by omega_using [hp0]⟩
  obtain hsp₀ : s.gpr .esp = s₀.gpr .esp := hI.keep.gpr _ (by decide)
  have hwr₀ : s.wr = s₀.wr := hI.keep.wr
  have hw := hL.w
  refine WP.withSp hsp (by rw [hsp₀]; exact hF.sp_lo) ?_
  unfold TCombCfg.step
  refine WP.seq (wp_decCounter hj hI.esi fun s₁ e₁ k₁ m₁ => WP.block_nil ?_)
  have hs₁ : Scr s₁ base size := hI.scr.of_keeps k₁ (by decide)
  obtain hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [m₁, hI.unch.wordsVal (fun w hw => tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]) w
        (List.mem_append_left _ hw))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  refine WP.seq (WP.mono (entry_ok hL hT hC hV hpn hs₁ (by rw [m₁]; exact hI.mod) (i := j - 1)
    (by omega_using [hj, hjn]) e₁ hF.k_lt (by rw [m₁]; exact hI.bits) hz (by rw [m₁]; exact hI.tsym)
    (hI.tbl.unch (by rw [k₁.2.1, k₁.2.2]) (fun _ _ _ _ => by rw [m₁])) hF.out) fun s₃ E₃ => ?_)
  obtain hEu : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW] s.mem s₃.mem := by rw [← m₁]; exact E₃.unch
  obtain hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW], w ∈ combWx K := fun w hw =>
    (List.mem_append.mp (show w ∈ combEntryW K.toComb ++ [(K.wk, 64 * K.M.n), Mont.outW] from hw)).elim
      (fun h => List.mem_append_left _ (combEntryW_sub w h)) (fun h => List.mem_append_right _ h)
  obtain U₁₃ : Unch base (combWx K) s.mem s₃.mem := hEu.mono hEW
  obtain hmoW : ∀ w ∈ combWx K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo :=
    fun w hw => tcombW_mo hL hI.mod w (List.mem_append_left _ hw)
  obtain hM₃ : ModOkW K.M size C.p s₃.mem base := hI.mod.unch U₁₃ hmoW (by omega_using [hn])
  obtain hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    hL.comb.wordsVal_entryX hsz hX hEu
  obtain U₃ : Unch base (combWx K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  obtain hroW : ∀ x ∈ combRo K.toComb, ∀ w ∈ combWx K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x :=
    fun x hx w hw => tcombW_ro hL hx w (List.mem_append_left _ hw)
  obtain hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (hroW x hx) (by have := hle x (combRo_slots x hx); omega_using [hn, this])
  obtain hSl : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  obtain hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
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
  obtain I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  obtain hSl' : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq (WP.mono (rcb_ok hL.comb.lay (hL.wkOk hV.fn) hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄, n₄⟩ => ?_)
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  have hs₄ := I₄.scr
  obtain hb₄ : s₄.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [P₄.gpr _ esi_not_clob, E₃.keep.gpr _ esi_not_clob, e₁]
  obtain U₄ : Unch base (combWx K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [progW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h | h | h
    · exact Or.inl (Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩)
    · exact Or.inl (Or.inr (by rw [h]; rfl))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
  obtain hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  -- `A = D`.
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₄ (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    (fun x hx y hy hxy => hL.comb.apart₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem) hxy)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> nd_ne hnd)
    (by nd_ne hnd)) fun s₅ ⟨ax₅, ay₅, az₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  obtain hb₅ : s₅.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [k₅.gpr _ (by decide), hb₄]
  refine wp_testCounter (by omega_using [hjn, hJ]) hb₅ fun s₆ F₆ z₆ => WP.block_nil fun fr => ⟨?_, z₆⟩
  obtain U₅ : Unch base (combWx K) s₄.mem s₅.mem := O₅.mono fun w hw =>
    List.mem_append_left _ (combSelW_A_sub (K := K.toComb) w hw)
  obtain U : Unch base (combWx K) s.mem s₆.mem := by
    rw [F₆.mem]
    exact (U₁₃.trans (U₄.trans U₅)).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with h | h | h <;> exact h
  obtain hcl : ∀ r ∈ [Reg.eax], r ∈ powClob := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact clob_powClob _ (by simp [clob])
  refine ⟨hs₅.of_keeps (F₆.keeps []) (by decide), by rw [F₆.gpr]; exact hb₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c₁ : KeepRegs (powClob) s s₁ := k₁.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    have c₃ : KeepRegs (powClob) s₁ s₃ := E₃.keep.mono clob_powClob
    obtain c₄ : KeepRegs (powClob) s₃ s₄ := Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob
    obtain c₅ : KeepRegs (powClob) s₄ s₅ := k₅.mono hcl
    obtain c₆ : KeepRegs (powClob) s₅ s₆ := (F₆.keeps []).mono fun _ h => nomatch h
    exact hI.keep.trans (c₁.trans (c₃.trans (c₄.trans (c₅.trans c₆))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  · exact hI.mod.unch U hmoW (by omega_using [hn])
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [F₆.mem, ax₅]; exact hDlt _ (by simp)
    · rw [F₆.mem, ay₅]; exact hDlt _ (by simp)
    · rw [F₆.mem, az₅]; exact hDlt _ (by simp)
  · -- The point.
    obtain e : ∀ {x y : Nat}, wordsVal s₆.mem base x K.M.n = wordsVal s₄.mem base y K.M.n →
        tmv C K.M.n base s₆ x = tmv C K.M.n base s₄ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    obtain eA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s x :=
      fun x hx => by show toM _ _ _ = toM _ _ _; rw [hAx x hx]
    rw [e (by rw [F₆.mem, ax₅]), e (by rw [F₆.mem, ay₅]), e (by rw [F₆.mem, az₅])]
    obtain hD : (tmv C K.M.n base s₄ K.D.x, tmv C K.M.n base s₄ K.D.y, tmv C K.M.n base s₄ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd (tmv C K.M.n base s₃ K.S.a) (tmv C K.M.n base s₃ K.S.b3)
          (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y) (tmv C K.M.n base s₃ K.A.z)
          (tmv C K.M.n base s₃ K.E.x) (tmv C K.M.n base s₃ K.E.y) (tmv C K.M.n base s₃ K.E.z) := by
      rw [← t₄]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp))]
    obtain ha : tmv C K.M.n base s₃ K.S.a = Fin.ofNat C.p C.a := by
      show toM _ _ _ = _
      rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.a
    obtain hb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p (3 * C.b) := by
      show toM _ _ _ = _
      rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hb3
    rw [ha, hb, eA _ (by simp), eA _ (by simp), eA _ (by simp)] at hD
    have hrep := hI.rep
    rw [show j = j - 1 + 1 by omega_using [hj]] at hrep
    have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega_using [hj, hjn])
    rw [← hadd]
    exact Rep.add hC (hC.onCurve_mul hG _) (by
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) hrep E₃.rep hD.symm
  · intro t ht
    rw [U.byte (combWx_bits hL ht) (by have := hL.bits; omega_using [this, ht, hn]), ]
    exact hI.bits t ht
  · exact hF.tblAt hwr₀ hsp₀ hI.tbl (by rw [F₆.rd, F₆.wr, k₅.rd, k₅.wr, P₄.rd, P₄.wr, E₃.keep.rd,
      E₃.keep.wr, k₁.2.1, k₁.2.2]) fr
  · rw [unch_read32 U (by have := hL.ptr_le; omega_using [hn, this]) (combW_ptr hL)]
    exact hI.tsym

/-- `A = [H Σ_{i<J} 2^(wi)]G` and `esi = J`: the invariant, before the first iteration. -/
theorem init_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.init) s
      (TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s · K.J) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hsz := hL.sz
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have ap : ∀ {x y : Nat}, x ∈ combWs K.toComb → y ∈ combWs K.toComb → x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun hx hy h => hL.comb.apart₂ hx hy h
  have hAx := hle K.A.x (by tcomb_mem)
  have hAy := hle K.A.y (by tcomb_mem)
  have hAz := hle K.A.z (by tcomb_mem)
  have hone : K.one < 2 ^ (64 * K.M.n) := Nat.lt_trans hV.one_lt hpn
  have hsx : K.start.1 < 2 ^ (64 * K.M.n) := Nat.lt_trans hV.start_lt.1 hpn
  have hsy : K.start.2 < 2 ^ (64 * K.M.n) := Nat.lt_trans hV.start_lt.2 hpn
  have pxy := ap (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  have pxz := ap (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  have pyz := ap (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
  unfold TCombCfg.init
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) hAx hsx) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) hAy hsy) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) hAz hone) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (movEsi_ok s₃ (j := K.J) (by omega_using [hJ])) fun s₄ ⟨b₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have hs₄ := hs₃.of_keeps k₄.keeps (by decide)
  have hcl : ∀ r ∈ [Reg.eax], r ∈ powClob := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact clob_powClob _ (by simp [clob])
  obtain UA : Unch base [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)] s.mem s₄.mem := by
    rw [m₄]
    refine (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  obtain U₄ : Unch base (combWx K) s.mem s₄.mem := UA.mono fun w hw =>
    List.mem_append_left _ (combSelW_A_sub (K := K.toComb) w hw)
  obtain hmoW : ∀ w ∈ combWx K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo :=
    fun w hw => tcombW_mo hL hM w (List.mem_append_left _ hw)
  have ex₄ : wordsVal s₄.mem base K.A.x K.M.n = K.start.1 := by
    rw [m₄, O₃.wordsVal pxz (by omega_using [hsz, hAx]), O₂.wordsVal pxy (by omega_using [hsz, hAx]), e₁]
  have ey₄ : wordsVal s₄.mem base K.A.y K.M.n = K.start.2 := by
    rw [m₄, O₃.wordsVal pyz (by omega_using [hsz, hAy]), e₂]
  have ez₄ : wordsVal s₄.mem base K.A.z K.M.n = K.one := by rw [m₄, e₃]
  refine ⟨hs₄, b₄, ?_, U₄, hM.unch U₄ hmoW (by omega_using [hn]), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((k₁.mono hcl).trans ((k₂.mono hcl).trans (k₃.mono hcl))).trans
      ((CKeeps.regs k₄).mono fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₄]; exact hV.start_lt.1
    · rw [ey₄]; exact hV.start_lt.2
    · rw [ez₄]; exact hV.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₄, ey₄, ez₄, hV.one, combEW_top]
    exact hV.start
  · intro t ht
    rw [U₄.byte (combWx_bits hL ht) (by have := hL.bits; omega_using [this, ht, hn])]
    exact hF.bits t ht
  · exact hF.tbl.of_unch (by rw [k₄.2.2.1, k₄.2.2.2, k₃.2.1, k₃.2.2, k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]) UA
      (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> with_reducible assumption) hF.out
  · rw [unch_read32 U₄ (by have := hL.ptr_le; omega_using [hn, this]) (combW_ptr hL)]
    exact hF.tsym

/-- `[k]G` into `A`, in projective coordinates, for `k` below `2^kbytes`
whose bits are the table at `K.bits`; only `powClob` and `combWx` change. -/
theorem comb_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hT : TCombTop K) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hb3 : tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hsp : SpOk K.comb 20) :
    WP isa K.comb s fun s' => KeepRegs (powClob) s s' ∧ Unch base (combWx K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  obtain hspS : SpOk K.step 20 := ⟨NoSp.loop hsp.right.1, hsp.right.2⟩
  unfold TCombCfg.comb
  refine WP.seq (WP.mono (init_ok hL hV hpn hs hM hF) fun s₄ I₄ => ?_)
  refine WP.mono (countLoop_ok (Q := fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' 0)
    (Inv := fun r s' => TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' r)
    (n := K.J)
    (fun r s' h1 h2 hi => step_ok hL hT hC hG hV hpn hF hb3 h1 h2 hi hspS)
    (fun s' hi => hi) hJ.1 I₄) fun s' I => ⟨I.keep, I.unch, I.mod, I.lt, ?_⟩
  have h := I.rep
  rwa [combEW_zero (Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hT.hi)))] at h

end VG.Proof.Weierstrass.X86
