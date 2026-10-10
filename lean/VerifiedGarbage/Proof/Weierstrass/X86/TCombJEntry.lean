import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
structure TEntryPostJ (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (bentry C K.w k i)

  /-- The entry is affine unless the digit is zero. -/
  z : tmv C K.M.n base s' K.E.z = if 1 ≤ bmag K.w k i then 1 else 0

/-- The entry of digit `i`, selected (from `esi = i`) and negated for a
negative digit. -/
theorem tentryJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .esi = BitVec.ofNat 32 i)
    (hb1 : 1 ≤ K.bits) {c : Bool} (hc : (c = true ∧ 1 ≤ i) ∨ (c = false ∧ i = 0))
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : (s.mem.readW (off base K.ptr) 32).setWidth 64 = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block (K.bdigit c ++ K.select)) s fun s₂ =>
      WP isa K.bnegY s₂ (TEntryPostJ K C base size k i s) := by
  have hn := hs.nowrap
  have hsz := hL.sz
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnn := hL.n
  have hzw : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
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
  refine WP.mono (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J) hw.1 hw.2 hwi (by omega_using [hzw, hbits']) hb1 hx hbits hc)
    fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 i := by rw [k₁.1 _ (by decide), hx]
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
    rw [← hT, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
      have := (s.mem.readW (off base K.ptr) 32).isLt; omega_using [])]
  have hpos : 0 < K.tblBytes := by
    unfold TCombCfg.tblBytes TCombCfg.H
    exact Nat.mul_pos (by omega_using [hnn]) (Nat.two_pow_pos _)
  have haddr : ((s.mem.readW (off base K.ptr) 32 + BitVec.ofNat 32 (i * K.tblBytes)).setWidth 64) =
      T + BitVec.ofNat 64 (i * K.tblBytes) := by
    change addr _ _ = _
    rw [addr_eq (by omega_using [hbound, hptrnat, hpos]), hT]
  have haddrNat : (T + BitVec.ofNat 64 (i * K.tblBytes)).toNat = T.toNat + i * K.tblBytes := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hbound] : i * K.tblBytes < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [hbound])]
  have h0x := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  have h0y := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  have h0z := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb])
  refine WP.mono (select_ok K hs₁ hnn (by omega_using [hHle]) (by have := hL.tbl; omega_using [this]) hL.ptr_le hexy hEy hEz
    (by
      have := ap (x := K.E.x) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
      have := ap (x := K.E.y) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega) hzl (by dsimp only [TCombCfg.toComb] at h0x h0y; omega_using [hexy, h0x, h0y]) h0z (Nat.lt_trans hV.one_lt hpn)
    (by rw [k₁.2.1]; exact hz) hx₁ m₁ hmag (T := s.mem.readW (off base K.ptr) 32)
    (by rw [k₁.2.1]) (by rw [haddr]; exact hreg) (by rw [haddr, haddrNat]; exact hbound)) fun s₂ S₂ => ?_
  rw [haddr] at S₂
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
  rw [TCombCfg.bnegY]
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
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    have hbw := hL.bits_w
    rw [U₃.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · have := hbw (K.neg, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.M.tmp, 8 * K.M.n) (by simp [combW, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · dsimp only; omega_using [hzw, hwkbits, ht]
        · dsimp only [Mont.outW]; omega_using [hsz, hzw, hbits', ht]) (by omega_using [hsz, hzw, hbits', ht]),
      U₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · have := hbw (K.E.x, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.E.y, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]
        · have := hbw (K.E.z, 8 * K.M.n) (by simp [combW, combWs, TCombCfg.toComb]); dsimp only at this ⊢
          omega_using [hzw, ht, this]) (by omega_using [hsz, hzw, hbits', ht])]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (bsignMask_ok K hs₃ (k := k) (j := i) (N := K.w * K.J) hw.1 (by omega_using [hw]) hwi (by omega)
    hx₃ hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄.keeps (by decide)
  refine WP.mono (selWords_ok hs₄ (decide (bcar K.w k (i + 1) = 1)) x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy hEy hneg (Or.inl (Nat.le_refl _))
      (by have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (ap (x := K.E.x) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega
      · have := htmp K.E.x (by tcomb_mem); dsimp only; omega
      · dsimp only; omega
      · dsimp only [Mont.outW]; omega) (by omega)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (ap (x := K.E.z) (y := K.E.y) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega
      · have := htmp K.E.z (by tcomb_mem); dsimp only; omega
      · dsimp only; omega
      · dsimp only [Mont.outW]; omega) (by omega)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · have := ap (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); dsimp only; omega
      · have := htmp K.E.y (by tcomb_mem); dsimp only; omega
      · dsimp only; omega
      · dsimp only [Mont.outW]; omega) (by omega)
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
  have hcl : ∀ r ∈ [Reg.eax, .ecx, .edx, .ebx], r ∈ clob := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · simp [clob]
  refine ⟨hs₄.of_keeps k₅ (by decide), ?_, ?_, ?_, ?_, ?_⟩
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

end VG.Proof.Weierstrass.X86
