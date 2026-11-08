module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
public import VerifiedGarbage.Proof.Ed448.Comb
public import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import VerifiedGarbage.Proof.X448.Field

/-!
# Ed448 on PPC64LE: the four-column comb

The base-point multiplication of `Impl/Ed448/PPC64LE/ScalarBase.lean`
(`combLoop`), proven as RISC-V's comb is (`Proof/Ed448/RISCV64/Comb.lean`):

* The point operations (`combDblOps`, `combAddOps`) are field programs of
  X448's (`opsProg_eq`), whose elements afterwards are those of
  `Proof.Ed448.double` (`dbl_vals`) and of RFC 8032's addition with `Z₂ = 1`
  (`add_vals`, `addAffine_eq`). Each is a function the loop calls
  (`call_ops`): it starts with the link register and `r0`, `r11` and `r12`
  unknown, which X448's operations never read, and returns with the slots
  updated, having written only the registers of `work` and the field area.
* `tabBuild` stores the sixteen entries of `Impl/Ed448/Comb.lean` at
  `CTAB` with `constField` (`tabBuild_ok`), entry `i`'s `x` at
  `CTAB + 112 i` and its `y` 56 bytes on (`TabOk`).
* `combDigit` reads the row's four bits of the scalar from `BITS` into the
  index `r10` (`digit_ok`, `Proof.Ed448.Comb.digit`). `combSelect` zeroes
  `(SX, SY)`, then ORs in each entry's fourteen doublewords under the mask
  of `r10 = i` (`entry_ok`), so that `(SX, SY)` holds the index's entry
  (`select_ok`, `sel_x`), every entry read whatever the index.
* One row (`step_ok`): with `R` representing `[accScalar k (t + 1)] B`
  before, it represents `[accScalar k t] B` after (`step_rep`, from
  `Proof/Ed448/Comb.lean`). The loop (`loop_ok`) runs the 114 rows; the
  memory it writes is the field area, so the table and the scalar's bits stay
  (`Fixed`).
-/

-- separate module: its proofs take about 6 s, which `BaseMain.lean`'s edits need not re-check

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Comb

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (ACC BITS)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point)

/-! ## The point operations -/

/-- An operation of the implementation as one of X448's. -/
def toF : COp → FOp
  | .mul o x y => .mul o x y
  | .add o x y => .add o x y
  | .sub o x y => .sub o x y

theorem opsProg_eq : ∀ ops : List COp, opsProg ops = opsCode (ops.map toF) (.block [])
  | [] => rfl
  | op :: ops => by
    rw [opsProg, List.map_cons, opsCode, opsProg_eq ops]
    cases op <;> rfl

/-- RFC 8032's addition of `p` and `(x : y : 1)`, with `A = Z₁`. -/
def addAffine (p : Point) (x y : Fe) : Point :=
  let b := p.Z * p.Z
  let c := p.X * x
  let d' := p.Y * y
  let e := Spec.Ed448.d * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (x + y)
  ⟨p.Z * f * (h - c - d'), p.Z * g * (d' - c), f * g⟩

theorem addAffine_eq (p : Point) (x y : Fe) : addAffine p x y = Spec.Ed448.pointAdd p ⟨x, y, 1⟩ := by
  simp only [addAffine, Spec.Ed448.pointAdd, Fin.mul_one]

/-- The slots kept across the doubling. -/
def DQ : List Nat := [RX, RY, RZ, DK]

/-- And across the addition. -/
def AQ : List Nat := [RX, RY, RZ, DK, SX, SY]

theorem dbl_ok : opsOk (combDblOps.map toF) DQ = true := by decide

theorem add_ok : opsOk (combAddOps.map toF) AQ = true := by decide

theorem dbl_sub : ∀ q ∈ DQ, q ∈ outsQ (combDblOps.map toF) DQ := by decide

theorem add_sub : ∀ q ∈ DQ, q ∈ outsQ (combAddOps.map toF) AQ := by decide

/-- The point in the slots `RX`, `RY`, `RZ`. -/
def ptOf (v : Nat → Fe) : Point := ⟨v RX, v RY, v RZ⟩

theorem dbl_vals (v : Nat → Fe) :
    ptOf (runOps (combDblOps.map toF) v) = Proof.Ed448.double (ptOf v) ∧
      runOps (combDblOps.map toF) v DK = v DK := by
  refine ⟨?_, ?_⟩
  · simp (disch := decide) only [ptOf, combDblOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_self, upd_of_ne]
    rfl
  · simp (disch := decide) only [combDblOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_of_ne]

theorem add_vals (v : Nat → Fe) (hd : v DK = Spec.Ed448.d) :
    ptOf (runOps (combAddOps.map toF) v) = addAffine (ptOf v) (v SX) (v SY) ∧
      runOps (combAddOps.map toF) v DK = v DK := by
  refine ⟨?_, ?_⟩
  · simp (disch := decide) only [ptOf, combAddOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_self, upd_of_ne]
    rw [hd]; rfl
  · simp (disch := decide) only [combAddOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_of_ne]

/-! ## The calls -/

theorem op_noCalls (op : FOp) : op.code.noCalls = true := by cases op <;> rfl

theorem ops_noCalls : ∀ ops : List FOp, (opsCode ops (.block [] : Prog isa)).noCalls = true
  | [] => rfl
  | op :: ops => by
    show (op.code.noCalls && (opsCode ops (.block [] : Prog isa)).noCalls) = true
    rw [op_noCalls, ops_noCalls ops]; rfl

section
variable {b : Addr}

/-- A function of field operations, called: from the slots `qs` holding `v`,
it returns with the slots `outsQ ops qs` holding `runOps ops v`, having
written only the registers of `work` and the field area. -/
theorem call_ops {name : String} {ops : List FOp} {qs : List Nat} {v : Nat → Fe}
    (hok : opsOk ops qs = true)
    (hlr : (instrs (opsCode ops (.block []) : Prog isa)).all (fun i => !i.writesLr) = true)
    {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) {Q : State → Prop}
    (k : ∀ s', Stp b s s' → SlotsOk s'.mem b (outsQ ops qs) (runOps ops v) → Q s') :
    WP isa (.call name (opsCode ops (.block []))) s Q := by
  have hcE : Ctx b s.callEntry :=
    ⟨by rw [State.callEntry_gpr s (by decide)]; exact hc.r6, by rw [State.callEntry_wr]; exact hc.wr⟩
  have C0 : Cur b s.callEntry (s.callEntry.gpr .r0) (s.callEntry.gpr .r12) qs v s.callEntry :=
    ⟨hcE, Stp.refl _ _, rfl, rfl, by rw [State.callEntry_mem]; exact hS⟩
  obtain ⟨tr, s3, he, h3⟩ := ops_ok (k := .block [])
    (Q := Cur b s.callEntry (s.callEntry.gpr .r0) (s.callEntry.gpr .r12) (outsQ ops qs) (runOps ops v))
    ops qs v _ hok C0 fun s' h => WP.block_nil h
  have hl3 : s3.lr = s.callEntry.lr := Exec.lr he (ops_noCalls ops) hlr
  have hret : isa.ret s.callEntry s3 = some s3 := by
    simp only [isa, ret]
    exact ite_eq_left_of_eq_true _ _ (eq_true hl3)
  refine ⟨_, s3, Exec.call (call_callEntry s) he hret, k s3 ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩ h3.slots⟩
  · rw [h3.stp.rest.gpr r hr, State.callEntry_gpr s (by cases r <;> simp_all [work, linkRegs])]
  · rw [h3.stp.rest.rd, State.callEntry_rd]
  · rw [h3.stp.rest.wr, State.callEntry_wr]
  · rw [h3.stp.rest.sp, State.callEntry_sp]
  · have := h3.stp.frame; rwa [State.callEntry_mem] at this

end

/-! ## The table -/

/-- The table's entries, as numbers. -/
def TabOk (b : Addr) (m : Mem) : Prop :=
  ∀ i < 16, V m b (CTAB + 112 * i) = (Impl.Ed448.Comb.entry i).1.val ∧
    V m b (CTAB + 112 * i + 56) = (Impl.Ed448.Comb.entry i).2.val

/-- The table's region. -/
abbrev TR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 CTAB, 1792⟩

section
variable {b : Addr}

/-- After the first `n` entries. -/
structure TabInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [TR b] s0.mem s.mem
  vals : ∀ i < n, V s.mem b (CTAB + 112 * i) = (Impl.Ed448.Comb.entry i).1.val ∧
    V s.mem b (CTAB + 112 * i + 56) = (Impl.Ed448.Comb.entry i).2.val

theorem entry_step {s0 : State} (hc : Ctx b s0) {i : Nat} (hi : i < 16) {s : State}
    (h : TabInv b s0 i s) :
    WP isa (.block (constField (CTAB + 112 * i) (Impl.Ed448.Comb.entry i).1.val ++
      constField (CTAB + 112 * i + 56) (Impl.Ed448.Comb.entry i).2.val)) s (TabInv b s0 (i + 1)) := by
  have hT : CTAB = 2048 := rfl
  have hc1 : Ctx b s := hc.of_rest h.rest (by decide)
  refine WP.append (constField_ok hc1 (o := CTAB + 112 * i) (by omega) (fe_lt _))
    fun t ⟨rt, ft, vt⟩ => ?_
  refine WP.mono (constField_ok (hc1.of_rest rt (by decide)) (o := CTAB + 112 * i + 56) (by omega)
    (fe_lt _)) fun u ⟨ru, fu, vu⟩ => ⟨h.rest.trans (rt.trans ru), ?_, fun j hj => ?_⟩
  · have F2 : Frame [TR b] s.mem t.mem :=
      ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    have F3 : Frame [TR b] t.mem u.mem :=
      fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    exact h.frame.trans (F2.trans F3)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨e1, e2⟩ := h.vals j hj
      refine ⟨?_, ?_⟩
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e1
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e2
    · exact ⟨by rw [slot_keep fu (by omega) (by omega) (by omega)]; exact vt, vu⟩

theorem tabBuild_ok {s : State} (hc : Ctx b s) :
    WP isa (.block tabBuild) s fun t => Rest [.r7] s t ∧ Frame [TR b] s.mem t.mem ∧ TabOk b t.mem :=
  WP.mono (wp_range_flatMap (M := isa) (TabInv b s) (fun i t hi h => entry_step hc hi h)
    16 (Nat.le_refl _) s ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, ht.vals⟩

end

/-! ## Instruction rules -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_load_d hn ho hin) (k _ (Upd.write _ _ _))

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_store_d hn ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-! ## The index -/

section
variable {b : Addr} {s : State}

theorem bit_val (k t : Nat) : ((k >>> t) &&& 1) = k / 2 ^ t % 2 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- The byte of bit `t` of the scalar, as `lbz` reads it. -/
theorem bit_byte {k t : Nat} (hb : Bits b k s.mem) (ht : t < 456) :
    BitVec.ofNat 64 (s.mem (b + BitVec.ofNat 64 (BITS + t))).toNat = BitVec.ofNat 64 (k / 2 ^ t % 2) := by
  rw [hb t ht, BitVec.toNat_ofNat, bit_val, Nat.mod_eq_of_lt (by omega)]

theorem digit_ok {k t : Nat} (hc : Ctx b s) (hb : Bits b k s.mem) (ht : t < 114)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 t) :
    WP isa (.block combDigit) s fun s' => s'.gpr .r10 = BitVec.ofNat 64 (Proof.Ed448.Comb.digit k t) ∧
      Rest [.r8, .r9, .r10] s s' ∧ s'.mem = s.mem := by
  have hB : BITS = 1064 := rfl
  simp only [combDigit]
  refine wp_add fun s1 u1 => ?_
  have e1 : s1.gpr .r9 = b + BitVec.ofNat 64 t := by rw [u1.gpr, hc.r6, h3]
  have hm1 : s1.mem = s.mem := u1.mem
  have ld : ∀ (s' : State) (o : Nat), o + t < 456 → s'.gpr .r9 = b + BitVec.ofNat 64 t →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .r9 + BitVec.ofNat 64 (BITS + o) = b + BitVec.ofNat 64 (BITS + (o + t)) ∧
        InRegions (s'.rd ++ s'.wr) (b + BitVec.ofNat 64 (BITS + (o + t))) 1 := fun s' o ho ha hr hw =>
    ⟨by rw [ha, Offset.add_add]; congr 2; omega, by rw [hr, hw]; exact hc.inR (by omega)⟩
  obtain ⟨a1, i1⟩ := ld s1 342 (by omega) e1 u1.rd u1.wr
  refine wp_lbz (by decide) (by decide) a1 i1 fun s2 u2 => ?_
  obtain ⟨a2, i2⟩ := ld s2 228 (by omega) (by rw [u2.other _ (by decide), e1]) (by rw [u2.rd, u1.rd])
    (by rw [u2.wr, u1.wr])
  refine wp_lbz (by decide) (by decide) a2 i2 fun s3 u3 => wp_add fun s4 u4 => wp_add fun s5 u5 => ?_
  obtain ⟨a3, i3⟩ := ld s5 114 (by omega)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) (by decide) a3 i3 fun s6 u6 => wp_add fun s7 u7 => wp_add fun s8 u8 => ?_
  obtain ⟨a4, i4⟩ := ld s8 0 (by omega)
    (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) (by decide) (by rw [Nat.add_zero] at a4; exact a4) i4 fun s9 u9 =>
    wp_add fun s10 u10 => wp_add fun s11 u11 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have m2 : s2.mem = s.mem := by rw [u2.mem, hm1]
    have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, m2]
    have m8 : s8.mem = s.mem := by rw [u8.mem, u7.mem, u6.mem, m5]
    have b1 := bit_byte (t := 342 + t) hb (by omega)
    have b2 := bit_byte (t := 228 + t) hb (by omega)
    have b3 := bit_byte (t := 114 + t) hb (by omega)
    have b4 := bit_byte (t := 0 + t) hb (by omega)
    rw [u11.gpr, u10.gpr, u10.other _ (by decide), u9.gpr, u9.other _ (by decide), u8.gpr, u7.gpr,
      u7.other _ (by decide), u6.gpr, u6.other _ (by decide), u5.gpr, u4.gpr, u4.other _ (by decide),
      u3.gpr, u3.other _ (by decide), u2.gpr, m8, m5, m2, hm1, b1, b2, b3, b4]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Proof.Ed448.Comb.digit]
    have := Nat.mod_lt (k / 2 ^ (342 + t)) (show 0 < 2 by decide)
    have := Nat.mod_lt (k / 2 ^ (228 + t)) (show 0 < 2 by decide)
    have := Nat.mod_lt (k / 2 ^ (114 + t)) (show 0 < 2 by decide)
    have := Nat.mod_lt (k / 2 ^ (0 + t)) (show 0 < 2 by decide)
    rw [Nat.zero_add] at *
    rw [Nat.add_comm 342 t, Nat.add_comm 228 t, Nat.add_comm 114 t]
    omega
  · have r : ∀ {x y : State} {r : Reg} {v : BitVec 64}, Upd x y r v → r ∈ [Reg.r8, .r9, .r10] →
        Rest [.r8, .r9, .r10] x y := fun u h => u.rest h
    exact (r u1 (by decide)).trans ((r u2 (by decide)).trans ((r u3 (by decide)).trans
      ((r u4 (by decide)).trans ((r u5 (by decide)).trans ((r u6 (by decide)).trans
      ((r u7 (by decide)).trans ((r u8 (by decide)).trans ((r u9 (by decide)).trans
      ((r u10 (by decide)).trans (r u11 (by decide)))))))))))
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, hm1]

end

/-! ## The selection -/

section
variable {b : Addr}

/-- Doubleword `j` of `(SX, SY)`. -/
abbrev sw (m : Mem) (b : Addr) (j : Nat) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (SX + 8 * j)) 64

/-- Doubleword `j` of entry `i`. -/
abbrev tw (m : Mem) (b : Addr) (i j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (CTAB + 112 * i + 8 * j)) 64

/-- The selection's region. -/
abbrev SR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SX, 112⟩

theorem tw_frame {m m' : Mem} (hf : Frame [SR b] m m') {i j : Nat} (hi : i < 16) (hj : j < 14) :
    tw m' b i j = tw m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by simp only [CTAB, SX]; omega)) (by simp only [CTAB]; omega)
    (by simp only [SX]; omega)

/-- The state of a selection from `s0`. -/
structure SelCtx (b : Addr) (s0 s : State) : Prop where
  ctx : Ctx b s
  r10 : s.gpr .r10 = s0.gpr .r10
  rest : Rest [.r4, .r5, .r11] s0 s
  frame : Frame [SR b] s0.mem s.mem

theorem SelCtx.next {s0 s s' : State} (h : SelCtx b s0 s) (hr : Rest [.r4, .r5, .r11] s s')
    (hf : Frame [SR b] s.mem s'.mem) : SelCtx b s0 s' :=
  ⟨h.ctx.of_rest hr (by decide), by rw [hr.gpr _ (by decide), h.r10], h.rest.trans hr, h.frame.trans hf⟩

theorem selWord_ok {s0 : State} {i j : Nat} (hi : i < 16) (hj : j < 14) {s : State}
    (h : SelCtx b s0 s) :
    WP isa (.block (selWord i j)) s fun s' => SelCtx b s0 s' ∧ s'.gpr .r11 = s.gpr .r11 ∧
      sw s'.mem b j = sw s.mem b j ||| (tw s.mem b i j &&& s.gpr .r11) ∧
      ∀ j' < 14, j' ≠ j → sw s'.mem b j' = sw s.mem b j' := by
  have hc := h.ctx
  have hS : SX = 168 := rfl
  have hT : CTAB = 2048 := rfl
  simp only [selWord]
  refine wp_ld (by decide) ⟨by omega, by omega⟩ (by rw [hc.r6]) (hc.inR (by omega)) fun s1 u1 => ?_
  refine wp_ld (by decide) ⟨by omega, by omega⟩ (by rw [u1.other _ (by decide), hc.r6])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega)) fun s2 u2 => wp_and fun s3 u3 => wp_or fun s4 u4 => ?_
  have hr4 : Rest [.r4, .r5] s s4 :=
    ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))))
  refine wp_std (by decide) ⟨by omega, by omega⟩ (by rw [hr4.gpr _ (by decide), hc.r6])
    (by rw [hr4.wr]; exact hc.inW (by omega)) fun s5 u5 => WP.block_nil ?_
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hf : Frame [SR b] s.mem s5.mem := by
    rw [u5.mem, hm4]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))
  have g4 : s4.gpr .r4 = sw s.mem b j ||| (tw s.mem b i j &&& s.gpr .r11) := by
    rw [u4.gpr, u3.other Reg.r4 (by decide), u3.gpr, u2.other Reg.r4 (by decide), u2.gpr,
      u2.other Reg.r11 (by decide), u1.gpr, u1.other Reg.r11 (by decide), u1.mem]
  refine ⟨h.next ((hr4.mono (by decide)).trans ⟨fun r _ => by rw [u5.gpr], u5.rd, u5.wr, u5.sp⟩) hf,
    by rw [u5.gpr, hr4.gpr _ (by decide)], ?_, fun j' hj' hne => ?_⟩
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_self64, g4]
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

/-- The mask of entry `i`. -/
theorem mask_eq : ∀ d < 16, ∀ i < 16,
    (0 : BitVec 64) - ((BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 d) - BitVec.ofNat 64 1) >>> 63 =
      if d = i then BitVec.allOnes 64 else 0 := by decide

/-- After the first `n` entries: `(SX, SY)` holds the index's entry if it is
below `n`, else zero. -/
structure SelInv (b : Addr) (s0 : State) (d n : Nat) (s : State) : Prop where
  ctx : SelCtx b s0 s
  vals : ∀ j < 14, sw s.mem b j = if d < n then tw s0.mem b d j else 0

theorem entry_ok {s0 : State} {d : Nat} (hd : d < 16) (h10 : s0.gpr .r10 = BitVec.ofNat 64 d)
    {i : Nat} (hi : i < 16) {s : State} (h : SelInv b s0 d i s) :
    WP isa (.block (selEntry i)) s (SelInv b s0 d (i + 1)) := by
  have hc := h.ctx
  simp only [selEntry, List.cons_append, List.nil_append]
  refine wp_li (by omega) fun s1 u1 => wp_xor fun s2 u2 => wp_subi (by decide) (by decide) fun s3 u3 =>
    wp_lsr (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  have hr6 : Rest [.r4, .r5, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have e6 : s6.gpr .r11 = if d = i then BitVec.allOnes 64 else 0 := by
    rw [u6.gpr, u5.gpr, u5.other Reg.r4 (by decide), u4.gpr, u3.gpr, u2.gpr, u1.gpr,
      u1.other Reg.r10 (by decide), hc.r10, h10, ← mask_eq d hd i hi]
    rfl
  have c6 : SelCtx b s0 s6 := hc.next hr6 (by rw [hm6]; exact Frame.refl _ _)
  -- The doublewords, one at a time.
  refine WP.mono (wp_range_flatMap (M := isa) (fun k t => SelCtx b s0 t ∧ t.gpr .r11 = s6.gpr .r11 ∧
      ∀ j < 14, sw t.mem b j = if j < k then sw s6.mem b j ||| (tw s0.mem b i j &&& s6.gpr .r11)
        else sw s6.mem b j)
    (fun k t hk ⟨ct, mt, vt⟩ => WP.mono (selWord_ok hi hk ct) fun u ⟨cu, mu, wu, ou⟩ =>
      ⟨cu, mu.trans mt, fun j hj => ?_⟩) 14 (Nat.le_refl _) s6
      ⟨c6, rfl, fun j hj => by simp⟩) fun t ⟨ct, _, vt⟩ => ⟨ct, fun j hj => ?_⟩
  · by_cases e : j = k
    · subst e
      rw [wu, vt j hj, tw_frame ct.frame hi hk, mt]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · rw [ou j hj e, vt j hj]
      by_cases hjk : j < k
      · simp only [hjk, ite_true, Nat.lt_succ_of_lt hjk]
      · simp only [hjk, ite_false, show ¬ j < k + 1 by omega]
  · rw [vt j hj]
    simp only [hj, ite_true]
    rw [show sw s6.mem b j = sw s.mem b j by rw [sw, sw, hm6], h.vals j hj, e6]
    by_cases e : d = i
    · subst e
      simp only [Nat.lt_irrefl, ite_false, ite_true, Nat.lt_succ_self]
      rw [BitVec.and_allOnes]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_or]
    · simp only [e, ite_false]
      by_cases hdi : d < i
      · simp [hdi, Nat.lt_succ_of_lt hdi]
      · simp [hdi, show ¬ d < i + 1 by omega]

theorem select_ok {d : Nat} (hd : d < 16) {s : State} (hc : Ctx b s)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 d) :
    WP isa (.block combSelect) s fun s' => Ctx b s' ∧ Rest [.r4, .r5, .r11] s s' ∧
      Frame [SR b] s.mem s'.mem ∧ ∀ j < 14, sw s'.mem b j = tw s.mem b d j := by
  have hS : SX = 168 := rfl
  simp only [combSelect, List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r4]) (by decide)) (by decide)
  -- Zero `(SX, SY)`.
  refine WP.append (wp_range_flatMap (M := isa) (fun k t => Ctx b t ∧ Rest [.r4] s t ∧
      t.gpr .r4 = 0 ∧ Frame [SR b] s.mem t.mem ∧ ∀ j < k, sw t.mem b j = 0)
    (fun k t hk ⟨ct, rt, zt, ft, vt⟩ => wp_std (by decide) ⟨by omega, by omega⟩ (by rw [ct.r6])
      (ct.inW (by omega)) fun u uu => by
        have ru : Rest [.r4] t u := ⟨fun r _ => by rw [uu.gpr], uu.rd, uu.wr, uu.sp⟩
        have fu : Frame [SR b] t.mem u.mem := by
          rw [uu.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (Offset.contains _ (by omega) (by omega) (by omega))
        refine WP.block_nil ⟨ct.of_rest ru (by decide), rt.trans ru, by rw [uu.gpr, zt], ft.trans fu,
          fun j hj => ?_⟩
        simp only [sw]; rw [uu.mem]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact vt j hj
        · rw [Mem.readW_writeW_self64, zt])
    14 (Nat.le_refl _) s1 ⟨hc1, u1.rest (by decide), by rw [u1.gpr]; rfl, by rw [u1.mem]; exact Frame.refl _ _,
      fun j hj => by omega⟩) fun t ⟨ct, rt, _, ft, vt⟩ => ?_
  have c0 : SelCtx b t t := ⟨ct, rfl, Rest.refl _ _, Frame.refl _ _⟩
  have tab : ∀ i < 16, ∀ j < 14, tw t.mem b i j = tw s.mem b i j := fun i hi j hj => tw_frame ft hi hj
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv b t d) (fun i u hi h => entry_ok hd
    (by rw [rt.gpr _ (by decide), h10]) hi h) 16 (Nat.le_refl _) t
    ⟨c0, fun j hj => by rw [vt j hj]; simp⟩) fun u ⟨cu, vu⟩ => ⟨cu.ctx, ?_, ?_, fun j hj => ?_⟩
  · exact (rt.mono (by decide)).trans cu.rest
  · exact ft.trans cu.frame
  · rw [vu j hj]
    simp only [hd, ite_true]
    exact tab d hd j hj

end

/-! ## The rows -/

open VG.Proof.Ed448 (Rep baseAff pointAdd_rep double_rep dZ)
open VG.Proof.Ed448.Comb (accScalar digit)

theorem step_rep {p : Point} {k t : Nat} (ht : t < 114)
    (hp : Rep p (accScalar k (t + 1) • baseAff)) :
    Rep (Spec.Ed448.pointAdd (Proof.Ed448.double p)
      (Proof.X448.basePt (Impl.Ed448.Comb.entry (digit k t)))) (accScalar k t • baseAff) := by
  have h := pointAdd_rep (double_rep hp) (Proof.Ed448.Comb.entry_rep _ (Proof.Ed448.Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Proof.Ed448.Comb.accScalar_step k t ht] at h
  exact h

section
variable {b : Addr}

/-- The 32-bit words of 112 bytes equal where their doublewords do. -/
theorem words_eq {m : Mem} {p q : Addr}
    (h : ∀ j < 14, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = m.readW (q + BitVec.ofNat 64 (8 * j)) 64) :
    ∀ k < 28, m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32 := by
  intro k hk
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [show 4 * (2 * j) = 8 * j by omega, Mem.readW_lo32 (h j (by omega)), Mem.readW_lo32 rfl]
  · rw [show 4 * (2 * j + 1) = 8 * j + 4 by omega, ← Offset.add_add, ← Offset.add_add,
      Mem.readW_hi32 (h j (by omega)), Mem.readW_hi32 rfl]

/-- The element at `SX` (`SY`) is entry `d`'s `x` (`y`) after the selection. -/
theorem sel_x {m : Mem} {d : Nat} (hd : d < 16) (htab : TabOk b m)
    (hs : ∀ j < 14, sw m b j = tw m b d j) :
    FS m b SX = (Impl.Ed448.Comb.entry d).1 ∧ FS m b SY = (Impl.Ed448.Comb.entry d).2 := by
  have hw := words_eq (m := m) (p := b + BitVec.ofNat 64 SX) (q := b + BitVec.ofNat 64 (CTAB + 112 * d))
    fun j hj => by rw [Offset.add_add, Offset.add_add]; exact hs j hj
  have hl : ∀ c, c ≤ 14 → ∀ k < 14, limb m b (SX + 4 * c) k = limb m b (CTAB + 112 * d + 4 * c) k :=
    fun c hc k hk => by
      have := hw (c + k) (by omega)
      rw [Offset.add_add, Offset.add_add] at this
      simp only [limb, wd]
      rw [show SX + 4 * c + 4 * k = SX + 4 * (c + k) by omega,
        show CTAB + 112 * d + 4 * c + 4 * k = CTAB + 112 * d + 4 * (c + k) by omega, this]
  have h0 : ∀ k < 14, limb m b SX k = limb m b (CTAB + 112 * d) k := by
    have := hl 0 (by omega); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this
  have h1 : ∀ k < 14, limb m b SY k = limb m b (CTAB + 112 * d + 56) k := by
    have := hl 14 (by omega); exact this
  obtain ⟨tx, ty⟩ := htab d hd
  exact ⟨by rw [FS, V, val32_congr h0, ← V, tx, Proof.X448.toFe_self],
    by rw [FS, V, val32_congr h1, ← V, ty, Proof.X448.toFe_self]⟩

end

theorem dbl_lr : (instrs (opsCode (combDblOps.map toF) (.block []) : Prog isa)).all
    (fun i => !i.writesLr) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem add_lr : (instrs (opsCode (combAddOps.map toF) (.block []) : Prog isa)).all
    (fun i => !i.writesLr) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

/-! ## The loop -/

/-- The registers the loop writes: X448's and the counter `r3`. -/
abbrev cw : List Reg := [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

section
variable {b : Addr}

/-- `s'` is `s` but for the registers `cw` and the field area. -/
structure CStp (b : Addr) (s s' : State) : Prop where
  rest : Rest cw s s'
  frame : Frame [FA b] s.mem s'.mem

theorem CStp.trans {s₁ s₂ s₃ : State} (h₁ : CStp b s₁ s₂) (h₂ : CStp b s₂ s₃) : CStp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem CStp.of_stp {s s' : State} (h : Stp b s s') : CStp b s s' := ⟨h.rest.mono (by decide), h.frame⟩

/-- The state before the row that leaves `n` rows. -/
structure LInv (b : Addr) (k : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  ctx : Ctx b s
  stp : CStp b s0 s
  r3 : s.gpr .r3 = BitVec.ofNat 64 n
  d : FS s.mem b DK = Spec.Ed448.d
  rep : Rep (ptOf (FS s.mem b)) (accScalar k n • baseAff)

/-- What the loop keeps of `s0`: the table and the bits, outside the field area. -/
structure Fixed (b : Addr) (k : Nat) (s0 : State) : Prop where
  tab : TabOk b s0.mem
  bits : Bits b k s0.mem

theorem fixed_tab {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hst : CStp b s0 s) : TabOk b s.mem := by
  intro i hi
  obtain ⟨e1, e2⟩ := hf.tab i hi
  have keep : ∀ o, ACC + 112 ≤ o → o + 56 ≤ 4096 → V s.mem b o = V s0.mem b o := fun o ho ho' => by
    unfold V
    refine val32_congr (limb_frame hst.frame fun r hr k hk => ?_)
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by omega) (by omega)
  have hA : ACC = 952 := rfl
  have hT : CTAB = 2048 := rfl
  exact ⟨by rw [keep _ (by omega) (by omega), e1], by rw [keep _ (by omega) (by omega), e2]⟩

theorem fixed_bits {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hst : CStp b s0 s) : Bits b k s.mem :=
  fun t ht => by
    have hA : ACC = 952 := rfl
    have hB : BITS = 1064 := rfl
    rw [byte_above hst.frame (by omega) (by omega)]
    exact hf.bits t ht

theorem step_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) {t : Nat} (ht : t < 114) {s : State}
    (h : LInv b k s0 (t + 1) s) :
    WP isa combStep s fun s' => LInv b k s0 t s' ∧ (s'.gpr .r3 != 0) = decide (t ≠ 0) := by
  have hc := h.ctx
  unfold combStep callDbl callAdd
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have e1 : s1.gpr .r3 = BitVec.ofNat 64 t := by
    rw [u1.gpr, h.r3, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
  have hst1 : CStp b s0 s1 :=
    h.stp.trans ⟨u1.rest (by decide), by rw [u1.mem]; exact Frame.refl _ _⟩
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  rw [opsProg_eq, opsProg_eq]
  refine WP.seq (call_ops (v := FS s1.mem b) dbl_ok dbl_lr hc1 (fun _ _ => rfl) fun s2 st2 sl2 => ?_)
  have hst2 : CStp b s0 s2 := hst1.trans (CStp.of_stp st2)
  have hc2 : Ctx b s2 := hc1.of_rest st2.rest (by decide)
  have e2 : s2.gpr .r3 = BitVec.ofNat 64 t := by rw [st2.rest.gpr _ (by decide), e1]
  -- The row's index and its entry.
  have bs2 := fixed_bits hfx hst2
  refine WP.seq (WP.append (digit_ok hc2 bs2 ht e2) fun s3 ⟨a3, r3, m3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  refine WP.mono (select_ok (Proof.Ed448.Comb.digit_lt k t) hc3 a3) fun s4 ⟨hc4, r4, f4, v4⟩ => ?_
  have hr34 : Rest cw s2 s4 := (r3.mono (by decide)).trans (r4.mono (by decide))
  have hst4 : CStp b s0 s4 := hst2.trans ⟨hr34, by
    rw [← m3]; exact f4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by simp only [SX, ACC]; omega)⟩⟩
  have tab4 : TabOk b s4.mem := fixed_tab hfx hst4
  have sxy := sel_x (Proof.Ed448.Comb.digit_lt k t) tab4 (fun j hj => by
    rw [v4 j hj, tw_frame f4 (Proof.Ed448.Comb.digit_lt k t) hj, m3])
  -- The slots of `R` and `d` stay through the selection.
  have keep : ∀ q ∈ DQ, FS s4.mem b q = FS s2.mem b q := fun q hq => by
    unfold FS V
    congr 1
    refine val32_congr (limb_frame (by rw [← m3]; exact f4) fun r hr k hk => ?_)
    rw [List.mem_singleton.mp hr]
    have hX : RX = 56 := rfl
    have hY : RY = 0 := rfl
    have hZ : RZ = 112 := rfl
    have hD : DK = 336 := rfl
    have hS : SX = 168 := rfl
    simp only [DQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have d4 : FS s4.mem b DK = Spec.Ed448.d := by
    rw [keep DK (by decide), sl2 DK (dbl_sub DK (by decide)), (dbl_vals _).2, u1.mem]
    exact h.d
  refine call_ops (v := FS s4.mem b) add_ok add_lr hc4 (fun _ _ => rfl) fun s5 st5 sl5 => ?_
  have p5 : ptOf (FS s5.mem b) = ptOf (runOps (combAddOps.map toF) (FS s4.mem b)) := by
    simp only [ptOf]
    rw [sl5 RX (by decide), sl5 RY (by decide), sl5 RZ (by decide)]
  have p4 : ptOf (FS s4.mem b) = Proof.Ed448.double (ptOf (FS s.mem b)) := by
    have e : ptOf (FS s4.mem b) = ptOf (runOps (combDblOps.map toF) (FS s1.mem b)) := by
      simp only [ptOf]
      rw [keep RX (by decide), keep RY (by decide), keep RZ (by decide),
        sl2 RX (dbl_sub RX (by decide)), sl2 RY (dbl_sub RY (by decide)),
        sl2 RZ (dbl_sub RZ (by decide))]
    rw [e, (dbl_vals _).1, u1.mem]
  have e5 : s5.gpr .r3 = BitVec.ofNat 64 t := by
    rw [st5.rest.gpr _ (by decide), r4.gpr _ (by decide), r3.gpr _ (by decide), e2]
  refine ⟨⟨hc4.of_rest st5.rest (by decide), hst4.trans (CStp.of_stp st5), e5, ?_, ?_⟩,
    by rw [e5, ofNat_ne_zero (by omega)]⟩
  · rw [sl5 DK (add_sub DK (by decide)), (add_vals _ d4).2, d4]
  · rw [p5, (add_vals _ d4).1, p4, sxy.1, sxy.2, addAffine_eq]
    exact step_rep ht h.rep

theorem loop_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 114 → LInv b k s0 n s →
      WP isa (.loop combStep (.nonzero .d .r3)) s (LInv b k s0 0) := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := LInv b k s0 0)
    (fun m s => 1 ≤ m ∧ m ≤ 114 ∧ LInv b k s0 m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hl⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (step_ok hfx (by omega) hl) fun s' ⟨hl', hz⟩ => ?_
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    exact .inl ⟨by rw [eval_nonzero, hz]; simp, hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [show t ≠ 0 by omega], t, by omega, by omega, by omega, hl'⟩

end

end VG.Proof.Ed448.PPC64LE.Comb
