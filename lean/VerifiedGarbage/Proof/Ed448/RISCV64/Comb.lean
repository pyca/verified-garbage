module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
public import VerifiedGarbage.Proof.Ed448.Comb
public import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.Field

/-!
# Ed448 on RISC-V: the four-column comb

The base-point multiplication of `Impl/Ed448/RISCV64/ScalarBase.lean`
(`combLoop`), proven as x86-64's comb is:

* The point operations (`dblOps`, `addOps`) are field programs of `R64`
  (`opsProg_eq`), whose elements afterwards are those of `Proof.Ed448.double`
  (`dbl_vals`) and of RFC 8032's addition with `Z₂ = 1` (`add_vals`,
  `addAffine_eq`).
* `tabBuild` moves `a3` to `b + CTAB`, stores the sixteen entries of
  `Impl/Ed448/Comb.lean` there with `constField` (`tabBuild_ok`), entry
  `i`'s `x` at `112 i` and its `y` at `112 i + 56` (`TabOk`), and moves `a3`
  back. The 2048 bytes at `b + CTAB` are writable (`TabW`).
* `combDigit` reads the row's four bits of the scalar from `BITS` into the
  index `a5` (`digit_ok`, `Proof.Ed448.Comb.digit`). `combSelect` zeroes
  `(SX, SY)`, then ORs in each entry's fourteen doublewords under the mask
  `-(a5 = i)` (`entry_ok`), so that `(SX, SY)` holds the index's entry
  (`select_ok`, `sel_x`), every entry read whatever the index.
* One row (`step_ok`): with `R` representing `[accScalar k (t + 1)] B`
  before, it represents `[accScalar k t] B` after (`step_rep`, from
  `Proof/Ed448/Comb.lean`). The loop (`loop_ok`) runs the 114 rows; the
  memory it writes is the field area, so the table and the scalar's bits stay
  (`Fixed`).
-/

-- separate module: its proofs take about 8 s, which `BaseMain.lean`'s edits need not re-check

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Comb

/-! ## The point operations -/



open VG VG.RISCV64 VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point)

/-- An operation of the implementation as one of `R64`'s. -/
def toF : COp → FOp
  | .mul o x y => .mul o x y
  | .add o x y => .add o x y
  | .sub o x y => .sub o x y

theorem opsProg_eq : ∀ ops : List COp, opsProg ops = R64.opsCode (ops.map toF) (.block [])
  | [] => rfl
  | op :: ops => by
    rw [opsProg, List.map_cons, R64.opsCode, opsProg_eq ops]
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

theorem dbl_ok : R64.opsOk (dblOps.map toF) DQ = true := by decide

theorem add_ok : R64.opsOk (addOps.map toF) AQ = true := by decide

theorem dbl_sub : ∀ q ∈ DQ, q ∈ outsQ (dblOps.map toF) DQ := by decide

theorem add_sub : ∀ q ∈ DQ, q ∈ outsQ (addOps.map toF) AQ := by decide

/-- The point in the slots `RX`, `RY`, `RZ`. -/
def ptOf (v : Nat → Fe) : Point := ⟨v RX, v RY, v RZ⟩

theorem dbl_vals (v : Nat → Fe) :
    ptOf (runOps (dblOps.map toF) v) = Proof.Ed448.double (ptOf v) ∧
      runOps (dblOps.map toF) v DK = v DK := by
  refine ⟨?_, ?_⟩
  · simp (disch := decide) only [ptOf, dblOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_self, upd_of_ne]
    rfl
  · simp (disch := decide) only [dblOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_of_ne]

theorem add_vals (v : Nat → Fe) (hd : v DK = Spec.Ed448.d) :
    ptOf (runOps (addOps.map toF) v) = addAffine (ptOf v) (v SX) (v SY) ∧
      runOps (addOps.map toF) v DK = v DK := by
  refine ⟨?_, ?_⟩
  · simp (disch := decide) only [ptOf, addOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_self, upd_of_ne]
    rw [hd]; rfl
  · simp (disch := decide) only [addOps, toF, List.map_cons, List.map_nil, runOps, FOp.out,
      FOp.val, upd_of_ne]


/-! ## The table -/



open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Spec.X448 (Fe)

/-- The table's base. -/
abbrev tb (b : Addr) : Addr := b + BitVec.ofNat 64 CTAB

/-- The 2048 bytes at `b + CTAB` are writable. -/
def TabW (b : Addr) (s : State) : Prop :=
  ∀ d n, d + n ≤ 2048 → InRegions s.wr (tb b + BitVec.ofNat 64 d) n

/-- The table's entries, as numbers. -/
def TabOk (b : Addr) (m : Mem) : Prop :=
  ∀ i < 16, V m (tb b) (112 * i) = (Impl.Ed448.Comb.entry i).1.val ∧
    V m (tb b) (112 * i + 56) = (Impl.Ed448.Comb.entry i).2.val

theorem tb_al {b : Addr} (h : b.toNat % 8 = 0) : (tb b).toNat % 8 = 0 :=
  Proof.X448.RISCV64.R64.al8 h (by decide)

section
variable {b : Addr}

/-- After the first `n` entries. -/
structure TabInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨tb b, 112 * n⟩] s0.mem s.mem
  vals : ∀ i < n, V s.mem (tb b) (112 * i) = (Impl.Ed448.Comb.entry i).1.val ∧
    V s.mem (tb b) (112 * i + 56) = (Impl.Ed448.Comb.entry i).2.val

theorem entry_step {s0 : State} (hc : Ctx (tb b) s0) {i : Nat} (hi : i < 16) {s : State}
    (h : TabInv b s0 i s) :
    WP isa (.block (constField (112 * i) (Impl.Ed448.Comb.entry i).1.val ++
      constField (112 * i + 56) (Impl.Ed448.Comb.entry i).2.val)) s (TabInv b s0 (i + 1)) := by
  have hc1 : Ctx (tb b) s := hc.of_rest h.rest (by decide)
  refine WP.append (constField_ok hc1 (o := 112 * i) (by omega) (by omega) (fe_lt _))
    fun t ⟨rt, ft, vt⟩ => ?_
  refine WP.mono (constField_ok (hc1.of_rest rt (by decide)) (o := 112 * i + 56) (by omega) (by omega)
    (fe_lt _)) fun u ⟨ru, fu, vu⟩ => ⟨h.rest.trans (rt.trans ru), ?_, fun j hj => ?_⟩
  · have F1 : Frame [⟨tb b, 112 * (i + 1)⟩] s0.mem s.mem :=
      h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩
    have F2 : Frame [⟨tb b, 112 * (i + 1)⟩] s.mem t.mem :=
      ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)⟩
    have F3 : Frame [⟨tb b, 112 * (i + 1)⟩] t.mem u.mem :=
      fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)⟩
    exact F1.trans (F2.trans F3)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨e1, e2⟩ := h.vals j hj
      refine ⟨?_, ?_⟩
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e1
      · rw [slot_keep fu (by omega) (by omega) (by omega), slot_keep ft (by omega) (by omega) (by omega)]
        exact e2
    · exact ⟨by rw [slot_keep fu (by omega) (by omega) (by omega)]; exact vt, vu⟩

theorem tabBuild_ok {s : State} (hc : Ctx b s) (hw : TabW b s) :
    WP isa (.block tabBuild) s fun t => Ctx b t ∧ Rest [.a3, .a4] s t ∧
      Frame [⟨tb b, 1792⟩] s.mem t.mem ∧ TabOk b t.mem := by
  simp only [tabBuild, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s1 u1 => wp_addi (by decide) fun s2 u2 => ?_
  have e2 : s2.gpr .a3 = tb b := by
    rw [u2.gpr, u1.gpr, hc.a3, BitVec.add_assoc]; rfl
  have hr2 : Rest [.a3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx (tb b) s2 := ⟨e2, tb_al hc.al, by rw [hr2.wr]; exact hw⟩
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (wp_range_flatMap (M := isa) (TabInv b s2) (fun i t hi h => entry_step hc2 hi h)
    16 (Nat.le_refl _) s2 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩) fun t ht => ?_
  refine wp_subi (by decide) fun u uu => WP.block_nil ⟨⟨?_, hc.al, ?_⟩, ?_, ?_, ?_⟩
  · rw [uu.gpr, ht.rest.gpr _ (by decide), e2, tb]; exact BitVec.add_sub_cancel _ _
  · rw [uu.wr, ht.rest.wr, hr2.wr]; exact hc.wr
  · exact (hr2.mono (ws' := [.a3, .a4]) (by decide)).trans ((ht.rest.mono (by decide)).trans
      (uu.rest (by decide)))
  · rw [uu.mem, ← hm2]; exact ht.frame
  · rw [uu.mem]; exact ht.vals

end


/-! ## The selection -/



open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (BITS)
open VG.Proof.X448.RISCV64.R64 (al8)

section
variable {b : Addr} {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_xori' {d n : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_logicImm (by unfold imm12; omega)) ?_
  simp only
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

/-! ## The index -/

theorem bit_val (k t : Nat) : ((k >>> t) &&& 1) = k / 2 ^ t % 2 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- The byte of bit `t` of the scalar, as `lbu` reads it. -/
theorem bit_byte {k t : Nat} (hb : Bits b k s.mem) (ht : t < 456) :
    BitVec.ofNat 64 (s.mem (b + BitVec.ofNat 64 (BITS + t))).toNat = BitVec.ofNat 64 (k / 2 ^ t % 2) := by
  rw [hb t ht, BitVec.toNat_ofNat, bit_val, Nat.mod_eq_of_lt (by omega)]

theorem digit_ok {k t : Nat} (hc : Ctx b s) (hb : Bits b k s.mem) (ht : t < 114)
    (h1 : s.gpr .t1 = BitVec.ofNat 64 t) :
    WP isa (.block combDigit) s fun s' => s'.gpr .a5 = BitVec.ofNat 64 (Proof.Ed448.Comb.digit k t) ∧
      Rest [.a1, .a4, .a5] s s' ∧ s'.mem = s.mem := by
  have hB : BITS = 1064 := rfl
  simp only [combDigit]
  refine wp_add fun s1 u1 => ?_
  have e1 : s1.gpr .a1 = b + BitVec.ofNat 64 t := by rw [u1.gpr, hc.a3, h1]
  have hm1 : s1.mem = s.mem := u1.mem
  have ld : ∀ (s' : State) (o : Nat), o + t < 456 → s'.gpr .a1 = b + BitVec.ofNat 64 t →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .a1 + BitVec.ofNat 64 (BITS + o) = b + BitVec.ofNat 64 (BITS + (o + t)) ∧
        InRegions (s'.rd ++ s'.wr) (b + BitVec.ofNat 64 (BITS + (o + t))) 1 := fun s' o ho ha hr hw =>
    ⟨by rw [ha, Offset.add_add]; congr 2; omega, by rw [hr, hw]; exact hc.inR (by omega)⟩
  obtain ⟨a1, i1⟩ := ld s1 342 (by omega) e1 u1.rd u1.wr
  refine wp_lbz (by decide) a1 i1 fun s2 u2 => ?_
  obtain ⟨a2, i2⟩ := ld s2 228 (by omega) (by rw [u2.other _ (by decide), e1]) (by rw [u2.rd, u1.rd])
    (by rw [u2.wr, u1.wr])
  refine wp_lbz (by decide) a2 i2 fun s3 u3 => wp_add fun s4 u4 => wp_add fun s5 u5 => ?_
  obtain ⟨a3, i3⟩ := ld s5 114 (by omega)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) a3 i3 fun s6 u6 => wp_add fun s7 u7 => wp_add fun s8 u8 => ?_
  obtain ⟨a4, i4⟩ := ld s8 0 (by omega)
    (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) (by rw [Nat.add_zero] at a4; exact a4) i4 fun s9 u9 => wp_add fun s10 u10 => wp_add fun s11 u11 =>
    WP.block_nil ⟨?_, ?_, ?_⟩
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
  · have r : ∀ {x y : State} {r : Reg} {v : BitVec 64}, Upd x y r v → r ∈ [Reg.a1, .a4, .a5] →
        Rest [.a1, .a4, .a5] x y := fun u h => u.rest h
    exact (r u1 (by decide)).trans ((r u2 (by decide)).trans ((r u3 (by decide)).trans
      ((r u4 (by decide)).trans ((r u5 (by decide)).trans ((r u6 (by decide)).trans
      ((r u7 (by decide)).trans ((r u8 (by decide)).trans ((r u9 (by decide)).trans
      ((r u10 (by decide)).trans (r u11 (by decide)))))))))))
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, hm1]

/-! ## The selection -/

/-- Doubleword `j` of `(SX, SY)`. -/
abbrev sw (m : Mem) (b : Addr) (j : Nat) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (SX + 8 * j)) 64

/-- Doubleword `j` of entry `i`. -/
abbrev tw (m : Mem) (b : Addr) (i j : Nat) : BitVec 64 :=
  m.readW (tb b + BitVec.ofNat 64 (112 * i + 8 * j)) 64

/-- The selection's region. -/
abbrev SR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SX, 112⟩

theorem tw_frame {m m' : Mem} (hf : Frame [SR b] m m') {i j : Nat} (hi : i < 16) (hj : j < 14) :
    tw m' b i j = tw m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr, tb, Offset.add_add]
  exact Offset.disjoint _ (.inr (by simp only [CTAB, SX]; omega)) (by simp only [CTAB]; omega)
    (by simp only [SX]; omega)

/-- `TabW` gives the entries' doublewords to load. -/
theorem tab_in {s : State} (hw : TabW b s) {i j : Nat} (hi : i < 16) (hj : j < 14) :
    InRegions (s.rd ++ s.wr) (tb b + BitVec.ofNat 64 (112 * i + 8 * j)) 8 :=
  let ⟨r, hr, hc⟩ := hw (112 * i + 8 * j) 8 (by omega)
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- The state of a selection from `s0`. -/
structure SelCtx (b : Addr) (s0 s : State) : Prop where
  ctx : Ctx b s
  tab : TabW b s
  t2 : s.gpr .t2 = tb b
  a5 : s.gpr .a5 = s0.gpr .a5
  rest : Rest [.a2, .a4, .a6, .t0, .t2] s0 s
  frame : Frame [SR b] s0.mem s.mem

theorem SelCtx.next {s0 s s' : State} (h : SelCtx b s0 s) (hr : Rest [.a2, .a4, .a6, .t0] s s')
    (hf : Frame [SR b] s.mem s'.mem) : SelCtx b s0 s' :=
  ⟨h.ctx.of_rest hr (by decide), fun d n hdn => by rw [hr.wr]; exact h.tab d n hdn,
    by rw [hr.gpr _ (by decide), h.t2], by rw [hr.gpr _ (by decide), h.a5],
    h.rest.trans (hr.mono (by decide)), h.frame.trans hf⟩

theorem selWord_ok {s0 : State} {i j : Nat} (hi : i < 16) (hj : j < 14) {s : State}
    (h : SelCtx b s0 s) :
    WP isa (.block (selWord i j)) s fun s' => SelCtx b s0 s' ∧ s'.gpr .t0 = s.gpr .t0 ∧
      sw s'.mem b j = sw s.mem b j ||| (tw s.mem b i j &&& s.gpr .t0) ∧
      ∀ j' < 14, j' ≠ j → sw s'.mem b j' = sw s.mem b j' := by
  have hc := h.ctx
  simp only [selWord]
  refine wp_ld (by simp only [SX]; omega) (by rw [hc.a3]) (al8 hc.al (by simp only [SX]; omega))
    (hc.inR (by simp only [SX]; omega)) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (by decide), h.t2]) (al8 (tb_al hc.al) (by omega))
    (by rw [u1.rd, u1.wr]; exact tab_in h.tab hi hj) fun s2 u2 => wp_and fun s3 u3 => wp_or fun s4 u4 => ?_
  have hr4 : Rest [.a2, .a4] s s4 :=
    ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))))
  refine wp_sd (by simp only [SX]; omega) (by rw [hr4.gpr _ (by decide), hc.a3])
    (al8 hc.al (by simp only [SX]; omega)) (by rw [hr4.wr]; exact hc.inW (by simp only [SX]; omega))
    fun s5 u5 => WP.block_nil ?_
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hf : Frame [SR b] s.mem s5.mem := by
    rw [u5.mem, hm4]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SX]; omega) (by simp only [SX]; omega) (by simp only [SX]; omega))
  have g4 : s4.gpr .a2 = sw s.mem b j ||| (tw s.mem b i j &&& s.gpr .t0) := by
    rw [u4.gpr, u3.other Reg.a2 (by decide), u3.gpr, u2.other Reg.a2 (by decide), u2.gpr,
      u2.other Reg.t0 (by decide), u1.gpr, u1.other Reg.t0 (by decide), u1.mem]
  refine ⟨h.next ((hr4.mono (by decide)).trans ⟨fun r _ => by rw [u5.gpr], u5.rd, u5.wr, u5.sp⟩) hf,
    by rw [u5.gpr, hr4.gpr _ (by decide)], ?_, fun j' hj' hne => ?_⟩
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_self64, g4]
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by simp only [SX]; omega)
      (by simp only [SX]; omega)) (by decide)]

/-- The mask of entry `i`. -/
theorem mask_eq : ∀ d < 16, ∀ i < 16,
    (0 : BitVec 64) - (if BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 i < 1 then 1 else 0) =
      if d = i then BitVec.allOnes 64 else 0 := by decide

/-- After the first `n` entries: `(SX, SY)` holds the index's entry if it is
below `n`, else zero. -/
structure SelInv (b : Addr) (s0 : State) (d n : Nat) (s : State) : Prop where
  ctx : SelCtx b s0 s
  vals : ∀ j < 14, sw s.mem b j = if d < n then tw s0.mem b d j else 0

theorem entry_ok {s0 : State} {d : Nat} (hd : d < 16) (h5 : s0.gpr .a5 = BitVec.ofNat 64 d)
    {i : Nat} (hi : i < 16) {s : State} (h : SelInv b s0 d i s) :
    WP isa (.block (selEntry i)) s (SelInv b s0 d (i + 1)) := by
  have hc := h.ctx
  simp only [selEntry, List.cons_append, List.nil_append]
  refine wp_xori' (by omega) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_sltu fun s3 u3 =>
    wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  have hr5 : Rest [.a2, .a4, .a6, .t0] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have e5 : s5.gpr .t0 = if d = i then BitVec.allOnes 64 else 0 := by
    rw [u5.gpr, u4.other Reg.a2 (by decide), u4.gpr, u3.gpr, u2.gpr, u2.other Reg.a2 (by decide), u1.gpr,
      hc.a5, h5, ← mask_eq d hd i hi]
    rfl
  have c5 : SelCtx b s0 s5 := hc.next hr5 (by rw [hm5]; exact Frame.refl _ _)
  -- The doublewords, one at a time.
  refine WP.mono (wp_range_flatMap (M := isa) (fun k t => SelCtx b s0 t ∧ t.gpr .t0 = s5.gpr .t0 ∧
      ∀ j < 14, sw t.mem b j = if j < k then sw s5.mem b j ||| (tw s0.mem b i j &&& s5.gpr .t0)
        else sw s5.mem b j)
    (fun k t hk ⟨ct, mt, vt⟩ => WP.mono (selWord_ok hi hk ct) fun u ⟨cu, mu, wu, ou⟩ =>
      ⟨cu, mu.trans mt, fun j hj => ?_⟩) 14 (Nat.le_refl _) s5
      ⟨c5, rfl, fun j hj => by simp⟩) fun t ⟨ct, _, vt⟩ => ⟨ct, fun j hj => ?_⟩
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
    rw [show sw s5.mem b j = sw s.mem b j by rw [sw, sw, hm5], h.vals j hj, e5]
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

theorem select_ok {d : Nat} (hd : d < 16) {s : State} (hc : Ctx b s) (hw : TabW b s)
    (h5 : s.gpr .a5 = BitVec.ofNat 64 d) :
    WP isa (.block combSelect) s fun s' => Ctx b s' ∧ Rest [.a2, .a4, .a6, .t0, .t2] s s' ∧
      Frame [SR b] s.mem s'.mem ∧ ∀ j < 14, sw s'.mem b j = tw s.mem b d j := by
  simp only [combSelect, List.cons_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a2]) (by decide)) (by decide)
  -- Zero `(SX, SY)`.
  refine WP.append (wp_range_flatMap (M := isa) (fun k t => Ctx b t ∧ Rest [.a2] s t ∧
      t.gpr .a2 = 0 ∧ Frame [SR b] s.mem t.mem ∧ ∀ j < k, sw t.mem b j = 0)
    (fun k t hk ⟨ct, rt, zt, ft, vt⟩ => wp_sd (by simp only [SX]; omega) (by rw [ct.a3])
      (al8 ct.al (by simp only [SX]; omega)) (ct.inW (by simp only [SX]; omega)) fun u uu => by
        have ru : Rest [.a2] t u := ⟨fun r _ => by rw [uu.gpr], uu.rd, uu.wr, uu.sp⟩
        have fu : Frame [SR b] t.mem u.mem := by
          rw [uu.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (Offset.contains _ (by simp only [SX]; omega) (by simp only [SX]; omega)
              (by simp only [SX]; omega))
        refine WP.block_nil ⟨ct.of_rest ru (by decide), rt.trans ru, by rw [uu.gpr, zt], ft.trans fu,
          fun j hj => ?_⟩
        simp only [sw]; rw [uu.mem]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by simp only [SX]; omega)
            (by simp only [SX]; omega)) (by decide)]
          exact vt j hj
        · rw [Mem.readW_writeW_self64, zt])
    14 (Nat.le_refl _) s1 ⟨hc1, u1.rest (by decide), by rw [u1.gpr]; rfl, by rw [u1.mem]; exact Frame.refl _ _,
      fun j hj => by omega⟩) fun t ⟨ct, rt, _, ft, vt⟩ => ?_
  -- The table's pointer.
  refine wp_addi (by decide) fun t1 v1 => wp_addi (by decide) fun t2 v2 => ?_
  have e2 : t2.gpr .t2 = tb b := by
    rw [v2.gpr, v1.gpr, ct.a3, BitVec.add_assoc]; rfl
  have hr2 : Rest [.a2, .t2] s t2 :=
    (rt.mono (by decide)).trans ((v1.rest (by decide)).trans (v2.rest (by decide)))
  have c2 : SelCtx b t2 t2 :=
    ⟨ct.of_rest ((v1.rest (ws := [.t2]) (by decide)).trans (v2.rest (by decide))) (by decide),
      fun d n hdn => by rw [hr2.wr]; exact hw d n hdn, e2, rfl, Rest.refl _ _, Frame.refl _ _⟩
  have hm2 : t2.mem = t.mem := by rw [v2.mem, v1.mem]
  have tab2 : ∀ i < 16, ∀ j < 14, tw t2.mem b i j = tw s.mem b i j := fun i hi j hj => by
    rw [hm2]; exact tw_frame ft hi hj
  rw [List.nil_append]
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv b t2 d) (fun i u hi h => entry_ok hd
    (by rw [hr2.gpr _ (by decide), h5]) hi h) 16 (Nat.le_refl _) t2
    ⟨c2, fun j hj => by rw [hm2, vt j hj]; simp⟩) fun u ⟨cu, vu⟩ => ⟨cu.ctx, ?_, ?_, fun j hj => ?_⟩
  · exact (hr2.mono (by decide)).trans cu.rest
  · rw [← hm2] at ft; exact ft.trans cu.frame
  · rw [vu j hj]
    simp only [hd, ite_true]
    exact tab2 d hd j hj

end


/-! ## The rows -/



open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Proof.Ed448 (Rep baseAff pointAdd_rep double_rep dZ)
open VG.Proof.Ed448.Comb (accScalar digit)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point)
open VG.Impl.X448.RISCV64 (ACC)

theorem step_rep {p : Point} {k t : Nat} (ht : t < 114)
    (hp : Rep p (accScalar k (t + 1) • baseAff)) :
    Rep (Spec.Ed448.pointAdd (Proof.Ed448.double p)
      (Proof.X448.basePt (Impl.Ed448.Comb.entry (digit k t)))) (accScalar k t • baseAff) := by
  have h := pointAdd_rep (double_rep hp) (Proof.Ed448.Comb.entry_rep _ (Proof.Ed448.Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Proof.Ed448.Comb.accScalar_step k t ht] at h
  exact h

section
variable {b : Addr}

/-- The element at `SX` (`SY`) is entry `d`'s `x` (`y`) after the selection. -/
theorem sel_x {m : Mem} {d : Nat} (hd : d < 16) (htab : TabOk b m)
    (hs : ∀ j < 14, sw m b j = tw m b d j) :
    FS m b SX = (Impl.Ed448.Comb.entry d).1 ∧ FS m b SY = (Impl.Ed448.Comb.entry d).2 := by
  have h7 : ∀ o e, (∀ i < 7, R64.ew m b o i = R64.ew m (tb b) e i) → V m b o = V m (tb b) e := fun o e h => by
    rw [R64.V_eq, R64.V_eq]; exact R64.val7_congr h
  obtain ⟨tx, ty⟩ := htab d hd
  refine ⟨?_, ?_⟩
  · rw [FS, h7 SX (112 * d) fun i hi => ?_, tx, Proof.X448.toFe_self]
    have := congrArg BitVec.toNat (hs i (by omega))
    simpa [R64.ew, R64.dw, sw, tw] using this
  · rw [FS, h7 SY (112 * d + 56) fun i hi => ?_, ty, Proof.X448.toFe_self]
    have := congrArg BitVec.toNat (hs (i + 7) (by omega))
    simp only [R64.ew, R64.dw, sw, tw] at this ⊢
    rw [show SY + 8 * i = SX + 8 * (i + 7) by simp only [SX, SY]; omega,
      show 112 * d + 56 + 8 * i = 112 * d + 8 * (i + 7) by omega]
    exact this

/-- The state before the row that leaves `n` rows. -/
structure LInv (b : Addr) (k : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  ctx : Ctx b s
  stp : R64.Stp b s0 s
  t1 : s.gpr .t1 = BitVec.ofNat 64 n
  d : FS s.mem b DK = Spec.Ed448.d
  rep : Rep (ptOf (FS s.mem b)) (accScalar k n • baseAff)

/-- What the loop keeps of `s0`: the table and the bits, outside the field area. -/
structure Fixed (b : Addr) (k : Nat) (s0 : State) : Prop where
  tabw : TabW b s0
  tab : TabOk b s0.mem
  bits : Bits b k s0.mem

theorem fixed_tab {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hst : R64.Stp b s0 s) : TabOk b s.mem := by
  intro i hi
  obtain ⟨e1, e2⟩ := hf.tab i hi
  have keep : ∀ o, o + 56 ≤ 2048 → V s.mem (tb b) o = V s0.mem (tb b) o := fun o ho => by
    unfold V
    refine val32_congr (limb_frame hst.frame fun r hr k hk => ?_)
    have hA : ACC = 952 := rfl
    rw [List.mem_singleton.mp hr, tb, Offset.add_add]
    exact Offset.disjoint_base _ (by simp only [CTAB]; omega) (by simp only [CTAB]; omega)
  exact ⟨by rw [keep _ (by omega), e1], by rw [keep _ (by omega), e2]⟩

theorem fixed_bits {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hst : R64.Stp b s0 s) : Bits b k s.mem :=
  fun t ht => by
    have hA : ACC = 952 := rfl
    have hB : Impl.X448.RISCV64.BITS = 1064 := rfl
    rw [byte_above hst.frame (by omega) (by omega)]
    exact hf.bits t ht

theorem step_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) {t : Nat} (ht : t < 114) {s : State}
    (h : LInv b k s0 (t + 1) s) :
    WP isa combStep s fun s' => LInv b k s0 t s' ∧ (s'.gpr .t1 != 0) = decide (t ≠ 0) := by
  have hc := h.ctx
  unfold combStep
  refine WP.seq (wp_subi (by decide) fun s1 u1 => WP.block_nil ?_)
  have e1 : s1.gpr .t1 = BitVec.ofNat 64 t := by
    rw [u1.gpr, h.t1, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
  have hst1 : R64.Stp b s0 s1 :=
    h.stp.trans (R64.Stp.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide) u1.mem)
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide)
  have C1 : R64.Cur b s0 (s1.gpr .t2) (BitVec.ofNat 64 t) DQ (FS s1.mem b) s1 :=
    ⟨hc1, hst1, rfl, e1, fun _ _ => rfl⟩
  rw [opsProg_eq]
  refine WP.seq (R64.ops_ok _ _ _ _ dbl_ok C1 fun s2 C2 => WP.block_nil ?_)
  -- The row's index and its entry.
  have bs2 := fixed_bits hfx C2.stp
  refine WP.seq (WP.append (digit_ok C2.ctx bs2 ht C2.t1) fun s3 ⟨a3, r3, m3⟩ => ?_)
  have hc3 : Ctx b s3 := C2.ctx.of_rest r3 (by decide)
  have tw3 : TabW b s3 := fun d n hdn => by
    rw [r3.wr, C2.stp.rest.wr]; exact hfx.tabw d n hdn
  refine WP.mono (select_ok (Proof.Ed448.Comb.digit_lt k t) hc3 tw3 a3) fun s4 ⟨hc4, r4, f4, v4⟩ => ?_
  have hr34 : Rest R64.work s2 s4 := (r3.mono (by decide)).trans (r4.mono (by decide))
  have hst4 : R64.Stp b s0 s4 := C2.stp.trans ⟨hr34, by
    rw [← m3]; exact f4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by simp only [SX, ACC]; omega)⟩⟩
  have tab4 : TabOk b s4.mem := fixed_tab hfx hst4
  have sxy := sel_x (Proof.Ed448.Comb.digit_lt k t) tab4 (fun j hj => by
    rw [v4 j hj, tw_frame f4 (Proof.Ed448.Comb.digit_lt k t) hj])
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
  have C4 : R64.Cur b s0 (s4.gpr .t2) (BitVec.ofNat 64 t) AQ (FS s4.mem b) s4 :=
    ⟨hc4, hst4, rfl, by rw [r4.gpr _ (by decide), r3.gpr _ (by decide), C2.t1], fun _ _ => rfl⟩
  have d4 : FS s4.mem b DK = Spec.Ed448.d := by
    rw [keep DK (by decide), C2.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, u1.mem]
    exact h.d
  refine R64.ops_ok _ _ _ _ add_ok C4 fun s5 C5 => WP.block_nil ?_
  have p5 : ptOf (FS s5.mem b) = ptOf (runOps (addOps.map toF) (FS s4.mem b)) := by
    simp only [ptOf]
    rw [C5.slots RX (by decide), C5.slots RY (by decide), C5.slots RZ (by decide)]
  have p4 : ptOf (FS s4.mem b) = Proof.Ed448.double (ptOf (FS s.mem b)) := by
    have e : ptOf (FS s4.mem b) = ptOf (runOps (dblOps.map toF) (FS s1.mem b)) := by
      simp only [ptOf]
      rw [keep RX (by decide), keep RY (by decide), keep RZ (by decide),
        C2.slots RX (dbl_sub RX (by decide)), C2.slots RY (dbl_sub RY (by decide)),
        C2.slots RZ (dbl_sub RZ (by decide))]
    rw [e, (dbl_vals _).1, u1.mem]
  refine ⟨⟨C5.ctx, C5.stp, C5.t1, ?_, ?_⟩, by rw [C5.t1, ofNat_ne_zero (by omega)]⟩
  · rw [C5.slots DK (add_sub DK (by decide)), (add_vals _ d4).2, d4]
  · rw [p5, (add_vals _ d4).1, p4, sxy.1, sxy.2, addAffine_eq]
    exact step_rep ht h.rep

theorem loop_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 114 → LInv b k s0 n s →
      WP isa (.loop combStep (.nonzero .t1)) s (LInv b k s0 0) := by
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

end VG.Proof.Ed448.RISCV64.Comb
