module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
public import VerifiedGarbage.Proof.Ed448.Comb
public import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.Field
meta import VerifiedGarbage.Proof.Framework.KernelRfl

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
  obtain hc1 : Ctx (tb b) s := hc.of_rest h.rest (by decide)
  refine WP.append (constField_ok hc1 (o := 112 * i) (by omega_using [hi]) (by omega_using []) (fe_lt _))
    fun t ⟨rt, ft, vt⟩ => ?_
  refine WP.mono (constField_ok (hc1.of_rest rt (by decide)) (o := 112 * i + 56) (by omega_using [hi]) (by omega_using [])
    (fe_lt _)) fun u ⟨ru, fu, vu⟩ => ⟨h.rest.trans (rt.trans ru), ?_, fun j hj => ?_⟩
  · have F1 : Frame [⟨tb b, 112 * (i + 1)⟩] s0.mem s.mem :=
      h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩
    obtain F2 : Frame [⟨tb b, 112 * (i + 1)⟩] s.mem t.mem :=
      ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [])⟩
    obtain F3 : Frame [⟨tb b, 112 * (i + 1)⟩] t.mem u.mem :=
      fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [])⟩
    exact F1.trans (F2.trans F3)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨e1, e2⟩ := h.vals j hj
      refine ⟨?_, ?_⟩
      · rw [slot_keep fu (by omega_using []) (by omega_using [hi]) (by omega_arith), slot_keep ft (by omega_using [hj]) (by omega_using [hi]) (by omega_arith)]
        exact e1
      · rw [slot_keep fu (by omega_using [hj]) (by omega_using [hi]) (by omega_arith), slot_keep ft (by omega_using []) (by omega_using [hi]) (by omega_arith)]
        exact e2
    · exact ⟨by rw [slot_keep fu (by omega_using []) (by omega_using [hi]) (by omega_using [hi])]; exact vt, vu⟩

theorem tabBuild_ok {s : State} (hc : Ctx b s) (hw : TabW b s) :
    WP isa (.block tabBuild) s fun t => Ctx b t ∧ Rest [.a3, .a4] s t ∧
      Frame [⟨tb b, 1792⟩] s.mem t.mem ∧ TabOk b t.mem := by
  simp only [tabBuild, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s1 u1 => wp_addi (by decide) fun s2 u2 => ?_
  obtain e2 : s2.gpr .a3 = tb b := by
    rw [u2.gpr, u1.gpr, hc.a3, BitVec.add_assoc]; rfl
  obtain hr2 : Rest [.a3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx (tb b) s2 := ⟨e2, tb_al hc.al, by rw [hr2.wr]; exact hw⟩
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
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
  refine WP.cons (exec_logicImm (by unfold imm12; omega_using [h])) ?_
  simp only
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

/-! ## The index -/

theorem bit_val (k t : Nat) : ((k >>> t) &&& 1) = k / 2 ^ t % 2 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

/-- The byte of bit `t` of the scalar, as `lbu` reads it. -/
theorem bit_byte {k t : Nat} (hb : Bits b k s.mem) (ht : t < 456) :
    BitVec.ofNat 64 (s.mem (b + BitVec.ofNat 64 (BITS + t))).toNat = BitVec.ofNat 64 (k / 2 ^ t % 2) := by
  rw [hb t ht, BitVec.toNat_ofNat, bit_val, Nat.mod_eq_of_lt (by omega_using [])]

theorem digit_ok {counter : Reg} {k t : Nat} (hc : Ctx b s) (hb : Bits b k s.mem) (ht : t < 114)
    (h1 : s.gpr counter = BitVec.ofNat 64 t) :
    WP isa (.block (combDigitAt counter)) s fun s' => s'.gpr .a5 = BitVec.ofNat 64 (Proof.Ed448.Comb.digit k t) ∧
      Rest [.a1, .a4, .a5] s s' ∧ s'.mem = s.mem := by
  have hB : BITS = 1064 := rfl
  simp only [combDigitAt]
  refine wp_add fun s1 u1 => ?_
  obtain e1 : s1.gpr .a1 = b + BitVec.ofNat 64 t := by rw [u1.gpr, hc.a3, h1]
  have hm1 : s1.mem = s.mem := u1.mem
  obtain ld : ∀ (s' : State) (o : Nat), o + t < 456 → s'.gpr .a1 = b + BitVec.ofNat 64 t →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .a1 + BitVec.ofNat 64 (BITS + o) = b + BitVec.ofNat 64 (BITS + (o + t)) ∧
        InRegions (s'.rd ++ s'.wr) (b + BitVec.ofNat 64 (BITS + (o + t))) 1 := fun s' o ho ha hr hw =>
    ⟨by rw [ha, Offset.add_add]; congr 2; omega_using [], by rw [hr, hw]; exact hc.inR (by omega_using [hB, ho])⟩
  obtain ⟨a1, i1⟩ := ld s1 342 (by omega_using [ht]) e1 u1.rd u1.wr
  refine wp_lbz (by decide) a1 i1 fun s2 u2 => ?_
  obtain ⟨a2, i2⟩ := ld s2 228 (by omega_using [ht]) (by rw [u2.other _ (by decide), e1]) (by rw [u2.rd, u1.rd])
    (by rw [u2.wr, u1.wr])
  refine wp_lbz (by decide) a2 i2 fun s3 u3 => wp_add fun s4 u4 => wp_add fun s5 u5 => ?_
  obtain ⟨a3, i3⟩ := ld s5 114 (by omega_using [ht])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) a3 i3 fun s6 u6 => wp_add fun s7 u7 => wp_add fun s8 u8 => ?_
  obtain ⟨a4, i4⟩ := ld s8 0 (by omega_using [ht])
    (by rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e1])
    (by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  refine wp_lbz (by decide) (by rw [Nat.add_zero] at a4; exact a4) i4 fun s9 u9 => wp_add fun s10 u10 => wp_add fun s11 u11 =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · have m2 : s2.mem = s.mem := by rw [u2.mem, hm1]
    obtain m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, m2]
    obtain m8 : s8.mem = s.mem := by rw [u8.mem, u7.mem, u6.mem, m5]
    obtain b1 := bit_byte (t := 342 + t) hb (by omega_using [ht])
    obtain b2 := bit_byte (t := 228 + t) hb (by omega_using [ht])
    obtain b3 := bit_byte (t := 114 + t) hb (by omega_using [ht])
    obtain b4 := bit_byte (t := 0 + t) hb (by omega_using [ht])
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
    omega_using []
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
  exact Offset.disjoint _ (.inr (by simp only [CTAB, SX]; omega_using [])) (by simp only [CTAB]; omega_using [hi, hj])
    (by simp only [SX]; omega_using [])

/-- `TabW` gives the entries' doublewords to load. -/
theorem tab_in {s : State} (hw : TabW b s) {i j : Nat} (hi : i < 16) (hj : j < 14) :
    InRegions (s.rd ++ s.wr) (tb b + BitVec.ofNat 64 (112 * i + 8 * j)) 8 :=
  let ⟨r, hr, hc⟩ := hw (112 * i + 8 * j) 8 (by omega_using [hi, hj])
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
  refine wp_ld (by simp only [SX]; omega_using [hj]) (by rw [hc.a3]) (al8 hc.al (by simp only [SX]; omega_using []))
    (hc.inR (by simp only [SX]; omega_using [hj])) fun s1 u1 => ?_
  refine wp_ld (by omega_using [hi, hj]) (by rw [u1.other _ (by decide), h.t2]) (al8 (tb_al hc.al) (by omega_using []))
    (by rw [u1.rd, u1.wr]; exact tab_in h.tab hi hj) fun s2 u2 => wp_and fun s3 u3 => wp_or fun s4 u4 => ?_
  obtain hr4 : Rest [.a2, .a4] s s4 :=
    ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))))
  refine wp_sd (by simp only [SX]; omega_using [hj]) (by rw [hr4.gpr _ (by decide), hc.a3])
    (al8 hc.al (by simp only [SX]; omega_using [])) (by rw [hr4.wr]; exact hc.inW (by simp only [SX]; omega_using [hj]))
    fun s5 u5 => WP.block_nil ?_
  obtain hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hf : Frame [SR b] s.mem s5.mem := by
    rw [u5.mem, hm4]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SX]; omega_using []) (by simp only [SX]; omega_using [hj]) (by simp only [SX]; omega_using []))
  obtain g4 : s4.gpr .a2 = sw s.mem b j ||| (tw s.mem b i j &&& s.gpr .t0) := by
    rw [u4.gpr, u3.other Reg.a2 (by decide), u3.gpr, u2.other Reg.a2 (by decide), u2.gpr,
      u2.other Reg.t0 (by decide), u1.gpr, u1.other Reg.t0 (by decide), u1.mem]
  refine ⟨h.next ((hr4.mono (by decide)).trans ⟨fun r _ => by rw [u5.gpr], u5.rd, u5.wr, u5.sp⟩) hf,
    by rw [u5.gpr, hr4.gpr _ (by decide)], ?_, fun j' hj' hne => ?_⟩
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_self64, g4]
  · simp only [sw]
    rw [u5.mem, hm4, Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hne]) (by simp only [SX]; omega_using [hj'])
      (by simp only [SX]; omega_using [hj])) (by decide)]

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
  refine wp_xori' (by omega_using [hi]) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_sltu fun s3 u3 =>
    wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  obtain hr5 : Rest [.a2, .a4, .a6, .t0] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  obtain hm5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain e5 : s5.gpr .t0 = if d = i then BitVec.allOnes 64 else 0 := by
    rw [u5.gpr, u4.other Reg.a2 (by decide), u4.gpr, u3.gpr, u2.gpr, u2.other Reg.a2 (by decide), u1.gpr,
      hc.a5, h5, ← mask_eq d hd i hi]
    rfl
  obtain c5 : SelCtx b s0 s5 := hc.next hr5 (by rw [hm5]; exact Frame.refl _ _)
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
      · simp only [hjk, ite_false, show ¬ j < k + 1 by omega_using [e, hjk]]
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
      · simp [hdi, show ¬ d < i + 1 by omega_using [e, hdi]]

theorem select_ok {d : Nat} (hd : d < 16) {s : State} (hc : Ctx b s) (hw : TabW b s)
    (h5 : s.gpr .a5 = BitVec.ofNat 64 d) :
    WP isa (.block combSelect) s fun s' => Ctx b s' ∧ Rest [.a2, .a4, .a6, .t0, .t2] s s' ∧
      Frame [SR b] s.mem s'.mem ∧ ∀ j < 14, sw s'.mem b j = tw s.mem b d j := by
  simp only [combSelect, List.cons_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a2]) (by decide)) (by decide)
  -- Zero `(SX, SY)`.
  refine WP.append (wp_range_flatMap (M := isa) (fun k t => Ctx b t ∧ Rest [.a2] s t ∧
      t.gpr .a2 = 0 ∧ Frame [SR b] s.mem t.mem ∧ ∀ j < k, sw t.mem b j = 0)
    (fun k t hk ⟨ct, rt, zt, ft, vt⟩ => wp_sd (by simp only [SX]; omega_using [hk]) (by rw [ct.a3])
      (al8 ct.al (by simp only [SX]; omega_using [])) (ct.inW (by simp only [SX]; omega_using [hk])) fun u uu => by
        obtain ru : Rest [.a2] t u := ⟨fun r _ => by rw [uu.gpr], uu.rd, uu.wr, uu.sp⟩
        obtain fu : Frame [SR b] t.mem u.mem := by
          rw [uu.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
            (Offset.contains _ (by simp only [SX]; omega_using []) (by simp only [SX]; omega_using [hk])
              (by simp only [SX]; omega_using []))
        refine WP.block_nil ⟨ct.of_rest ru (by decide), rt.trans ru, by rw [uu.gpr, zt], ft.trans fu,
          fun j hj => ?_⟩
        simp only [sw]; rw [uu.mem]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hj]) (by simp only [SX]; omega_arith)
            (by simp only [SX]; omega_using [hk])) (by decide)]
          exact vt j hj
        · rw [Mem.readW_writeW_self64, zt])
    14 (Nat.le_refl _) s1 ⟨hc1, u1.rest (by decide), by rw [u1.gpr]; rfl, by rw [u1.mem]; exact Frame.refl _ _,
      fun j hj => by omega⟩) fun t ⟨ct, rt, _, ft, vt⟩ => ?_
  -- The table's pointer.
  refine wp_addi (by decide) fun t1 v1 => wp_addi (by decide) fun t2 v2 => ?_
  obtain e2 : t2.gpr .t2 = tb b := by
    rw [v2.gpr, v1.gpr, ct.a3, BitVec.add_assoc]; rfl
  obtain hr2 : Rest [.a2, .t2] s t2 :=
    (rt.mono (by decide)).trans ((v1.rest (by decide)).trans (v2.rest (by decide)))
  obtain c2 : SelCtx b t2 t2 :=
    ⟨ct.of_rest ((v1.rest (ws := [.t2]) (by decide)).trans (v2.rest (by decide))) (by decide),
      fun d n hdn => by rw [hr2.wr]; exact hw d n hdn, e2, rfl, Rest.refl _ _, Frame.refl _ _⟩
  obtain hm2 : t2.mem = t.mem := by rw [v2.mem, v1.mem]
  obtain tab2 : ∀ i < 16, ∀ j < 14, tw t2.mem b i j = tw s.mem b i j := fun i hi j hj => by
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
  obtain h := pointAdd_rep (double_rep hp) (Proof.Ed448.Comb.entry_rep _ (Proof.Ed448.Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Proof.Ed448.Comb.accScalar_step k t ht] at h
  exact h

section
variable {b : Addr}

/-- The element at `SX` (`SY`) is entry `d`'s `x` (`y`) after the selection. -/
theorem sel_x {m : Mem} {d : Nat} (hd : d < 16) (htab : TabOk b m)
    (hs : ∀ j < 14, sw m b j = tw m b d j) :
    FS m b SX = (Impl.Ed448.Comb.entry d).1 ∧ FS m b SY = (Impl.Ed448.Comb.entry d).2 := by
  obtain h7 : ∀ o e, (∀ i < 7, R64.ew m b o i = R64.ew m (tb b) e i) → V m b o = V m (tb b) e := fun o e h => by
    rw [R64.V_eq, R64.V_eq]; exact R64.val7_congr h
  obtain ⟨tx, ty⟩ := htab d hd
  refine ⟨?_, ?_⟩
  · rw [FS, h7 SX (112 * d) fun i hi => ?_, tx, Proof.X448.toFe_self]
    have := congrArg BitVec.toNat (hs i (by omega_using [hi]))
    simpa [R64.ew, R64.dw, sw, tw] using this
  · rw [FS, h7 SY (112 * d + 56) fun i hi => ?_, ty, Proof.X448.toFe_self]
    have := congrArg BitVec.toNat (hs (i + 7) (by omega_using [hi]))
    simp only [R64.ew, R64.dw, sw, tw] at this ⊢
    rw [show SY + 8 * i = SX + 8 * (i + 7) by simp only [SX, SY]; omega_using [],
      show 112 * d + 56 + 8 * i = 112 * d + 8 * (i + 7) by omega_using []]
    exact this


end

/-! ## The point operations as functions

A call site (`viaCall`) keeps `t1`, `t2` and `ra` in the first three
doublewords of X448's slot `Y` (`SAVT1`), calls the field program, and loads
them back. The program's outputs are all below `Y` (`outsLow`), so it writes
only below `Y` and the accumulator (`Low`), and the doublewords stay: around
the call site, `Cur` holds as around the field program inlined (`viaCall_ok`). -/

section Via

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC)
open VG.Proof.X448.RISCV64.R64 (Cur Stp opsCode opsOk fcode work mulSF addSF subSF al8 Sep8)
open VG.Spec.X448 (Fe)

variable {b : Addr}

/-- What field operations with outputs below `Y` write: below `Y`, and the accumulator. -/
abbrev Low (b : Addr) : List Region := [⟨b, SAVT1⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩]

/-- Every operation's output is below `Y`. -/
def outsLow : List FOp → Bool
  | [] => true
  | op :: ops => decide (op.out + 56 ≤ SAVT1) && outsLow ops

theorem low_of {o : Nat} (ho : o + 56 ≤ SAVT1) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m') : Frame (Low b) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ ho⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- A field operation with its output below `Y`. -/
theorem opLow {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep8 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hlo : op.out + 56 ≤ SAVT1) (hx : op.x ∈ qs)
    (hy : op.y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (fcode op) s fun t =>
      Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v)) t ∧ Frame (Low b) s.mem t.mem := by
  cases op with
  | mul o x y =>
    exact WP.mono (mulSF hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => ⟨h.next hr (frame_FA ho hf) hS, low_of hlo hf⟩
  | add o x y =>
    exact WP.mono (addSF hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => ⟨h.next hr (frame_FA ho hf) hS, low_of hlo hf⟩
  | sub o x y =>
    exact WP.mono (subSF hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => ⟨h.next hr (frame_FA ho hf) hS, low_of hlo hf⟩

/-- Field operations with their outputs below `Y`, then `k`. -/
theorem opsLowK_ok {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true → outsLow ops = true →
      Cur b s0 a c qs v s →
      (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' fun t => Q t ∧ Frame (Low b) s'.mem t.mem) →
      WP isa (opsCode ops k) s fun t => Q t ∧ Frame (Low b) s.mem t.mem
  | [], _, _, s, _, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, hlo, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    simp only [outsLow, Bool.and_eq_true, decide_eq_true_eq] at hlo
    obtain ⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    exact WP.seq (WP.mono (opLow op h1 h3 hlo.1 h4 h5 h) fun s' ⟨h', f'⟩ =>
      WP.mono (opsLowK_ok ops _ _ s' h6 hlo.2 h' hk) fun _ ⟨ht, ft⟩ => ⟨ht, f'.trans ft⟩)

/-- Field operations with their outputs below `Y`. -/
theorem opsLow_ok {s0 : State} {a c : BitVec 64} (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State)
    (hok : opsOk ops qs = true) (hlo : outsLow ops = true) (h : Cur b s0 a c qs v s) :
    WP isa (opsCode ops (.block [])) s fun t =>
      Cur b s0 a c (outsQ ops qs) (runOps ops v) t ∧ Frame (Low b) s.mem t.mem :=
  opsLowK_ok ops qs v s hok hlo h fun _ h' => WP.block_nil ⟨h', Frame.refl _ _⟩

/-- A call's code run from the call's entry state, which leaves `ra` as it
found it, returns. -/
theorem callBody_wp {name : String} {body : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa body s.callEntry fun u => u.gpr .ra = s.callEntry.gpr .ra ∧ Q u) :
    WP isa (.call name body) s Q := by
  obtain ⟨t, u, he, hra, hq⟩ := h
  have hret : isa.ret s.callEntry u = some u := by
    simp only [isa, ret]; exact ite_eq_left_of_eq_true _ _ (eq_true hra)
  exact ⟨_, u, Exec.call (call_callEntry s) he hret, hq⟩

/-- A call site of code that keeps `Cur` and writes only `Low` (field
operations with their outputs below `Y`), for slots `qs` apart from `Y`: as
the code inlined. -/
theorem viaCall_ok {name : String} {body : Prog isa} {s0 : State} {a c : BitVec 64} {qs qs' : List Nat}
    {v v' : Nat → Fe}
    (hb : ∀ sE, Cur b sE (sE.gpr .t2) (sE.gpr .t1) qs v sE →
      WP isa body sE fun u => Cur b sE (sE.gpr .t2) (sE.gpr .t1) qs' v' u ∧ Frame (Low b) sE.mem u.mem)
    (hsep : Sep1 SAVT1 qs = true) (hne : SAVT1 ∉ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (viaCall name body) s (Cur b s0 a c qs' v') := by
  have hc := h.ctx
  obtain w1 := hc.wr SAVT1 8 (by decide); obtain w2 := hc.wr SAVT2 8 (by decide); obtain w3 := hc.wr SAVRA 8 (by decide)
  obtain a1 := al8 hc.al (d := SAVT1) (by decide); obtain a2 := al8 hc.al (d := SAVT2) (by decide)
  obtain a3 := al8 hc.al (d := SAVRA) (by decide)
  obtain cY : ∀ d, d + 8 ≤ 56 →
      (⟨b + BitVec.ofNat 64 SAVT1, 56⟩ : Region).Contains (b + BitVec.ofNat 64 (SAVT1 + d)) (64 / 8) :=
    fun d hd => Offset.contains _ (by omega_using []) (by omega_using [hd]) (by decide)
  unfold viaCall
  -- `t1`, `t2` and `ra` into `Y`.
  refine WP.seq (wp_sd (by decide) (by rw [hc.a3]) a1 w1 fun v1 u1 => wp_sd (by decide) (by rw [u1.gpr, hc.a3]) a2
    (by rw [u1.wr]; exact w2) fun v2 u2 => wp_sd (by decide) (by rw [u2.gpr, u1.gpr, hc.a3]) a3
    (by rw [u2.wr, u1.wr]; exact w3) fun s₁ u3 => WP.block_nil ?_)
  have hf1 : Frame [⟨b + BitVec.ofNat 64 SAVT1, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s₁.mem := by
    rw [u3.mem, u2.mem, u1.mem]
    exact (((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (by simpa using cY 0 (by decide))).writeW
      (List.mem_cons_self ..) _ (cY 8 (by decide))).writeW (List.mem_cons_self ..) _ (cY 16 (by decide))
  have g1 : s₁.gpr = s.gpr := by rw [u3.gpr, u2.gpr, u1.gpr]
  have hS1 : SlotsOk s₁.mem b qs v := fun q hq =>
    slots_after hsep (by decide) hf1 h.slots hq fun e => hne (e ▸ hq)
  have wr1 : s₁.wr = s.wr := by rw [u3.wr, u2.wr, u1.wr]
  -- The call, from its entry state.
  have hE : Cur b s₁.callEntry (s₁.callEntry.gpr .t2) (s₁.callEntry.gpr .t1) qs v s₁.callEntry :=
    ⟨⟨by rw [State.callEntry_gpr _ (by decide), g1, hc.a3], hc.al, by rw [State.callEntry_wr, wr1]; exact hc.wr⟩,
      Stp.refl _ _, rfl, rfl, by rw [State.callEntry_mem]; exact hS1⟩
  refine WP.seq (callBody_wp (WP.mono (hb _ hE) fun u ⟨cu, fu⟩ =>
    ⟨cu.stp.rest.gpr _ (by decide), ?_⟩))
  -- `t1`, `t2` and `ra` back.
  have hu3 := cu.ctx.a3
  have r1 := cu.ctx.inR (d := SAVT1) (n := 8) (by decide); have r2 := cu.ctx.inR (d := SAVT2) (n := 8) (by decide)
  have r3 := cu.ctx.inR (d := SAVRA) (n := 8) (by decide)
  refine wp_ld (by decide) (by rw [hu3]) a3 r3 fun x1 y1 => wp_ld (by decide) (by rw [y1.other _ (by decide), hu3]) a1
    (by rw [y1.rd, y1.wr]; exact r1) fun x2 y2 => wp_ld (by decide)
    (by rw [y2.other _ (by decide), y1.other _ (by decide), hu3]) a2 (by rw [y2.rd, y2.wr, y1.rd, y1.wr]; exact r2)
    fun t y3 => WP.block_nil ?_
  -- The doublewords of `Y` read back.
  have hlow : ∀ d, d + 8 ≤ 24 → u.mem.readW (b + BitVec.ofNat 64 (SAVT1 + d)) 64 =
      s₁.mem.readW (b + BitVec.ofNat 64 (SAVT1 + d)) 64 := fun d hd => by
    rw [← State.callEntry_mem s₁]
    refine fu.readW (Region.contains_self _ (64 / 8)) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by simp only [SAVT1]; omega_using []) (by simp only [SAVT1]; omega_using [hd])
    · exact Offset.disjoint _ (Or.inl (by simp only [SAVT1, ACC]; omega_using [hd])) (by simp only [SAVT1]; omega_using [hd])
        (by decide)
  have rd1 : s₁.mem.readW (b + BitVec.ofNat 64 SAVRA) 64 = s.gpr .ra := by
    rw [u3.mem, Mem.readW_writeW_self64, u2.gpr, u1.gpr]
  have rd2 : s₁.mem.readW (b + BitVec.ofNat 64 SAVT1) 64 = s.gpr .t1 := by
    rw [u3.mem, Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      u2.mem, Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      u1.mem, Mem.readW_writeW_self64]
  have rd3 : s₁.mem.readW (b + BitVec.ofNat 64 SAVT2) 64 = s.gpr .t2 := by
    rw [u3.mem, Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      u2.mem, Mem.readW_writeW_self64, u1.gpr]
  have mt : t.mem = u.mem := by rw [y3.mem, y2.mem, y1.mem]
  have rt : Rest [.ra, .t1, .t2] u t := (y1.rest (by decide)).trans ((y2.rest (by decide)).trans (y3.rest (by decide)))
  have tra : t.gpr .ra = s.gpr .ra := by
    rw [y3.other _ (by decide), y2.other _ (by decide), y1.gpr, ← rd1]; exact hlow 16 (by decide)
  have tt1 : t.gpr .t1 = s.gpr .t1 := by
    rw [y3.other _ (by decide), y2.gpr, y1.mem, ← rd2]; simpa using hlow 0 (by decide)
  have tt2 : t.gpr .t2 = s.gpr .t2 := by rw [y3.gpr, y2.mem, y1.mem, ← rd3]; exact hlow 8 (by decide)
  have rest : Rest work s0 t := by
    refine ⟨fun r hr => ?_, by rw [rt.rd, cu.stp.rest.rd, State.callEntry_rd, u3.rd, u2.rd, u1.rd, h.stp.rest.rd],
      by rw [rt.wr, cu.stp.rest.wr, State.callEntry_wr, wr1, h.stp.rest.wr],
      by rw [rt.sp, cu.stp.rest.sp, State.callEntry_sp, u3.sp, u2.sp, u1.sp, h.stp.rest.sp]⟩
    by_cases e : r = .ra
    · subst e; rw [tra, h.stp.rest.gpr _ hr]
    · have hl : r ∉ linkRegs := fun hm => by
        simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact e rfl | exact hr (by decide)
      rw [rt.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨e, fun h' => hr (h' ▸ by decide),
          fun h' => hr (h' ▸ by decide)⟩), cu.stp.rest.gpr _ hr, State.callEntry_gpr _ hl, g1, h.stp.rest.gpr _ hr]
  have toFA : ∀ {m m' : Mem} {rs : List Region}, (∀ r ∈ rs, Region.Sub r (FA b)) → Frame rs m m' → Frame [FA b] m m' :=
    fun hs hf => hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩
  have frame : Frame [FA b] s0.mem t.mem := by
    refine (h.stp.frame.trans (toFA ?_ hf1)).trans ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)
    · rw [mt, ← State.callEntry_mem s₁]
      refine toFA (fun r hr => ?_) fu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun x hx => Offset.sub_base _ (d := 0) (n := SAVT1) (by decide) x (by rw [BitVec.add_zero]; exact hx)
      · exact Offset.sub_base _ (by decide)
  exact ⟨cu.ctx.of_rest rt (by decide), ⟨rest, frame⟩, by rw [tt2, h.t2], by rw [tt1, h.t1], by rw [mt]; exact cu.slots⟩

/-- A call site of field operations with their outputs below `Y`. -/
theorem viaCallOps_ok {name : String} {s0 : State} {a c : BitVec 64} {ops : List FOp} {qs : List Nat}
    {v : Nat → Fe} (hok : opsOk ops qs = true) (hlo : outsLow ops = true) (hsep : Sep1 SAVT1 qs = true)
    (hne : SAVT1 ∉ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (viaCall name (opsCode ops (.block []))) s (Cur b s0 a c (outsQ ops qs) (runOps ops v)) :=
  viaCall_ok (fun _ hE => opsLow_ok ops qs v _ hok hlo hE) hsep hne h

end Via

/-! ## The field product with explicit operand pointers -/

section Product

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64
open VG.Impl.X448.RISCV64.R64 (product reduce)

/-- Read and write through the working-space pointer at the caller's offsets. -/
private def rebase (o x y : Nat) : Instr → Instr
  | .load .d r .s1 off => .load .d r .a3 (x + off)
  | .load .d r .s2 off => .load .d r .a3 (y + off)
  | .store .d r .a0 off => .store .d r .a3 (o + off)
  | i => i

private def inElement : Instr → Bool
  | .load .d _ .s1 off | .load .d _ .s2 off | .store .d _ .a0 off => off < 56
  | _ => true

private def pointerRegs : List Reg := [.a0, .a3, .s1, .s2]

private structure ProductPtrs (o x y : Nat) (s : State) : Prop where
  o : s.gpr .a0 = s.gpr .a3 + BitVec.ofNat 64 o
  x : s.gpr .s1 = s.gpr .a3 + BitVec.ofNat 64 x
  y : s.gpr .s2 = s.gpr .a3 + BitVec.ofNat 64 y

private theorem addr_rebase {s : State} {r : Reg} {base off : Nat}
    (h : s.gpr r = s.gpr .a3 + BitVec.ofNat 64 base) (ho : off < 56) (hb : base + 56 ≤ 2048) :
    addr s 8 .a3 (base + off) = addr s 8 r off := by
  have h₁ : base + off < 2048 := by omega_using [hb, ho]
  have h₂ : off < 2048 := by omega_using [ho]
  simp only [addr, BitVec.ofNat_add, ← BitVec.add_assoc, h, h₁, h₂, true_and]

private theorem rebase_exec {o x y : Nat} {s : State} (h : ProductPtrs o x y s)
    (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048) (i : Instr)
    (hi : inElement i = true) : exec (rebase o x y i) s = exec i s := by
  cases i <;> try rfl
  case load z d r off =>
    cases z <;> cases r <;> try rfl
    · have hOff : off < 56 := of_decide_eq_true hi
      simp only [rebase, exec, Width.bytes, addr_rebase h.x hOff hx]
    · have hOff : off < 56 := of_decide_eq_true hi
      simp only [rebase, exec, Width.bytes, addr_rebase h.y hOff hy]
  case store z d r off =>
    cases z <;> cases r <;> try rfl
    have hOff : off < 56 := of_decide_eq_true hi
    simp only [rebase, exec, Width.bytes, addr_rebase h.o hOff ho]

private theorem productPtrs_step {o x y : Nat} {s t : State} (h : ProductPtrs o x y s)
    {i : Instr} (hi : ∀ r ∈ pointerRegs, dstOf i ≠ some r) (he : exec i s = some t) : ProductPtrs o x y t := by
  have a3 := exec_gpr (hi .a3 (by decide)) he
  exact ⟨by rw [exec_gpr (hi .a0 (by decide)) he, a3, h.o],
    by rw [exec_gpr (hi .s1 (by decide)) he, a3, h.x],
    by rw [exec_gpr (hi .s2 (by decide)) he, a3, h.y]⟩

private theorem rebase_wp {o x y : Nat} {Q : State → Prop}
    (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048) :
    ∀ (is : List Instr) {s : State}, ProductPtrs o x y s →
      (∀ i ∈ is, inElement i = true) → (∀ i ∈ is, ∀ r ∈ pointerRegs, dstOf i ≠ some r) →
      WP isa (.block (is.map (rebase o x y))) s Q → WP isa (.block is) s Q
  | [], _, _, _, _, wp => wp
  | i :: is, _, h, hOff, hRegs, wp => by
    obtain ⟨t, he, wt⟩ := WP.block_cons_iff.mp wp
    change exec (rebase o x y i) _ = some t at he
    rw [rebase_exec h ho hx hy i (hOff i List.mem_cons_self)] at he
    exact WP.cons he (rebase_wp ho hx hy is (productPtrs_step h (hRegs i List.mem_cons_self) he)
      (fun j hj => hOff j (List.mem_cons_of_mem _ hj)) (fun j hj => hRegs j (List.mem_cons_of_mem _ hj)) wt)

private theorem product_offsets : ∀ i ∈ combProduct, inElement i = true :=
  List.all_eq_true.mp (by lit_decide)

private theorem product_preserves_ptrs : ∀ i ∈ combProduct, ∀ r ∈ pointerRegs, dstOf i ≠ some r := by
  have h : combProduct.all (fun i => pointerRegs.all fun r => decide (dstOf i ≠ some r)) = true := by lit_decide
  exact fun i hi r hr => of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr)

/-- The shared product reads and writes the caller's field slots. -/
private theorem product_rebased {o x y : Nat} {Q : State → Prop} {s : State}
    (ho : o + 56 ≤ 2048) (hx : x + 56 ≤ 2048) (hy : y + 56 ≤ 2048) (h : ProductPtrs o x y s)
    (he : combProduct.map (rebase o x y) = product x y ++ reduce o)
    (wp : WP isa (.block (product x y ++ reduce o)) s Q) : WP isa (.block combProduct) s Q :=
  rebase_wp ho hx hy combProduct h product_offsets product_preserves_ptrs (he ▸ wp)

open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X448.RISCV64.R64 (clob64 mulSF addSF subSF Sep8 opsOk work sep8_sep1)
open VG.Impl.X448.RISCV64 (ACC)

private def hasProductLayout : COp → Prop
  | .mul o x y => x ≠ y → combProduct.map (rebase o x y) = product x y ++ reduce o
  | _ => True

private theorem addProductLayouts (op : COp) (h : op ∈ addOps) : hasProductLayout op := by
  simp only [addOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | trivial | (intro hne; exact absurd rfl hne) | (intro _; kernel_rfl)

/-- Registers the shared addition can change. `s0` holds the returned public
key's output pointer and `s3` holds the row number. -/
abbrev addWrites : List Reg := [.ra, .s1, .s2] ++ work

private theorem productCall_slots_ok {b : Addr} {o x y : Nat} {qs : List Nat} {v : Nat → Fe} {s : State}
    (hxy : x ≠ y) (he : combProduct.map (rebase o x y) = product x y ++ reduce o)
    (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs)
    (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) (h0 : s.gpr .a0 = s.gpr .s0) :
    WP isa (productCall o x y) s fun t => Rest addWrites s t ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem t.mem ∧
      SlotsOk t.mem b (o :: qs) (upd v o (v x * v y)) := by
  have hA : ACC = 952 := rfl
  have hx' := (sep1_get (sep8_sep1 hq) hx).2.1
  have hy' := (sep1_get (sep8_sep1 hq) hy).2.1
  unfold productCall
  refine WP.seq (wp_addi (by omega_using [hA, ho]) fun s₁ u₁ => wp_addi (by omega_using [hA, hx'])
    fun s₂ u₂ => wp_addi (by omega_using [hA, hy']) fun s₃ u₃ => WP.block_nil ?_)
  have g3 : s₃.gpr .a3 = s.gpr .a3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have g0 : s₃.gpr .a0 = s.gpr .a3 + BitVec.ofNat 64 o := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have g1 : s₃.gpr .s1 = s.gpr .a3 + BitVec.ofNat 64 x := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  have g2 : s₃.gpr .s2 = s.gpr .a3 + BitVec.ofNat 64 y := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have rp : ProductPtrs o x y s₃.callEntry := ⟨
    by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), g0, g3],
    by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), g1, g3],
    by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), g2, g3]⟩
  have km : s₃.callEntry.mem = s.mem := by rw [State.callEntry_mem, u₃.mem, u₂.mem, u₁.mem]
  have hlink : ∀ r ∈ linkRegs, r ∈ .a0 :: addWrites := by decide
  have rk : Rest (.a0 :: addWrites) s s₃.callEntry :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ⟨fun r hr => State.callEntry_gpr s₃ (fun hl => hr (hlink r hl)), rfl, rfl, rfl⟩))
  have src := mulSF hq ho hx hy (hc.of_rest rk (by decide)) (by rw [km]; exact hS)
  rw [show Impl.X448.RISCV64.R64.mul o x y = .block (product x y ++ reduce o) by
    simp only [Impl.X448.RISCV64.R64.mul, ite_eq_right hxy]] at src
  refine WP.seq (callBody_wp (WP.mono (product_rebased (by omega_using [hA, ho])
    (by omega_using [hA, hx']) (by omega_using [hA, hy']) rp he src) fun u ⟨ru, fu, su⟩ =>
      ⟨ru.gpr .ra (by decide), ?_⟩))
  refine wp_mv fun t ut => WP.block_nil ?_
  have rku := rk.trans (ru.mono (by decide))
  have r : Rest addWrites s t := by
    refine ⟨fun r hr => ?_, ut.rd.trans rku.rd, ut.wr.trans rku.wr, ut.sp.trans rku.sp⟩
    by_cases e : r = Reg.a0
    · subst r
      rw [ut.gpr, rku.gpr _ (by decide), h0]
    · rw [ut.other _ e, rku.gpr _ (fun hm => (List.mem_cons.mp hm).elim e hr)]
  exact ⟨r, by rw [ut.mem, ← km]; exact fu, by rw [ut.mem]; exact su⟩

private theorem addOp_ok {b : Addr} {qs : List Nat} {v : Nat → Fe} {s : State} (op : COp)
    (hLayout : hasProductLayout op) (hq : Sep8 (toF op).out qs = true)
    (ho : (toF op).out + 56 ≤ ACC) (hlo : (toF op).out + 56 ≤ SAVT1)
    (hx : (toF op).x ∈ qs) (hy : (toF op).y ∈ qs)
    (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) (h0 : s.gpr .a0 = s.gpr .s0) :
    WP isa (addOp op) s fun t => Rest addWrites s t ∧ Frame (Low b) s.mem t.mem ∧
      SlotsOk t.mem b ((toF op).out :: qs) (upd v (toF op).out ((toF op).val v)) := by
  cases op with
  | mul o x y =>
    change WP isa (if x = y then Impl.X448.RISCV64.R64.mul o x y else productCall o x y) s _
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      exact WP.mono (mulSF hq ho hx hy hc hS) fun _ ⟨hr, hf, hslots⟩ =>
        ⟨hr.mono (by decide), low_of hlo hf, hslots⟩
    · rw [ite_eq_right hxy]
      exact WP.mono (productCall_slots_ok hxy (hLayout hxy) hq ho hx hy hc hS h0) fun _ ⟨hr, hf, hslots⟩ =>
        ⟨hr, low_of hlo hf, hslots⟩
  | add o x y => exact WP.mono (addSF hq ho hx hy hc hS) fun _ ⟨hr, hf, hslots⟩ =>
      ⟨hr.mono (by decide), low_of hlo hf, hslots⟩
  | sub o x y => exact WP.mono (subSF hq ho hx hy hc hS) fun _ ⟨hr, hf, hslots⟩ =>
      ⟨hr.mono (by decide), low_of hlo hf, hslots⟩

private theorem addProg_ok {b : Addr} : ∀ (ops : List COp) (qs : List Nat) (v : Nat → Fe) {s : State},
    opsOk (ops.map toF) qs = true → outsLow (ops.map toF) = true →
    (∀ op ∈ ops, hasProductLayout op) → Ctx b s → SlotsOk s.mem b qs v → s.gpr .a0 = s.gpr .s0 →
    WP isa (addProg ops) s fun t => Rest addWrites s t ∧ Frame (Low b) s.mem t.mem ∧
      SlotsOk t.mem b (outsQ (ops.map toF) qs) (runOps (ops.map toF) v)
  | [], _, _, s, _, _, _, _, hS, _ => WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, hS⟩
  | op :: ops, qs, v, _, hok, hlo, layouts, hc, hS, h0 => by
    simp only [List.map_cons, opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    simp only [List.map_cons, outsLow, Bool.and_eq_true, decide_eq_true_eq] at hlo
    obtain ⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    refine WP.seq (WP.mono (addOp_ok op (layouts op List.mem_cons_self) h1 h3 hlo.1 h4 h5 hc hS h0)
      fun u ⟨r, f, hS'⟩ => ?_)
    refine WP.mono (addProg_ok ops _ _ h6 hlo.2 (fun p hp => layouts p (List.mem_cons_of_mem _ hp))
      (hc.of_rest r (by decide)) hS' (by rw [r.gpr .a0 (by decide), r.gpr .s0 (by decide), h0]))
      (fun _ ⟨r', f', hS''⟩ => ⟨r.trans r', f.trans f', hS''⟩)

open VG.Proof.X448.RISCV64.R64 (Cur Stp opsCode)

abbrev combWrites : List Reg := .s3 :: addWrites

/-- The state before the row that leaves `n` rows. The field operations
preserve the slots where the comb saved its registers. -/
structure LInv (b : Addr) (k : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest combWrites s0 s
  frame : Frame (Low b) s0.mem s.mem
  count : s.gpr .s3 = BitVec.ofNat 64 n
  output : s.gpr .a0 = s.gpr .s0
  d : FS s.mem b DK = Spec.Ed448.d
  rep : Rep (ptOf (FS s.mem b)) (accScalar k n • baseAff)

private theorem field_frame {b : Addr} {m m' : Mem} (f : Frame (Low b) m m') : Frame [FA b] m m' :=
  f.sub fun r hr => by
    simp only [Low, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (Nat.le_refl _)⟩

section
variable {b : Addr}

/-- What the loop keeps of `s0`: the table and the bits, outside the field area. -/
structure Fixed (b : Addr) (k : Nat) (s0 : State) : Prop where
  tabw : TabW b s0
  tab : TabOk b s0.mem
  bits : Bits b k s0.mem

theorem fixed_tab {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hf0 : Frame [FA b] s0.mem s.mem) : TabOk b s.mem := by
  intro i hi
  obtain ⟨e1, e2⟩ := hf.tab i hi
  obtain keep : ∀ o, o + 56 ≤ 2048 → V s.mem (tb b) o = V s0.mem (tb b) o := fun o ho => by
    unfold V
    refine val32_congr (limb_frame hf0 fun r hr k hk => ?_)
    have hA : ACC = 952 := rfl
    rw [List.mem_singleton.mp hr, tb, Offset.add_add]
    exact Offset.disjoint_base _ (by simp only [CTAB]; omega_using [hA]) (by simp only [CTAB]; omega_using [ho, hk])
  exact ⟨by rw [keep _ (by omega_using [hi]), e1], by rw [keep _ (by omega_using [hi]), e2]⟩

theorem fixed_bits {k : Nat} {s0 s : State} (hf : Fixed b k s0) (hf0 : Frame [FA b] s0.mem s.mem) : Bits b k s.mem :=
  fun t ht => by
    have hA : ACC = 952 := rfl
    have hB : Impl.X448.RISCV64.BITS = 1064 := rfl
    rw [byte_above hf0 (by omega_using [hA, hB]) (by omega_using [ht, hB])]
    exact hf.bits t ht

theorem step_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) {t : Nat} (ht : t < 114) {s : State}
    (h : LInv b k s0 (t + 1) s) :
    WP isa combStep s fun s' => LInv b k s0 t s' ∧ (s'.gpr .s3 != 0) = decide (t ≠ 0) := by
  unfold combStep
  refine WP.seq (wp_subi (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain e1 : s1.gpr .s3 = BitVec.ofNat 64 t := by
    rw [u1.gpr, h.count, ofNat_sub_one (by omega_using []) (by omega_using [ht]), Nat.add_sub_cancel]
  obtain hc1 : Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.s3]) (by decide)) (by decide)
  obtain C1 : R64.Cur b s1 (s1.gpr .t2) (s1.gpr .t1) DQ (FS s1.mem b) s1 :=
    ⟨hc1, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [opsProg_eq]
  refine WP.seq (WP.mono (opsLow_ok _ _ _ _ dbl_ok (by decide) C1) fun s2 ⟨C2, F2⟩ => ?_)
  have f2 : Frame (Low b) s0.mem s2.mem := h.frame.trans (by rw [u1.mem] at F2; exact F2)
  have rc2 := C2.stp.rest
  have e2 : s2.gpr .s3 = BitVec.ofNat 64 t := (rc2.gpr _ (by decide)).trans e1
  -- The row's index and its entry.
  obtain bs2 := fixed_bits hfx (field_frame f2)
  refine WP.seq (WP.append (digit_ok C2.ctx bs2 ht e2) fun s3 ⟨a3, r3, m3⟩ => ?_)
  obtain hc3 : Ctx b s3 := C2.ctx.of_rest r3 (by decide)
  obtain tw3 : TabW b s3 := fun d n hdn => by
    rw [r3.wr, rc2.wr, u1.wr, h.rest.wr]; exact hfx.tabw d n hdn
  refine WP.mono (select_ok (Proof.Ed448.Comb.digit_lt k t) hc3 tw3 a3) fun s4 ⟨hc4, r4, f4, v4⟩ => ?_
  have r34 : Rest combWrites s2 s4 := (r3.mono (by decide)).trans (r4.mono (by decide))
  have r14 : Rest combWrites s s4 :=
    (u1.rest (by decide)).trans ((rc2.mono (by decide)).trans r34)
  have f4' : Frame (Low b) s0.mem s4.mem := f2.trans (by
    rw [← m3]
    exact f4.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  obtain tab4 : TabOk b s4.mem := fixed_tab hfx (field_frame f4')
  obtain sxy := sel_x (Proof.Ed448.Comb.digit_lt k t) tab4 (fun j hj => by
    rw [v4 j hj, tw_frame f4 (Proof.Ed448.Comb.digit_lt k t) hj])
  -- The slots of `R` and `d` stay through the selection.
  obtain keep : ∀ q ∈ DQ, FS s4.mem b q = FS s2.mem b q := fun q hq => by
    unfold FS V
    refine congrArg _ ?_
    refine val32_congr (limb_frame (by rw [← m3]; exact f4) fun r hr k hk => ?_)
    rw [List.mem_singleton.mp hr]
    have hX : RX = 56 := rfl
    have hY : RY = 0 := rfl
    have hZ : RZ = 112 := rfl
    have hD : DK = 336 := rfl
    have hS : SX = 168 := rfl
    simp only [DQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_using [hS])
  obtain d4 : FS s4.mem b DK = Spec.Ed448.d := by
    rw [keep DK (by decide), C2.slots DK (dbl_sub DK (by decide)), (dbl_vals _).2, u1.mem]
    exact h.d
  refine WP.mono (addProg_ok addOps AQ (FS s4.mem b) add_ok (by decide) addProductLayouts hc4 (fun _ _ => rfl)
    (by rw [r14.gpr .a0 (by decide), r14.gpr .s0 (by decide), h.output])) fun s5 ⟨r5, f5, slots5⟩ => ?_
  obtain p5 : ptOf (FS s5.mem b) = ptOf (runOps (addOps.map toF) (FS s4.mem b)) := by
    simp only [ptOf]
    rw [slots5 RX (by decide), slots5 RY (by decide), slots5 RZ (by decide)]
  obtain p4 : ptOf (FS s4.mem b) = Proof.Ed448.double (ptOf (FS s.mem b)) := by
    obtain e : ptOf (FS s4.mem b) = ptOf (runOps (dblOps.map toF) (FS s1.mem b)) := by
      simp only [ptOf]
      rw [keep RX (by decide), keep RY (by decide), keep RZ (by decide),
        C2.slots RX (dbl_sub RX (by decide)), C2.slots RY (dbl_sub RY (by decide)),
        C2.slots RZ (dbl_sub RZ (by decide))]
    rw [e, (dbl_vals _).1, u1.mem]
  have e5 : s5.gpr .s3 = BitVec.ofNat 64 t := by
    rw [r5.gpr .s3 (by decide), r4.gpr .s3 (by decide), r3.gpr .s3 (by decide)]
    exact e2
  have r15 : Rest combWrites s s5 := r14.trans (r5.mono (by decide))
  refine ⟨⟨hc4.of_rest r5 (by decide), h.rest.trans r15, f4'.trans f5, e5,
    by rw [r15.gpr .a0 (by decide), r15.gpr .s0 (by decide), h.output], ?_, ?_⟩,
    by rw [e5, ofNat_ne_zero (by omega_using [ht])]⟩
  · rw [slots5 DK (add_sub DK (by decide)), (add_vals _ d4).2, d4]
  · rw [p5, (add_vals _ d4).1, p4, sxy.1, sxy.2, addAffine_eq]
    exact step_rep ht h.rep

theorem loop_ok {k : Nat} {s0 : State} (hfx : Fixed b k s0) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 114 → LInv b k s0 n s →
      WP isa (.loop combStep (.nonzero .s3)) s (LInv b k s0 0) := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := LInv b k s0 0)
    (fun m s => 1 ≤ m ∧ m ≤ 114 ∧ LInv b k s0 m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hl⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega_using [hm1]⟩
  refine WP.mono (step_ok hfx (by omega_using [hm2]) hl) fun s' ⟨hl', hz⟩ => ?_
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    exact .inl ⟨by rw [eval_nonzero, hz]; simp, hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [show t ≠ 0 by omega_using [h0]], t, by omega_using [], by omega_using [h0], by omega_using [hm2], hl'⟩

end

/-! ## The comb's saved registers -/

section Spill

open VG.Proof.X448.RISCV64.R64 (ld_ok sd_ok)
variable {b : Addr}

private abbrev spillRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SAVT1, 56⟩

private def spillWords (b : Addr) (rs : List (Reg × Nat)) : List Region :=
  rs.map fun (_, d) => ⟨b + BitVec.ofNat 64 d, 8⟩

private def savedWords (b : Addr) (rs : List (Reg × Nat)) (s u : State) : Prop :=
  ∀ p ∈ rs, u.mem.readW (b + BitVec.ofNat 64 p.2) 64 = s.gpr p.1

private abbrev spillFits (p : Reg × Nat) : Prop := p.2 + 8 ≤ 2048 ∧ p.2 % 8 = 0

private theorem save_words_ok : ∀ (rs : List (Reg × Nat)) {s : State},
    (∀ p ∈ rs, spillFits p) → rs.Pairwise (fun p q => p.2 + 8 ≤ q.2 ∨ q.2 + 8 ≤ p.2) → Ctx b s →
    WP isa (.block (rs.map fun (r, d) => .store .d r .a3 d)) s
      fun u => Rest [] s u ∧ Frame (spillWords b rs) s.mem u.mem ∧ savedWords b rs s u
  | [], _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by cases h⟩
  | (r, d) :: rs, s, fit, sep, hc => by
    have hd := fit (r,d) List.mem_cons_self
    refine sd_ok hc hd.1 hd.2 fun v w => ?_
    have rw := w.rest []
    refine WP.mono (save_words_ok rs (fun p hp => fit p (List.mem_cons_of_mem _ hp))
      (List.pairwise_cons.mp sep).2 (hc.of_rest rw (by decide))) fun u ⟨ru, fu, su⟩ => ?_
    have fw : Frame (spillWords b ((r,d) :: rs)) s.mem v.mem := by
      rw [w.mem]
      exact (Frame.refl _ s.mem).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
    refine ⟨rw.trans ru, fw.trans (fu.mono fun p hp => List.mem_cons_of_mem _ hp), ?_⟩
    intro p hp
    obtain rfl | hp := List.mem_cons.mp hp
    · rw [fu.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide), w.mem, Mem.readW_writeW_self64]
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hq
      exact Offset.disjoint b ((List.pairwise_cons.mp sep).1 p hpm)
        (by unfold spillFits at hd; omega_using [hd.1])
        (by have h := (fit p (List.mem_cons_of_mem _ hpm)).1; omega_using [h])
    · rw [su p hp, w.gpr]

private theorem restore_words_ok : ∀ (rs : List (Reg × Nat)) {s : State},
    (∀ p ∈ rs, spillFits p ∧ p.1 ≠ .a3) → rs.Pairwise (fun p q => p.1 ≠ q.1) → Ctx b s →
    WP isa (.block (rs.map fun (r,d) => .load .d r .a3 d)) s fun u =>
      Rest (rs.map Prod.fst) s u ∧ u.mem = s.mem ∧ savedWords b rs u s
  | [], _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, rfl, fun _ h => by cases h⟩
  | (r,d) :: rs, _, fit, distinct, hc => by
    have hd := fit (r,d) List.mem_cons_self
    refine ld_ok hc hd.1.1 hd.1.2 fun v w => ?_
    have rw : Rest [r] _ v := w.rest (by simp)
    have hv := hc.of_rest rw (by simp [Ne.symm hd.2])
    refine WP.mono (restore_words_ok rs (fun p hp => fit p (List.mem_cons_of_mem _ hp))
      (List.pairwise_cons.mp distinct).2 hv) fun u ⟨ru, mu, su⟩ => ?_
    refine ⟨(rw.mono (by simp)).trans (ru.mono (fun _ h => List.mem_cons_of_mem _ h)), mu.trans w.mem, ?_⟩
    intro p hp
    obtain rfl | hp := List.mem_cons.mp hp
    · rw [ru.gpr _ (fun hm => ?_), w.gpr]
      obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
      exact (List.pairwise_cons.mp distinct).1 p hp e.symm
    · rw [← w.mem]; exact su p hp

private theorem comb_save_ok {s : State} (hc : Ctx b s) : WP isa (.block combSave) s fun u =>
    Ctx b u ∧ Rest [.s0, .s3] s u ∧ u.gpr .s3 = 114#64 ∧ u.gpr .a0 = u.gpr .s0 ∧
      Frame [spillRegion b] s.mem u.mem ∧ savedWords b combSpill s u := by
  unfold combSave
  refine WP.append (save_words_ok combSpill (by decide) (by decide) hc) fun v ⟨rv, fv, sv⟩ => ?_
  refine wp_mv fun w uw => wp_li (by decide) fun u uu => WP.block_nil ?_
  have r : Rest [.s0, .s3] s u := (rv.mono (by decide)).trans
    ((uw.rest (by decide)).trans (uu.rest (by decide)))
  have hm := uu.mem.trans uw.mem
  refine ⟨hc.of_rest r (by decide), r, uu.gpr, ?_, ?_, ?_⟩
  · rw [r.gpr .a0 (by decide), uu.other _ (by decide), uw.gpr, rv.gpr _ (by decide)]
  · rw [hm]
    refine fv.sub fun p hp => ?_
    obtain ⟨⟨r,d⟩, hd, rfl⟩ := List.mem_map.mp hp
    have fl : ∀ p ∈ combSpill, SAVT1 ≤ p.2 ∧ p.2 + 8 ≤ SAVT1 + 56 := by decide
    obtain ⟨lo, hi⟩ := fl (r,d) hd
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ (spillRegion b)
    rw [show d = SAVT1 + (d - SAVT1) by omega_using [lo], ← Offset.add_add]
    exact Offset.sub_base _ (by omega_using [hi, lo])
  · intro p hp
    rw [hm]; exact sv p hp

private theorem saved_words_keep {s u v : State} (h : savedWords b combSpill s u) (f : Frame (Low b) u.mem v.mem) :
    savedWords b combReload s v := by
  intro p hp
  have hp' := (show ∀ p ∈ combReload, p ∈ combSpill by decide) p hp
  have fit : ∀ p ∈ combReload, SAVT1 ≤ p.2 ∧ p.2 + 8 ≤ ACC := by decide
  obtain ⟨lo, hi⟩ := fit p hp
  rw [f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact h p hp'
  · simp only [Low, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base b lo (by omega_using [hi, VG.Proof.X448.RISCV64.ACC_eq])
    · exact Offset.disjoint b (.inl hi) (by omega_using [hi, VG.Proof.X448.RISCV64.ACC_eq]) (by decide)

/-- The save and restore surround the loop. Between them only the field
slots and accumulator may change. -/
theorem combLoop_ok {k : Nat} {s : State} (fx : Fixed b k s) (hc : Ctx b s)
    (hd : FS s.mem b DK = Spec.Ed448.d) (hrep : Rep (ptOf (FS s.mem b)) (accScalar k 114 • baseAff)) :
    WP isa combLoop s fun t => Ctx b t ∧ Rest work s t ∧
      FS t.mem b DK = Spec.Ed448.d ∧ Rep (ptOf (FS t.mem b)) (accScalar k 0 • baseAff) := by
  unfold combLoop
  refine WP.seq (WP.mono (comb_save_ok hc) fun u ⟨hu, ru, n, out, f, saved⟩ => ?_)
  have fa : Frame [FA b] s.mem u.mem := f.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  have keep {q : Nat} (hq : q + 56 ≤ SAVT1) : FS u.mem b q = FS s.mem b q := by
    unfold FS V
    refine congrArg _ (val32_congr (limb_frame f fun r hr i hi => ?_))
    rw [List.mem_singleton.mp hr]
    have hY : SAVT1 = 896 := rfl
    exact Offset.disjoint b (.inl (by omega_using [hq, hi])) (by omega_using [hq, hi, hY]) (by decide)
  have initial : LInv b k u 114 u := ⟨hu, Rest.refl _ _, Frame.refl _ _, n, out,
    by rw [keep (q := DK) (by decide), hd], by
      simpa only [ptOf, keep (q := RX) (by decide), keep (q := RY) (by decide), keep (q := RZ) (by decide)] using hrep⟩
  have fxu : Fixed b k u :=
    ⟨fun d n h => by rw [ru.wr]; exact fx.tabw d n h, fixed_tab fx fa, fixed_bits fx fa⟩
  refine WP.seq (WP.mono (loop_ok fxu 114 u (by decide) (by decide) initial) fun v hv => ?_)
  have hsaved := saved_words_keep saved hv.frame
  refine WP.mono (restore_words_ok combReload (by decide) (by decide) hv.ctx) fun t ⟨rt, mt, loads⟩ => ?_
  have hctx := hv.ctx.of_rest rt (by decide)
  have keepR : ∀ r ∉ work, t.gpr r = s.gpr r := by
    intro r hr
    by_cases hreload : r ∈ combReload.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hreload
      exact (loads p hp).symm.trans (hsaved p hp)
    · have rf : ∀ r ∈ combWrites, r ∈ work ∨ r ∈ combReload.map Prod.fst := by decide
      have rs : ∀ r ∈ [Reg.s0, .s3], r ∈ combReload.map Prod.fst := by decide
      rw [rt.gpr r hreload, hv.rest.gpr r (fun h => (rf r h).elim hr hreload), ru.gpr r (fun h => hreload (rs r h))]
  exact ⟨hctx, ⟨keepR, rt.rd.trans (hv.rest.rd.trans ru.rd), rt.wr.trans (hv.rest.wr.trans ru.wr),
    rt.sp.trans (hv.rest.sp.trans ru.sp)⟩, by rw [mt]; exact hv.d, by rw [mt]; exact hv.rep⟩

end Spill

end Product

end VG.Proof.Ed448.RISCV64.Comb
