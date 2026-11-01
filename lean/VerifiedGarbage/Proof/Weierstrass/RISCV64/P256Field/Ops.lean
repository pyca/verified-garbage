module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Reduce
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Csub
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: the product

`mulCore` (`Impl/Weierstrass/RISCV64/P256Field.lean`) on pointers `t4`, `t5`
and `t2` (`mulCore_ok`): the operands copied to `MA` and `MB`
(`copyIn_ok`), their product (or the square of the first, if the pointers
are equal) at `ACC` by X25519's columns (`product_ok`, `square_ok`), whose
number is `prodV` (`accW_prodV`), reduced (`reduce_ok`) and stored at `[t2]`
(`csub_ok`): Montgomery's product modulo `p`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest V)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other al8 dw_frame)

/-- The registers the operations write. -/
abbrev clobM : List Reg := [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The own area the product writes: the copies and the product's words. -/
abbrev areaM (b : Addr) : Region := ⟨b + BitVec.ofNat 64 MA, 128⟩

/-- The words of the operand at `p` are the four doublewords at it. -/
theorem copyIn_ok {b A : Addr} {s : State} (hc : Ctx b s) {p : Reg} (hp : s.gpr p = A)
    (hp3 : p ≠ .t3 := by decide) (hp6 : p ≠ .t6 := by decide) (hp1 : p ≠ .a1 := by decide)
    (hal : A.toNat % 8 = 0) (hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    {o : Nat} (ho : o + 32 ≤ 2048) (ho8 : o % 8 = 0) :
    WP isa (.block (copyIn p o)) s fun s' =>
      Ctx b s' ∧ Rest [.t3, .t6, .a1, .a4] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      d4 s'.mem (b + BitVec.ofNat 64 o) = d4 s.mem A := by
  unfold copyIn
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  refine wp_ld (off := 0) (a := A + BitVec.ofNat 64 0) (by decide) (by rw [hp]) (al8 hal (by decide)) h0
    fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := A + BitVec.ofNat 64 8) (by decide) (by rw [u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u1.rd, u1.wr]; exact h1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := A + BitVec.ofNat 64 16) (by decide) (by rw [u2.other _ hp6, u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact h2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := A + BitVec.ofNat 64 24) (by decide)
    (by rw [u3.other _ hp1, u2.other _ hp6, u1.other _ hp3, hp])
    (al8 hal (by decide)) (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h3) fun s4 u4 => ?_
  have r4 : Rest [.t3, .t6, .a1, .a4] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hc4 : Ctx b s4 := hc.of_rest r4 (by decide)
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have v0 : s4.gpr .t3 = s.mem.readW (A + BitVec.ofNat 64 0) 64 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have v1 : s4.gpr .t6 = s.mem.readW (A + BitVec.ofNat 64 8) 64 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]
  have v2 : s4.gpr .a1 = s.mem.readW (A + BitVec.ofNat 64 16) 64 := by
    rw [u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]
  have v3 : s4.gpr .a4 = s.mem.readW (A + BitVec.ofNat 64 24) 64 := by
    rw [u4.gpr, u3.mem, u2.mem, u1.mem]
  refine sd_ok hc4 (d := o) (by omega) ho8 fun s5 u5 => ?_
  have hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine sd_ok hc5 (d := o + 8) (by omega) (by omega) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine sd_ok hc6 (d := o + 16) (by omega) (by omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine sd_ok hc7 (d := o + 24) (by omega) (by omega) fun s8 u8 => WP.block_nil ?_
  have g8 : s8.gpr = s4.gpr := by rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr]
  have hm : s8.mem = (((s.mem.writeW (b + BitVec.ofNat 64 o) (s4.gpr .t3)).writeW
      (b + BitVec.ofNat 64 (o + 8)) (s4.gpr .t6)).writeW (b + BitVec.ofNat 64 (o + 16)) (s4.gpr .a1)).writeW
      (b + BitVec.ofNat 64 (o + 24)) (s4.gpr .a4) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4, u7.gpr, u6.gpr, u5.gpr]
  have r48 : Rest [] s4 s8 := ⟨fun r _ => by rw [g8], by rw [u8.rd, u7.rd, u6.rd, u5.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr], by rw [u8.sp, u7.sp, u6.sp, u5.sp]⟩
  refine ⟨hc4.of_rest r48 (by decide), r4.trans (r48.mono (by decide)), ?_, ?_⟩
  · rw [hm]
    have c : ∀ k < 4, (⟨b + BitVec.ofNat 64 o, 32⟩ : Region).Contains (b + BitVec.ofNat 64 (o + 8 * k)) 8 :=
      fun k hk => Offset.contains b (by omega) (by omega) (by omega)
    have c0 := c 0 (by decide)
    have c1 := c 1 (by decide)
    have c2 := c 2 (by decide)
    have c3 := c 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3
  · have e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    have r : ∀ k, dw s8.mem (b + BitVec.ofNat 64 o) k = dw s8.mem b (o + k) := fun k => by
      simp only [dw, e]
    simp only [d4, r, Nat.add_zero]
    rw [hm, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self,
      dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_write_self, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self, dw_write_self,
      v0, v1, v2, v3]
    rfl

open VG.Proof.X25519.RISCV64.R64 (val4 V_eq4 accW accW_eq product_ok square_ok AR)
open VG.Impl.X25519.RISCV64.R64 (product square)

/-- The four doublewords at `b + o`, as offsets from `b`. -/
theorem d4_add (m : Mem) (b : Addr) (o : Nat) :
    d4 m (b + BitVec.ofNat 64 o) = val4 (fun i => dw m b (o + 8 * i)) := by
  have e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simp only [d4, val4, dw, e, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  omega

/-- The number `V` of X25519's code at `b + o`. -/
theorem V_d4 (m : Mem) (b : Addr) (o : Nat) : V m b o = d4 m (b + BitVec.ofNat 64 o) := by
  rw [V_eq4, d4_add]

/-- The product's words, as `reduce` reads them. -/
theorem accW_prodV (m : Mem) (b : Addr) : accW ACC m b 8 = prodV m b := by
  rw [accW_eq]
  simp only [VG.Proof.X448.RISCV64.R64.colsV, prodV, upW, T, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
  omega

theorem d4_lt (m : Mem) (O : Addr) : d4 m O < 2 ^ 256 := by
  have := dw_lt m O 0; have := dw_lt m O 8; have := dw_lt m O 16; have := dw_lt m O 24
  unfold d4; omega

/-- `b + o` from `W`, for `b = W + e`. -/
theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The four doublewords at `W + x`, through a frame of a region apart from them. -/
theorem d4_frame {m m' : Mem} {W : Addr} {e k x : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, k⟩] m m')
    (hd : x + 32 ≤ e ∨ e + k ≤ x) (hx : x + 32 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    d4 m' (W + BitVec.ofNat 64 x) = d4 m (W + BitVec.ofNat 64 x) := by
  rw [d4_add, d4_add]
  simp only [val4]
  have g : ∀ i < 4, dw m' W (x + 8 * i) = dw m W (x + 8 * i) := fun i hi =>
    dw_frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint W (by omega) (by omega) he
  rw [g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide)]

/-- The working space at `W`, its own area from `W + 2048`, and `a3` its base. -/
structure WsAt (W : Addr) (s : State) : Prop where
  al : W.toNat % 8 = 0
  wr : (⟨W, 8192⟩ : Region) ∈ s.wr
  fit : W.toNat + 8192 ≤ 2 ^ 64
  a3 : s.gpr .a3 = W + BitVec.ofNat 64 2048

theorem WsAt.ctx {W : Addr} {s : State} (h : WsAt W s) : Ctx (W + BitVec.ofNat 64 2048) s :=
  ⟨h.a3, al8 h.al (by decide), fun d n hd => by
    rw [off_add]; exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega) (by omega)⟩

theorem WsAt.of_rest {W : Addr} {s s' : State} {ws : List Reg} (h : WsAt W s) (hr : Rest ws s s')
    (h3 : Reg.a3 ∉ ws) : WsAt W s' :=
  ⟨h.al, by rw [hr.wr]; exact h.wr, h.fit, by rw [hr.gpr _ h3, h.a3]⟩

/-- A pointer to the `32` bytes at `W + x` of the working space. -/
theorem WsAt.inR {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 32 ≤ 8192) :
    ∀ j < 4, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  obtain ⟨r, hr, hc⟩ := VG.Proof.X25519.RISCV64.in_base (n := 8) h.wr (d := x + 8 * j) (by omega) (by omega)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem WsAt.inW {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 32 ≤ 8192) :
    ∀ j < 4, InRegions s.wr (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega) (by omega)

/-- The regions `mulCore` writes, from `W`: the copies, the product and the result. -/
abbrev mulW (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 3840, 32⟩, ⟨W + BitVec.ofNat 64 3872, 32⟩, ⟨W + BitVec.ofNat 64 3904, 64⟩,
    ⟨W + BitVec.ofNat 64 o, 32⟩]

/-- An operand apart from the copies and the product. -/
abbrev Apart (x : Nat) : Prop := x + 32 ≤ 3840 ∨ 3968 ≤ x

theorem P_pos : 0 < P := by unfold P; omega

/-- `mulCore`: `[t2] = [t4] [t5] 2⁻²⁵⁶ mod p`. -/
theorem mulCore_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 32 ≤ 8192) (hb : bb + 32 ≤ 8192) (ho : o + 32 ≤ 8192) (hdb : Apart bb)
    (hB : d4 s.mem (W + BitVec.ofNat 64 bb) < P) :
    WP isa mulCore s fun s' =>
      d4 s'.mem (W + BitVec.ofNat 64 o) < P ∧
      d4 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 256 % P =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) % P ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hw.ctx
  have alA : (W + BitVec.ofNat 64 a).toNat % 8 = 0 := al8 hw.al ha8
  have alB : (W + BitVec.ofNat 64 bb).toNat % 8 = 0 := al8 hw.al hb8
  have eMA : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MA = W + BitVec.ofNat 64 3840 := off_add _ _ _
  have eMB : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MB = W + BitVec.ofNat 64 3872 := off_add _ _ _
  have eAC : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 ACC = W + BitVec.ofNat 64 3904 := off_add _ _ _
  -- The product at `ACC`, by either branch.
  have hprod : WP isa (.ite (.eq .t4 .t5) (.block (copyIn .t4 MA ++ square ACC MA))
      (.block (copyIn .t4 MA ++ copyIn .t5 MB ++ product ACC MA MB))) s fun s' =>
      Ctx (W + BitVec.ofNat 64 2048) s' ∧ Rest clob64 s s' ∧ Frame (mulW W o) s.mem s'.mem ∧
      prodV s'.mem (W + BitVec.ofNat 64 2048) =
        d4 s.mem (W + BitVec.ofNat 64 a) * d4 s.mem (W + BitVec.ofNat 64 bb) := by
    refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun heq => ?_) (fun _ => ?_)
    · have hab : W + BitVec.ofNat 64 a = W + BitVec.ofNat 64 bb := by
        rw [← h4, ← h5]; exact beq_iff_eq.mp heq
      refine WP.block_append (WP.mono (copyIn_ok hc (p := .t4) h4 (hal := alA) (hr := hw.inR ha) (o := MA) (ho := by decide) (ho8 := by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
      refine WP.mono (square_ok (acc := ACC) (x := MA) (by decide) (by decide) (by decide) (by decide) c1)
        fun s2 ⟨c2, r2, f2, v2⟩ => ⟨c2, (r1.mono (by decide)).trans r2, ?_, ?_⟩
      · rw [eMA] at f1
        simp only [AR, eAC] at f2
        exact (f1.mono (by simp)).trans (f2.mono (by simp))
      · rw [← accW_prodV, v2, V_d4, v1, ← hab]
    · refine WP.block_append (WP.block_append (WP.mono
        (copyIn_ok hc (p := .t4) h4 (hal := alA) (hr := hw.inR ha) (o := MA) (ho := by decide) (ho8 := by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => WP.mono (copyIn_ok c1 (p := .t5) (by rw [r1.gpr _ (by decide), h5]) (hal := alB)
          (hr := (hw.of_rest r1 (by decide)).inR hb) (o := MB) (ho := by decide) (ho8 := by decide))
        fun s2 ⟨c2, r2, f2, v2⟩ => ?_))
      refine WP.mono (product_ok (acc := ACC) (x := MA) (y := MB) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) c2) fun s3 ⟨c3, r3, f3, v3⟩ => ⟨c3, ((r1.trans r2).mono (by decide)).trans r3, ?_, ?_⟩
      · rw [eMA] at f1
        rw [eMB] at f2
        simp only [AR, eAC] at f3
        exact ((f1.mono (by simp)).trans (f2.mono (by simp))).trans (f3.mono (by simp))
      · rw [eMA] at f1 v1
        rw [eMB] at f2 v2
        rw [← accW_prodV, v3, V_d4, V_d4, eMA, eMB, v2, d4_frame f1 (by unfold Apart at hdb; omega) (by omega)
          (by omega), d4_frame f2 (by omega) (by omega) (by omega), v1]
  refine WP.seq (WP.mono hprod fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
  refine WP.block_append (WP.mono (reduce_ok c1) fun s2 ⟨c2, r2, m2, x2, Q, hQ, hv2⟩ => ?_)
  have hw2 : WsAt W s2 := hw.of_rest (r1.trans r2) (by decide)
  have hlt : prodV s1.mem (W + BitVec.ofNat 64 2048) < 2 ^ 256 * P := by
    rw [v1]
    exact Nat.mul_lt_mul_of_lt_of_le (d4_lt _ _) (Nat.le_of_lt hB) P_pos
  have hx : v4 s2 X0 X1 X2 X3 + 2 ^ 256 * (s2.gpr XC).toNat < 2 * P := by
    simp only [v4]
    generalize (s2.gpr X0).toNat + 2 ^ 64 * (s2.gpr X1).toNat + 2 ^ 128 * (s2.gpr X2).toNat +
      2 ^ 192 * (s2.gpr X3).toNat + 2 ^ 256 * (s2.gpr XC).toNat = x at hv2 ⊢
    have h1 : Q * P < 2 ^ 256 * P := Nat.mul_lt_mul_of_pos_right hQ P_pos
    have h2 : x * 2 ^ 256 < 2 * P * 2 ^ 256 := by
      rw [hv2]
      calc _ < 2 ^ 256 * P + 2 ^ 256 * P := Nat.add_lt_add hlt h1
        _ = 2 * P * 2 ^ 256 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 256) P, Nat.mul_assoc]
    exact Nat.lt_of_mul_lt_mul_right h2
  refine WP.mono (csub_ok (O := W + BitVec.ofNat 64 o) (by rw [(r1.trans r2).gpr _ (by decide), h2])
    (al8 hw.al ho8) (hw2.inW ho) x2 hx) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_
  have hm2 : s2.mem = s1.mem := m2
  rw [hm2] at f3
  refine ⟨by rw [v3]; exact Nat.mod_lt _ (by decide), ?_, f1.trans (f3.mono (by simp)), fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v3, Nat.mod_mul_mod]
    simp only [v4] at hv2 ⊢
    rw [hv2, Nat.add_mul_mod_self_right, v1]
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    have s6 : ∀ x ∈ clob64, x ∈ clobM := by decide
    rw [g3 r (fun h => hr (sC r h)), (r1.trans r2).gpr r (fun h => hr (s6 r h))]
  · rw [rd3, r2.rd, r1.rd]
  · rw [wr3, r2.wr, r1.wr]
  · rw [sp3, r2.sp, r1.sp]

end VG.Proof.Weierstrass.RISCV64.P256Field
