module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common

/-!
# ML-DSA on PPC64LE: calling the samplers, `Power2Round` and the packing

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_rej_ntt_poly`,
`vg_mldsa_rej_bounded_poly`, `vg_mldsa_power2round`,
`vg_mldsa_simple_bit_pack` and `vg_mldsa_bit_pack`. An integer argument is
moved to the whole register; the callees read its low word (`imm32`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v :=
  VG.Proof.MlDsa.PPC64LE.Arith.setWidth32_ofNat (imm_toNat (by omega)) h

theorem imm32_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem argOk_imm {v : Nat} (h : v < 2 ^ 31) : argOk (.imm v) = true := by
  simp only [argOk, decide_eq_true_eq]; exact h

/-! ## `vg_mldsa_rej_ntt_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr}

abbrev rnArgs (sd a w : Ptr) : List (Reg × Arg) := [(.r3, .ptr sd), (.r4, .ptr a), (.r5, .ptr w)]
abbrev rnRd (L : Lay) (sd : Ptr) : List Region := [L.R (ix sd.1) sd.2 34]
abbrev rnWr (L : Lay) (a w : Ptr) : List Region := [L.R (ix a.1) a.2 1024, L.R (ix w.1) w.2 2048]

/-- The facts `vg_mldsa_rej_ntt_poly` needs of its pointers. -/
structure RnOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : PtrIn L sd 34
  pa : PtrIn L a 1024
  pw : PtrIn L w 2048
  wa : ix a.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri sd 34) (tri a 1024) = true
  d2 : sepB L.sizes (tri sd 34) (tri w 2048) = true
  d3 : sepB L.sizes (tri a 1024) (tri w 2048) = true

theorem RnOk.hg (m : RnOk L Wb sd a w) : glueOk (rnArgs sd a w) = true := by
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1]

theorem rnArgs_nodup : ((rnArgs sd a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem rn_vg {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) (rd wr : List Region) :
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r3 = lpa L sd ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r4 = lpa L a ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .r5 = lpa L w :=
  ⟨hs.vG m.hg rnArgs_nodup (by simp) m.ps.1 (by decide) _ _, hs.vG m.hg rnArgs_nodup (by simp) m.pa.1 (by decide) _ _,
    hs.vG m.hg rnArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem rn_cov {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) :
    Covers (rnRd L sd ++ rnWr L a w) (s.rd ++ s.wr) ∧ Covers (rnWr L a w) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ps) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil))),
    Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem rn_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RnOk L Wb sd a w) :
    (rejNTTContract PPC64LE.abi stk).pre (view (glueSt s (rnArgs sd a w)) (rnRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rnArgs sd a w) (rnRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5⟩ := rn_vg hs m (rnRd L sd) (rnWr L a w)
  exact rejNtt_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))

theorem rn_ok {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .r3).setWidth 32)
        (polyAt s'.mem (lpa L a)) → Q s') :
    WP isa (callAt name c (rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rn_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, -⟩ := rn_vg hs m (rnRd L sd) (rnWr L a w)
    have := rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, view_glue_mem] at this
  exacts [this.1, this.2]

theorem rn_tr {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RnOk L Wb sd a w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L sd) 34 = bytesAt y.mem (lpa L sd) 34) :
    RelCT isa P (callAt name c (rnArgs sd a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := rn_vg hx m (rnRd L sd) (rnWr L a w)
  obtain ⟨gy3, gy4, gy5⟩ := rn_vg hy m (rnRd L sd) (rnWr L a w)
  refine ⟨rnRd L sd, rnWr L a w, rn_preS hx (Nat.le_trans hstk hS) m, rn_preS hy (Nat.le_trans hstk hS) m,
    rejNtt_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]) ?_,
    (rn_cov hx m).1, (rn_cov hx m).2, (rn_cov hy m).1, (rn_cov hy m).2⟩
  rw [gx3, gy3, view_glue_mem, view_glue_mem]
  exact hl

end

/-! ## `vg_mldsa_rej_bounded_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr} {η : Nat}

abbrev rbArgs (sd : Ptr) (η : Nat) (a w : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr sd), (.r4, .imm η), (.r5, .ptr a), (.r6, .ptr w)]
abbrev rbRd (L : Lay) (sd : Ptr) : List Region := [L.R (ix sd.1) sd.2 66]

/-- The facts `vg_mldsa_rej_bounded_poly` needs of its pointers. -/
structure RbOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : PtrIn L sd 66
  pa : PtrIn L a 1024
  pw : PtrIn L w 2048
  wa : ix a.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri sd 66) (tri a 1024) = true
  d2 : sepB L.sizes (tri sd 66) (tri w 2048) = true
  d3 : sepB L.sizes (tri a 1024) (tri w 2048) = true

theorem RbOk.hg (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) : glueOk (rbArgs sd η a w) = true := by
  have : argOk (.imm η) = true := argOk_imm (by omega)
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1, this]

theorem rbArgs_nodup : ((rbArgs sd η a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem rb_vg {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) (rd wr : List Region) :
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r3 = lpa L sd ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r4 = BitVec.ofNat 64 η ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r5 = lpa L a ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .r6 = lpa L w :=
  ⟨hs.vG (m.hg hη) rbArgs_nodup (by simp) m.ps.1 (by decide) _ _, vI (m.hg hη) rbArgs_nodup (by simp) (by decide) _ _,
    hs.vG (m.hg hη) rbArgs_nodup (by simp) m.pa.1 (by decide) _ _,
    hs.vG (m.hg hη) rbArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem rb_cov {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) :
    Covers (rbRd L sd ++ rnWr L a w) (s.rd ++ s.wr) ∧ Covers (rnWr L a w) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ps) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil))),
    Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem rb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RbOk L Wb sd a w)
    (hη : η = 2 ∨ η = 4) :
    (rejBoundedContract PPC64LE.abi stk).pre (view (glueSt s (rbArgs sd η a w)) (rbRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rbArgs sd η a w) (rbRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5, g6⟩ := rb_vg hs m hη (rbRd L sd) (rnWr L a w)
  have e4 : ((view (glueSt s (rbArgs sd η a w)) (rbRd L sd) (rnWr L a w)).gpr .r4).setWidth 32 = BitVec.ofNat 32 η := by
    rw [g4]; exact imm32 (by omega)
  exact rejBounded_pre g3 e4 g5 g6 rfl rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [imm32_toNat (by omega)]; exact hη)

theorem rb_ok {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => (rejBoundedPoly η b.rejBounded (bytesAt s.mem (lpa L sd) 66)).map toRq)
        ((s'.gpr .r3).setWidth 32) (polyAt s'.mem (lpa L a)) → Q s') :
    WP isa (callAt name c (rbArgs sd η a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rb_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) (m.hg hη) (rb_preS hs (Nat.le_trans hstk hS) m hη) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, -⟩ := rb_vg hs m hη (rbRd L sd) (rnWr L a w)
    have := rejBounded_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, view_glue_mem, imm32 (by omega),
      imm32_toNat (by omega)] at this
  exacts [this.1, this.2]

theorem rb_tr {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      rejBoundedLeak η (bytesAt x.mem (lpa L sd) 66) = rejBoundedLeak η (bytesAt y.mem (lpa L sd) 66)) :
    RelCT isa P (callAt name c (rbArgs sd η a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (m.hg hη) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := rb_vg hx m hη (rbRd L sd) (rnWr L a w)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := rb_vg hy m hη (rbRd L sd) (rnWr L a w)
  refine ⟨rbRd L sd, rnWr L a w, rb_preS hx (Nat.le_trans hstk hS) m hη, rb_preS hy (Nat.le_trans hstk hS) m hη,
    rejBounded_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) (by rw [gx6, gy6]) ?_, (rb_cov hx m).1, (rb_cov hx m).2, (rb_cov hy m).1, (rb_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm32 (by omega), imm32_toNat (by omega)]
  exact hl

end

/-! ## `vg_mldsa_power2round` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t t1 t0 : Ptr}

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.r3, .ptr t), (.r4, .ptr t1), (.r5, .ptr t0)]
abbrev p2rRd (L : Lay) (t : Ptr) : List Region := [L.R (ix t.1) t.2 1024]
abbrev p2rWr (L : Lay) (t1 t0 : Ptr) : List Region := [L.R (ix t1.1) t1.2 1024, L.R (ix t0.1) t0.2 1024]

/-- The facts `vg_mldsa_power2round` needs of its pointers. -/
structure P2rOk (L : Lay) (Wb : List Nat) (t t1 t0 : Ptr) : Prop where
  pt : PtrIn L t 1024
  p1 : PtrIn L t1 1024
  p0 : PtrIn L t0 1024
  w1 : ix t1.1 ∈ Wb
  w0 : ix t0.1 ∈ Wb
  d1 : sepB L.sizes (tri t 1024) (tri t1 1024) = true
  d2 : sepB L.sizes (tri t 1024) (tri t0 1024) = true
  d3 : sepB L.sizes (tri t1 1024) (tri t0 1024) = true

theorem P2rOk.hg (m : P2rOk L Wb t t1 t0) : glueOk (p2rArgs t t1 t0) = true := by
  simp [glueOk, argReg, m.pt.1, m.p1.1, m.p0.1]

theorem p2rArgs_nodup : ((p2rArgs t t1 t0).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem p2r_vg {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) (rd wr : List Region) :
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r3 = lpa L t ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r4 = lpa L t1 ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .r5 = lpa L t0 :=
  ⟨hs.vG m.hg p2rArgs_nodup (by simp) m.pt.1 (by decide) _ _, hs.vG m.hg p2rArgs_nodup (by simp) m.p1.1 (by decide) _ _,
    hs.vG m.hg p2rArgs_nodup (by simp) m.p0.1 (by decide) _ _⟩

theorem p2r_cov {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) :
    Covers (p2rRd L t ++ p2rWr L t1 t0) (s.rd ++ s.wr) ∧ Covers (p2rWr L t1 t0) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pt) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.p1 m.w1) (Covers.cons (hs.cwE m.p0 m.w0) Covers.nil))),
    Covers.cons (hs.cwE m.p1 m.w1) (Covers.cons (hs.cwE m.p0 m.w0) Covers.nil)⟩

theorem p2r_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : P2rOk L Wb t t1 t0)
    (hr : Reduced s.mem (lpa L t)) :
    (power2RoundContract PPC64LE.abi stk).pre (view (glueSt s (p2rArgs t t1 t0)) (p2rRd L t) (p2rWr L t1 t0)) := by
  have hsp := view_glue_sp s (p2rArgs t t1 t0) (p2rRd L t) (p2rWr L t1 t0)
  obtain ⟨g3, g4, g5⟩ := p2r_vg hs m (p2rRd L t) (p2rWr L t1 t0)
  refine p2r_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.w1))
    (hs.dE m.d2 (.inr m.w0)) (hs.dE m.d3 (.inl m.w1)) (hs.kE m.pt hstk hsp) (hs.kE m.p1 hstk hsp)
    (hs.kE m.p0 hstk hsp) (hs.fitE m.pt (by decide)) (hs.fitE m.p1 (by decide)) (hs.fitE m.p0 (by decide)) ?_
  rw [view_glue_mem]; exact hr

theorem p2r_ok {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : P2rOk L Wb t t1 t0) (hr : Reduced s.mem (lpa L t))
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri t1 1024, tri t0 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L t1) ((polyAt s.mem (lpa L t)).map fun c => (power2Round c).1.toNat) →
      PolyIs s'.mem (lpa L t0) ((polyAt s.mem (lpa L t)).map fun c => ofInt (power2Round c).2) → Q s') :
    WP isa (callAt name c (p2rArgs t t1 t0)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := p2r_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (p2r_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri t1 1024, tri t0 1024] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5⟩ := p2r_vg hs m (p2rRd L t) (p2rWr L t1 t0)
    have := p2r_post hp
    rw [State.withRegions_mem, g3, g4, g5, view_glue_mem] at this
  exacts [this.1, this.2]

theorem p2r_tr {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : P2rOk L Wb t t1 t0) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L t) ∧
      Reduced y.mem (lpa L t)) :
    RelCT isa P (callAt name c (p2rArgs t t1 t0)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := p2r_vg hx m (p2rRd L t) (p2rWr L t1 t0)
  obtain ⟨gy3, gy4, gy5⟩ := p2r_vg hy m (p2rRd L t) (p2rWr L t1 t0)
  exact ⟨p2rRd L t, p2rWr L t1 t0, p2r_preS hx (Nat.le_trans hstk hS) m rx, p2r_preS hy (Nat.le_trans hstk hS) m ry,
    p2r_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (p2r_cov hx m).1, (p2r_cov hx m).2, (p2r_cov hy m).1, (p2r_cov hy m).2⟩

end

/-! ## `vg_mldsa_simple_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {b l : Nat}

abbrev sbpArgs (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr f), (.r4, .imm b), (.r5, .ptr o), (.r6, .imm l)]
abbrev sbpRd (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]
abbrev sbpWr (L : Lay) (o : Ptr) (l : Nat) : List Region := [L.R (ix o.1) o.2 l]

/-- The facts `vg_mldsa_simple_bit_pack` needs of its arguments. -/
structure SbpOk (L : Lay) (Wb : List Nat) (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : PtrIn L f 1024
  po : PtrIn L o l
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri o l) = true
  hb : b ∈ simpleBitPackBounds
  hl : l = 32 * bitlen b

theorem SbpOk.lt (m : SbpOk L Wb f b o l) : b < 2 ^ 31 ∧ 0 < l ∧ l < 2 ^ 31 := by
  have hb := m.hb
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [m.hl]
  rcases hb with rfl | rfl | rfl <;> decide

theorem SbpOk.hg (m : SbpOk L Wb f b o l) : glueOk (sbpArgs f b o l) = true := by
  have h1 : argOk (.imm b) = true := argOk_imm m.lt.1
  have h2 : argOk (.imm l) = true := argOk_imm m.lt.2.2
  simp [glueOk, argReg, m.pf.1, m.po.1, h1, h2]

theorem sbpArgs_nodup : ((sbpArgs f b o l).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem sbp_vg {s : State} (hs : Site L Wb STK s) (m : SbpOk L Wb f b o l) (rd wr : List Region) :
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r3 = lpa L f ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r4 = BitVec.ofNat 64 b ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r5 = lpa L o ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .r6 = BitVec.ofNat 64 l :=
  ⟨hs.vG m.hg sbpArgs_nodup (by simp) m.pf.1 (by decide) _ _, vI m.hg sbpArgs_nodup (by simp) (by decide) _ _,
    hs.vG m.hg sbpArgs_nodup (by simp) m.po.1 (by decide) _ _, vI m.hg sbpArgs_nodup (by simp) (by decide) _ _⟩

theorem sbp_cov {s : State} (hs : Site L Wb STK s) (m : SbpOk L Wb f b o l) :
    Covers (sbpRd L f ++ sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (sbpWr L o l) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pf) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)),
    Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem sbp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : SbpOk L Wb f b o l)
    (hc : ∀ i < n, (coeffAt s.mem (lpa L f) i).toNat ≤ b) :
    (simpleBitPackContract PPC64LE.abi stk).pre (view (glueSt s (sbpArgs f b o l)) (sbpRd L f) (sbpWr L o l)) := by
  have hsp := view_glue_sp s (sbpArgs f b o l) (sbpRd L f) (sbpWr L o l)
  obtain ⟨g3, g4, g5, g6⟩ := sbp_vg hs m (sbpRd L f) (sbpWr L o l)
  obtain ⟨lb, l0, ll⟩ := m.lt
  have e4 : ((view (glueSt s (sbpArgs f b o l)) (sbpRd L f) (sbpWr L o l)).gpr .r4).setWidth 32 = BitVec.ofNat 32 b := by
    rw [g4]; exact imm32 (by omega)
  refine sbp_pre g3 e4 g5 g6 rfl (by rw [State.withRegions_wr, imm_toNat (by omega)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ (hs.kE m.pf hstk hsp) ?_ (hs.fitE m.pf (by decide))
    (by rw [imm_toNat (by omega)]; exact hs.fitE m.po l0)
    (by rw [imm32_toNat (by omega)]; exact m.hb) (by rw [imm_toNat (by omega), imm32_toNat (by omega)]; exact m.hl) ?_
  · rw [imm_toNat (by omega)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [imm_toNat (by omega)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, imm32_toNat (by omega)]; exact hc

theorem sbp_ok {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : SbpOk L Wb f b o l)
    (hcf : ∀ i < n, (coeffAt s.mem (lpa L f) i).toNat ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L o) l = simpleBitPack (natPolyAt s.mem (lpa L f)) b → Q s') :
    WP isa (callAt name c (sbpArgs f b o l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := sbp_cov hs m
  obtain ⟨lb, l0, ll⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (sbp_preS hs (Nat.le_trans hstk hS) m hcf) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o l] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6⟩ := sbp_vg hs m (sbpRd L f) (sbpWr L o l)
  have := sbp_post hp
  rwa [State.withRegions_mem, g3, g4, g5, g6, view_glue_mem, imm32 (by omega), imm32_toNat (by omega),
    imm_toNat (by omega)] at this

theorem sbp_tr {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : SbpOk L Wb f b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      (∀ i < n, (coeffAt x.mem (lpa L f) i).toNat ≤ b) ∧ (∀ i < n, (coeffAt y.mem (lpa L f) i).toNat ≤ b)) :
    RelCT isa P (callAt name c (sbpArgs f b o l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := sbp_vg hx m (sbpRd L f) (sbpWr L o l)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := sbp_vg hy m (sbpRd L f) (sbpWr L o l)
  exact ⟨sbpRd L f, sbpWr L o l, sbp_preS hx (Nat.le_trans hstk hS) m rx, sbp_preS hy (Nat.le_trans hstk hS) m ry,
    sbp_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (sbp_cov hx m).1, (sbp_cov hx m).2, (sbp_cov hy m).1, (sbp_cov hy m).2⟩

end

/-! ## `vg_mldsa_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {a b l : Nat}

abbrev bpArgs (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr f), (.r4, .imm a), (.r5, .imm b), (.r6, .ptr o), (.r7, .imm l)]

/-- The facts `vg_mldsa_bit_pack` needs of its arguments. -/
structure BpOk (L : Lay) (Wb : List Nat) (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : PtrIn L f 1024
  po : PtrIn L o l
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri o l) = true
  hab : (a, b) ∈ bitPackParams
  hl : l = 32 * bitlen (a + b)

theorem BpOk.lt (m : BpOk L Wb f a b o l) : a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ 0 < l ∧ l < 2 ^ 31 := by
  have hab := m.hab
  simp only [bitPackParams, d, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rw [m.hl]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem BpOk.hg (m : BpOk L Wb f a b o l) : glueOk (bpArgs f a b o l) = true := by
  obtain ⟨la, lb, -, ll⟩ := m.lt
  have h1 : argOk (.imm a) = true := argOk_imm la
  have h2 : argOk (.imm b) = true := argOk_imm lb
  have h3 : argOk (.imm l) = true := argOk_imm ll
  simp [glueOk, argReg, m.pf.1, m.po.1, h1, h2, h3]

theorem bpArgs_nodup : ((bpArgs f a b o l).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem bp_vg {s : State} (hs : Site L Wb STK s) (m : BpOk L Wb f a b o l) (rd wr : List Region) :
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .r3 = lpa L f ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .r4 = BitVec.ofNat 64 a ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .r5 = BitVec.ofNat 64 b ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .r6 = lpa L o ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .r7 = BitVec.ofNat 64 l :=
  ⟨hs.vG m.hg bpArgs_nodup (by simp) m.pf.1 (by decide) _ _, vI m.hg bpArgs_nodup (by simp) (by decide) _ _,
    vI m.hg bpArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg bpArgs_nodup (by simp) m.po.1 (by decide) _ _,
    vI m.hg bpArgs_nodup (by simp) (by decide) _ _⟩

theorem bp_cov {s : State} (hs : Site L Wb STK s) (m : BpOk L Wb f a b o l) :
    Covers (sbpRd L f ++ sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (sbpWr L o l) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pf) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)),
    Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem bp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BpOk L Wb f a b o l)
    (hr : Reduced s.mem (lpa L f))
    (hc : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (lpa L f) i).toNat q ∧
      modPm (coeffAt s.mem (lpa L f) i).toNat q ≤ b) :
    (bitPackContract PPC64LE.abi stk).pre (view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)) := by
  have hsp := view_glue_sp s (bpArgs f a b o l) (sbpRd L f) (sbpWr L o l)
  obtain ⟨g3, g4, g5, g6, g7⟩ := bp_vg hs m (sbpRd L f) (sbpWr L o l)
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have e4 : ((view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)).gpr .r4).setWidth 32 = BitVec.ofNat 32 a := by
    rw [g4]; exact imm32 (by omega)
  have e5 : ((view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)).gpr .r5).setWidth 32 = BitVec.ofNat 32 b := by
    rw [g5]; exact imm32 (by omega)
  refine bp_pre g3 e4 e5 g6 g7 rfl
    (by rw [State.withRegions_wr, imm_toNat (by omega)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_
    (hs.kE m.pf hstk hsp) ?_ (hs.fitE m.pf (by decide)) (by rw [imm_toNat (by omega)]; exact hs.fitE m.po l0)
    (by rw [imm32_toNat (by omega), imm32_toNat (by omega)]; exact m.hab)
    (by rw [imm_toNat (by omega), imm32_toNat (by omega), imm32_toNat (by omega)]; exact m.hl)
    (by rw [view_glue_mem]; exact hr) ?_
  · rw [imm_toNat (by omega)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [imm_toNat (by omega)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, imm32_toNat (by omega), imm32_toNat (by omega)]; exact hc

theorem bp_ok {c : Prog isa} (hc : Callee c (fun stk => bitPackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BpOk L Wb f a b o l)
    (hr : Reduced s.mem (lpa L f))
    (hcf : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (lpa L f) i).toNat q ∧
      modPm (coeffAt s.mem (lpa L f) i).toNat q ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L o) l = bitPack ((polyAt s.mem (lpa L f)).map fun c => modPm c.val q) a b → Q s') :
    WP isa (callAt name c (bpArgs f a b o l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bp_cov hs m
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (bp_preS hs (Nat.le_trans hstk hS) m hr hcf) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o l] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6, g7⟩ := bp_vg hs m (sbpRd L f) (sbpWr L o l)
  have := bp_post hp
  rwa [State.withRegions_mem, g3, g4, g5, g6, g7, view_glue_mem, imm32 (by omega), imm32 (by omega),
    imm32_toNat (by omega), imm32_toNat (by omega), imm_toNat (by omega)] at this

theorem bp_tr {c : Prog isa} (hc : Callee c (fun stk => bitPackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BpOk L Wb f a b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt x.mem (lpa L f) i).toNat q ∧
        modPm (coeffAt x.mem (lpa L f) i).toNat q ≤ b) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt y.mem (lpa L f) i).toNat q ∧
        modPm (coeffAt y.mem (lpa L f) i).toNat q ≤ b)) :
    RelCT isa P (callAt name c (bpArgs f a b o l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry, cx, cy⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := bp_vg hx m (sbpRd L f) (sbpWr L o l)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := bp_vg hy m (sbpRd L f) (sbpWr L o l)
  exact ⟨sbpRd L f, sbpWr L o l, bp_preS hx (Nat.le_trans hstk hS) m rx cx, bp_preS hy (Nat.le_trans hstk hS) m ry cy,
    bp_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]), (bp_cov hx m).1, (bp_cov hx m).2, (bp_cov hy m).1, (bp_cov hy m).2⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
