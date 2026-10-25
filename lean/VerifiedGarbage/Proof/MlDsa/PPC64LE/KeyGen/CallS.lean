module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallSP
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.ContractsS
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
import VerifiedGarbage.Proof.Framework.Covers

/-!
# ML-DSA on PPC64LE: calling the primitives only signing uses

As `ip_ok` and `ip_tr` (`Call.lean`), in the buffers of a `Site`:
`vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_expand_mask_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr} {g1 : Nat}

abbrev emArgs (sd : Ptr) (g1 : Nat) (a w : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr sd), (.r4, .imm g1), (.r5, .ptr a), (.r6, .ptr w)]

theorem em_hg (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) : glueOk (emArgs sd g1 a w) = true := by
  have : argOk (.imm g1) = true := argOk_imm (by omega_arith)
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1, this]

theorem emArgs_nodup : ((emArgs sd g1 a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem em_vg {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19)
    (rd wr : List Region) :
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r3 = lpa L sd ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r4 = BitVec.ofNat 64 g1 ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r5 = lpa L a ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r6 = lpa L w :=
  ⟨hs.vG (em_hg m hg) emArgs_nodup (by simp) m.ps.1 (by decide) _ _,
    vI (em_hg m hg) emArgs_nodup (by simp) (by decide) _ _,
    hs.vG (em_hg m hg) emArgs_nodup (by simp) m.pa.1 (by decide) _ _,
    hs.vG (em_hg m hg) emArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem em_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RbOk L Wb sd a w)
    (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) :
    (expandMaskContract PPC64LE.abi stk).pre (view (glueSt s (emArgs sd g1 a w)) (rbRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (emArgs sd g1 a w) (rbRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5, g6⟩ := em_vg hs m hg (rbRd L sd) (rnWr L a w)
  have e4 : ((view (glueSt s (emArgs sd g1 a w)) (rbRd L sd) (rnWr L a w)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g1 := by
    rw [g4]; exact imm32 (by omega_arith)
  exact em_pre g3 e4 g5 g6 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [imm32_toNat (by omega_arith)]; exact hg)

theorem em_ok {c : Prog isa} (hc : Callee c (fun stk => expandMaskContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L a) (toRq (bitUnpack (H (bytesAt s.mem (lpa L sd) 66) (32 * (1 + bitlen (g1 - 1))))
        (g1 - 1) g1)) → Q s') :
    WP isa (callAt name c (emArgs sd g1 a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rb_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) (em_hg m hg) (em_preS hs (Nat.le_trans hstk hS) m hg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, -⟩ := em_vg hs m hg (rbRd L sd) (rnWr L a w)
  have := em_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith)] at this

theorem em_tr {c : Prog isa} (hc : Callee c (fun stk => expandMaskContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (emArgs sd g1 a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (em_hg m hg) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := em_vg hx m hg (rbRd L sd) (rnWr L a w)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := em_vg hy m hg (rbRd L sd) (rnWr L a w)
  exact ⟨rbRd L sd, rnWr L a w, em_preS hx (Nat.le_trans hstk hS) m hg, em_preS hy (Nat.le_trans hstk hS) m hg,
    em_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (rb_cov hx m).1, (rb_cov hx m).2, (rb_cov hy m).1, (rb_cov hy m).2⟩

end

/-! ## `vg_mldsa_high_bits`, `vg_mldsa_low_bits` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {r o : Ptr} {g2 : Nat}

abbrev bitsArgs (r : Ptr) (g2 : Nat) (o : Ptr) : List (Reg × Arg) := [(.r3, .ptr r), (.r4, .imm g2), (.r5, .ptr o)]
abbrev bitsRd (L : Lay) (r : Ptr) : List Region := [L.R (ix r.1) r.2 1024]
abbrev bitsWr (L : Lay) (o : Ptr) : List Region := [L.R (ix o.1) o.2 1024]

/-- The facts `vg_mldsa_high_bits` and `vg_mldsa_low_bits` need of their arguments. -/
structure BitsOk (L : Lay) (Wb : List Nat) (r : Ptr) (g2 : Nat) (o : Ptr) : Prop where
  pr : PtrIn L r 1024
  po : PtrIn L o 1024
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri r 1024) (tri o 1024) = true
  hg : g2 ∈ gamma2s
  lt : g2 < 2 ^ 31

theorem BitsOk.hg' (m : BitsOk L Wb r g2 o) : glueOk (bitsArgs r g2 o) = true := by
  have h1 : argOk (.imm g2) = true := argOk_imm m.lt
  simp [glueOk, argReg, m.pr.1, m.po.1, h1]

theorem bitsArgs_nodup : ((bitsArgs r g2 o).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem bits_vg {s : State} (hs : Site L Wb STK s) (m : BitsOk L Wb r g2 o) (rd wr : List Region) :
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r3 = lpa L r ∧
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r4 = BitVec.ofNat 64 g2 ∧
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r5 = lpa L o :=
  ⟨hs.vG m.hg' bitsArgs_nodup (by simp) m.pr.1 (by decide) _ _, vI m.hg' bitsArgs_nodup (by simp) (by decide) _ _,
    hs.vG m.hg' bitsArgs_nodup (by simp) m.po.1 (by decide) _ _⟩

theorem bits_cov {s : State} (hs : Site L Wb STK s) (m : BitsOk L Wb r g2 o) :
    Covers (bitsRd L r ++ bitsWr L o) (s.rd ++ s.wr) ∧ Covers (bitsWr L o) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pr) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)),
    Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem hb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (highBitsContract PPC64LE.abi stk).pre (view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)) := by
  have hsp := view_glue_sp s (bitsArgs r g2 o) (bitsRd L r) (bitsWr L o)
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have e4 : ((view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g4]; exact imm32 (by have := m.lt; omega_arith)
  refine hb_pre g3 e4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wo))
    (hs.kE m.pr hstk hsp) (hs.kE m.po hstk hsp) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_
  rw [view_glue_mem]; exact hr

theorem lb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (lowBitsContract PPC64LE.abi stk).pre (view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)) := by
  have hsp := view_glue_sp s (bitsArgs r g2 o) (bitsRd L r) (bitsWr L o)
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have e4 : ((view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g4]; exact imm32 (by have := m.lt; omega_arith)
  refine lb_pre g3 e4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wo))
    (hs.kE m.pr hstk hsp) (hs.kE m.po hstk hsp) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_
  rw [view_glue_mem]; exact hr

theorem hb_ok {c : Prog isa} (hc : Callee c (fun stk => highBitsContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L o) ((polyAt s.mem (lpa L r)).map fun c => (highBits g2 c).toNat) → Q s') :
    WP isa (callAt name c (bitsArgs r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bits_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (hb_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have := hb_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by have := m.lt; omega_arith),
    imm32_toNat (by have := m.lt; omega_arith)] at this

theorem lb_ok {c : Prog isa} (hc : Callee c (fun stk => lowBitsContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L o) ((polyAt s.mem (lpa L r)).map fun c => ofInt (lowBits g2 c)) → Q s') :
    WP isa (callAt name c (bitsArgs r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bits_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (lb_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have := lb_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by have := m.lt; omega_arith),
    imm32_toNat (by have := m.lt; omega_arith)] at this

theorem hb_tr {c : Prog isa} (hc : Callee c (fun stk => highBitsContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BitsOk L Wb r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (bitsArgs r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := bits_vg hx m (bitsRd L r) (bitsWr L o)
  obtain ⟨gy3, gy4, gy5⟩ := bits_vg hy m (bitsRd L r) (bitsWr L o)
  exact ⟨bitsRd L r, bitsWr L o, hb_preS hx (Nat.le_trans hstk hS) m rx, hb_preS hy (Nat.le_trans hstk hS) m ry,
    hb_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (bits_cov hx m).1, (bits_cov hx m).2, (bits_cov hy m).1, (bits_cov hy m).2⟩

theorem lb_tr {c : Prog isa} (hc : Callee c (fun stk => lowBitsContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BitsOk L Wb r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (bitsArgs r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := bits_vg hx m (bitsRd L r) (bitsWr L o)
  obtain ⟨gy3, gy4, gy5⟩ := bits_vg hy m (bitsRd L r) (bitsWr L o)
  exact ⟨bitsRd L r, bitsWr L o, lb_preS hx (Nat.le_trans hstk hS) m rx, lb_preS hy (Nat.le_trans hstk hS) m ry,
    lb_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (bits_cov hx m).1, (bits_cov hx m).2, (bits_cov hy m).1, (bits_cov hy m).2⟩

end

/-! ## `vg_mldsa_make_hint` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {z r h : Ptr} {g2 : Nat}

abbrev mhArgs (z r : Ptr) (g2 : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr z), (.r4, .ptr r), (.r5, .imm g2), (.r6, .ptr h)]

theorem mh_vg {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb z r g2 h) (rd wr : List Region) :
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r3 = lpa L z ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r4 = lpa L r ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r5 = BitVec.ofNat 64 g2 ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r6 = lpa L h :=
  uh_vg hs m rd wr

theorem mh_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : UhOk L Wb z r g2 h)
    (hz : Reduced s.mem (lpa L z)) (hr : Reduced s.mem (lpa L r)) :
    (makeHintContract PPC64LE.abi stk).pre (view (glueSt s (mhArgs z r g2 h)) (uhRd L z r) (uhWr L h)) := by
  have hsp := view_glue_sp s (mhArgs z r g2 h) (uhRd L z r) (uhWr L h)
  obtain ⟨g3, g4, g5, g6⟩ := mh_vg hs m (uhRd L z r) (uhWr L h)
  have e5 : ((view (glueSt s (mhArgs z r g2 h)) (uhRd L z r) (uhWr L h)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g5]; exact imm32 (by have := m.lt; omega_arith)
  refine mh_pre g3 g4 e5 g6 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    (hs.dE m.d1 (.inr m.wo)) (hs.dE m.d2 (.inr m.wo)) (hs.kE m.ph hstk hsp) (hs.kE m.pr hstk hsp)
    (hs.kE m.po hstk hsp) (hs.fitE m.ph (by decide)) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_ ?_
  · rw [view_glue_mem]; exact hz
  · rw [view_glue_mem]; exact hr

theorem mh_ok {c : Prog isa} (hc : Callee c (fun stk => makeHintContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : UhOk L Wb z r g2 h)
    (hz : Reduced s.mem (lpa L z)) (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      HintIs s'.mem (lpa L h) 1 [Vector.zipWith (makeHint g2) (polyAt s.mem (lpa L z)) (polyAt s.mem (lpa L r))] →
      ((s'.gpr .r3).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint g2) (polyAt s.mem (lpa L z)) (polyAt s.mem (lpa L r))] → Q s') :
    WP isa (callAt name c (mhArgs z r g2 h)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := uh_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (mh_preS hs (Nat.le_trans hstk hS) m hz hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6⟩ := mh_vg hs m (uhRd L z r) (uhWr L h)
    have := mh_post hp
    rw [g3, g4, g5, g6, view_glue_mem, State.withRegions_mem, State.withRegions_gpr, imm32 (by have := m.lt; omega_arith),
      imm32_toNat (by have := m.lt; omega_arith)] at this
  exacts [this.1, this.2]

theorem mh_tr {c : Prog isa} (hc : Callee c (fun stk => makeHintContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : UhOk L Wb z r g2 h) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L z) ∧
      Reduced x.mem (lpa L r) ∧ Reduced y.mem (lpa L z) ∧ Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (mhArgs z r g2 h)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxz, rxr, ryz, ryr⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := mh_vg hx m (uhRd L z r) (uhWr L h)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := mh_vg hy m (uhRd L z r) (uhWr L h)
  exact ⟨uhRd L z r, uhWr L h, mh_preS hx (Nat.le_trans hstk hS) m rxz rxr,
    mh_preS hy (Nat.le_trans hstk hS) m ryz ryr,
    mh_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (uh_cov hx m).1, (uh_cov hx m).2, (uh_cov hy m).1, (uh_cov hy m).2⟩

end

/-! ## `vg_mldsa_hint_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h y : Ptr} {hl om len : Nat}

abbrev hbpArgs (h : Ptr) (hl om : Nat) (y : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr h), (.r4, .imm hl), (.r5, .imm om), (.r6, .ptr y), (.r7, .imm len)]
abbrev hbpRd (L : Lay) (h : Ptr) (hl : Nat) : List Region := [L.R (ix h.1) h.2 (hl * 4)]
abbrev hbpWr (L : Lay) (y : Ptr) (len : Nat) : List Region := [L.R (ix y.1) y.2 len]

/-- The facts `vg_mldsa_hint_bit_pack` needs of its arguments. -/
structure HbpOk (L : Lay) (Wb : List Nat) (h : Ptr) (hl om : Nat) (y : Ptr) (len : Nat) : Prop where
  ph : PtrIn L h (hl * 4)
  py : PtrIn L y len
  wy : ix y.1 ∈ Wb
  d1 : sepB L.sizes (tri h (hl * 4)) (tri y len) = true
  hp : (om, len - om) ∈ hintParams
  ho : om ≤ len
  hh : hl = 256 * (len - om)
  lt : 0 < len ∧ len < 2 ^ 31 ∧ om < 2 ^ 31 ∧ 0 < hl * 4 ∧ hl < 2 ^ 31

theorem HbpOk.hg (m : HbpOk L Wb h hl om y len) : glueOk (hbpArgs h hl om y len) = true := by
  obtain ⟨-, l1, l2, -, l4⟩ := m.lt
  have h1 : argOk (.imm hl) = true := argOk_imm l4
  have h2 : argOk (.imm om) = true := argOk_imm l2
  have h3 : argOk (.imm len) = true := argOk_imm l1
  simp [glueOk, argReg, m.ph.1, m.py.1, h1, h2, h3]

theorem hbpArgs_nodup : ((hbpArgs h hl om y len).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem hbp_vg {s : State} (hs : Site L Wb STK s) (m : HbpOk L Wb h hl om y len) (rd wr : List Region) :
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r3 = lpa L h ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r4 = BitVec.ofNat 64 hl ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r5 = BitVec.ofNat 64 om ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r6 = lpa L y ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r7 = BitVec.ofNat 64 len :=
  ⟨hs.vG m.hg hbpArgs_nodup (by simp) m.ph.1 (by decide) _ _, vI m.hg hbpArgs_nodup (by simp) (by decide) _ _,
    vI m.hg hbpArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg hbpArgs_nodup (by simp) m.py.1 (by decide) _ _,
    vI m.hg hbpArgs_nodup (by simp) (by decide) _ _⟩

theorem hbp_cov {s : State} (hs : Site L Wb STK s) (m : HbpOk L Wb h hl om y len) :
    Covers (hbpRd L h hl ++ hbpWr L y len) (s.rd ++ s.wr) ∧ Covers (hbpWr L y len) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ph) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.py m.wy) Covers.nil)),
    Covers.cons (hs.cwE m.py m.wy) Covers.nil⟩

theorem hbp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : HbpOk L Wb h hl om y len)
    (hc : hintOnes (hintAt s.mem (lpa L h) (len - om)) ≤ om) :
    (hintBitPackContract PPC64LE.abi stk).pre
      (view (glueSt s (hbpArgs h hl om y len)) (hbpRd L h hl) (hbpWr L y len)) := by
  have hsp := view_glue_sp s (hbpArgs h hl om y len) (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨g3, g4, g5, g6, g7⟩ := hbp_vg hs m (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have e5 : ((view (glueSt s (hbpArgs h hl om y len)) (hbpRd L h hl) (hbpWr L y len)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 om := by
    rw [g5]; exact imm32 (by omega_arith)
  refine hbp_pre g3 g4 e5 g6 g7 (by rw [State.withRegions_rd, imm_toNat (by omega_arith)])
    (by rw [State.withRegions_wr, imm_toNat (by omega_arith)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_
    (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.ph h0) (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.py l0)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hp)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.ho)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hh)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith), view_glue_mem]; exact hc)
  · rw [imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wy)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.ph hstk hsp
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.py hstk hsp

theorem hbp_ok {c : Prog isa} (hc : Callee c (fun stk => hintBitPackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : HbpOk L Wb h hl om y len)
    (hcn : hintOnes (hintAt s.mem (lpa L h) (len - om)) ≤ om) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri y len, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L y) len = hintBitPack om (len - om) (hintAt s.mem (lpa L h) (len - om)) → Q s') :
    WP isa (callAt name c (hbpArgs h hl om y len)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := hbp_cov hs m
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (hbp_preS hs (Nat.le_trans hstk hS) m hcn) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri y len] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6, g7⟩ := hbp_vg hs m (hbpRd L h hl) (hbpWr L y len)
  have := hbp_post hp
  rwa [g3, g5, g6, g7, view_glue_mem, State.withRegions_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith),
    imm_toNat (by omega_arith)] at this

theorem hbp_tr {c : Prog isa} (hc : Callee c (fun stk => hintBitPackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : HbpOk L Wb h hl om y len) {P : State → State → Prop}
    (hP : ∀ x y', P x y' → Site L Wb STK x ∧ Site L Wb STK y' ∧ x.sp = y'.sp ∧
      hintOnes (hintAt x.mem (lpa L h) (len - om)) ≤ om ∧ hintOnes (hintAt y'.mem (lpa L h) (len - om)) ≤ om ∧
      (List.range hl).map (fun i => (coeffAt x.mem (lpa L h) i).toNat) =
        (List.range hl).map (fun i => (coeffAt y'.mem (lpa L h) i).toNat)) :
    RelCT isa P (callAt name c (hbpArgs h hl om y len)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV_tr hver.1 hver.2.1 m.hg fun x y' hxy => ?_
  obtain ⟨hx, hy, hsp, cx, cy, hl'⟩ := hP x y' hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := hbp_vg hx m (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := hbp_vg hy m (hbpRd L h hl) (hbpWr L y len)
  refine ⟨hbpRd L h hl, hbpWr L y len, hbp_preS hx (Nat.le_trans hstk hS) m cx, hbp_preS hy (Nat.le_trans hstk hS) m cy,
    hbp_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (hbp_cov hx m).1, (hbp_cov hx m).2, (hbp_cov hy m).1,
    (hbp_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm_toNat (by omega_arith)]
  exact hl'

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
